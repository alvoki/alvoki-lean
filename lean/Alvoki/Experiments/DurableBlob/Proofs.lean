import Alvoki.Experiments.DurableBlob.Protocol

namespace DurableBlob

/-- Only the active name and bytes it can select after power loss are observable.
The staging field represents exact synced bytes; an unsynced stage cannot be renamed. -/
structure Image where
  active : ByteArray
  survivors : List ByteArray
  written : Option ByteArray := none
  synced : Option ByteArray := none

def Image.settled (bytes : ByteArray) : Image := ⟨bytes, [bytes], none, none⟩

def Image.barrier (image : Image) : Image :=
  { image with survivors := [image.active] }

private inductive Operation where
  | writeStaged
  | syncStaged
  | renameStaged
  | syncDirectory

inductive Report where
  | ok
  | beforeEffect
  | afterEffect

/-- Primitive errors can occur before or after the effect. A partial staging
write is abstracted away: it cannot change the active name or its survivors,
and the next publication overwrites the stage before using it. -/
private def perform (report : Report) (effect : Image → Image) : EStateM Unit Image Unit :=
  fun image => match report with
  | .ok => .ok () (effect image)
  | .beforeEffect => .error () image
  | .afterEffect => .error () (effect image)

private def model (report : Operation → Report) (readOK : Bool) :
    Files (EStateM Unit Image) Unit where
  writeStaged bytes := perform (report .writeStaged)
    fun image => {image with written := some bytes, synced := none}
  syncStaged _ := perform (report .syncStaged)
    fun image => {image with synced := image.written}
  renameStaged := perform (report .renameStaged) fun image =>
    match image.synced with
    | none => image  -- unreachable in the publication schedule
    | some bytes => ⟨bytes, bytes :: image.survivors, none, none⟩
  syncDirectory := perform (report .syncDirectory) Image.barrier
  readActive := fun image => if readOK then .ok image.active image else .error () image

def Image.Admits (image : Image) (known : ByteArray) (pending : Option ByteArray) : Prop :=
  Permitted known pending image.active ∧
    ∀ value ∈ image.survivors, Permitted known pending value

def Image.Stable (image : Image) (value : ByteArray) : Prop :=
  image.active = value ∧ image.survivors = [value]

private theorem stable_admits {image : Image} (h : image.Stable known) : image.Admits known pending := by
  obtain ⟨active, survivors⟩ := h
  simp [Image.Admits, active, survivors, Permitted]

private theorem publish_outcome (report : Operation → Report) (image : Image)
    (stable : image.Stable old) (proposed : ByteArray) :
    match (model report true).backend.publish proposed image with
    | .ok _ after => after.Stable proposed
    | .error _ after => after.Admits old (some proposed) := by
  obtain ⟨active, survivors⟩ := stable
  cases rw : report .writeStaged <;> cases rs : report .syncStaged <;>
    cases rr : report .renameStaged <;> cases rd : report .syncDirectory <;>
    simp [Files.backend, model, perform,
      rw, rs, rr, rd, Bind.bind, Pure.pure, EStateM.bind, Image.barrier, Image.Stable, Image.Admits,
      active, survivors, Permitted]

private theorem reopen_outcome (report : Operation → Report) (readOK : Bool)
    (image : Image) (admitted : image.Admits old pending) :
    match (model report readOK).backend.reopen image with
    | .ok value after => Permitted old pending value ∧ after.Stable value
    | .error _ after => after.Admits old pending := by
  cases readOK <;> cases hr : report .syncDirectory <;>
    simp [Files.backend, model, perform, hr, Bind.bind, Pure.pure, EStateM.bind, EStateM.pure,
      Image.barrier, Image.Stable] <;>
    first | exact admitted | exact admitted.1 | simpa [Image.Admits, Image.barrier] using admitted.1

/-- Executions of the shared protocol with primitive reports. A process stop
leaves the live image; power loss independently selects an admitted image.
Losing the reply of a completed publication is also an uncertain outcome. -/
inductive Run (initial : ByteArray) : List (Event ByteArray) → Bool → Image → Prop where
  | initial : Run initial [] false (.settled initial)
  | published : Run initial events true before →
      (model report true).backend.publish bytes before = .ok () after →
      Run initial (events ++ [.published bytes]) true after
  | uncertain : Run initial events true before →
      (model report true).backend.publish bytes before = result →
      Run initial (events ++ [.uncertain bytes]) false (match result with | .ok _ after | .error _ after => after)
  | opened : Run initial events false before →
      (model report readOK).backend.reopen before = .ok bytes after →
      Run initial (events ++ [.opened bytes]) true after
  | openFailed : Run initial events false before →
      (model report readOK).backend.reopen before = .error () after →
      Run initial (events ++ [.openFailed]) false after
  | reopenInterrupted : Run initial events false before →
      (model report true).backend.reopen before = .ok bytes after →
      Run initial (events ++ [.stop]) false after
  | stop : Run initial events online before →
      Run initial (events ++ [.stop]) false before
  | crash : Run initial events online before → bytes ∈ before.survivors →
      Run initial (events ++ [.stop]) false (.settled bytes)

private def Represents (image : Image) (online : Bool) : State ByteArray → Prop
  | .ready value => online = true ∧ image.Stable value
  | .offline old pending => online = false ∧ image.Admits old pending

theorem Run.refines {initial : ByteArray} (run : Run initial events online image) :
    ∃ state, Allows initial events state ∧ Represents image online state := by
  induction run with
  | initial => exact ⟨_, .initial, rfl, stable_admits ⟨rfl, rfl⟩⟩
  | @published _ before report bytes _ _ ran ih =>
    obtain ⟨_ | _, trace, ⟨_, h⟩⟩ := ih
    all_goals try contradiction
    have effect := publish_outcome report before h bytes
    rw [ran] at effect
    exact ⟨_, trace.next .published, rfl, effect⟩
  | @uncertain _ before report bytes result _ ran ih =>
    obtain ⟨_ | _, trace, ⟨_, h⟩⟩ := ih
    all_goals try contradiction
    have effect := publish_outcome report before h bytes
    rw [ran] at effect
    cases result with
    | ok value after =>
      obtain ⟨active, survivors⟩ := effect
      exact ⟨_, trace.next .uncertain, rfl, by simp [Image.Admits, active, survivors, Permitted]⟩
    | error error after => exact ⟨_, trace.next .uncertain, rfl, effect⟩
  | @opened _ before report readOK _ _ _ ran ih =>
    obtain ⟨_ | _, trace, ⟨_, h⟩⟩ := ih
    all_goals try contradiction
    have effect := reopen_outcome report readOK before h
    rw [ran] at effect
    exact ⟨_, trace.next (.opened effect.1), rfl, effect.2⟩
  | @openFailed _ before report readOK _ _ ran ih =>
    obtain ⟨_ | _, trace, ⟨_, h⟩⟩ := ih
    all_goals try contradiction
    have effect := reopen_outcome report readOK before h
    rw [ran] at effect
    exact ⟨_, trace.next .openFailed, rfl, effect⟩
  | @reopenInterrupted _ before report _ _ _ ran ih =>
    obtain ⟨_ | _, trace, ⟨_, h⟩⟩ := ih
    all_goals try contradiction
    have effect := reopen_outcome report true before h
    rw [ran] at effect
    obtain ⟨chosen, active, survivors⟩ := effect
    exact ⟨_, trace.next .stopAgain, rfl, by simpa [Image.Admits, active, survivors] using chosen⟩
  | stop _ ih =>
    obtain ⟨_ | _, trace, ⟨_, h⟩⟩ := ih
    · exact ⟨_, trace.next .stop, rfl, stable_admits h⟩
    · exact ⟨_, trace.next .stopAgain, rfl, h⟩
  | crash _ survived ih =>
    obtain ⟨_ | _, trace, ⟨_, h⟩⟩ := ih
    · have chosen := (stable_admits (pending := none) h).2 _ survived
      exact ⟨_, trace.next .stop, rfl, by simpa [Image.Admits, Image.settled] using chosen⟩
    · exact ⟨_, trace.next .stopAgain, rfl, by
        simpa [Image.Admits, Image.settled] using h.2 _ survived⟩

theorem Run.healthy_open {initial : ByteArray} (run : Run initial events false image) :
    Run initial (events ++ [.opened image.active]) true image.barrier :=
  .opened (report := fun _ => .ok) (readOK := true) run rfl

/-- Process exit can expose a renamed but unsettled file. Recovery settles
that binding, so a subsequent power loss cannot restore the previous one. -/
private def recoveryRegression : Bool := Id.run do
  let old := ByteArray.mk #[1]
  let proposed := ByteArray.mk #[2]
  let publish := (model (fun
    | .syncDirectory => .beforeEffect
    | _ => .ok) true).backend.publish proposed
  let .error _ interrupted := publish (.settled old) | return false
  unless interrupted.active == proposed && interrupted.survivors.any (· == old) do return false
  let reopen := (model (fun _ => .ok) true).backend.reopen
  let .ok selected recovered := reopen interrupted | return false
  let [survivor] := recovered.survivors | return false
  let .ok reopened _ := reopen (.settled survivor) | return false
  return selected == proposed && reopened == selected

#guard recoveryRegression

end DurableBlob
