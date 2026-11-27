import Alvoki.Experiments.DurableBlob.Native
import Std.WP
import Std.Tactic.Do
import Lean

namespace DurableBlob

/-- Only the active name and bytes it can select after power loss are observable.
The staging fields are private scratch bookkeeping. Only a completed write,
flush and sync in the current publication can supply the next active bytes. -/
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

private def Image.recordWrite (bytes : ByteArray) (image : Image) : Image :=
  {image with written := some bytes, synced := none}

private def Image.syncWriter (image : Image) : Image :=
  {image with synced := image.written}

private def Image.replace (image : Image) : Image :=
  match image.synced with
  | none => image  -- unreachable after a successful staging sync
  | some bytes => ⟨bytes, bytes :: image.survivors, none, none⟩

private def model (report : Operation → Report) (readOK : Bool) :
    Files (EStateM Unit Image) Unit where
  writeStaged bytes := perform (report .writeStaged) (Image.recordWrite bytes)
  syncStaged _ := perform (report .syncStaged) Image.syncWriter
  renameStaged := perform (report .renameStaged) Image.replace
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

private abbrev M := EStateM Unit Image

/-- Exact outcomes in the existing disk projection. A late error keeps the
effect and a pre-effect error keeps the input. -/
private def Effect (result : EStateM.Result Unit Image α) (value : α)
    (before after : Image) : Prop :=
  match result with
  | .ok returned reached => returned = value ∧ reached = after
  | .error _ reached => reached = before ∨ reached = after

private theorem perform_effect (report : Report) (change : Image → Image) (s : Image) :
    Effect (perform report change s) () s (change s) := by
  cases report <;> simp [perform, Effect]

/-- Success returns the writer for this call. Sync is specified at that
writer. Stable exclusive bindings justify interpreting rename on its bytes. -/
structure FileEffects (files : Files M writer) (held : writer) : Prop where
  write : ∀ bytes s, Effect (files.writeStaged bytes s) held s (s.recordWrite bytes)
  sync : ∀ s, Effect (files.syncStaged held s) () s s.syncWriter
  rename : ∀ s, Effect (files.renameStaged s) () s s.replace
  barrier : ∀ s, Effect (files.syncDirectory s) () s s.barrier
  read : ∀ s, Effect (files.readActive s) s.active s s

private theorem modelEffects (report : Operation → Report) (readOK : Bool) :
    FileEffects (model report readOK) () where
  write _ _ := perform_effect _ _ _
  sync _ := perform_effect _ _ _
  rename _ := perform_effect _ _ _
  barrier _ := perform_effect _ _ _
  read _ := by cases readOK <;> simp [model, Effect]

open Std.WP Lean.Order
set_option experimental.vcgen true

/-- Adequacy for the same EStateM result consumed by Run. -/
private def Post (result : EStateM.Result Unit Image α) (ok : α → Image → Prop)
    (failed : Image → Prop) : Prop :=
  match result with
  | .ok value reached => ok value reached
  | .error _ reached => failed reached

private theorem triple_iff (action : M α) (P : Image → Prop)
    (Q : α → Image → Prop) (F : Image → Prop) :
    (⦃P⦄ action ⦃Q; fun _ => F⦄) ↔ ∀ s, P s → Post (action s) Q F := by
  constructor
  · intro ⟨h⟩ s pre
    have reached := h s pre
    cases ran : action s <;> simpa [wp, WP.trans, ran, Post] using reached
  · intro h
    refine ⟨fun s pre => ?_⟩
    have reached := h s pre
    cases ran : action s <;> simpa [wp, WP.trans, ran, Post] using reached

private theorem effectSpec {action : M α} {value : α}
    (localEffect : Effect (action before) value before after) :
    ⦃fun s => s = before⦄ action
    ⦃fun v s => v = value ∧ s = after; fun _ s => s = before ∨ s = after⦄ := by
  rw [triple_iff]
  intro s same
  subst s
  cases ran : action before <;> simpa only [ran, Effect, Post] using localEffect

private def PublishCut (before : Image) (bytes : ByteArray) (s : Image) : Prop :=
  let staged := before.recordWrite bytes
  let synced := staged.syncWriter
  let renamed := synced.replace
  s = before ∨ s = staged ∨ s = synced ∨ s = renamed ∨ s = renamed.barrier

private theorem publish_spec (effects : FileEffects files held) (before : Image) (bytes : ByteArray) :
    ⦃fun s => s = before⦄ files.backend.publish bytes
    ⦃fun _ s => s = ((before.recordWrite bytes).syncWriter.replace).barrier;
      fun _ => PublishCut before bytes⦄ := by
  have write {s : Image} := effectSpec (effects.write bytes s)
  have sync (writer : _) {s : Image} :
      ⦃fun t => writer = held ∧ t = s⦄ files.syncStaged writer
      ⦃fun _ t => t = s.syncWriter; fun _ t => t = s ∨ t = s.syncWriter⦄ := by
    rw [triple_iff]
    rintro t ⟨sameWriter, sameState⟩
    subst writer
    subst t
    have localProof := effects.sync s
    cases ran : files.syncStaged held s <;> simp [ran, Effect, Post] at localProof ⊢ <;> exact localProof
  have rename {s : Image} := effectSpec (effects.rename s)
  have barrier {s : Image} := effectSpec (effects.barrier s)
  simp only [Files.backend]
  vcgen [write, sync, rename, barrier] <;> grind [PublishCut]

private theorem reopen_spec (effects : FileEffects files held) (before : Image) :
    ⦃fun s => s = before⦄ files.backend.reopen
    ⦃fun value s => value = before.active ∧ s = before.barrier;
      fun _ s => s = before ∨ s = before.barrier⦄ := by
  have read {s : Image} := effectSpec (effects.read s)
  have barrier {s : Image} := effectSpec (effects.barrier s)
  simp only [Files.backend]
  vcgen [read, barrier] <;> grind

theorem publish_stable (effects : FileEffects files held) (before : Image) (bytes : ByteArray) :
    Post (files.backend.publish bytes before) (fun _ s => s.Stable bytes)
      (PublishCut before bytes) := by
  have post := (triple_iff _ _ _ _).mp (publish_spec effects before bytes) before rfl
  cases ran : files.backend.publish bytes before with
  | error => simpa only [ran, Post] using post
  | ok _ s =>
    simp only [ran, Post] at post ⊢
    rw [post]
    simp [Image.Stable, Image.recordWrite, Image.syncWriter, Image.replace, Image.barrier]

private theorem publish_outcome (effects : FileEffects files held) (image : Image)
    (stable : image.Stable old) (proposed : ByteArray) :
    Post (files.backend.publish proposed image) (fun _ s => s.Stable proposed)
      (fun s => s.Admits old (some proposed)) := by
  have effect := publish_stable effects image proposed
  cases ran : files.backend.publish proposed image with
  | ok => simpa only [ran, Post] using effect
  | error _ s =>
    simp only [ran, Post] at effect ⊢
    obtain ⟨active, survivors⟩ := stable
    rcases (show PublishCut image proposed s from effect) with h | h | h | h | h <;>
      rw [h] <;>
      simp [Image.Admits, Permitted, Image.recordWrite, Image.syncWriter, Image.replace,
        Image.barrier, active, survivors]

theorem reopen_binding (effects : FileEffects files held) (before : Image) :
    Post (files.backend.reopen before)
      (fun bytes s => bytes = before.active ∧ s.Stable bytes)
      (fun s => s = before ∨ s = before.barrier) := by
  have post := (triple_iff _ _ _ _).mp (reopen_spec effects before) before rfl
  cases ran : files.backend.reopen before with
  | error => simpa only [ran, Post] using post
  | ok value s =>
    simp only [ran, Post] at post ⊢
    obtain ⟨rfl, rfl⟩ := post
    exact ⟨rfl, rfl, rfl⟩

private theorem reopen_outcome (effects : FileEffects files held) (image : Image)
    (admitted : image.Admits old pending) :
    Post (files.backend.reopen image)
      (fun value s => Permitted old pending value ∧ s.Stable value)
      (fun s => s.Admits old pending) := by
  have post := reopen_binding effects image
  cases ran : files.backend.reopen image with
  | error _ s =>
    simp only [ran, Post] at post ⊢
    rcases (show s = image ∨ s = image.barrier from post) with rfl | rfl
    · exact admitted
    · exact ⟨admitted.1, by simpa [Image.barrier] using admitted.1⟩
  | ok value s =>
    simp only [ran, Post] at post ⊢
    exact ⟨post.1.symm ▸ admitted.1, post.2⟩

/-- Executions of the shared protocol with primitive reports. A process stop
leaves the live image; power loss independently selects an admitted image.
Losing the reply of a completed publication is also an uncertain outcome. -/
inductive Run (initial : ByteArray) : List (Event ByteArray) → Bool → Image → Prop where
  | initial : Run initial [] false (.settled initial)
  | publishedWith : Run initial events true before → FileEffects files held →
      files.backend.publish bytes before = .ok () after →
      Run initial (events ++ [.published bytes]) true after
  | uncertainWith : Run initial events true before → FileEffects files held →
      files.backend.publish bytes before = result →
      Run initial (events ++ [.uncertain bytes]) false (match result with | .ok _ after | .error _ after => after)
  | openedWith : Run initial events false before → FileEffects files held →
      files.backend.reopen before = .ok bytes after →
      Run initial (events ++ [.opened bytes]) true after
  | openFailedWith : Run initial events false before → FileEffects files held →
      files.backend.reopen before = .error () after →
      Run initial (events ++ [.openFailed]) false after
  | reopenInterruptedWith : Run initial events false before → FileEffects files held →
      files.backend.reopen before = result →
      Run initial (events ++ [.stop]) false (match result with | .ok _ after | .error _ after => after)
  | stop : Run initial events online before →
      Run initial (events ++ [.stop]) false before
  | crash : Run initial events online before → bytes ∈ before.survivors →
      Run initial (events ++ [.stop]) false (.settled bytes)

namespace LinuxEffects

open System

/-- Abstract identities of the held directory and private writer. The
owner's stable namespace and descriptor lifetime justify using these
identities through one call. -/
inductive Handle where
  | directory
  | writer

structure Reports where
  readActive : Bool
  openDirectory : Bool
  syncDirectory : Report
  openWriter : Bool
  write : Bool
  flush : Bool
  syncWriter : Report
  rename : Report

private def checked (ok : Bool) (value : α) : M α :=
  fun image => if ok then .ok value image else .error () image

/-- Local observations of the filesystem, interpreted at the supplied path
or held description. Errors outside the reserved namespace are irrelevant
to this adapter, but this interpreter rejects such calls. -/
def primitives (directory : FilePath) (reports : Reports) : Primitives M Handle where
  openFile path mode := match mode with
    | .read => checked (path == directory && reports.openDirectory) .directory
    | .write => checked (path == directory / "BLOB.next" && reports.openWriter) .writer
    | _ => checked false .writer
  write
    | .writer, bytes => perform (if reports.write then .ok else .beforeEffect)
        (Image.recordWrite bytes)
    | .directory, _ => checked false ()
  flush
    | .writer => checked reports.flush ()
    | .directory => checked false ()
  sync
    | .directory => perform reports.syncDirectory Image.barrier
    | .writer => perform reports.syncWriter Image.syncWriter
  rename source target :=
    if source == directory / "BLOB.next" && target == directory / "BLOB" then
      perform reports.rename Image.replace
    else checked false ()
  read path := fun image =>
    checked (path == directory / "BLOB" && reports.readActive) image.active image

def backend (directory : FilePath) (reports : Reports) : Backend M ByteArray :=
  (primitives directory reports).backend directory

private theorem fileEffects (directory : FilePath) (reports : Reports) :
    FileEffects ((primitives directory reports).files directory (primitives directory reports).sync) .writer where
  write bytes s := by
    cases o : reports.openWriter <;> cases w : reports.write <;> cases f : reports.flush <;>
      simp [Primitives.files, primitives, checked, perform, Effect, o, w, f,
        Bind.bind, EStateM.bind, Pure.pure, EStateM.pure]
  sync s := perform_effect reports.syncWriter Image.syncWriter s
  rename s := by
    simpa [Primitives.files, primitives] using perform_effect reports.rename Image.replace s
  barrier s := by
    cases o : reports.openDirectory
    · simp [Primitives.files, primitives, checked, Effect, o, Bind.bind, EStateM.bind]
    · simpa [Primitives.files, primitives, checked, o, Bind.bind, EStateM.bind] using
        perform_effect reports.syncDirectory Image.barrier s
  read s := by
    cases r : reports.readActive <;> simp [Primitives.files, primitives, checked, Effect, r]

/-- Continue the public component trace with the result of the very same
reopen body used by `native`, interpreted with Linux primitive effects. -/
theorem reopen (directory : FilePath) (reports : Reports)
    (prior : Run initial events false before) :
    match (backend directory reports).reopen before with
    | .ok bytes after => Run initial (events ++ [.opened bytes]) true after
    | .error _ after => Run initial (events ++ [.openFailed]) false after := by
  split
  next eq => exact .openedWith prior (fileEffects directory reports) eq
  next eq => exact .openFailedWith prior (fileEffects directory reports) eq

/-- A reported success confirms the submitted bytes. Every returned error
keeps the reached image and leaves exactly that proposal pending. -/
theorem publish (directory : FilePath) (reports : Reports) (bytes : ByteArray)
    (prior : Run initial events true before) :
    match (backend directory reports).publish bytes before with
    | .ok _ after => Run initial (events ++ [.published bytes]) true after
    | .error _ after => Run initial (events ++ [.uncertain bytes]) false after := by
  split
  next eq => exact .publishedWith prior (fileEffects directory reports) eq
  next eq => exact .uncertainWith prior (fileEffects directory reports) eq

/-- Loss of the reply keeps the state reached by publication, regardless of
whether the last reached primitive reports success or failure. -/
theorem publishUncertain (directory : FilePath) (reports : Reports) (bytes : ByteArray)
    (prior : Run initial events true before) :
    Run initial (events ++ [.uncertain bytes]) false
      (match (backend directory reports).publish bytes before with
       | .ok _ after | .error _ after => after) := by
  exact .uncertainWith prior (fileEffects directory reports) rfl

/-- An interrupted reopen retains any directory-barrier effect but issues
no ready session. A cutoff is encoded by an error at the first uncompleted
primitive, or by loss of the final reply. -/
theorem reopenInterrupted (directory : FilePath) (reports : Reports)
    (prior : Run initial events false before) :
    Run initial (events ++ [.stop]) false
      (match (backend directory reports).reopen before with
       | .ok _ after | .error _ after => after) := by
  exact .reopenInterruptedWith prior (fileEffects directory reports) rfl

theorem publishUncertainAdmits (directory : FilePath) (reports : Reports)
    (stable : before.Stable old) (proposed : ByteArray) :
    let after := match (backend directory reports).publish proposed before with
      | .ok _ after | .error _ after => after
    Step (.ready old) (.uncertain proposed) (.offline old (some proposed)) ∧
      after.Admits old (some proposed) := by
  have effect := publish_outcome (fileEffects directory reports) before stable proposed
  change Post ((backend directory reports).publish proposed before) _ _ at effect
  cases result : (backend directory reports).publish proposed before with
  | ok _ after =>
    rw [result] at effect
    obtain ⟨active, survivors⟩ := effect
    exact ⟨.uncertain, by simp [Image.Admits, Permitted, active, survivors]⟩
  | error _ after =>
    rw [result] at effect
    exact ⟨.uncertain, effect⟩

/-- Reopen leaves the live binding alone and settles a successful reply. -/
theorem reopenBinding (directory : FilePath) (reports : Reports) (before : Image) :
    match (backend directory reports).reopen before with
    | .ok bytes after => bytes = before.active ∧ after.Stable bytes
    | .error _ after => after.active = before.active := by
  have reached := reopen_binding (fileEffects directory reports) before
  change Post ((backend directory reports).reopen before) _ _ at reached
  split
  next ran => simpa only [ran, Post] using reached
  next ran =>
    simp only [ran, Post] at reached
    rcases reached with rfl | rfl <;> rfl

/-- Even on a reported error, the live binding is the old value or the proposal. -/
theorem publishActive (directory : FilePath) (reports : Reports) (before : Image)
    (proposed : ByteArray) :
    match (backend directory reports).publish proposed before with
    | .ok _ after => after.Stable proposed
    | .error _ after => Permitted before.active (some proposed) after.active := by
  have reached := publish_stable (fileEffects directory reports) before proposed
  change Post ((backend directory reports).publish proposed before) _ _ at reached
  split
  next ran => simpa only [ran, Post] using reached
  next after ran =>
    simp only [ran, Post] at reached
    rcases (show PublishCut before proposed after from reached) with h | h | h | h | h <;>
      rw [h] <;> simp [Permitted, Image.recordWrite, Image.syncWriter, Image.replace, Image.barrier]

theorem reopenFailedAdmits (directory : FilePath) (reports : Reports)
    (admitted : before.Admits old pending)
    (returned : (backend directory reports).reopen before = .error err after) :
    Step (.offline old pending) .openFailed (.offline old pending) ∧ after.Admits old pending := by
  have outcome := reopen_outcome (fileEffects directory reports) before admitted
  change Post ((backend directory reports).reopen before) _ _ at outcome
  rw [returned] at outcome
  exact ⟨.openFailed, outcome⟩

theorem reopenSettles (directory : FilePath) (reports : Reports)
    (admitted : before.Admits old pending)
    (returned : (backend directory reports).reopen before = .ok bytes after) :
    Step (.offline old pending) (.opened bytes) (.ready bytes) ∧ after.Stable bytes := by
  have outcome := reopen_outcome (fileEffects directory reports) before admitted
  change Post ((backend directory reports).reopen before) _ _ at outcome
  rw [returned] at outcome
  exact ⟨.opened outcome.1, outcome.2⟩

/-- A second successful reopen after a process stop or a power loss returns
the first reply. A power loss selects from the singleton settled binding. -/
theorem reopenAgain (directory : FilePath) (first second : Reports)
    (admitted : before.Admits old pending)
    (opened : (backend directory first).reopen before = .ok bytes settled)
    (restart : rebooted = settled ∨ ∃ survivor ∈ settled.survivors, rebooted = .settled survivor)
    (reopened : (backend directory second).reopen rebooted = .ok again after) :
    again = bytes ∧ after.Stable bytes := by
  have stable := (reopenSettles directory first admitted opened).2
  have bootStable : rebooted.Stable bytes := by
    rcases restart with rfl | ⟨survivor, survived, rfl⟩
    · exact stable
    · have same : survivor = bytes := by simpa [stable.2] using survived
      subst survivor
      exact ⟨rfl, rfl⟩
  have next := reopenSettles directory second (stable_admits (pending := none) bootStable) reopened
  have same : again = bytes := by
    cases next.1 with
    | opened choice => simpa [Permitted] using choice
  exact ⟨same, same ▸ next.2⟩

end LinuxEffects

private def Represents (image : Image) (online : Bool) : State ByteArray → Prop
  | .ready value => online = true ∧ image.Stable value
  | .offline old pending => online = false ∧ image.Admits old pending

theorem Run.refines {initial : ByteArray} (run : Run initial events online image) :
    ∃ state, Allows initial events state ∧ Represents image online state := by
  induction run with
  | initial => exact ⟨_, .initial, rfl, stable_admits ⟨rfl, rfl⟩⟩
  | @publishedWith _ before _ files held bytes after prior effects ran ih =>
    obtain ⟨_ | _, trace, ⟨_, h⟩⟩ := ih
    all_goals try contradiction
    have effect := publish_outcome effects before h bytes
    rw [ran] at effect
    exact ⟨_, trace.next .published, rfl, effect⟩
  | @uncertainWith _ before _ files held bytes result prior effects ran ih =>
    obtain ⟨_ | _, trace, ⟨_, h⟩⟩ := ih
    all_goals try contradiction
    have effect := publish_outcome effects before h bytes
    rw [ran] at effect
    cases result with
    | ok value after =>
      obtain ⟨active, survivors⟩ := effect
      exact ⟨_, trace.next .uncertain, rfl, by simp [Image.Admits, active, survivors, Permitted]⟩
    | error error after => exact ⟨_, trace.next .uncertain, rfl, effect⟩
  | openedWith prior effects ran ih =>
    obtain ⟨_ | _, trace, ⟨_, h⟩⟩ := ih
    all_goals try contradiction
    have effect := reopen_outcome effects _ h
    rw [ran] at effect
    exact ⟨_, trace.next (.opened effect.1), rfl, effect.2⟩
  | openFailedWith prior effects ran ih =>
    obtain ⟨_ | _, trace, ⟨_, h⟩⟩ := ih
    all_goals try contradiction
    have effect := reopen_outcome effects _ h
    rw [ran] at effect
    exact ⟨_, trace.next .openFailed, rfl, effect⟩
  | @reopenInterruptedWith _ before _ files held result prior effects ran ih =>
    obtain ⟨_ | _, trace, ⟨_, h⟩⟩ := ih
    all_goals try contradiction
    have effect := reopen_outcome effects _ h
    rw [ran] at effect
    cases result with
    | ok _ after =>
      obtain ⟨chosen, active, survivors⟩ := effect
      exact ⟨_, trace.next .stopAgain, rfl, by simpa [Image.Admits, active, survivors] using chosen⟩
    | error _ after => exact ⟨_, trace.next .stopAgain, rfl, effect⟩
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

theorem Run.refinesReady {initial : ByteArray} (run : Run initial events true image) :
    Allows initial events (.ready image.active) := by
  obtain ⟨_ | _, allowed, represented⟩ := run.refines
  · rw [represented.2.1]
    exact allowed
  · exact False.elim (Bool.noConfusion represented.1)

theorem Run.healthy_open {initial : ByteArray} (run : Run initial events false image) :
    Run initial (events ++ [.opened image.active]) true image.barrier :=
  .openedWith run (modelEffects (fun _ => .ok) true) rfl

/-- Process exit can expose a renamed but unsettled file. Recovery settles
that binding, so a subsequent power loss cannot restore the previous one. -/
private def recoveryRegression : Bool := Id.run do
  let old := ByteArray.mk #[1]
  let proposed := ByteArray.mk #[2]
  let directory : System.FilePath := "manifest"
  let reports : LinuxEffects.Reports := {
    readActive := true
    openDirectory := true
    syncDirectory := .ok
    openWriter := true
    write := true
    flush := true
    syncWriter := .ok
    rename := .ok
  }
  let interruptedRename := LinuxEffects.backend directory { reports with rename := .afterEffect }
  let .error _ interrupted := interruptedRename.publish proposed (.settled old) | return false
  unless interrupted.active == proposed && interrupted.survivors.any (· == old) do return false
  let barrierError := LinuxEffects.backend directory { reports with syncDirectory := .afterEffect }
  let .error _ settled := barrierError.reopen interrupted | return false
  unless settled.survivors == [proposed] do return false
  let reopen := (LinuxEffects.backend directory reports).reopen
  let .ok retried _ := reopen settled | return false
  unless retried == proposed do return false
  let .ok selected recovered := reopen interrupted | return false
  let [survivor] := recovered.survivors | return false
  let .ok reopened _ := reopen (.settled survivor) | return false
  return selected == proposed && reopened == selected

#guard recoveryRegression

end DurableBlob
