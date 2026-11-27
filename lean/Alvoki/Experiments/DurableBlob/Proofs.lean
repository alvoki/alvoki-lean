import Alvoki.Experiments.DurableBlob.Native

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

private theorem publish_outcome (report : Operation → Report) (image : Image)
    (stable : image.Stable old) (proposed : ByteArray) :
    match (model report true).backend.publish proposed image with
    | .ok _ after => after.Stable proposed
    | .error _ after => after.Admits old (some proposed) := by
  obtain ⟨active, survivors⟩ := stable
  cases rw : report .writeStaged <;> cases rs : report .syncStaged <;>
    cases rr : report .renameStaged <;> cases rd : report .syncDirectory <;>
    simp [Files.backend, model, perform,
      rw, rs, rr, rd, Image.recordWrite, Image.syncWriter, Image.replace, Bind.bind, Pure.pure, EStateM.bind, Image.barrier, Image.Stable, Image.Admits,
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
      (model report readOK).backend.reopen before = result →
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

private abbrev M := EStateM Unit Image

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

private def Reports.directoryEffect (reports : Reports) : Report :=
  if reports.openDirectory then reports.syncDirectory else .beforeEffect

private def Reports.publication (reports : Reports) : Operation → Report
  | .writeStaged =>
    if reports.openWriter && reports.write then
      if reports.flush then .ok else .afterEffect
    else .beforeEffect
  | .syncStaged => reports.syncWriter
  | .renameStaged => reports.rename
  | .syncDirectory => reports.directoryEffect

private theorem reopen_eq (directory : FilePath) (reports : Reports) (before : Image) :
    (backend directory reports).reopen before =
      (model (fun _ => reports.directoryEffect) reports.readActive).backend.reopen before := by
  cases r : reports.readActive <;> cases o : reports.openDirectory <;>
    cases d : reports.syncDirectory <;>
      simp [r, o, d, backend, Primitives.backend, primitives, Primitives.files, Files.backend, checked,
        Reports.directoryEffect, model, perform, Bind.bind, Pure.pure, EStateM.bind, EStateM.pure]

private theorem directory_eq (directory : FilePath) (reports : Reports) (before : Image) :
    ((primitives directory reports).files directory (primitives directory reports).sync).syncDirectory
      before = perform reports.directoryEffect Image.barrier before := by
  cases o : reports.openDirectory <;>
    simp [o, primitives, Primitives.files, checked, Reports.directoryEffect, perform,
      Bind.bind, EStateM.bind]

private theorem stage_eq (directory : FilePath) (reports : Reports) (before : Image)
    (bytes : ByteArray) :
    (((primitives directory reports).files directory (primitives directory reports).sync)
      |>.writeStaged bytes before) =
      match perform (reports.publication .writeStaged) (Image.recordWrite bytes) before with
      | .ok _ after => .ok .writer after
      | .error e after => .error e after := by
  cases o : reports.openWriter <;> cases w : reports.write <;> cases f : reports.flush <;>
    simp [o, w, f, primitives, Primitives.files, checked, Reports.publication, perform,
      Bind.bind, Pure.pure, EStateM.bind, EStateM.pure]

private theorem publish_eq (directory : FilePath) (reports : Reports) (before : Image)
    (bytes : ByteArray) :
    (backend directory reports).publish bytes before =
      (model reports.publication true).backend.publish bytes before := by
  simp only [backend, Primitives.backend, Files.backend, Bind.bind, EStateM.bind, stage_eq, model]
  cases perform (reports.publication .writeStaged) (Image.recordWrite bytes) before with
  | error => rfl
  | ok _ staged =>
    have rename_eq (image : Image) :
        ((primitives directory reports).files directory
          (primitives directory reports).sync).renameStaged image =
            perform reports.rename Image.replace image := by simp [Primitives.files, primitives]
    have sync_eq (image : Image) :
        ((primitives directory reports).files directory
          (primitives directory reports).sync).syncStaged .writer image =
            perform reports.syncWriter Image.syncWriter image := rfl
    simp only [sync_eq, rename_eq, directory_eq, Reports.publication]

/-- Continue the public component trace with the result of the very same
reopen body used by `native`, interpreted with Linux primitive effects. -/
theorem reopen (directory : FilePath) (reports : Reports)
    (prior : Run initial events false before) :
    match (backend directory reports).reopen before with
    | .ok bytes after => Run initial (events ++ [.opened bytes]) true after
    | .error _ after => Run initial (events ++ [.openFailed]) false after := by
  rw [reopen_eq]
  split
  next eq => exact .opened prior eq
  next eq => exact .openFailed prior eq

/-- A reported success confirms the submitted bytes. Every returned error
keeps the reached image and leaves exactly that proposal pending. -/
theorem publish (directory : FilePath) (reports : Reports) (bytes : ByteArray)
    (prior : Run initial events true before) :
    match (backend directory reports).publish bytes before with
    | .ok _ after => Run initial (events ++ [.published bytes]) true after
    | .error _ after => Run initial (events ++ [.uncertain bytes]) false after := by
  rw [publish_eq]
  split
  next eq => exact .published prior eq
  next eq => exact Run.uncertain prior eq

/-- Loss of the reply keeps the state reached by publication, regardless of
whether the last reached primitive reports success or failure. -/
theorem publishUncertain (directory : FilePath) (reports : Reports) (bytes : ByteArray)
    (prior : Run initial events true before) :
    Run initial (events ++ [.uncertain bytes]) false
      (match (backend directory reports).publish bytes before with
       | .ok _ after | .error _ after => after) := by
  rw [publish_eq]
  exact .uncertain prior rfl

/-- An interrupted reopen retains any directory-barrier effect but issues
no ready session. A cutoff is encoded by an error at the first uncompleted
primitive, or by loss of the final reply. -/
theorem reopenInterrupted (directory : FilePath) (reports : Reports)
    (prior : Run initial events false before) :
    Run initial (events ++ [.stop]) false
      (match (backend directory reports).reopen before with
       | .ok _ after | .error _ after => after) := by
  rw [reopen_eq]
  exact .reopenInterrupted prior rfl

theorem reopenSettles (directory : FilePath) (reports : Reports)
    (admitted : before.Admits old pending)
    (returned : (backend directory reports).reopen before = .ok bytes after) :
    Step (.offline old pending) (.opened bytes) (.ready bytes) ∧ after.Stable bytes := by
  rw [reopen_eq] at returned
  have outcome := reopen_outcome (fun _ => reports.directoryEffect) reports.readActive before admitted
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
  | @reopenInterrupted _ before report readOK result _ ran ih =>
    obtain ⟨_ | _, trace, ⟨_, h⟩⟩ := ih
    all_goals try contradiction
    have effect := reopen_outcome report readOK before h
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

theorem Run.healthy_open {initial : ByteArray} (run : Run initial events false image) :
    Run initial (events ++ [.opened image.active]) true image.barrier :=
  .opened (report := fun _ => .ok) (readOK := true) run rfl

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
