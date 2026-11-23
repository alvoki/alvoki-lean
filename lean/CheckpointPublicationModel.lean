import CheckpointPublication
import DiskPublicationModel
import Manifest

namespace Alvoki.Storage.CheckpointPublication

/-- The ordered bytes written by the checkpoint plan. The caller supplies the
same run order to the executable interpreter and to this model. -/
structure RunSet where
  header : Manifest.Checkpoint
  files : List ByteArray

abbrev RunFiles := UInt64 → Nat → Option ByteArray

/-- Guaranteed durable run names and bytes in an already durable directory.
An absent claim means the model makes no assertion about that file. In
particular, an older orphan with an out-of-range index may remain on disk. -/
structure Image where
  manifest : Publication.Image
  durable : RunFiles

/-- Before the run directory barrier, the current attempt's staged writes and
file syncs affect only its unreachable generation. Early persistence of
these files does not change which referenced bytes can be recovered. -/
private structure Pending where
  image : Image
  synced : Nat := 0
  written : Bool := false

private def installRunNames (image : Image) (next : RunSet) : Image :=
  { image with durable := fun generation index =>
      if generation = next.header.generation then next.files[index]? else image.durable generation index }

private def Pending.step (state : Pending) (next : RunSet) (action : Step) : Option Pending :=
  match action with
  | .writeRun index =>
    if index = state.synced ∧ index < next.files.length then
      some { state with written := true }
    else none
  | .syncRun index =>
    if index = state.synced ∧ state.written then
      some { state with synced := state.synced + 1, written := false }
    else none
  | .syncRunsDirectory =>
    if state.synced = next.files.length ∧ !state.written then
      some { state with image := installRunNames state.image next }
    else none
  | .manifest replace =>
    (state.image.manifest.step (Manifest.encode next.header) replace).map fun manifest =>
      { state with image := { state.image with manifest := manifest } }

private def Pending.execute (state : Pending) (next : RunSet) (actions : List Step) : Option Pending :=
  actions.foldlM (fun current action => current.step next action) state

private theorem Pending.execute_append (state : Pending) (next : RunSet) (first rest : List Step) :
    state.execute next (first ++ rest) = (state.execute next first).bind (·.execute next rest) :=
  List.foldlM_append

private theorem Pending.execute_cons (state : Pending) (next : RunSet) (first : Step) (rest : List Step) :
    state.execute next (first :: rest) = (state.step next first).bind (·.execute next rest) :=
  List.foldlM_cons

/-- The cut includes every reported success and can straddle an I/O failure
whose last operation did take effect. Partially written unreachable run files
can be overwritten in the next attempt. -/
def Image.execute (initial : Image) (next : RunSet) (actions : List Step) : Option Image :=
  (Pending.execute ⟨initial, 0, false⟩ next actions).map Pending.image

/-- The new generation may contain orphan files. It must be unreachable both
from the live manifest and from every manifest that could survive a crash. -/
def Image.Unreachable (image : Image) (generation : UInt64) : Prop :=
  ∀ bytes, (image.manifest.active = some bytes ∨ some bytes ∈ image.manifest.crashImages) →
    ∀ header, Manifest.decode bytes = .ok header → header.generation ≠ generation

/-- A manifest names exactly the specified run bytes, with a watermark covered
by the already synced WAL boundary. The specification can relate those bytes
to the abstract state of a particular checkpoint. -/
def Image.Accepts (image : Image) (walSequence : UInt64)
    (expected : Manifest.Checkpoint → List ByteArray → Prop) : Option ByteArray → Prop
  | none => True
  | some bytes => ∃ header files,
      Manifest.decode bytes = .ok header ∧ expected header files ∧ walSequence ≥ header.committed ∧
      header.runCount.toNat = files.length ∧
      ∀ index, index < files.length → image.durable header.generation index = files[index]?

def Image.Valid (image : Image) (walSequence : UInt64)
    (expected : Manifest.Checkpoint → List ByteArray → Prop) : Prop :=
  image.manifest.Valid (image.Accepts walSequence expected)

private theorem runs_prefix (initial : Image) (next : RunSet) (count : Nat)
    (fits : count ≤ next.files.length) :
    Pending.execute ⟨initial, 0, false⟩ next (runSteps count) = some ⟨initial, count, false⟩ := by
  induction count with
  | zero => rfl
  | succ n ih =>
    have smaller : n ≤ next.files.length := Nat.le_trans (Nat.le_succ _) fits
    have inside : n < next.files.length := fits
    rw [show runSteps (n + 1) = runSteps n ++ [.writeRun n, .syncRun n] by
      simp [runSteps, List.range_succ]]
    rw [Pending.execute_append, ih smaller]
    simp [Pending.execute, Pending.step, inside]

private def carriesRunOnly : Step → Prop
  | .writeRun _ | .syncRun _ => True
  | _ => False

private theorem runSteps_only (count : Nat) {action : Step} (present : action ∈ runSteps count) :
    carriesRunOnly action := by
  obtain ⟨_, _, paired⟩ := List.mem_flatMap.mp present
  simp at paired
  rcases paired with rfl | rfl <;> trivial

private theorem run_only_does_not_publish (state : Pending) (next : RunSet) (actions : List Step)
    (only : ∀ action ∈ actions, carriesRunOnly action) {after : Pending}
    (ran : state.execute next actions = some after) : after.image = state.image := by
  induction actions generalizing state after with
  | nil => cases ran; rfl
  | cons action tail ih =>
    have first := only action (List.mem_cons_self ..)
    have rest : ∀ action ∈ tail, carriesRunOnly action := fun action mem => only action (List.mem_cons_of_mem _ mem)
    cases stepped : state.step next action with
    | none => simp [Pending.execute, stepped] at ran
    | some middle =>
      have same : middle.image = state.image := by
        cases action <;> simp [carriesRunOnly] at first
        · simp only [Pending.step] at stepped
          split at stepped
          · cases stepped; rfl
          · contradiction
        · simp only [Pending.step] at stepped
          split at stepped
          · cases stepped; rfl
          · contradiction
      have ranTail : middle.execute next tail = some after := by
        simpa [Pending.execute, stepped] using ran
      exact (ih middle rest ranTail).trans same

private theorem promote_run_names (initial : Image) (next : RunSet) :
    Pending.execute ⟨initial, 0, false⟩ next (runSteps next.files.length ++ [.syncRunsDirectory]) =
      some ⟨installRunNames initial next, next.files.length, false⟩ := by
  rw [Pending.execute_append, runs_prefix initial next _ (Nat.le_refl _)]
  simp [Pending.execute, Pending.step]

private theorem manifest_steps (state : Pending) (next : RunSet) (actions : List Publication.Step) :
    state.execute next (actions.map Step.manifest) =
      (state.image.manifest.execute (Manifest.encode next.header) actions).map
        (fun manifest => { state with image := { state.image with manifest := manifest } }) := by
  induction actions generalizing state with
  | nil => rfl
  | cons action rest ih =>
    simp only [List.map_cons, Pending.execute_cons, Pending.step, Publication.Image.execute, List.foldlM_cons]
    cases applied : state.image.manifest.step (Manifest.encode next.header) action with
    | none => rfl
    | some manifest =>
      simp only [Option.map_some, Option.bind_some]
      exact ih { state with image := { state.image with manifest := manifest } }

private theorem old_names_preserved {old : Image} {next : RunSet} {walSequence : UInt64}
    {expected : Manifest.Checkpoint → List ByteArray → Prop}
    (fresh : old.Unreachable next.header.generation) {candidate : Option ByteArray}
    (selectable : old.manifest.active = candidate ∨ candidate ∈ old.manifest.crashImages)
    (good : old.Accepts walSequence expected candidate) :
    (installRunNames old next).Accepts walSequence expected candidate := by
  cases candidate with
  | none => exact True.intro
  | some bytes =>
    obtain ⟨header, files, decoded, known, covered, length, fileEq⟩ := good
    have disjoint := fresh bytes selectable header decoded
    exact ⟨header, files, decoded, known, covered, length, fun index inside => by
      simpa [installRunNames, disjoint] using fileEq index inside⟩

/-- A crash cut before run-directory sync preserves all old witnesses. After
that sync the new durable run set is complete before any manifest rename. -/
theorem checkpoint_cut_valid {initial after : Image} {next : RunSet} {walSequence : UInt64}
    {expected : Manifest.Checkpoint → List ByteArray → Prop}
    (initialValid : initial.Valid walSequence expected)
    (fresh : initial.Unreachable next.header.generation)
    (covered : next.header.committed ≤ walSequence)
    (floor : next.header.floor ≤ next.header.committed)
    (count : next.header.runCount.toNat = next.files.length)
    (intent : expected next.header next.files)
    (cut : Nat) (ran : initial.execute next ((steps next.files.length).take cut) = some after) :
    after.Valid walSequence expected := by
  let prep := runSteps next.files.length
  let barrier := prep ++ [.syncRunsDirectory]
  have plan : steps next.files.length = barrier ++ Publication.steps.map Step.manifest := rfl
  by_cases early : cut ≤ prep.length
  · have cutSteps : (steps next.files.length).take cut = prep.take cut := by
      rw [plan, show barrier = prep ++ [.syncRunsDirectory] from rfl, List.append_assoc,
        List.take_append_of_le_length early]
    rw [cutSteps] at ran
    unfold Image.execute at ran
    cases result : Pending.execute ⟨initial, 0, false⟩ next (prep.take cut) with
    | none => simp [result] at ran
    | some middle =>
      have imageEq : middle.image = initial := run_only_does_not_publish _ _ _
        (fun _ mem => runSteps_only _ (List.mem_of_mem_take mem)) result
      simp [result, imageEq] at ran
      simpa [← ran] using initialValid
  · have past : barrier.length ≤ cut := by
      simp [barrier]
      omega
    have cutSteps : (steps next.files.length).take cut =
        barrier ++ (Publication.steps.take (cut - barrier.length)).map Step.manifest := by
      rw [plan, List.take_append, List.take_of_length_le past, ← List.map_take]
    rw [cutSteps] at ran
    unfold Image.execute at ran
    rw [Pending.execute_append, show barrier = runSteps next.files.length ++ [.syncRunsDirectory] from rfl,
      promote_run_names, Option.bind_some, manifest_steps, Option.map_map] at ran
    let installed := installRunNames initial next
    let finish := fun manifest : Publication.Image => { installed with manifest := manifest }
    change ((initial.manifest.execute (Manifest.encode next.header)
      (Publication.steps.take (cut - barrier.length))).map finish) = some after at ran
    obtain ⟨manifest, replaced, rfl⟩ := Option.map_eq_some_iff.mp ran
    let accepts := installed.Accepts walSequence expected
    have prior : initial.manifest.Valid accepts := {
      hasCrashImage := initialValid.hasCrashImage
      activeValid := old_names_preserved fresh (.inl rfl) initialValid.activeValid
      crashValid := fun candidate survives =>
        old_names_preserved fresh (.inr survives) (initialValid.crashValid candidate survives)
    }
    have published : accepts (some (Manifest.encode next.header)) :=
      ⟨next.header, next.files, Manifest.decode_encode _ floor, intent, covered, count,
        fun _ _ => by simp [installed, installRunNames]⟩
    have path : Publication.Retry (fun _ bytes => accepts (some bytes)) initial.manifest manifest :=
      .attempt (.refl _) published _ replaced
    exact Publication.retry_preserves (fun _ _ _ witness => witness) prior path

/-- Running the entire checkpoint schedule settles the new manifest and the
exact ordered run set. Earlier generations are left intact. -/
theorem checkpoint_complete (initial : Image) (next : RunSet) :
    ∃ after, initial.execute next (steps next.files.length) = some after ∧
      after.manifest = .settled (some (Manifest.encode next.header)) ∧
      (∀ index, after.durable next.header.generation index = next.files[index]?) ∧
      ∀ generation, generation ≠ next.header.generation →
        ∀ index, after.durable generation index = initial.durable generation index := by
  refine ⟨{ installRunNames initial next with manifest := .settled (some (Manifest.encode next.header)) },
    ?_, rfl, ?_, ?_⟩
  · unfold Image.execute
    rw [steps, Pending.execute_append, promote_run_names, Option.bind_some, manifest_steps,
      Publication.successful_replace]
    rfl
  · intro index
    simp [installRunNames]
  · intro generation disjoint index
    simp [installRunNames, disjoint]

/-- The directory barrier at a successful reopen fixes the currently visible
manifest. The caller must have validated the files and synced the chosen WAL
prefix before taking this transition. -/
def Image.settleVisible (image : Image) : Image :=
  { image with manifest := .settled image.manifest.active }

theorem Image.unreachable_after_reopen (image : Image) (generation : UInt64)
    (fresh : ∀ bytes, image.manifest.active = some bytes →
      ∀ header, Manifest.decode bytes = .ok header → header.generation ≠ generation) :
    image.settleVisible.Unreachable generation := by
  intro bytes selectable header decoded
  have fromActive : image.manifest.active = some bytes := by
    rcases selectable with same | survives
    · exact same
    · exact (List.mem_singleton.mp survives).symm
  exact fresh bytes fromActive header decoded

/-- A successful `DiskTable.openLocked` installs the decoded generation from
`openCheckpoint` or zero for an absent manifest. Once reopen settles the
visible manifest, the successor chosen by `DiskTable.checkpoint` is unreachable
from every live or durable manifest. `fits` is the generation overflow guard. -/
theorem Image.next_generation_unreachable_after_reopen (image : Image) (installedGeneration : UInt64)
    (loaded : (image.manifest.active = none ∧ installedGeneration = 0) ∨
      ∃ bytes header, image.manifest.active = some bytes ∧ Manifest.decode bytes = .ok header ∧
        installedGeneration = header.generation)
    (fits : installedGeneration.toNat + 1 < UInt64.size) :
    image.settleVisible.Unreachable (UInt64.ofNat (installedGeneration.toNat + 1)) := by
  apply image.unreachable_after_reopen
  intro bytes active header decoded
  rcases loaded with ⟨missing, _⟩ | ⟨loadedBytes, loadedHeader, visible, read, generation⟩
  · rw [missing] at active
    contradiction
  · have sameBytes : bytes = loadedBytes := Option.some.inj (active.symm.trans visible)
    rw [sameBytes, read] at decoded
    cases decoded
    intro same
    have naturals := congrArg UInt64.toNat same
    rw [UInt64.toNat_ofNat_of_lt' fits, generation] at naturals
    omega

/-- Repeated checkpoint attempts, power loss, and successful reopen barriers
with a fixed synced WAL watermark. A process failure leaves the visible image
of its cut; a power loss chooses one of the admitted durable manifest images. -/
inductive Retry (walSequence : UInt64) (expected : Manifest.Checkpoint → List ByteArray → Prop) :
    Image → Image → Prop where
  | refl (image) : Retry walSequence expected image image
  | attempt (prior : Retry walSequence expected initial before) (next : RunSet)
      (fresh : before.Unreachable next.header.generation)
      (covered : next.header.committed ≤ walSequence)
      (floor : next.header.floor ≤ next.header.committed)
      (count : next.header.runCount.toNat = next.files.length)
      (intent : expected next.header next.files)
      (cut : Nat) (ran : before.execute next ((steps next.files.length).take cut) = some after) :
      Retry walSequence expected initial after
  | crash (prior : Retry walSequence expected initial before) (survives : candidate ∈ before.manifest.crashImages) :
      Retry walSequence expected initial { before with manifest := .settled candidate }
  | reopen (prior : Retry walSequence expected initial before) :
      Retry walSequence expected initial before.settleVisible

/-- Every live or power-loss manifest reachable by retries selects a complete
durable run set and is covered by the synced WAL watermark. -/
theorem checkpoint_retry_valid {initial after : Image} {walSequence : UInt64}
    {expected : Manifest.Checkpoint → List ByteArray → Prop}
    (initialValid : initial.Valid walSequence expected) (trace : Retry walSequence expected initial after) :
    after.Valid walSequence expected := by
  induction trace with
  | refl => exact initialValid
  | attempt _ _ fresh covered floor count intent cut ran previous =>
    exact checkpoint_cut_valid previous fresh covered floor count intent cut ran
  | crash _ survives previous =>
    exact Publication.Image.settled_valid (previous.crashValid _ survives)
  | reopen _ previous => exact Publication.Image.settled_valid previous.activeValid

end Alvoki.Storage.CheckpointPublication
