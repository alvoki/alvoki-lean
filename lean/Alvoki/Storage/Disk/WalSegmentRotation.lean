import Alvoki.Storage.Disk.WalSegmentCollection
import Alvoki.Storage.Disk.WalSegmentFileName
import Alvoki.Storage.Disk.WalSegmentRotationIO

namespace Alvoki.Storage

private def WalSegment.emptyAt (first : Nat) : WalSegment := ⟨first, first, ByteArray.empty⟩

/-- Closing the previous active segment moves its unchanged bytes into the sealed list.
The empty successor starts at the previous segment's absolute end. -/
def WalSegmentImage.rotated (image : WalSegmentImage) : WalSegmentImage :=
  { image with sealed := image.sealed ++ [image.active], active := .emptyAt image.active.last }

namespace WalSegmentRotation

/-- Rotation begins with a nonempty active file, its contents already at
the validated history end, and all sealed descriptors before its start.
The caller must additionally obtain exclusive creation of the fresh name. -/
structure CanRotate (image : WalSegmentImage) (history : List WAL.Write) : Prop where
  nonempty : image.active.first < image.active.last
  atEnd : image.active.last = history.length
  sealedBefore : ∀ segment ∈ image.sealed, segment.first < image.active.first

theorem CanRotate.successorDistinct {image : WalSegmentImage} {history : List WAL.Write}
    (plan : CanRotate image history) (dir : DiskDirectory) {segment : WalSegment}
    (member : segment ∈ image.sealed ++ [image.active]) :
    dir.file (.walSegment image.active.last) ≠ dir.file (.walSegment segment.first) := by
  have earlier : segment.first ≤ image.active.first := by
    rcases List.mem_append.mp member with sealed | active
    · exact Nat.le_of_lt (plan.sealedBefore segment sealed)
    · exact List.mem_singleton.mp active ▸ Nat.le_refl _
  exact fun alias => Nat.ne_of_lt (Nat.lt_of_le_of_lt earlier plan.nonempty)
    (dir.walSegment_path_injective alias).symm

private theorem chain_append_empty {history : List WAL.Write} {first : Nat} {sealed : List WalSegment}
    {active : WalSegment} (chain : WalSegment.Chain history first (sealed ++ [active]))
    (nonempty : active.first < active.last) :
    WalSegment.Chain history first (sealed ++ [active, .emptyAt history.length]) := by
  induction sealed generalizing first with
  | nil =>
    cases chain with
    | cons bounds _ bytes tail =>
      have ends {offset : Nat} (finished : WalSegment.Chain history offset []) : offset = history.length := by
        cases finished
        rfl
      refine .cons bounds (fun same => False.elim (Nat.ne_of_lt nonempty same)) bytes ?_
      rw [ends tail]
      refine .cons (segment := .emptyAt history.length) (Nat.le_refl _) (fun _ => rfl) ?_ .endOfHistory
      change ByteArray.empty = WAL.encode ((history.drop history.length).take (history.length - history.length))
      simp [WAL.encode]
  | cons segment rest ih =>
    cases chain with
    | cons bounds emptyLast bytes tail =>
      exact .cons bounds (fun same => False.elim (by simpa using emptyLast same)) bytes (ih tail)

private theorem rotated_tail (image : WalSegmentImage) (watermark : Nat) :
    image.rotated.afterWatermark watermark = image.afterWatermark watermark ++
      ([image.rotated.active].filter (fun segment => decide (watermark < segment.last))) := by
  simp only [WalSegmentImage.rotated, WalSegmentImage.afterWatermark, List.filter_append]

theorem _root_.Alvoki.Storage.WalSegment.concatenate_append_empty (segments : List WalSegment) (first : Nat) :
    WalSegment.concatenate (segments ++ [⟨first, first, ByteArray.empty⟩]) = WalSegment.concatenate segments := by
  induction segments with
  | nil => simp [WalSegment.concatenate]
  | cons segment rest ih => simp [WalSegment.concatenate, ih]

/-- Observing the successor changes no recoverable byte concatenation. -/
theorem rotated_bytes (image : WalSegmentImage) (watermark : Nat) :
    WalSegment.concatenate (image.rotated.afterWatermark watermark) =
      WalSegment.concatenate (image.afterWatermark watermark) := by
  rw [rotated_tail]
  by_cases needed : watermark < image.active.last
  · simpa [WalSegmentImage.rotated, WalSegment.emptyAt, needed] using
      WalSegment.concatenate_append_empty (image.afterWatermark watermark) image.active.last
  · simp [WalSegmentImage.rotated, WalSegment.emptyAt, needed]

theorem CanRotate.valid_rotated {image : WalSegmentImage} {history : List WAL.Write}
    (plan : CanRotate image history) (valid : image.Valid history) : image.rotated.Valid history := by
  intro pair chosen
  obtain ⟨range, first, decoded, starts, through, chain⟩ := valid pair chosen
  refine ⟨range, first, decoded, starts, through, ?_⟩
  rw [rotated_tail]
  by_cases needed : range.watermark < image.active.last
  · let sealed := image.sealed.filter (fun segment => decide (range.watermark < segment.last))
    have old : WalSegment.Chain history first (sealed ++ [image.active]) := by
      simpa [WalSegmentImage.afterWatermark, List.filter_append, needed, sealed] using chain
    have expanded := chain_append_empty old plan.nonempty
    simpa [WalSegmentImage.afterWatermark, WalSegmentImage.rotated, WalSegment.emptyAt,
      List.filter_append, needed, ← plan.atEnd, sealed, List.append_assoc] using expanded
  · simpa [WalSegmentImage.rotated, WalSegment.emptyAt, needed] using chain

/-- The state tracks only the new canonical name. Existing segment names
and immutable contents are kept. Syncing the inode and the directory are
separate effects, and only the latter can establish durable visibility. -/
inductive Binding where
  | absent
  | created
  | fileSynced
  | durable
  deriving DecidableEq

structure State where
  metadata : DirectoryPublication.Image
  successor : Binding

def State.initial (image : WalSegmentImage) : State := ⟨image.directory, .absent⟩

/-- The lookup contract supplies absence or the exact regular zero-byte
successor under writer exclusion and stable file identity. -/
def State.observeSuccessor (state : State) : Option ByteArray :=
  if state.successor = .absent then none else some ByteArray.empty

def State.visible (state : State) (image : WalSegmentImage) : WalSegmentImage :=
  let withMetadata := { image with directory := state.metadata }
  if state.successor = .absent then withMetadata else withMetadata.rotated

/-- Before directory settlement, a power loss can retain or lose a created
successor. If it retains the file, its bytes still describe the empty
successor. A durable binding cannot be absent after a crash. -/
def Binding.MaySurvive : Binding → Bool → Prop
  | .absent, present => present = false
  | .created, _ | .fileSynced, _ => True
  | .durable, present => present = true

def State.step (state : State) : Step → Option State
  | .createEmpty => if state.successor = .absent then some { state with successor := .created } else none
  | .syncFile =>
    match state.successor with
    | .absent => none
    | .created => some { state with successor := .fileSynced }
    | .fileSynced | .durable => some state
  | .syncDirectory =>
    if state.successor = .fileSynced ∨ state.successor = .durable then
      some ⟨state.metadata.syncDirectory, .durable⟩
    else none

/-- The observed successor decides whether to create the file. Every
attempt syncs the empty inode and directory, including a retry that only
observes the bytes left by an earlier report. -/
def State.steps (state : State) : List Step :=
  WalSegmentRotation.steps state.observeSuccessor.isSome

theorem State.create_iff_absent (state : State) :
    Step.createEmpty ∈ state.steps ↔ state.observeSuccessor = none := by
  cases seen : state.observeSuccessor <;> simp [State.steps, WalSegmentRotation.steps, seen]

def State.execute (state : State) (actions : List Step) : Option State :=
  actions.foldlM State.step state

private def perform (reports : Step → WAL.Boundary.OperationResult) (action : Step) : EStateM Unit State Unit :=
  fun state => match reports action with
    | .errorBeforeEffect => .error () state
    | .errorAfterEffect => .error () ((state.step action).getD state)
    | .success => match state.step action with
      | none => .error () state
      | some after => .ok () after

/-- Successful reports implement a step. An error may report either before
the effect or after it completed. -/
def EffectReports (perform : Step → EStateM ε State Unit) : Prop :=
  ∀ action state, match perform action state with
    | .ok _ after => state.step action = some after
    | .error _ after => after = state ∨ state.step action = some after

private theorem perform_effect (reports : Step → WAL.Boundary.OperationResult) : EffectReports (perform reports) := by
  intro action state
  cases reported : reports action <;> cases applied : state.step action <;> simp [perform, reported, applied]

def State.run (state : State) (reports : Step → WAL.Boundary.OperationResult) : EStateM.Result Unit State Unit :=
  WalSegmentRotation.run state.observeSuccessor.isSome (perform reports) state

/-- Apply the shared executable schedule to observed callbacks. A reported
failure can stop just before or just after an individual file effect. -/
theorem State.runObserved_effects (state : State) (present : Bool) (action : Step → EStateM ε State Unit)
    (reports : EffectReports action) :
    match WalSegmentRotation.run present action state with
    | .ok _ after => state.execute (WalSegmentRotation.steps present) = some after
    | .error _ after => ∃ cut, state.execute ((WalSegmentRotation.steps present).take cut) = some after := by
  have outcome := Publication.run_effects_outcome State.step action (by
    intro step before
    have report := reports step before
    cases ran : action step before <;> simpa only [ran] using report) (WalSegmentRotation.steps present) state
  unfold WalSegmentRotation.run
  cases ran : ((WalSegmentRotation.steps present).forM action) state <;> simpa only [ran, State.execute] using outcome

theorem State.run_effects (state : State) (reports : Step → WAL.Boundary.OperationResult) :
    match state.run reports with
    | .ok _ after => state.execute state.steps = some after
    | .error _ after => ∃ cut, state.execute (state.steps.take cut) = some after := by
  have outcome := state.runObserved_effects state.observeSuccessor.isSome (perform reports) (perform_effect reports)
  unfold State.run
  cases ran : WalSegmentRotation.run state.observeSuccessor.isSome (perform reports) state <;>
    simpa only [ran, State.steps] using outcome

/-- A successful report settles the successor and the same visible
directory pair. A failure after effect can yield this physical state too. -/
theorem State.run_settled {state after : State} {reports : Step → WAL.Boundary.OperationResult}
    (ran : state.run reports = .ok () after) :
    after = ⟨state.metadata.syncDirectory, .durable⟩ := by
  have effects := state.run_effects reports
  rw [ran] at effects
  have complete : state.execute state.steps = some ⟨state.metadata.syncDirectory, .durable⟩ := by
    cases state with
    | mk _ successor => cases successor <;> rfl
  exact Option.some.inj (effects.symm.trans complete)

/-- Any prefix of a rotation attempt can be followed by a crash and retry.
Before the barrier, name survival and the selected directory pair are
conservatively independent. The shared barrier settles both. -/
inductive Trace (initial : WalSegmentImage) : State → Prop where
  | start : Trace initial (.initial initial)
  | effect (prior : Trace initial before) (applied : before.step action = some after) : Trace initial after
  | crash (prior : Trace initial before) (pair : DirectoryPublication.Bindings)
      (selected : pair ∈ before.metadata.crashImages) {present : Bool} (allowed : before.successor.MaySurvive present) :
      Trace initial ⟨.settled pair, if present then .durable else .absent⟩

private theorem Trace.execute {initial : WalSegmentImage} {before after : State} {steps : List Step}
    (trace : Trace initial before) (ran : before.execute steps = some after) : Trace initial after := by
  induction steps generalizing before with
  | nil => cases ran; exact trace
  | cons step rest ih =>
    change (before.step step >>= fun next => next.execute rest) = some after at ran
    cases applied : before.step step with
    | none => rw [applied] at ran; contradiction
    | some next =>
      rw [applied] at ran
      exact ih (.effect trace applied) ran

/-- The shared path dispatch extends the same crash/retry trace when its
primitive outcomes satisfy the step contract. -/
theorem Trace.afterObservedReport {initial : WalSegmentImage} {before : State} (trace : Trace initial before)
    (present : Bool) (action : Step → EStateM ε State Unit)
    (reports : EffectReports action) :
    match WalSegmentRotation.run present action before with
    | .ok _ after | .error _ after => Trace initial after := by
  have effects := before.runObserved_effects present action reports
  cases ran : WalSegmentRotation.run present action before
  · rw [ran] at effects
    exact trace.execute effects
  · rw [ran] at effects
    obtain ⟨_, cut⟩ := effects
    exact trace.execute cut

theorem Trace.afterReport {initial : WalSegmentImage} {before : State} (trace : Trace initial before)
    (reports : Step → WAL.Boundary.OperationResult) :
    match before.run reports with
    | .ok _ after | .error _ after => Trace initial after := by
  have outcome := trace.afterObservedReport before.observeSuccessor.isSome (perform reports) (perform_effect reports)
  unfold State.run
  cases ran : WalSegmentRotation.run before.observeSuccessor.isSome (perform reports) before <;>
    simpa only [ran] using outcome

private theorem State.step_metadata {before after : State} {step : Step} (ran : before.step step = some after) :
    after.metadata = before.metadata ∨ after.metadata = before.metadata.syncDirectory := by
  cases before with
  | mk _ successor => cases step <;> cases successor <;> simp [State.step] at ran <;> cases ran <;> simp

theorem Trace.selectsOriginal {initial : WalSegmentImage} {state : State} (trace : Trace initial state)
    {pair : DirectoryPublication.Bindings} (chosen : pair ∈ state.metadata.active :: state.metadata.crashImages) :
    initial.Selects pair := by
  induction trace with
  | start => exact chosen
  | effect _ applied prior =>
    rcases State.step_metadata applied with same | settled
    · rw [same] at chosen
      exact prior chosen
    · rw [settled] at chosen
      have live := (by simpa [DirectoryPublication.Image.syncDirectory, List.mem_cons] using chosen : pair = _)
      exact prior (List.mem_cons.mpr (.inl live))
  | crash _ _ selected _ prior =>
    have retained := (by simpa [DirectoryPublication.Image.settled, List.mem_cons] using chosen : pair = _)
    exact prior (List.mem_cons.mpr (.inr (retained.symm ▸ selected)))

theorem State.visible_metadata (state : State) (image : WalSegmentImage) :
    (state.visible image).directory = state.metadata := by
  by_cases absent : state.successor = .absent <;> simp [visible, absent, WalSegmentImage.rotated]

/-- Both surviving layouts have a verified recovery chain. Every pair
still selectable at this cut reads the same exact bytes as at the start. -/
theorem Trace.preservesRecovery {initial : WalSegmentImage} {history : List WAL.Write} {state : State}
    (trace : Trace initial state) (plan : CanRotate initial history) (valid : initial.Valid history) :
    (state.visible initial).Valid history ∧ ∀ pair, (state.visible initial).Selects pair →
      initial.Selects pair ∧ ∀ range, pair.walRange = some range →
        WalSegment.concatenate ((state.visible initial).afterWatermark range.watermark) =
          WalSegment.concatenate (initial.afterWatermark range.watermark) := by
  have earlier : ∀ pair, (state.visible initial).Selects pair → initial.Selects pair := by
    intro pair chosen
    apply trace.selectsOriginal
    simpa only [WalSegmentImage.Selects, state.visible_metadata] using chosen
  constructor
  · intro pair chosen
    have original := earlier pair chosen
    by_cases absent : state.successor = .absent
    · simpa only [State.visible, absent, ite_true, WalSegmentImage.afterWatermark] using valid pair original
    · simpa only [State.visible, absent, ite_false, WalSegmentImage.afterWatermark, WalSegmentImage.rotated] using
        plan.valid_rotated valid pair original
  · intro pair chosen
    refine ⟨earlier pair chosen, fun range _ => ?_⟩
    by_cases absent : state.successor = .absent
    · simp [State.visible, absent, WalSegmentImage.afterWatermark]
    · simpa only [State.visible, absent, ite_false, WalSegmentImage.afterWatermark, WalSegmentImage.rotated] using
        rotated_bytes initial range.watermark

/-- Append can resume only at a durable empty successor and a settled
directory pair whose marker covers the whole retained history. -/
structure AppendReady (state : State) (initial : WalSegmentImage) (history : List WAL.Write) : Prop where
  successorDurable : state.successor = .durable
  directorySettled : state.metadata.crashImages = [state.metadata.active]
  exactMarker : ∃ range, state.metadata.active.walRange = some range ∧ range.through = history.length
  emptyAtEnd : (state.visible initial).active = ⟨history.length, history.length, ByteArray.empty⟩
  recoverable : (state.visible initial).Valid history

/-- A successful retry can hand off to the writer when its current pair
agrees with the end at which the successor was created. If an earlier marker
survives, recovery is still valid. Appending then requires a separate repair. -/
theorem Trace.readyForAppend {initial : WalSegmentImage} {history : List WAL.Write} {before after : State}
    (trace : Trace initial before) (plan : CanRotate initial history) (valid : initial.Valid history)
    {reports : Step → WAL.Boundary.OperationResult} (ran : before.run reports = .ok () after)
    (atMarker : ∃ range, before.metadata.active.walRange = some range ∧ range.through = history.length) :
    AppendReady after initial history := by
  have actual := trace.afterReport reports
  rw [ran] at actual
  have recovery := (actual.preservesRecovery plan valid).1
  have settled := State.run_settled ran
  subst after
  refine ⟨rfl, rfl, atMarker, ?_, recovery⟩
  simp [State.visible, WalSegmentImage.rotated, WalSegment.emptyAt, plan.atEnd]

end WalSegmentRotation

end Alvoki.Storage
