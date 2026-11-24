import Alvoki.Storage.Disk.WalSegmentUnlinkSchedule

namespace Alvoki.Storage

/-- The visible WAL namespace and admitted sealed lists after power loss.
Each listed descriptor keeps its complete immutable bytes. The current
directory image independently records the possible metadata pairs. -/
structure WalSealedUnlinkImage where
  visible : WalSegmentImage
  crashSealed : List (List WalSegment)

namespace WalSealedUnlinkImage

def start (image : WalSegmentImage) : WalSealedUnlinkImage :=
  ⟨image, [image.sealed]⟩

private def eraseName (first : Nat) (segments : List WalSegment) : List WalSegment :=
  segments.filter fun segment => segment.first != first

/-- A name already absent from the visible namespace has no new unlink
effect. In particular, an earlier covered binding can remain crash-selectable
until the directory barrier, even when retry observes ENOENT. -/
def unlink (image : WalSealedUnlinkImage) (first : Nat) : WalSealedUnlinkImage :=
  if image.visible.sealed.any (fun segment => segment.first == first) then
    ⟨{ image.visible with sealed := eraseName first image.visible.sealed },
      image.crashSealed.map (eraseName first) ++ image.crashSealed⟩
  else image

def syncDirectory (image : WalSealedUnlinkImage) : WalSealedUnlinkImage :=
  start (image.visible.applyCollectionStep .syncDirectory)

def crash (image : WalSealedUnlinkImage) (pair : DirectoryPublication.Bindings)
    (sealed : List WalSegment) : WalSealedUnlinkImage :=
  start { image.visible with directory := .settled pair, sealed }

def applyCollectionStep (image : WalSealedUnlinkImage) : RunCollection.Step Nat → WalSealedUnlinkImage
  | .unlink first => image.unlink first
  | .syncDirectory => image.syncDirectory

theorem unlink_of_absent {image : WalSealedUnlinkImage} {first : Nat}
    (missing : ∀ segment ∈ image.visible.sealed, segment.first ≠ first) : image.unlink first = image := by
  have absent : image.visible.sealed.any (fun segment => segment.first == first) = false := by
    apply Bool.eq_false_iff.mpr
    intro present
    obtain ⟨segment, member, equal⟩ := List.any_eq_true.mp present
    exact missing segment member (beq_iff_eq.mp equal)
  simp [unlink, absent]

private theorem unlink_sealed (image : WalSealedUnlinkImage) (first : Nat) :
    (image.unlink first).visible.sealed = eraseName first image.visible.sealed := by
  unfold unlink
  split
  · rfl
  · rename_i absent
    apply Eq.symm
    rw [eraseName, List.filter_eq_self]
    intro segment member
    have different : segment.first ≠ first := by
      intro same
      exact absent (List.any_eq_true.mpr ⟨segment, member, by simp [same]⟩)
    simpa using different

/-- A complete pass leaves precisely the unplanned visible names. The
directory barrier makes that same list the only sealed crash choice. -/
theorem completeSealed (before : WalSealedUnlinkImage) (offsets : List Nat) :
    let after := (RunCollection.steps offsets).foldl applyCollectionStep before
    let kept := before.visible.sealed.filter (fun segment => !offsets.contains segment.first)
    after.visible.sealed = kept ∧ after.crashSealed = [kept] := by
  have eraseAll (image : WalSealedUnlinkImage) (names : List Nat) :
      ((names.map RunCollection.Step.unlink).foldl applyCollectionStep image).visible.sealed =
        image.visible.sealed.filter (fun segment => !names.contains segment.first) := by
    induction names generalizing image with
    | nil =>
      simp only [List.map_nil, List.foldl_nil, List.contains_nil, Bool.not_false]
      exact (List.filter_eq_self.mpr (fun _ _ => rfl)).symm
    | cons first rest ih =>
      change ((rest.map RunCollection.Step.unlink).foldl applyCollectionStep
        (image.unlink first)).visible.sealed = _
      rw [ih, unlink_sealed, eraseName, List.filter_filter]
      apply List.filter_congr
      intro segment _
      by_cases same : segment.first = first <;> simp [same, Bool.and_comm]
  simp only [RunCollection.steps, List.foldl_append, List.foldl_cons, List.foldl_nil]
  change _ = _ ∧ [_] = [_]
  exact ⟨eraseAll before offsets, congrArg (fun sealed => [sealed]) (eraseAll before offsets)⟩

end WalSealedUnlinkImage

/-- Collection retries operate on the approved offsets of the starting
inventory. A crash may restore an unbarriered name with exactly its original
sealed bytes. The active file is kept fixed throughout this stretch. -/
inductive WalSealedUnlinkTrace (initial : WalSegmentImage) : WalSealedUnlinkImage → Prop where
  | start : WalSealedUnlinkTrace initial (.start initial)
  | unlink (prior : WalSealedUnlinkTrace initial before) (approved : first ∈ initial.collectionOffsets) :
      WalSealedUnlinkTrace initial (before.unlink first)
  | sync (prior : WalSealedUnlinkTrace initial before) :
      WalSealedUnlinkTrace initial before.syncDirectory
  | powerLoss (prior : WalSealedUnlinkTrace initial before)
      (pairSurvives : pair ∈ before.visible.directory.crashImages)
      (sealedSurvives : sealed ∈ before.crashSealed) :
      WalSealedUnlinkTrace initial (before.crash pair sealed)

private theorem WalSegmentCollectionRetry.eraseSealedName {initial current : WalSegmentImage}
    {history : List WAL.Write} {first : Nat}
    (prior : WalSegmentCollectionRetry initial current) (layout : initial.ReadLayout history)
    (approved : first ∈ initial.collectionOffsets) :
    WalSegmentCollectionRetry initial { current with sealed := WalSealedUnlinkImage.eraseName first current.sealed } := by
  apply prior.unlink
  have eligible segment (member : segment ∈ current.sealed) (same : segment.first = first) : current.Eligible segment := by
    have original := (layout.collectionOffsets_approved approved).2 segment (prior.sealedSublist.subset member) same
    exact ⟨prior.keepsActive ▸ original.sealedBeforeActive,
      fun pair chosen => original.covered pair (prior.preservesSelected chosen).1⟩
  have deletion (segments : List WalSegment)
      (allowed : ∀ segment ∈ segments, segment.first = first → current.Eligible segment) :
      WalSegmentDeletion current.Eligible segments (WalSealedUnlinkImage.eraseName first segments) := by
    induction segments with
    | nil => exact .empty
    | cons segment rest ih =>
      have tail := ih (fun later member => allowed later (List.mem_cons_of_mem _ member))
      by_cases same : segment.first = first
      · simpa [WalSealedUnlinkImage.eraseName, same] using
          WalSegmentDeletion.remove (allowed segment List.mem_cons_self same) tail
      · simpa [WalSealedUnlinkImage.eraseName, same] using tail.keep (segment := segment)
  exact deletion current.sealed eligible

/-- Both the visible image and all its possible sealed survivor lists
project into the existing deletion model. The latter may follow a different
allowed deletion history than the visible image. -/
theorem WalSealedUnlinkTrace.projects {initial : WalSegmentImage} {after : WalSealedUnlinkImage}
    {history : List WAL.Write} (trace : WalSealedUnlinkTrace initial after) (layout : initial.ReadLayout history) :
    WalSegmentCollectionRetry initial after.visible ∧
      ∀ sealed ∈ after.crashSealed, WalSegmentCollectionRetry initial { after.visible with sealed } := by
  induction trace with
  | start =>
    refine ⟨.start, ?_⟩
    intro sealed survives
    obtain rfl := List.mem_singleton.mp survives
    cases initial
    exact .start
  | @unlink before first prior approved ih =>
    unfold WalSealedUnlinkImage.unlink
    split
    · refine ⟨ih.1.eraseSealedName layout approved, ?_⟩
      intro sealed survives
      rcases List.mem_append.mp survives with removed | unchanged
      · obtain ⟨earlier, member, rfl⟩ := List.mem_map.mp removed
        exact (ih.2 earlier member).eraseSealedName layout approved
      · exact ih.2 sealed unchanged
    · exact ih
  | sync prior ih =>
    have settled := ih.1.settle
    refine ⟨settled, ?_⟩
    intro sealed survives
    obtain rfl := List.mem_singleton.mp survives
    exact settled
  | powerLoss prior pairSurvives sealedSurvives ih =>
    have crashed := (ih.2 _ sealedSurvives).crash pairSurvives
    refine ⟨crashed, ?_⟩
    intro sealed survives
    obtain rfl := List.mem_singleton.mp survives
    exact crashed

/-- The result of a physical crash keeps the exact active file and the same
ordered marked read descriptors for the surviving manifest/marker pair. -/
theorem WalSealedUnlinkTrace.powerLossReads {initial : WalSegmentImage} {before : WalSealedUnlinkImage}
    {history : List WAL.Write} (trace : WalSealedUnlinkTrace initial before) (layout : initial.ReadLayout history)
    (valid : initial.Valid history)
    {pair : DirectoryPublication.Bindings} (pairSurvives : pair ∈ before.visible.directory.crashImages)
    {sealed : List WalSegment} (sealedSurvives : sealed ∈ before.crashSealed)
    {range : MarkedWalRange} (decoded : pair.walRange = some range) :
    let after := (before.crash pair sealed).visible
    WalSegmentCollectionRetry initial after ∧ after.active = initial.active ∧
      after.readDescriptors range.watermark = initial.readDescriptors range.watermark ∧
      ∃ first, first ≤ range.watermark ∧
        selectWalSegmentReads (after.segments.map WalSegment.first) range.watermark =
          some (first, (initial.readDescriptors range.watermark).map WalSegment.first) ∧
        WalSegment.concatenate (after.readDescriptors range.watermark) = WAL.encode (history.drop first) := by
  intro after
  have retry := ((trace.powerLoss pairSurvives sealedSurvives).projects layout).1
  have chosen : after.Selects pair := List.mem_cons_self ..
  have descriptors := retry.keepsReadDescriptors chosen decoded
  obtain ⟨first, covered, _, readPlan, _, bytes⟩ := (retry.readLayout layout).selects (retry.valid valid) chosen decoded
  exact ⟨retry, retry.keepsActive, descriptors, first, covered, by simpa only [descriptors] using readPlan, bytes⟩

/-- The actual unlink callback can fail before or after removing a name.
An accepted ENOENT leaves the full crash namespace unchanged. The
directory barrier can also report an error after settling names. -/
def WalSealedUnlinkReports (directory : DiskDirectory)
    (removeFile : System.FilePath → EStateM IO.Error WalSealedUnlinkImage (Except IO.Error Unit))
    (syncDirectory : System.FilePath → EStateM IO.Error WalSealedUnlinkImage Unit) : Prop :=
  (∀ first before, match removeFile (directory.file (.walSegment first)) before with
    | .error _ after => after = before ∨ after = before.unlink first
    | .ok (.ok _) after => after = before.unlink first
    | .ok (.error cause) after =>
      match RunCollection.ownedUnlinkResult (.error cause) with
      | .ok _ => (∀ segment ∈ before.visible.sealed, segment.first ≠ first) ∧ after = before
      | .error _ => after = before ∨ after = before.unlink first) ∧
  ∀ before, match syncDirectory directory.path before with
    | .ok _ after => after = before.syncDirectory
    | .error _ after => after = before ∨ after = before.syncDirectory

private theorem WalSealedUnlinkTrace.steps {initial : WalSegmentImage} {before : WalSealedUnlinkImage}
    (trace : WalSealedUnlinkTrace initial before) (actions : List (RunCollection.Step Nat))
    (approved : ∀ first, RunCollection.Step.unlink first ∈ actions → first ∈ initial.collectionOffsets) :
    WalSealedUnlinkTrace initial (actions.foldl WalSealedUnlinkImage.applyCollectionStep before) := by
  induction actions generalizing before with
  | nil => exact trace
  | cons action rest ih =>
    have step : WalSealedUnlinkTrace initial (before.applyCollectionStep action) := by
      cases action with
      | unlink first => exact .unlink trace (approved first List.mem_cons_self)
      | syncDirectory => exact .sync trace
    exact ih step (fun first member => approved first (List.mem_cons_of_mem _ member))

/-- Dispatch the shared collection actions with callbacks reporting the
full physical namespace, including the sealed crash choices. -/
def WalSealedUnlinkImage.performPaths (directory : DiskDirectory)
    (removeFile : System.FilePath → EStateM IO.Error WalSealedUnlinkImage (Except IO.Error Unit))
    (syncDirectory : System.FilePath → EStateM IO.Error WalSealedUnlinkImage Unit) :=
  RunCollection.performPaths removeFile syncDirectory (fun error image => .error error image)
    (fun first => directory.file (.walSegment first)) directory.path

private theorem WalSealedUnlinkReports.actionOutcome {directory removeFile syncDirectory}
    (reports : WalSealedUnlinkReports directory removeFile syncDirectory)
    (action : RunCollection.Step Nat) (image : WalSealedUnlinkImage) :
    match WalSealedUnlinkImage.performPaths directory removeFile syncDirectory action image with
    | .ok _ after => some (image.applyCollectionStep action) = some after
    | .error _ after => after = image ∨ some (image.applyCollectionStep action) = some after := by
  cases action with
  | syncDirectory =>
    have synced := reports.2 image
    cases outcome : syncDirectory directory.path image <;>
      simpa [WalSealedUnlinkImage.performPaths, RunCollection.performPaths, WalSealedUnlinkImage.applyCollectionStep, outcome, eq_comm]
        using synced
  | unlink first =>
    have unlinked := reports.1 first image
    simp only [WalSealedUnlinkImage.performPaths, RunCollection.performPaths, Bind.bind, EStateM.bind]
    cases outcome : removeFile (directory.file (.walSegment first)) image with
    | error cause after =>
      simpa only [outcome, Option.some.injEq, WalSealedUnlinkImage.applyCollectionStep, eq_comm] using unlinked
    | ok result after =>
      rw [outcome] at unlinked
      cases result with
      | ok success =>
        simpa [RunCollection.ownedUnlinkResult, Pure.pure, EStateM.pure, WalSealedUnlinkImage.applyCollectionStep,
          eq_comm] using unlinked
      | error cause =>
        change (match RunCollection.ownedUnlinkResult (.error cause) with
          | .ok _ => (∀ segment ∈ image.visible.sealed, segment.first ≠ first) ∧ after = image
          | .error _ => after = image ∨ after = image.unlink first) at unlinked
        cases accepted : RunCollection.ownedUnlinkResult (.error cause) with
        | error error => simpa [accepted, WalSealedUnlinkImage.applyCollectionStep, eq_comm] using unlinked
        | ok success =>
          cases success
          rw [accepted] at unlinked
          simp [accepted, Pure.pure, EStateM.pure, WalSealedUnlinkImage.applyCollectionStep, unlinked.2,
            WalSealedUnlinkImage.unlink_of_absent unlinked.1]

private theorem WalSealedUnlinkReports.outcome {directory removeFile syncDirectory}
    (reports : WalSealedUnlinkReports directory removeFile syncDirectory)
    (actions : List (RunCollection.Step Nat)) (before : WalSealedUnlinkImage) :
    match actions.forM (WalSealedUnlinkImage.performPaths directory removeFile syncDirectory) before with
    | .ok _ after => actions.foldl WalSealedUnlinkImage.applyCollectionStep before = after
    | .error _ after => ∃ cut, (actions.take cut).foldl WalSealedUnlinkImage.applyCollectionStep before = after := by
  let perform := WalSealedUnlinkImage.performPaths directory removeFile syncDirectory
  have outcomes := Publication.run_effects_outcome
    (fun (image : WalSealedUnlinkImage) action => some (image.applyCollectionStep action))
    perform (by
      intro action image
      have evidence := reports.actionOutcome action image
      cases applied : perform action image <;> simpa only [perform, applied] using evidence)
    actions before
  have folded (steps : List (RunCollection.Step Nat)) :
      steps.foldlM (fun image action => some (image.applyCollectionStep action)) before =
        some (steps.foldl WalSealedUnlinkImage.applyCollectionStep before) :=
    List.foldlM_pure (m := Option)
  change (match actions.forM perform before with
    | .ok _ after => actions.foldl WalSealedUnlinkImage.applyCollectionStep before = after
    | .error _ after => ∃ cut, (actions.take cut).foldl WalSealedUnlinkImage.applyCollectionStep before = after)
  cases ran : actions.forM perform before <;>
    simpa only [ran, folded, Option.some.injEq] using outcomes

private theorem approvedScheduleStep {initial : WalSegmentImage} {offsets : List Nat}
    (approved : ∀ first ∈ offsets, first ∈ initial.collectionOffsets)
    {first : Nat} (member : RunCollection.Step.unlink first ∈ RunCollection.steps offsets) :
    first ∈ initial.collectionOffsets := by
  have occurs : first ∈ offsets := by simpa [RunCollection.steps] using member
  exact approved first occurs

/-- Follow the exact physical namespace produced by the shared unlink
schedule. A failed dispatch reports a reached prefix, with both sealed
survival choices retained up to the effective directory barrier. -/
theorem WalSealedUnlinkTrace.runPaths {initial : WalSegmentImage} {before : WalSealedUnlinkImage}
    (trace : WalSealedUnlinkTrace initial before) (directory : DiskDirectory) (offsets : List Nat)
    (approved : ∀ first ∈ offsets, first ∈ initial.collectionOffsets)
    (removeFile : System.FilePath → EStateM IO.Error WalSealedUnlinkImage (Except IO.Error Unit))
    (syncDirectory : System.FilePath → EStateM IO.Error WalSealedUnlinkImage Unit)
    (reports : WalSealedUnlinkReports directory removeFile syncDirectory) :
    let perform := WalSealedUnlinkImage.performPaths directory removeFile syncDirectory
    match RunCollection.run offsets perform before with
    | .ok _ after => after = (RunCollection.steps offsets).foldl WalSealedUnlinkImage.applyCollectionStep before ∧
      WalSealedUnlinkTrace initial after
    | .error _ after => ∃ cut,
      after = ((RunCollection.steps offsets).take cut).foldl WalSealedUnlinkImage.applyCollectionStep before ∧
      WalSealedUnlinkTrace initial after := by
  intro perform
  have outcomes := reports.outcome (RunCollection.steps offsets) before
  unfold RunCollection.run
  cases applied : ((RunCollection.steps offsets).forM perform) before with
  | ok _ after =>
    rw [applied] at outcomes
    obtain rfl := outcomes
    exact ⟨rfl, trace.steps _ (fun _ => approvedScheduleStep approved)⟩
  | error _ after =>
    rw [applied] at outcomes
    obtain ⟨cut, rfl⟩ := outcomes
    exact ⟨cut, rfl, trace.steps _ (fun _ member => approvedScheduleStep approved (List.mem_of_mem_take member))⟩

/-- Locate the namespace at an interruption before the next callback
returns. Only that callback can add an effect to the successful prefix. -/
theorem WalSealedUnlinkTrace.inFlightCut {initial : WalSegmentImage} {before : WalSealedUnlinkImage}
    (trace : WalSealedUnlinkTrace initial before) (directory : DiskDirectory) (offsets : List Nat)
    (approved : ∀ first ∈ offsets, first ∈ initial.collectionOffsets)
    (removeFile : System.FilePath → EStateM IO.Error WalSealedUnlinkImage (Except IO.Error Unit))
    (syncDirectory : System.FilePath → EStateM IO.Error WalSealedUnlinkImage Unit)
    (reports : WalSealedUnlinkReports directory removeFile syncDirectory)
    (completed : Fin ((RunCollection.steps offsets).length + 1)) {reached cut : WalSealedUnlinkImage}
    (returned : ((RunCollection.steps offsets).take completed.val).forM
      (WalSealedUnlinkImage.performPaths directory removeFile syncDirectory) before = .ok () reached)
    (effect : cut = reached ∨ ∃ action, (RunCollection.steps offsets)[completed.val]? = some action ∧
      cut = reached.applyCollectionStep action) :
    WalSealedUnlinkTrace initial cut := by
  have prefixRan := reports.outcome ((RunCollection.steps offsets).take completed.val) before
  rw [returned] at prefixRan
  have ran : WalSealedUnlinkTrace initial reached := prefixRan ▸ trace.steps _
    (fun _ member => approvedScheduleStep approved (List.mem_of_mem_take member))
  rcases effect with rfl | ⟨action, index, rfl⟩
  · exact ran
  · cases action with
    | unlink first => exact .unlink ran (approvedScheduleStep approved (List.mem_of_getElem? index))
    | syncDirectory => exact .sync ran

/-- A direct power loss may happen before the next callback returns. Only
that callback's physical effect is optional after the observed successful
prefix. The crash then chooses admitted metadata and sealed survivors. -/
theorem WalSealedUnlinkTrace.inFlightPowerLoss {initial : WalSegmentImage} {before : WalSealedUnlinkImage}
    (trace : WalSealedUnlinkTrace initial before) (directory : DiskDirectory) (offsets : List Nat)
    (approved : ∀ first ∈ offsets, first ∈ initial.collectionOffsets)
    (removeFile : System.FilePath → EStateM IO.Error WalSealedUnlinkImage (Except IO.Error Unit))
    (syncDirectory : System.FilePath → EStateM IO.Error WalSealedUnlinkImage Unit)
    (reports : WalSealedUnlinkReports directory removeFile syncDirectory)
    (completed : Fin ((RunCollection.steps offsets).length + 1)) {reached cut : WalSealedUnlinkImage}
    (returned : ((RunCollection.steps offsets).take completed.val).forM
      (WalSealedUnlinkImage.performPaths directory removeFile syncDirectory) before = .ok () reached)
    (effect : cut = reached ∨ ∃ action, (RunCollection.steps offsets)[completed.val]? = some action ∧
      cut = reached.applyCollectionStep action)
    {pair : DirectoryPublication.Bindings} {sealed : List WalSegment}
    (pairSurvives : pair ∈ cut.visible.directory.crashImages) (sealedSurvives : sealed ∈ cut.crashSealed) :
    WalSealedUnlinkTrace initial (cut.crash pair sealed) :=
  (trace.inFlightCut directory offsets approved removeFile syncDirectory reports completed returned effect).powerLoss
    pairSurvives sealedSurvives

end Alvoki.Storage
