import Alvoki.Storage.Disk.SegmentedCollectionReadPlan
import Alvoki.Storage.Disk.WalSegmentBoundedOpenReports
import Alvoki.Storage.Publication.RunCollection

namespace Alvoki.Storage

/-- The canonical sealed offsets whose complete spans are covered by
every selected metadata pair. -/
def WalSegmentImage.collectionOffsets (image : WalSegmentImage) : List Nat :=
  (image.sealed.filter image.canRemove).map WalSegment.first

private theorem sameStart {segments : List WalSegment}
    (ordered : segments.Pairwise (fun earlier later => earlier.first < later.first))
    {left right : WalSegment} (leftIn : left ∈ segments) (rightIn : right ∈ segments)
    (same : left.first = right.first) : left = right := by
  induction segments with
  | nil => simp at leftIn
  | cons segment rest ih =>
    obtain ⟨before, further⟩ := List.pairwise_cons.mp ordered
    rcases List.mem_cons.mp leftIn with rfl | earlier <;> rcases List.mem_cons.mp rightIn with rfl | later
    · rfl
    · exact False.elim ((Nat.ne_of_lt (before right later)) same)
    · exact False.elim ((Nat.ne_of_lt (before left earlier)) same.symm)
    · exact ih further earlier later

theorem WalSegmentImage.ReadLayout.collectionOffsets_approved {image : WalSegmentImage} {history : List WAL.Write}
    (layout : image.ReadLayout history) {first : Nat} (planned : first ∈ image.collectionOffsets) :
    (∃ segment ∈ image.sealed, segment.first = first) ∧
      ∀ segment ∈ image.sealed, segment.first = first → image.Eligible segment := by
  obtain ⟨selected, included, offset⟩ := List.mem_map.mp planned
  obtain ⟨sealed, eligible⟩ := List.mem_filter.mp included
  refine ⟨⟨selected, sealed, offset⟩, ?_⟩
  have ordered := (List.pairwise_append.mp layout.ordered).1.imp (fun pair => pair.1)
  intro segment member same
  have identical := sameStart ordered member sealed (same.trans offset.symm)
  rw [identical]
  exact WalSegmentImage.canRemove_iff.mp eligible

/-- The bounded worker's held inventory authenticates each approved
offset at its actual canonical, no-follow regular file path. -/
theorem WalSegmentImage.collectionOffsets_observed {directory owners descriptor image pair watermark durable tail}
    (raw : WalSegmentRepair.HealthyBoundedWalReports directory owners descriptor image pair watermark durable tail)
    {first : Nat} (planned : first ∈ image.collectionOffsets) :
    renderWalSegmentName first ∈ raw.entries.toList.map (·.fileName) ∧
      ∃ metadata, raw.reports.lstat (directory.file (.walSegment first)) = .ok metadata ∧
        metadata.type = .file ∧ metadata.numLinks = 1 := by
  obtain ⟨segment, included, rfl⟩ := List.mem_map.mp planned
  have sealed := (List.mem_filter.mp included).1
  have listed : segment.first ∈ image.segments.map WalSegment.first :=
    List.mem_map_of_mem (List.mem_append_left _ sealed)
  exact ⟨(raw.names _).mpr listed, raw.regular _ listed⟩

/-- A completed unlink can remove the guarantee for its exact sealed
address. The directory barrier then settles the visible metadata pair. -/
def WalSegmentImage.applyCollectionStep (image : WalSegmentImage) : RunCollection.Step Nat → WalSegmentImage
  | .unlink first => { image with sealed := image.sealed.filter (fun segment => segment.first != first) }
  | .syncDirectory => { image with directory := image.directory.syncDirectory }

/-- Callback outcomes at the canonical segment paths in the owned directory.
An error may report either side of its effect. Accepted ENOENT already
has no guaranteed segment at that address. -/
def WalSegmentUnlinkReports (directory : DiskDirectory)
    (removeFile : System.FilePath → EStateM IO.Error WalSegmentImage (Except IO.Error Unit))
    (syncDirectory : System.FilePath → EStateM IO.Error WalSegmentImage Unit) : Prop :=
  (∀ first before, match removeFile (directory.file (.walSegment first)) before with
    | .error _ after => after = before ∨ after = before.applyCollectionStep (.unlink first)
    | .ok (.ok _) after => after = before.applyCollectionStep (.unlink first)
    | .ok (.error cause) after =>
      match RunCollection.ownedUnlinkResult (.error cause) with
      | .ok _ => (∀ segment ∈ before.sealed, segment.first ≠ first) ∧ after = before
      | .error _ => after = before ∨ after = before.applyCollectionStep (.unlink first)) ∧
  ∀ before, match syncDirectory directory.path before with
    | .ok _ after => after = before.applyCollectionStep .syncDirectory
    | .error _ after => after = before ∨ after = before.applyCollectionStep .syncDirectory

private theorem deletionAt {image : WalSegmentImage} {first : Nat} {segments : List WalSegment}
    (allowed : ∀ segment ∈ segments, segment.first = first → image.Eligible segment) :
    WalSegmentDeletion image.Eligible segments (segments.filter (fun segment => segment.first != first)) := by
  induction segments with
  | nil => exact .empty
  | cons segment rest ih =>
    have tail := ih (fun later member => allowed later (List.mem_cons_of_mem _ member))
    by_cases same : segment.first = first
    · simpa [same] using WalSegmentDeletion.remove (allowed segment List.mem_cons_self same) tail
    · simpa [same] using tail.keep (segment := segment)

private theorem WalSegmentCollectionRetry.collectionSteps {initial before : WalSegmentImage}
    (prior : WalSegmentCollectionRetry initial before) (actions : List (RunCollection.Step Nat))
    (approved : ∀ action ∈ actions, match action with
      | .unlink first => ∀ segment ∈ initial.sealed, segment.first = first → initial.Eligible segment
      | .syncDirectory => True) :
    WalSegmentCollectionRetry initial (actions.foldl WalSegmentImage.applyCollectionStep before) := by
  induction actions generalizing before with
  | nil => exact prior
  | cons action rest ih =>
    have eligible := approved action List.mem_cons_self
    have step : WalSegmentCollectionRetry initial (before.applyCollectionStep action) := by
      cases action with
      | syncDirectory => exact .settle prior
      | unlink first =>
        apply WalSegmentCollectionRetry.unlink prior
        apply deletionAt
        intro segment member same
        have original := eligible segment (prior.sealedSublist.subset member) same
        refine ⟨prior.keepsActive ▸ original.sealedBeforeActive, ?_⟩
        intro pair chosen
        exact original.covered pair (prior.preservesSelected chosen).1
    exact ih step (fun next member => approved next (List.mem_cons_of_mem _ member))

/-- The shared finite dispatcher applies only approved sealed-WAL unlinks
and its directory barrier. The returned projection is exact on success,
and every reported error leaves an admitted prefix. -/
theorem WalSegmentCollectionRetry.runPaths {initial before : WalSegmentImage}
    (prior : WalSegmentCollectionRetry initial before) (directory : DiskDirectory) (offsets : List Nat)
    (approved : ∀ first ∈ offsets, (∃ segment ∈ initial.sealed, segment.first = first) ∧
      ∀ segment ∈ initial.sealed, segment.first = first → initial.Eligible segment)
    (removeFile : System.FilePath → EStateM IO.Error WalSegmentImage (Except IO.Error Unit))
    (syncDirectory : System.FilePath → EStateM IO.Error WalSegmentImage Unit)
    (reports : WalSegmentUnlinkReports directory removeFile syncDirectory) :
    (∀ first ∈ offsets, first ≠ initial.active.first) ∧
      let perform := RunCollection.performPaths removeFile syncDirectory (fun error image => .error error image)
        (fun first => directory.file (.walSegment first)) directory.path
      match RunCollection.run offsets perform before with
      | .ok _ after => after = (RunCollection.steps offsets).foldl WalSegmentImage.applyCollectionStep before ∧
        WalSegmentCollectionRetry initial after
      | .error _ after => ∃ cut,
        after = ((RunCollection.steps offsets).take cut).foldl WalSegmentImage.applyCollectionStep before ∧
        WalSegmentCollectionRetry initial after := by
  constructor
  · intro first planned
    obtain ⟨⟨segment, member, rfl⟩, eligible⟩ := approved first planned
    exact (eligible _ member rfl).notActive
  intro perform
  have reported : ∀ action image, match perform action image with
      | .ok _ after => some (image.applyCollectionStep action) = some after
      | .error _ after => after = image ∨ some (image.applyCollectionStep action) = some after := by
    intro action image
    cases action with
    | syncDirectory =>
      have synced := reports.2 image
      cases outcome : syncDirectory directory.path image <;>
        simpa [perform, RunCollection.performPaths, outcome, eq_comm] using synced
    | unlink first =>
      have unlinked := reports.1 first image
      simp only [perform, RunCollection.performPaths, Bind.bind, EStateM.bind]
      cases outcome : removeFile (directory.file (.walSegment first)) image with
      | error cause after => simpa only [outcome, Option.some.injEq, eq_comm] using unlinked
      | ok result after =>
        rw [outcome] at unlinked
        cases result with
        | ok _ => simpa [RunCollection.ownedUnlinkResult, Pure.pure, EStateM.pure, eq_comm] using unlinked
        | error cause =>
          change (match RunCollection.ownedUnlinkResult (.error cause) with
            | .ok _ => (∀ segment ∈ image.sealed, segment.first ≠ first) ∧ after = image
            | .error _ => after = image ∨ after = image.applyCollectionStep (.unlink first)) at unlinked
          cases accepted : RunCollection.ownedUnlinkResult (.error cause) with
          | error error =>
            simpa [accepted, eq_comm] using unlinked
          | ok success =>
            cases success
            rw [accepted] at unlinked
            have keeps : image.sealed.filter (fun segment => segment.first != first) = image.sealed :=
              List.filter_eq_self.mpr (fun segment member => by simpa using unlinked.1 segment member)
            simp [accepted, Pure.pure, EStateM.pure, WalSegmentImage.applyCollectionStep, keeps, unlinked.2]
  have allowed : ∀ action ∈ RunCollection.steps offsets, match action with
      | .unlink first => ∀ segment ∈ initial.sealed, segment.first = first → initial.Eligible segment
      | .syncDirectory => True := by
    intro action member
    rcases List.mem_append.mp member with unlink | barrier
    · obtain ⟨first, present, rfl⟩ := List.mem_map.mp unlink
      exact (approved first present).2
    · obtain rfl := List.mem_singleton.mp barrier
      trivial
  have outcomes := Publication.run_effects_outcome
    (fun (image : WalSegmentImage) (action : RunCollection.Step Nat) => some (image.applyCollectionStep action))
    perform (by
      intro action image
      have evidence := reported action image
      cases applied : perform action image <;> simpa only [applied] using evidence)
    (RunCollection.steps offsets) before
  have folded (actions : List (RunCollection.Step Nat)) :
      actions.foldlM (fun image action => some (WalSegmentImage.applyCollectionStep image action)) before =
        some (actions.foldl WalSegmentImage.applyCollectionStep before) :=
    List.foldlM_pure (m := Option)
  unfold RunCollection.run
  simp only [folded] at outcomes
  cases applied : ((RunCollection.steps offsets).forM perform) before with
  | ok _ after =>
    rw [applied] at outcomes
    obtain rfl := Option.some.inj outcomes
    exact ⟨rfl, prior.collectionSteps _ allowed⟩
  | error _ after =>
    rw [applied] at outcomes
    obtain ⟨cut, same⟩ := outcomes
    refine ⟨cut, (Option.some.inj same).symm, ?_⟩
    rw [← Option.some.inj same]
    exact prior.collectionSteps _ (fun action member => allowed action (List.mem_of_mem_take member))

end Alvoki.Storage
