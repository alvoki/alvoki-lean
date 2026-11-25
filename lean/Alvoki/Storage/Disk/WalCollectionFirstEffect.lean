import Alvoki.Storage.Disk.WalCollectionFirstUnlink
import Alvoki.Storage.Disk.WalSealedUnlinkSurvivors

namespace Alvoki.Storage.DiskSession

open System

/-- A returned first unlink with a live lookup in the held parent. The
observer reports whether that binding was removed, the other bindings in
the same parent, and the immutable descriptors still visible by name.
Before directory sync, either the original or the locally changed sealed
list can survive power loss. The report need only include survivors that
actually remain possible. -/
structure WalFirstUnlinkReport {calls : WalCollectionReads} {directory : DiskDirectory} {first : Nat}
    (resolved : WalSealUnlinkResolution calls directory first)
    (initial : WalSegmentImage) (result : Except IO.Error Unit) (reached : WalSealedUnlinkImage) where
  afterView : DirectoryReadNamespace
  removed : Bool
  binding : afterView.child resolved.root (renderWalSegmentName first) =
    if removed then none else some resolved.unlinkChild.child
  otherBindings : ∀ name, name ≠ renderWalSegmentName first →
    afterView.child resolved.root name = resolved.unlinkView.child resolved.root name
  sealedBound : ∀ segment ∈ initial.sealed,
    ∃ inode, resolved.unlinkView.child resolved.root (renderWalSegmentName segment.first) = some inode
  visibleSealed : reached.visible.sealed = initial.sealed.filter fun segment =>
    (afterView.child resolved.root (renderWalSegmentName segment.first)).isSome
  keeper : reached.visible.active = initial.active
  metadata : reached.visible.directory = initial.directory
  survivors : ∀ sealed ∈ reached.crashSealed,
    sealed = initial.sealed ∨ removed = true ∧ sealed = reached.visible.sealed
  completed : result = .ok () → removed = true
  missing : ∀ path message, result = .error (.noFileOrDirectory path 2 message) →
    resolved.unlinkView.child resolved.root (renderWalSegmentName first) = none

namespace WalFirstUnlinkReport

variable {calls : WalCollectionReads} {directory : DiskDirectory} {first : Nat}
variable {resolved : WalSealUnlinkResolution calls directory first}
variable {initial : WalSegmentImage} {result : Except IO.Error Unit} {reached : WalSealedUnlinkImage}

private theorem keepsName (report : WalFirstUnlinkReport resolved initial result reached)
    {segment : WalSegment} (member : segment ∈ initial.sealed) :
    (report.afterView.child resolved.root (renderWalSegmentName segment.first)).isSome =
      (!report.removed || segment.first != first) := by
  by_cases same : segment.first = first
  · rw [same, report.binding]
    cases report.removed <;> simp
  · have other : renderWalSegmentName segment.first ≠ renderWalSegmentName first := by
      intro equal
      apply same
      simpa only [parseWalSegmentName_render, Option.some.injEq] using congrArg parseWalSegmentName equal
    obtain ⟨inode, bound⟩ := report.sealedBound segment member
    simp [report.otherBindings _ other, bound, same]

/-- A truthful no-entry diagnostic cannot be accepted as a successful
retry at this first lookup, which saw the binding still present. -/
theorem ownedResult (report : WalFirstUnlinkReport resolved initial result reached) :
    RunCollection.ownedUnlinkResult result = result := by
  cases result with
  | ok value => rfl
  | error cause =>
    cases accepted : RunCollection.ownedUnlinkResult (.error cause) with
    | ok value =>
      cases value
      rcases RunCollection.ownedUnlinkResult_ok_iff.mp accepted with impossible | ⟨path, message, raw⟩
      · contradiction
      · have live := resolved.unlinkChild.binds
        rw [resolved.unlinkChild.atRoot, resolved.unlinkChild.atName, report.missing path message raw] at live
        contradiction
    | error error =>
      cases cause <;> simp_all [RunCollection.ownedUnlinkResult]
      split at accepted <;> simp_all

private theorem walImage_eq {left right : WalSegmentImage}
    (metadata : left.directory = right.directory) (seals : left.sealed = right.sealed)
    (keeper : left.active = right.active) : left = right := by
  cases left
  cases right
  simp_all

/-- Interpret the physical report with the existing WAL unlink trace. A
real detach contributes one unlink and allows every reported survivor.
An error with no detach leaves the original abstract image. -/
theorem projects (report : WalFirstUnlinkReport resolved initial result reached)
    {history : List WAL.Write} (layout : initial.ReadLayout history) (approved : first ∈ initial.collectionOffsets) :
    let start := WalSealedUnlinkImage.start initial
    let projected := if report.removed then start.unlink first else start
    WalSealedUnlinkTrace initial projected ∧ reached.visible = projected.visible ∧
      ∀ sealed ∈ reached.crashSealed, sealed ∈ projected.crashSealed := by
  intro start projected
  have seals := List.filter_congr (fun _ member => report.keepsName member)
  have visible := report.visibleSealed.trans seals
  by_cases removed : report.removed = true
  · obtain ⟨segment, member, offset⟩ := (layout.collectionOffsets_approved approved).1
    have present : initial.sealed.any (fun segment => segment.first == first) = true :=
      List.any_eq_true.mpr ⟨segment, member, by simp [offset]⟩
    have selected : projected = start.unlink first := by simp [projected, removed]
    rw [selected]
    have removedSealed : reached.visible.sealed = initial.sealed.filter (fun segment => segment.first != first) := by
      simpa only [removed, Bool.not_true, Bool.false_or] using visible
    refine ⟨.unlink .start approved, ?_, ?_⟩
    · simp only [WalSealedUnlinkImage.unlink, start, WalSealedUnlinkImage.start, present, ite_true]
      exact walImage_eq report.metadata removedSealed report.keeper
    · intro sealed member
      simp only [WalSealedUnlinkImage.unlink, start, WalSealedUnlinkImage.start, present, ite_true,
        List.map_cons, List.map_nil, List.cons_append, List.nil_append]
      rcases report.survivors sealed member with original | ⟨_, changed⟩
      · exact List.mem_cons_of_mem _ (List.mem_singleton.mpr original)
      · rw [changed, removedSealed]
        exact List.mem_cons_self
  · have selected : projected = start := by simp [projected, removed]
    rw [selected]
    refine ⟨.start, ?_, ?_⟩
    · have noRemoval : report.removed = false := Bool.eq_false_iff.mpr removed
      have unchanged : reached.visible.sealed = initial.sealed :=
        visible.trans (List.filter_eq_self.mpr (fun _ _ => by simp [noRemoval]))
      exact walImage_eq report.metadata unchanged report.keeper
    · intro sealed member
      rcases report.survivors sealed member with original | ⟨effective, _⟩
      · exact List.mem_singleton.mpr original
      · exact (removed effective).elim

/-- Every originally planned offset still names an eligible seal, except
for the first offset when its name was removed. This also handles a
repeated first offset in an incomplete inventory report. -/
theorem remaining (report : WalFirstUnlinkReport resolved initial result reached) {offset : Nat}
    (approved : offset ∈ initial.collectionOffsets) :
    offset ∈ reached.visible.collectionOffsets ↔ !report.removed || offset != first := by
  rw [WalSegmentImage.collectionOffsets] at approved ⊢
  have canRemove segment : reached.visible.canRemove segment = initial.canRemove segment := by
    simp [WalSegmentImage.canRemove, report.keeper, report.metadata]
  constructor
  · intro present
    obtain ⟨segment, eligible, offset⟩ := List.mem_map.mp present
    obtain ⟨member, _⟩ := List.mem_filter.mp eligible
    rw [report.visibleSealed] at member
    obtain ⟨original, named⟩ := List.mem_filter.mp member
    rw [report.keepsName original, offset] at named
    exact named
  · intro kept
    obtain ⟨segment, eligible, offset⟩ := List.mem_map.mp approved
    obtain ⟨original, removable⟩ := List.mem_filter.mp eligible
    refine List.mem_map.mpr ⟨segment, List.mem_filter.mpr ⟨?_, (canRemove segment).trans removable⟩, offset⟩
    rw [report.visibleSealed]
    exact List.mem_filter.mpr ⟨original, by rw [report.keepsName original, offset]; exact kept⟩

end WalFirstUnlinkReport

/-- The reached result from that exact first canonical unlink refines the
shared collection trace. Its reported survivors and the eligible portion
of the original ordered tail follow from a single observed local effect. -/
theorem SegmentedWriterState.RetainedReady.firstWalUnlinkEffect
    {directory : DiskDirectory} {descriptor : Nat} {before : SegmentedWriterState}
    (ready : before.RetainedReady directory descriptor) (calls : WalCollectionReads)
    {first : Nat} {rest : List Nat}
    (planned : calls.plan directory before.installed = .ok (first :: rest))
    (approved : ∀ offset ∈ first :: rest, offset ∈ before.wal.collectionOffsets)
    (resolved : WalSealUnlinkResolution calls directory first)
    (removeFile : FilePath → EStateM IO.Error WalSealedUnlinkImage (Except IO.Error Unit))
    (syncDirectory : FilePath → EStateM IO.Error WalSealedUnlinkImage Unit)
    {result : Except IO.Error Unit} {reached : WalSealedUnlinkImage}
    (returned : removeFile resolved.unlinkPath (.start before.wal) = .ok result reached)
    (report : WalFirstUnlinkReport resolved before.wal result reached) :
    let start := WalSealedUnlinkImage.start before.wal
    let projected := if report.removed then start.unlink first else start
    resolved.unlinkChild.child = resolved.statChild.child ∧
      WalSealedUnlinkTrace before.wal projected ∧ reached.visible = projected.visible ∧
      (∀ sealed ∈ reached.crashSealed, sealed ∈ projected.crashSealed) ∧
      (∀ sealed ∈ reached.crashSealed, WalSegmentCollectionRetry before.wal {reached.visible with sealed}) ∧
      rest.filter (fun offset => reached.visible.collectionOffsets.contains offset) =
        rest.filter (fun offset => !report.removed || offset != first) ∧
      (result = .ok () → report.removed = true) ∧
      (∀ cause, result = .error cause →
        calls.collectWithEffects directory removeFile syncDirectory (.ready before.installed, ⟨start, before.owners⟩) =
          .error cause (.poisoned, ⟨reached, before.owners⟩)) := by
  intro start projected
  obtain ⟨trace, visible, survivors⟩ := report.projects ready.layout (approved first List.mem_cons_self)
  refine ⟨resolved.sameChild, trace, visible, survivors, ?_, ?_, report.completed, ?_⟩
  · intro sealed member
    rw [visible]
    exact (trace.projects ready.layout).2 sealed (survivors sealed member)
  · apply List.filter_congr
    intro offset member
    have keeps := report.remaining (approved offset (List.mem_cons_of_mem _ member))
    exact Bool.eq_iff_iff.mpr (List.contains_iff_mem.trans keeps)
  · intro cause failed
    rw [resolved.canonicalUnlink] at returned
    rw [calls.collectWithEffects_afterFirst directory removeFile syncDirectory before.installed
      ⟨start, before.owners⟩ planned returned, report.ownedResult, failed]

end Alvoki.Storage.DiskSession
