import Alvoki.Storage.Disk.WalCollectionFirstEffect

namespace Alvoki.Storage.DiskSession

open System

/-- One invocation's no-follow lookup in the fixed parent, its local
detach effect, and the before/after physical projection. An already
missing name may report ENOENT and leave earlier crash choices intact. -/
structure WalUnlinkEffect (root : DeviceInode) (first : Nat) (view : DirectoryReadNamespace)
    (before : WalSealedUnlinkImage) (result : Except IO.Error Unit)
    (afterView : DirectoryReadNamespace) (after : WalSealedUnlinkImage) where
  target : Option DeviceInode
  lookup : view.child root (renderWalSegmentName first) = target
  removed : Bool
  detach : removed = true → target.isSome = true
  binding : afterView.child root (renderWalSegmentName first) = if removed then none else target
  frame : ∀ name, name ≠ renderWalSegmentName first → afterView.child root name = view.child root name
  visible : after.visible.sealed = before.visible.sealed.filter fun segment =>
    (afterView.child root (renderWalSegmentName segment.first)).isSome
  keeper : after.visible.active = before.visible.active
  metadata : after.visible.directory = before.visible.directory
  survivors : ∀ sealed ∈ after.crashSealed, ∃ earlier ∈ before.crashSealed,
    sealed = earlier ∨ removed = true ∧ sealed = earlier.filter (fun segment => segment.first != first)
  completed : result = .ok () → removed = true
  missing : ∀ path message, result = .error (.noFileOrDirectory path 2 message) → target = none

namespace WalUnlinkEffect

variable {root : DeviceInode} {first : Nat} {view afterView : DirectoryReadNamespace}
  {before after : WalSealedUnlinkImage} {result : Except IO.Error Unit}

theorem lookupAfter (report : WalUnlinkEffect root first view before result afterView after) (offset : Nat) :
    afterView.child root (renderWalSegmentName offset) =
      if report.removed && offset == first then none else view.child root (renderWalSegmentName offset) := by
  by_cases equal : offset = first
  · simp [equal, report.binding, report.lookup]
  · have different : renderWalSegmentName offset ≠ renderWalSegmentName first := by
      intro same
      exact equal (by simpa only [parseWalSegmentName_render, Option.some.injEq] using congrArg parseWalSegmentName same)
    simp [equal, report.frame _ different]

/-- At the first invocation this primitive target is the object whose
extent the planner measured. Later invocations use the evolving view. -/
theorem firstTarget {calls : WalCollectionReads} {directory : DiskDirectory}
    (resolved : WalSealUnlinkResolution calls directory first)
    (report : WalUnlinkEffect resolved.root first resolved.unlinkView before result afterView after) :
    report.target = some resolved.statChild.child := by
  have binding := resolved.unlinkChild.binds
  rw [resolved.unlinkChild.atRoot, resolved.unlinkChild.atName, resolved.sameChild] at binding
  exact report.lookup.symm.trans binding

/-- A successful classified unlink either detached that binding or
observed that the canonical name was already absent. -/
theorem accepted (report : WalUnlinkEffect root first view before result afterView after)
    (success : RunCollection.ownedUnlinkResult result = .ok ()) :
    report.removed = true ∨ view.child root (renderWalSegmentName first) = none := by
  rcases RunCollection.ownedUnlinkResult_ok_iff.mp success with completed | ⟨path, message, missing⟩
  · exact .inl (report.completed completed)
  · exact .inr (report.lookup.trans (report.missing path message missing))

/-- Lift the physical name frame to the ordered list of immutable seals. -/
theorem sealedAfter (report : WalUnlinkEffect root first view before result afterView after)
    (bound : ∀ segment ∈ before.visible.sealed,
      (view.child root (renderWalSegmentName segment.first)).isSome = true) :
    after.visible.sealed = before.visible.sealed.filter (fun segment => !report.removed || segment.first != first) := by
  rw [report.visible]
  apply List.filter_congr
  intro segment member
  rw [report.lookupAfter]
  have present := bound segment member
  by_cases same : segment.first = first
  · rw [same] at present ⊢
    cases report.removed <;> simp [present]
  · simp [same, present]

theorem eligibleAfter (report : WalUnlinkEffect root first view before result afterView after)
    (bound : ∀ segment ∈ before.visible.sealed,
      (view.child root (renderWalSegmentName segment.first)).isSome = true) (offset : Nat) :
    offset ∈ after.visible.collectionOffsets ↔
      offset ∈ before.visible.collectionOffsets ∧ (!report.removed || offset != first) = true := by
  have canRemove segment : after.visible.canRemove segment = before.visible.canRemove segment := by
    simp [WalSegmentImage.canRemove, report.keeper, report.metadata]
  simp only [WalSegmentImage.collectionOffsets, List.mem_map, List.mem_filter, report.sealedAfter bound, canRemove]
  constructor
  · rintro ⟨segment, ⟨⟨member, kept⟩, eligible⟩, rfl⟩
    exact ⟨⟨segment, ⟨member, eligible⟩, rfl⟩, kept⟩
  · rintro ⟨⟨segment, ⟨member, eligible⟩, rfl⟩, kept⟩
    exact ⟨segment, ⟨⟨member, kept⟩, eligible⟩, rfl⟩

end WalUnlinkEffect

/-- The first resolved stat/unlink report is the base callback for the
ordered proof. Its original inode is preserved as the raw target. -/
def WalFirstUnlinkReport.toOrderedEffect {calls : WalCollectionReads} {directory : DiskDirectory} {first : Nat}
    {resolved : WalSealUnlinkResolution calls directory first} {initial : WalSegmentImage}
    {result : Except IO.Error Unit} {after : WalSealedUnlinkImage}
    (report : WalFirstUnlinkReport resolved initial result after)
    {history : List WAL.Write} (layout : initial.ReadLayout history) (approved : first ∈ initial.collectionOffsets) :
    WalUnlinkEffect resolved.root first resolved.unlinkView (.start initial) result report.afterView after where
  target := some resolved.unlinkChild.child
  lookup := by
    have bound := resolved.unlinkChild.binds
    simpa only [resolved.unlinkChild.atRoot, resolved.unlinkChild.atName] using bound
  removed := report.removed
  detach := fun _ => rfl
  binding := report.binding
  frame := report.otherBindings
  visible := report.visibleSealed
  keeper := report.keeper
  metadata := report.metadata
  survivors := by
    intro sealed member
    refine ⟨initial.sealed, List.mem_cons_self, ?_⟩
    rcases report.survivors sealed member with unchanged | ⟨removed, changed⟩
    · exact .inl unchanged
    · refine .inr ⟨removed, ?_⟩
      have visible := (report.projects layout approved).2.1
      obtain ⟨segment, included, atFirst⟩ := (layout.collectionOffsets_approved approved).1
      have found : initial.sealed.any (fun segment => segment.first == first) = true :=
        List.any_eq_true.mpr ⟨segment, included, by simp [atFirst]⟩
      simp only [removed, ite_true, WalSealedUnlinkImage.start, WalSealedUnlinkImage.unlink, found] at visible
      exact changed.trans (congrArg WalSegmentImage.sealed visible)
  completed := report.completed
  missing := by
    intro path message missing
    have bound := resolved.unlinkChild.binds
    rw [resolved.unlinkChild.atRoot, resolved.unlinkChild.atName, report.missing path message missing] at bound
    contradiction

/-- Link the evolving native bindings and reported sealed possibilities
to the initial writer. The abstract list may contain additional crash
choices. Each original sealed descriptor has its exact reached binding
presence, so a later effect cannot reuse an obsolete namespace view. -/
structure WalUnlinkInvariant (initial : WalSegmentImage) (root : DeviceInode)
    (view : DirectoryReadNamespace) (physical projected : WalSealedUnlinkImage) : Prop where
  trace : WalSealedUnlinkTrace initial projected
  visible : physical.visible = projected.visible
  survivors : ∀ sealed ∈ physical.crashSealed, sealed ∈ projected.crashSealed
  sealedNames : ∀ segment ∈ initial.sealed,
    segment ∈ physical.visible.sealed ↔ (view.child root (renderWalSegmentName segment.first)).isSome = true

namespace WalUnlinkInvariant

variable {initial : WalSegmentImage} {root : DeviceInode} {view : DirectoryReadNamespace}
  {physical projected : WalSealedUnlinkImage}

theorem start (bound : ∀ segment ∈ initial.sealed,
    (view.child root (renderWalSegmentName segment.first)).isSome = true) :
    WalUnlinkInvariant initial root view (.start initial) (.start initial) :=
  ⟨.start, rfl, fun _ member => member, fun segment member => ⟨fun _ => bound segment member, fun _ => member⟩⟩

theorem bound {history : List WAL.Write} (prior : WalUnlinkInvariant initial root view physical projected)
    (layout : initial.ReadLayout history) (segment : WalSegment) (member : segment ∈ physical.visible.sealed) :
    (view.child root (renderWalSegmentName segment.first)).isSome = true := by
  have retry := (prior.trace.projects layout).1
  have original := retry.sealedSublist.subset (prior.visible ▸ member)
  exact (prior.sealedNames segment original).mp member

private theorem image_eq {left right : WalSegmentImage}
    (metadata : left.directory = right.directory) (seals : left.sealed = right.sealed)
    (keeper : left.active = right.active) : left = right := by
  cases left
  cases right
  simp_all

theorem unlink {history : List WAL.Write} (prior : WalUnlinkInvariant initial root view physical projected)
    (layout : initial.ReadLayout history) {first : Nat} (approved : first ∈ initial.collectionOffsets)
    {afterView : DirectoryReadNamespace} {result : Except IO.Error Unit} {after : WalSealedUnlinkImage}
    (report : WalUnlinkEffect root first view physical result afterView after) :
    WalUnlinkInvariant initial root afterView after (if report.removed then projected.unlink first else projected) := by
  have filtered := report.sealedAfter (prior.bound layout)
  have named segment (original : segment ∈ initial.sealed) :
      segment ∈ after.visible.sealed ↔
        (afterView.child root (renderWalSegmentName segment.first)).isSome = true := by
    rw [report.visible, List.mem_filter, prior.sealedNames segment original, report.lookupAfter]
    by_cases same : segment.first = first <;> cases report.removed <;> simp [same]
  have keeper := report.keeper.trans (congrArg WalSegmentImage.active prior.visible)
  have metadata := report.metadata.trans (congrArg WalSegmentImage.directory prior.visible)
  by_cases removed : report.removed = true
  · obtain ⟨segment, original, atFirst⟩ := (layout.collectionOffsets_approved approved).1
    have present : segment ∈ projected.visible.sealed := by
      rw [← prior.visible]
      apply (prior.sealedNames segment original).mpr
      rw [atFirst, report.lookup]
      exact report.detach removed
    have found : projected.visible.sealed.any (fun segment => segment.first == first) = true :=
      List.any_eq_true.mpr ⟨segment, present, by simp [atFirst]⟩
    simp only [removed, ite_true]
    refine ⟨.unlink prior.trace approved, ?_, ?_, named⟩
    · simp only [WalSealedUnlinkImage.unlink, found, ite_true]
      refine image_eq ?_ ?_ ?_
      · exact metadata
      · rw [filtered, prior.visible]
        simp only [removed, Bool.not_true, Bool.false_or]
        rfl
      · exact keeper
    · intro sealed member
      simp only [WalSealedUnlinkImage.unlink, found, ite_true]
      obtain ⟨earlier, previous, equal | ⟨_, equal⟩⟩ := report.survivors sealed member
      · exact List.mem_append_right _ (equal ▸ prior.survivors earlier previous)
      · apply List.mem_append_left
        exact List.mem_map.mpr ⟨earlier, prior.survivors earlier previous, equal.symm⟩
  · have inert : report.removed = false := Bool.eq_false_iff.mpr removed
    simp only [removed]
    refine ⟨prior.trace, ?_, ?_, named⟩
    · apply image_eq metadata _ keeper
      exact filtered.trans ((List.filter_eq_self.mpr (fun _ _ => by simp [inert])).trans
        (congrArg WalSegmentImage.sealed prior.visible))
    · intro sealed member
      obtain ⟨earlier, previous, equal | ⟨detached, _⟩⟩ := report.survivors sealed member
      · exact equal ▸ prior.survivors earlier previous
      · exact (removed detached).elim

end WalUnlinkInvariant

/-- Ordered completed callbacks in the originally planned sequence.
Stopping before the next invocation leaves the pending suffix, including
the directory sync when the suffix is empty. A returned unlink error
terminates at that invocation. If failure leaves the image unchanged,
no successful lookup is needed. Each step uses the namespace reached by
the previous callback. -/
inductive WalUnlinkPrefix (directory : DiskDirectory) (root : DeviceInode)
    (removeFile : FilePath → EStateM IO.Error WalSealedUnlinkImage (Except IO.Error Unit)) :
    List Nat → DirectoryReadNamespace → WalSealedUnlinkImage →
      List Nat → Option IO.Error → DirectoryReadNamespace → WalSealedUnlinkImage → List Nat → Prop where
  | pause : WalUnlinkPrefix directory root removeFile pending view before pending none view before []
  | next
      (call : removeFile (directory.file (.walSegment first)) before = .ok result middle)
      (effect : WalUnlinkEffect root first view before result middleView middle)
      (accepted : RunCollection.ownedUnlinkResult result = .ok ())
      (tail : WalUnlinkPrefix directory root removeFile rest middleView middle pending failure afterView after removed) :
      WalUnlinkPrefix directory root removeFile (first :: rest) view before pending failure afterView after
        ((if effect.removed then [first] else []) ++ removed)
  | failed
      (call : removeFile (directory.file (.walSegment first)) before = .ok result after)
      (effect : WalUnlinkEffect root first view before result afterView after)
      (returned : RunCollection.ownedUnlinkResult result = .error cause) :
      WalUnlinkPrefix directory root removeFile (first :: rest) view before rest (some cause) afterView after
        (if effect.removed then [first] else [])
  | failedWithoutEffect
      (call : removeFile (directory.file (.walSegment first)) before = .ok result before)
      (returned : RunCollection.ownedUnlinkResult result = .error cause) :
      WalUnlinkPrefix directory root removeFile (first :: rest) view before rest (some cause) view before []

namespace WalUnlinkPrefix

variable {directory : DiskDirectory} {root : DeviceInode}
  {removeFile : FilePath → EStateM IO.Error WalSealedUnlinkImage (Except IO.Error Unit)}
  {offsets pending removed : List Nat} {failure : Option IO.Error}
  {view afterView : DirectoryReadNamespace} {before after : WalSealedUnlinkImage}

/-- Every canonical name outside the detached offsets still binds to
its exact original inode after these calls. -/
theorem lookupAfter
    (reported : WalUnlinkPrefix directory root removeFile offsets view before pending failure afterView after removed)
    (offset : Nat) :
    afterView.child root (renderWalSegmentName offset) =
      if removed.contains offset then none else view.child root (renderWalSegmentName offset) := by
  induction reported with
  | pause => rfl
  | next call effect accepted tail ih =>
    rw [ih, effect.lookupAfter]
    simp only [List.contains_append]
    cases effect.removed with
    | false => simp
    | true =>
      simp only [Bool.true_and, ↓reduceIte, List.contains_cons, List.contains_nil, Bool.or_false]
      rw [Bool.or_comm]
      split <;> simp_all
  | failed call effect returned =>
    rw [effect.lookupAfter]
    cases effect.removed <;> simp
  | failedWithoutEffect => rfl

theorem dispatch (reported : WalUnlinkPrefix directory root removeFile offsets view before pending failure afterView after removed)
    (syncDirectory : FilePath → EStateM IO.Error WalSealedUnlinkImage Unit)
    (installed : Installed) (owner : LockOwners) :
    WalCollectionReads.continueWithEffects directory removeFile syncDirectory installed offsets (.poisoned, ⟨before, owner⟩) =
      match failure with
      | none => WalCollectionReads.continueWithEffects directory removeFile syncDirectory installed pending
          (.poisoned, ⟨after, owner⟩)
      | some cause => .error cause (.poisoned, ⟨after, owner⟩) := by
  induction reported with
  | pause => rfl
  | next call _ accepted _ ih =>
    rw [WalCollectionReads.continueWithEffects_unlink directory removeFile syncDirectory installed ⟨_, owner⟩ call,
      accepted]
    exact ih
  | failed call _ returned | failedWithoutEffect call returned =>
    rw [WalCollectionReads.continueWithEffects_unlink directory removeFile syncDirectory installed ⟨_, owner⟩ call,
      returned]

/-- The finite physical reports refine the same shared trace along their
exact sequence. The removed-offset list records effects even when the
last callback returns an error. -/
theorem projects
    (reported : WalUnlinkPrefix directory root removeFile offsets view before pending failure afterView after removed)
    {initial : WalSegmentImage} {projected : WalSealedUnlinkImage} {history : List WAL.Write}
    (layout : initial.ReadLayout history) (prior : WalUnlinkInvariant initial root view before projected)
    (approved : ∀ offset ∈ offsets, offset ∈ initial.collectionOffsets) :
    (∃ final, WalUnlinkInvariant initial root afterView after final) ∧
      pending.Sublist offsets ∧
      ∀ offset, offset ∈ after.visible.collectionOffsets ↔
        offset ∈ before.visible.collectionOffsets ∧ offset ∉ removed := by
  induction reported generalizing projected with
  | pause => exact ⟨⟨projected, prior⟩, List.Sublist.refl _, by simp⟩
  | next call effect accepted tail ih =>
    have advanced := prior.unlink layout (approved _ List.mem_cons_self) effect
    obtain ⟨final, included, eligible⟩ := ih advanced (fun offset member => approved offset (List.mem_cons_of_mem _ member))
    refine ⟨final, included.cons _, ?_⟩
    intro offset
    rw [eligible, effect.eligibleAfter (prior.bound layout)]
    by_cases effective : effect.removed = true <;> simp [effective, and_assoc, and_left_comm]
  | failed call effect returned =>
    refine ⟨⟨_, prior.unlink layout (approved _ List.mem_cons_self) effect⟩, (List.Sublist.refl _).cons _, ?_⟩
    intro offset
    rw [effect.eligibleAfter (prior.bound layout)]
    by_cases effective : effect.removed = true <;> simp [effective]
  | failedWithoutEffect =>
    exact ⟨⟨projected, prior⟩, (List.Sublist.refl _).cons _, by simp⟩

end WalUnlinkPrefix

/-- Compose the actual observed planner and its approved offsets with
the reached mutation prefix. An error returns the original diagnostic
and exact files under the poisoned owner. A successful prefix resumes
the same schedule, including the directory barrier after the final name. -/
theorem SegmentedWriterState.RetainedReady.reportedWalUnlinkPrefix
    {directory : DiskDirectory} {descriptor : Nat} {before : SegmentedWriterState}
    (ready : before.RetainedReady directory descriptor) (calls : WalCollectionReads)
    {root : DeviceInode} {view afterView : DirectoryReadNamespace}
    {offsets pending removed : List Nat} {failure : Option IO.Error} {after : WalSealedUnlinkImage}
    (planned : calls.plan directory before.installed = .ok offsets)
    (approved : ∀ offset ∈ offsets, offset ∈ before.wal.collectionOffsets)
    (bound : ∀ segment ∈ before.wal.sealed,
      (view.child root (renderWalSegmentName segment.first)).isSome = true)
    (removeFile : FilePath → EStateM IO.Error WalSealedUnlinkImage (Except IO.Error Unit))
    (syncDirectory : FilePath → EStateM IO.Error WalSealedUnlinkImage Unit)
    (reported : WalUnlinkPrefix directory root removeFile offsets view (.start before.wal)
      pending failure afterView after removed) :
    (∃ final, WalUnlinkInvariant before.wal root afterView after final) ∧
      (∀ sealed ∈ after.crashSealed, WalSegmentCollectionRetry before.wal {after.visible with sealed}) ∧
      (∀ offset, afterView.child root (renderWalSegmentName offset) =
        if removed.contains offset then none else view.child root (renderWalSegmentName offset)) ∧
      pending.filter (fun offset => after.visible.collectionOffsets.contains offset) =
        pending.filter (fun offset => !removed.contains offset) ∧
      calls.collectWithEffects directory removeFile syncDirectory (.ready before.installed, ⟨.start before.wal, before.owners⟩) =
        match failure with
        | some cause => .error cause (.poisoned, ⟨after, before.owners⟩)
        | none => WalCollectionReads.continueWithEffects directory removeFile syncDirectory before.installed pending
            (.poisoned, ⟨after, before.owners⟩) := by
  obtain ⟨⟨final, invariant⟩, included, eligible⟩ :=
    reported.projects ready.layout (WalUnlinkInvariant.start bound) approved
  refine ⟨⟨final, invariant⟩, ?_, reported.lookupAfter, ?_, ?_⟩
  · intro sealed member
    rw [invariant.visible]
    exact (invariant.trace.projects ready.layout).2 sealed (invariant.survivors sealed member)
  · apply List.filter_congr
    intro offset member
    have originally := approved offset (included.subset member)
    have iff := (eligible offset).trans (and_iff_right originally)
    have survives : (!removed.contains offset) = true ↔ offset ∉ removed := by simp
    exact Bool.eq_iff_iff.mpr (List.contains_iff_mem.trans (iff.trans survives.symm))
  · rw [calls.collectWithEffects_plan directory removeFile syncDirectory before.installed _ planned]
    cases failure <;> exact reported.dispatch syncDirectory before.installed before.owners

end Alvoki.Storage.DiskSession
