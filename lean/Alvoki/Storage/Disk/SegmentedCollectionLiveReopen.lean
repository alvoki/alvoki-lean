import Alvoki.Storage.Disk.SegmentedCollectionLockHandoff

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair

/-- Early failed opens and observed lock-reference drops can change the
owner of a pending collection, while its full namespace still survives. -/
inductive PendingCollectionOpenTrace (directory : DiskDirectory) (scratch : Option (ByteArray × Bool))
    (initial : LockedFileState WalSealedUnlinkImage) : LockedFileState WalSealedUnlinkImage → Prop where
  | start : PendingCollectionOpenTrace directory scratch initial initial
  | earlyFailure (prior : PendingCollectionOpenTrace directory scratch initial before)
      (attempt : BoundedReopenAttempt) (acquisition : TryLockObserves before.owners directory attempt.acquired)
      (localUnlock : attempt.unlock.LocalFlock)
      (early : attempt.acquired ≠ .ok true ∨ ∃ cause, attempt.prepare directory = .error cause)
      (returned : attempt.run directory (before.collectionReopenFiles scratch) = .error cause result) :
      PendingCollectionOpenTrace directory scratch initial { before with owners := result.owners }
  | referenceDrops (prior : PendingCollectionOpenTrace directory scratch initial before)
      (references : HeldLockReferences description) (drops : List LockReferenceDrop) :
      PendingCollectionOpenTrace directory scratch initial (references.afterFileDrops drops directory before)

theorem PendingCollectionOpenTrace.keepsNamespace {directory scratch initial after}
    (trace : PendingCollectionOpenTrace directory scratch initial after) : after.image = initial.image := by
  induction trace with
  | start => rfl
  | earlyFailure _ attempt _ _ early returned ih =>
    exact (attempt.keepsPendingCollectionBeforeBarrier _ scratch early returned).2.trans ih
  | referenceDrops _ _ _ ih => exact ih

private def releasedCollection (directory : DiskDirectory) (before : SegmentedWriterState)
    (reached : WalSealedUnlinkImage) : LockedFileState WalSealedUnlinkImage :=
  ⟨reached, before.owners.set (directory.file .lock) none⟩

/-- Close the poisoned handle after a collection error, then use the
bounded opener with the exact ownership map left by earlier attempts. -/
structure SegmentedCollectionReopenReport (directory : DiskDirectory) (before : SegmentedWriterState)
    (writer descriptor : Nat) where
  reached : WalSealedUnlinkImage
  failed : SegmentedCollectionErrors directory before reached
  pending : LockedFileState WalSealedUnlinkImage
  attempts : PendingCollectionOpenTrace directory before.files.keeper.staged
    (releasedCollection directory before reached) pending
  reopen : BoundedReopenAttempt
  raw : HealthyBoundedWalReports directory (pending.owners.set (directory.file .lock) (some reopen.descriptor))
    reopen.descriptor reached.visible reached.visible.directory.active before.target.range.watermark before.published.durable
    ByteArray.empty
  liveRefs : List Nat
  syncWithNamespace : Array FilePath → EStateM IO.Error (FileImage × WalSealedUnlinkImage) Unit

namespace SegmentedCollectionReopenReport

variable {directory : DiskDirectory} {before : SegmentedWriterState} {writer descriptor : Nat}

def files (report : SegmentedCollectionReopenReport directory before writer descriptor) :
    LockedFileState FileImage :=
  report.pending.collectionReopenFiles before.files.keeper.staged

def barrier (report : SegmentedCollectionReopenReport directory before writer descriptor) :
    EStateM.Result IO.Error (FileImage × WalSealedUnlinkImage) Unit :=
  report.syncWithNamespace #[directory.path] (report.files.image, report.pending.image)

structure Valid (report : SegmentedCollectionReopenReport directory before writer descriptor) : Prop where
  descriptorEq : report.reopen.descriptor = descriptor
  acquired : report.reopen.acquired = .ok true
  acquisition : TryLockObserves report.pending.owners directory report.reopen.acquired
  reads : report.reopen.recover directory =
    report.raw.reopen report.reopen.removeFile report.reopen.write report.reopen.sync report.reopen.renameFile
  fresh : ∀ ref ∈ report.liveRefs, ref < report.reopen.nextRef
  directoryProjection : report.reopen.sync #[directory.path] report.files.image =
    projectCollectionBarrier report.barrier
  directoryEffect : report.barrier = .ok () (report.files.image.syncDirectory, report.pending.image.syncDirectory)
  syncKeeper : report.reopen.sync #[directory.file (.walSegment report.reached.visible.active.first)]
      report.files.image.syncDirectory = .ok () report.files.image.syncDirectory.syncKeeper

private def reopenedWriter (report : SegmentedCollectionReopenReport directory before writer descriptor)
    (installed : Installed) (final : LockedFileState FileImage) : SegmentedWriterState :=
  SegmentedWriterState.ofReopen installed report.reached.visible before.history before.published before.target
    before.checkpoint final

structure Installs (report : SegmentedCollectionReopenReport directory before writer descriptor)
    (after : SegmentedWriterState) : Prop where
  closed : runCloseWithFiles directory writer .success ((.poisoned : Phase Installed), ⟨report.reached, before.owners⟩) =
    .ok () (.closed, releasedCollection directory before report.reached)
  opened : ∃ session final installed,
    report.reopen.run directory report.files = .ok session final ∧ session.phase = .ready installed ∧
    after = report.reopenedWriter installed final

private theorem sameTarget {left right : Target} (pair : left.pair = right.pair)
    (first : left.first = right.first) (trimmed : left.trimmed = right.trimmed) : left = right := by
  have range : left.range = right.range := Option.some.inj (left.decoded.symm.trans (pair ▸ right.decoded))
  cases left
  cases right
  cases pair
  cases range
  cases first
  cases trimmed
  rfl

/-- Assemble the writer from the actual close and last bounded attempt.
Every earlier failure uses the exact owners left by its predecessor. -/
theorem installs (report : SegmentedCollectionReopenReport directory before writer descriptor)
    (observed : report.Valid) (ready : before.RetainedReady directory writer) :
    ∃ after, report.Installs after ∧ after.RetainedReady directory descriptor := by
  have closed := report.failed.close ready (phase := .poisoned) (by simp)
  have namespaceEq : report.pending.image = report.reached := report.attempts.keepsNamespace
  have filesEq : report.files =
      (⟨report.reached, report.pending.owners⟩ : LockedFileState WalSealedUnlinkImage).collectionReopenFiles
        before.files.keeper.staged := by
    unfold files LockedFileState.collectionReopenFiles
    rw [namespaceEq]
  obtain ⟨_, session, final, after, returned, _, _, phase, nextFiles, nextOwners, _, _, pair, history, checkpoint,
    next, wal, durable⟩ :=
    report.failed.openAfterRelease ready report.reopen observed.acquired observed.acquisition report.raw observed.reads
      report.liveRefs
      observed.fresh report.syncWithNamespace (by simpa only [barrier, filesEq, namespaceEq] using observed.directoryProjection)
      (by simpa only [barrier, filesEq, namespaceEq] using observed.directoryEffect)
      (by simpa only [filesEq] using observed.syncKeeper)
  have actual : report.reopen.run directory report.files = .ok session final := by
    simpa only [filesEq] using returned
  have kept := ((report.failed.keepsNamespace ready).1.projects ready.layout).1.keepsActive
  have first : after.target.first = before.target.first := by
    rw [next.active, wal]
    exact (congrArg WalSegment.first kept).trans ready.active.symm
  have target : after.target = before.target := sameTarget pair first (by
    rw [next.resumed.contents, history, first, ready.resumed.contents])
  have manifest := next.manifestFiles.trans (congrArg (fun image : FileImage => image.directory.project .manifest) nextFiles)
  have published : after.published = { before.published with manifest := final.image.directory.project .manifest } := by
    cases nextPub : after.published
    cases prevPub : before.published
    simp only [nextPub] at manifest
    simp only [nextPub, prevPub] at durable
    exact CheckpointPublication.Image.mk.injEq .. |>.mpr ⟨manifest, durable⟩
  have same : after = report.reopenedWriter after.installed final := by
    cases after
    simp only [reopenedWriter, SegmentedWriterState.ofReopen, SegmentedWriterState.mk.injEq, true_and]
    exact ⟨wal, history, nextFiles, published, target, checkpoint, nextOwners⟩
  exact ⟨after, ⟨closed, session, final, after.installed, actual, phase, same⟩, observed.descriptorEq ▸ next⟩

theorem Installs.unique {report : SegmentedCollectionReopenReport directory before writer descriptor}
    {left right : SegmentedWriterState} (a : report.Installs left) (b : report.Installs right) : left = right := by
  obtain ⟨_, _, leftInstalled, leftOpen, leftPhase, rfl⟩ := a.opened
  obtain ⟨_, _, rightInstalled, rightOpen, rightPhase, rfl⟩ := b.opened
  obtain ⟨rfl, rfl⟩ := EStateM.Result.ok.inj (leftOpen.symm.trans rightOpen)
  rw [Phase.ready.inj (leftPhase.symm.trans rightPhase)]

theorem Installs.preservesRetained {report : SegmentedCollectionReopenReport directory before writer descriptor}
    {after : SegmentedWriterState} (endpoint : report.Installs after) (observed : report.Valid)
    (ready : before.RetainedReady directory writer) : after.RetainedReady directory descriptor := by
  obtain ⟨_, exactEndpoint, next⟩ := report.installs observed ready
  exact exactEndpoint.unique endpoint ▸ next

theorem Installs.history {report : SegmentedCollectionReopenReport directory before writer descriptor}
    {after : SegmentedWriterState} (endpoint : report.Installs after) : after.history = before.history := by
  obtain ⟨_, _, _, _, _, rfl⟩ := endpoint.opened
  rfl

end SegmentedCollectionReopenReport
end Alvoki.Storage.DiskSession
