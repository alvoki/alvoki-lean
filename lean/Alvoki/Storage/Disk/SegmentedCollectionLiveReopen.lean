import Alvoki.Storage.Disk.SegmentedCollectionKeeperError

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair

/-- Failed opens keep the exact returned physical namespace, scratch binding,
and lock. A directory barrier may settle the list even if it reports an error. -/
inductive PendingCollectionOpenTrace (directory : DiskDirectory) (initialScratch : Option (ByteArray × Bool))
    (initial : LockedFileState WalSealedUnlinkImage) :
    LockedFileState WalSealedUnlinkImage → Option (ByteArray × Bool) → Prop where
  | start : PendingCollectionOpenTrace directory initialScratch initial initial initialScratch
  | earlyFailure (prior : PendingCollectionOpenTrace directory initialScratch initial before scratch)
      (attempt : BoundedReopenAttempt) (acquisition : TryLockObserves before.owners directory attempt.acquired)
      (localUnlock : attempt.unlock.LocalFlock)
      (early : attempt.acquired ≠ .ok true ∨ ∃ cause, attempt.prepare directory = .error cause)
      (returned : attempt.run directory (before.collectionReopenFiles scratch) = .error cause result) :
      PendingCollectionOpenTrace directory initialScratch initial { before with owners := result.owners } scratch
  | barrierFailure (prior : PendingCollectionOpenTrace directory initialScratch initial before scratch)
      (report : PendingCollectionBarrierFailure directory scratch before) :
      PendingCollectionOpenTrace directory initialScratch initial report.after scratch
  | keeperFailure (prior : PendingCollectionOpenTrace directory initialScratch initial before scratch)
      (report : PendingCollectionKeeperFailure directory scratch before) :
      PendingCollectionOpenTrace directory initialScratch initial report.after report.nextFiles.keeper.staged
  | referenceDrops (prior : PendingCollectionOpenTrace directory initialScratch initial before scratch)
      (references : HeldLockReferences description) (drops : List LockReferenceDrop) :
      PendingCollectionOpenTrace directory initialScratch initial (references.afterFileDrops drops directory before) scratch

private theorem syncPending {initial reached : WalSealedUnlinkImage}
    (same : reached = initial ∨ reached = initial.syncDirectory) :
    reached.syncDirectory = initial.syncDirectory := by
  rcases same with rfl | rfl <;> rfl

/-- Each observed attempt leaves the original namespace or settles its
exact visible files. Later failures cannot restore alternatives once settled. -/
theorem PendingCollectionOpenTrace.keepsNamespace {directory initialScratch initial after scratch}
    (trace : PendingCollectionOpenTrace directory initialScratch initial after scratch) :
    after.image = initial.image ∨ after.image = initial.image.syncDirectory := by
  induction trace with
  | start => exact Or.inl rfl
  | earlyFailure _ attempt _ _ early returned ih =>
    rw [(attempt.keepsPendingCollectionBeforeBarrier _ _ early returned).2]
    exact ih
  | barrierFailure _ report ih =>
    rcases report.namespaceState with unchanged | settled
    · rw [unchanged]
      exact ih
    · exact Or.inr (settled.trans (syncPending ih))
  | keeperFailure _ _ ih => exact Or.inr (syncPending ih)
  | referenceDrops _ _ _ ih => exact ih

theorem PendingCollectionOpenTrace.keepsVisible {directory initialScratch initial after scratch}
    (trace : PendingCollectionOpenTrace directory initialScratch initial after scratch)
    (metadata : initial.image.visible.directory.crashImages = [initial.image.visible.directory.active]) :
    after.image.visible = initial.image.visible := by
  rcases trace.keepsNamespace with unchanged | settled
  · rw [unchanged]
  · rw [settled]
    exact (CollectionBarrierErrorEffect.afterEffect (files := (initial.collectionReopenFiles initialScratch).image)
      (pending := initial.image)).keepsVisible metadata

theorem PendingCollectionOpenTrace.keepsSettled {directory initialScratch initial after scratch}
    (trace : PendingCollectionOpenTrace directory initialScratch initial after scratch)
    (settled : initial.image.syncDirectory = initial.image) : after.image = initial.image :=
  trace.keepsNamespace.elim id (fun finished => finished.trans settled)

theorem PendingCollectionOpenTrace.continues {directory initialScratch initial after scratch} {wal : WalSegmentImage}
    (trace : PendingCollectionOpenTrace directory initialScratch initial after scratch)
    (prior : WalSealedUnlinkTrace wal initial.image) : WalSealedUnlinkTrace wal after.image := by
  induction trace with
  | start => exact prior
  | earlyFailure _ _ _ _ _ _ ih => exact ih
  | barrierFailure _ report ih => exact report.effect.reaches ih
  | keeperFailure _ _ ih => exact ih.sync
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
  scratch : Option (ByteArray × Bool)
  attempts : PendingCollectionOpenTrace directory before.files.keeper.staged
    (releasedCollection directory before reached) pending scratch
  reopen : BoundedReopenAttempt
  raw : HealthyBoundedWalReports directory (pending.owners.set (directory.file .lock) (some reopen.descriptor))
    reopen.descriptor pending.image.visible pending.image.visible.directory.active before.target.range.watermark before.published.durable
    ByteArray.empty
  liveRefs : List Nat
  syncWithNamespace : Array FilePath → EStateM IO.Error (FileImage × WalSealedUnlinkImage) Unit

namespace SegmentedCollectionReopenReport

variable {directory : DiskDirectory} {before : SegmentedWriterState} {writer descriptor : Nat}

def files (report : SegmentedCollectionReopenReport directory before writer descriptor) :
    LockedFileState FileImage :=
  report.pending.collectionReopenFiles report.scratch

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
  syncKeeper : report.reopen.sync #[directory.file (.walSegment report.pending.image.visible.active.first)]
      report.files.image.syncDirectory = .ok () report.files.image.syncDirectory.syncKeeper

private def reopenedWriter (report : SegmentedCollectionReopenReport directory before writer descriptor)
    (installed : Installed) (final : LockedFileState FileImage) : SegmentedWriterState :=
  SegmentedWriterState.ofReopen installed report.pending.image.visible before.history before.published before.target
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
  obtain ⟨_, session, final, after, returned, _, _, phase, nextFiles, nextOwners, _, _, pair, history, checkpoint,
    next, wal, durable⟩ :=
    report.failed.openAfterRelease ready report.attempts.keepsNamespace (scratch := report.scratch) report.reopen observed.acquired
      observed.acquisition report.raw observed.reads report.liveRefs observed.fresh report.syncWithNamespace
      observed.directoryProjection observed.directoryEffect observed.syncKeeper
  have actual : report.reopen.run directory report.files = .ok session final := returned
  have reached := report.attempts.continues (report.failed.keepsNamespace ready).1
  have kept := (reached.projects ready.layout).1.keepsActive
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
