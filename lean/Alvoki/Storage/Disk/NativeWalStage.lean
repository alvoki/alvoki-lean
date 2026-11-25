import Alvoki.Storage.Disk.NativeWalAppend

namespace Alvoki.Storage.DiskSession

open System SyncHandleRouting

/-- Literal callbacks for the staging action of an opened table. `drop`
reports the release reached after a newly opened stream fails a data action. -/
structure RawWalStageCalls (heap : Type) where
  tryCreate : FilePath → EStateM IO.Error heap (Except IO.Error IO.FS.Handle)
  stat : FilePath → EStateM IO.Error heap (Except IO.Error IO.FS.Metadata)
  unlink : FilePath → EStateM IO.Error heap (Except IO.Error Unit)
  create : FilePath → EStateM IO.Error heap IO.FS.Handle
  write : IO.FS.Handle → ByteArray → EStateM IO.Error heap Unit
  flush : IO.FS.Handle → EStateM IO.Error heap Unit
  drop : IO.FS.Handle → EStateM IO.Error heap Unit
  remember : IO.Ref (List (FilePath × IO.FS.Handle)) →
    (List (FilePath × IO.FS.Handle) → List (FilePath × IO.FS.Handle)) → EStateM IO.Error heap Unit

/-- Refine the continuation exposed by `OpenSyncFiles.stageCacheSchedule`
to literal staging callbacks followed by the same pending-reference write. -/
theorem freshStageCacheSchedule (pending : IO.Ref (List (FilePath × IO.FS.Handle)))
    (path : FilePath) (bytes : ByteArray) :
    (writeFreshStagedHandle path bytes >>= fun handle => pending.modify (pushPending path handle)) =
      (writeFreshStagedWith (m := IO) (fun name => (IO.FS.Handle.mk name .writeNew).toBaseIO)
        (removeStaleStagingWith (m := IO) (fun name => name.symlinkMetadata.toBaseIO)
          (fun name => (IO.FS.removeFile name).toBaseIO))
        (fun name => IO.FS.Handle.mk name .writeNew) IO.FS.Handle.write IO.FS.Handle.flush path bytes >>= fun handle =>
        pending.modify (pushPending path handle)) := by
  rw [writeFreshStagedHandle_schedule]

namespace RawWalStageCalls

variable {heap : Type}

noncomputable def acquire (calls : RawWalStageCalls heap) (path : FilePath) :
    EStateM IO.Error heap IO.FS.Handle :=
  withFreshStaging calls.tryCreate (removeStaleStagingWith calls.stat calls.unlink) calls.create path pure

noncomputable def fresh (calls : RawWalStageCalls heap) (path : FilePath) (bytes : ByteArray) :
    EStateM IO.Error heap IO.FS.Handle :=
  writeFreshStagedWith calls.tryCreate (removeStaleStagingWith calls.stat calls.unlink) calls.create
    (fun file bytes => withDataErrorDrop calls.drop file (calls.write file bytes))
    (fun file => withDataErrorDrop calls.drop file (calls.flush file)) path bytes

noncomputable def run (calls : RawWalStageCalls heap) (pending : IO.Ref (List (FilePath × IO.FS.Handle)))
    (path : FilePath) (bytes : ByteArray) : EStateM IO.Error heap Unit := do
  let file ← calls.fresh path bytes
  calls.remember pending (pushPending path file)

private theorem keepsAfterBind {α β footprint : Type} (observe : heap → footprint)
    (first : EStateM IO.Error heap α) (next : α → EStateM IO.Error heap β) (entry : heap)
    (firstKeeps : observe (reachedState (first entry)) = observe entry)
    (nextKeeps : ∀ {value after}, first entry = .ok value after →
      observe (reachedState (next value after)) = observe after) :
    observe (reachedState ((first >>= next) entry)) = observe entry := by
  cases returned : first entry with
  | error cause after =>
    have kept : observe after = observe entry := by simpa [returned, reachedState] using firstKeeps
    simpa [Bind.bind, EStateM.bind, returned, reachedState] using kept
  | ok value after =>
    have kept := nextKeeps returned
    rw [returned] at firstKeeps
    simpa [Bind.bind, EStateM.bind, returned] using kept.trans firstKeeps

/-- Only the reached metadata read, unlink and exclusive retries can
affect the protected observation during scratch acquisition. -/
theorem acquireKeeps {footprint : Type} (calls : RawWalStageCalls heap) (path : FilePath)
    (observe : heap → footprint) (entry : heap)
    (tryKeeps : observe (reachedState (calls.tryCreate path entry)) = observe entry)
    (statKeeps : ∀ before, observe (reachedState (calls.stat path before)) = observe before)
    (unlinkKeeps : ∀ before, observe (reachedState (calls.unlink path before)) = observe before)
    (createKeeps : ∀ before, observe (reachedState (calls.create path before)) = observe before) :
    observe (reachedState (calls.acquire path entry)) = observe entry := by
  have detachKeeps : ∀ before, observe (reachedState (removeStaleStagingWith calls.stat calls.unlink path before)) =
      observe before := by
    intro before
    unfold removeStaleStagingWith
    refine keepsAfterBind observe _ _ before (statKeeps before) ?_
    intro metadata after returned
    split
    · rename_i info
      by_cases regular : info.type == .file
      · simp only [regular, ite_true]
        refine keepsAfterBind observe _ _ after (unlinkKeeps after) ?_
        intro result reached _
        cases RunCollection.ownedUnlinkResult result <;> rfl
      · simp [regular, Bind.bind, EStateM.bind, throw, throwThe, MonadExceptOf.throw, EStateM.throw, reachedState]
    next => rfl
    next => rfl
  unfold acquire withFreshStaging
  refine keepsAfterBind observe _ _ entry tryKeeps ?_
  intro result after _
  split
  next => rfl
  next =>
    refine keepsAfterBind observe _ _ after (detachKeeps after) ?_
    intro _ atCreate _
    exact keepsAfterBind observe _ _ atCreate (createKeeps atCreate) (fun _ => rfl)
  next => rfl

/-- The named scratch binding comes from the exclusive create that
actually returned the selected handle, including a retry after EEXIST. -/
theorem acquireBinds (calls : RawWalStageCalls heap) (path : FilePath)
    (binding : heap → FilePath → Option Nat) (inode : IO.FS.Handle → Nat)
    {entry opened : heap} {file : IO.FS.Handle}
    (acquired : calls.acquire path entry = .ok file opened)
    (first : ∀ {file reached}, calls.tryCreate path entry = .ok (.ok file) reached →
      binding reached path = some (inode file))
    (retry : ∀ {file before reached}, calls.create path before = .ok file reached →
      binding reached path = some (inode file)) :
    binding opened path = some (inode file) := by
  unfold acquire withFreshStaging at acquired
  cases tried : calls.tryCreate path entry with
  | error => simp [Bind.bind, EStateM.bind, tried] at acquired
  | ok initial reached =>
    simp only [Bind.bind, EStateM.bind, tried] at acquired
    split at acquired
    next selected =>
      simp [Pure.pure] at acquired
      obtain ⟨rfl, rfl⟩ := acquired
      exact first tried
    next =>
      cases detached : removeStaleStagingWith calls.stat calls.unlink path reached with
      | error => simp [EStateM.bind, detached] at acquired
      | ok value atRetry =>
        cases value
        cases created : calls.create path atRetry with
        | error => simp [EStateM.bind, detached, created] at acquired
        | ok selected atOpen =>
          simp [EStateM.bind, detached, created, Pure.pure] at acquired
          obtain ⟨rfl, rfl⟩ := acquired
          exact retry created
    next => simp [EStateM.bind, throw, throwThe, MonadExceptOf.throw, EStateM.throw] at acquired

private theorem freshStagingThen {handle α : Type}
    (tryCreate : FilePath → EStateM IO.Error heap (Except IO.Error handle))
    (detach : FilePath → EStateM IO.Error heap Unit) (create : FilePath → EStateM IO.Error heap handle)
    (path : FilePath) (use : handle → EStateM IO.Error heap α) :
    withFreshStaging tryCreate detach create path use =
      (withFreshStaging tryCreate detach create path pure >>= use) := by
  simp only [withFreshStaging, bind_assoc, pure_bind]
  congr 1
  funext outcome
  split <;> simp [bind_assoc]

/-- Derive the reached error from the failed acquisition or data action.
Release can change the file image and leaves the original diagnostic. -/
theorem fresh_effect (calls : RawWalStageCalls heap) (path : FilePath) (bytes : ByteArray) (entry : heap) :
    calls.fresh path bytes entry =
      match calls.acquire path entry with
      | .error cause reached => .error cause reached
      | .ok file opened => match calls.write file bytes opened with
        | .error cause reached => .error cause (dataErrorDropState calls.drop file reached)
        | .ok () written => match calls.flush file written with
          | .error cause reached => .error cause (dataErrorDropState calls.drop file reached)
          | .ok () flushed => .ok file flushed := by
  unfold fresh writeFreshStagedWith
  rw [freshStagingThen]
  change (calls.acquire path >>= fun file => do
    withDataErrorDrop calls.drop file (calls.write file bytes)
    withDataErrorDrop calls.drop file (calls.flush file)
    pure file) entry = _
  cases opened : calls.acquire path entry with
  | error => simp [Bind.bind, EStateM.bind, opened]
  | ok file openedAt =>
    cases written : calls.write file bytes openedAt with
    | error => simp [Bind.bind, EStateM.bind, opened, withDataErrorDrop, written]
    | ok value writtenAt =>
      cases value
      cases flushed : calls.flush file writtenAt <;>
        simp [Bind.bind, EStateM.bind, opened, withDataErrorDrop, written, flushed, Pure.pure, EStateM.pure]

/-- Invert a returned stage into the selected fresh stream and its exact
write, flush and pending-cell store. The store is part of the action. -/
theorem returned (calls : RawWalStageCalls heap) {pending : IO.Ref (List (FilePath × IO.FS.Handle))}
    {path : FilePath} {bytes : ByteArray} {entry reached : heap}
    (staged : calls.run pending path bytes entry = .ok () reached) :
    ∃ (file : IO.FS.Handle) (opened written flushed : heap),
      calls.acquire path entry = .ok file opened ∧
      calls.write file bytes opened = .ok () written ∧ calls.flush file written = .ok () flushed ∧
      calls.remember pending (pushPending path file) flushed = .ok () reached := by
  simp only [run, Bind.bind, EStateM.bind, fresh_effect] at staged
  cases opened : calls.acquire path entry with
  | error => simp [opened] at staged
  | ok file atOpen =>
    cases wrote : calls.write file bytes atOpen with
    | error => simp [opened, wrote] at staged
    | ok value atWrite =>
      cases value
      cases flushed : calls.flush file atWrite with
      | error => simp [opened, wrote, flushed] at staged
      | ok value atFlush =>
        cases value
        exact ⟨file, atOpen, atWrite, atFlush, rfl, wrote, flushed, by simpa [opened, wrote, flushed] using staged⟩

/-- The original pending ref contains the returned marker handle. The
stage keeps any protected observation shared with the prior append, such
as the keeper binding, and the reached marker name identifies the new inode. -/
theorem retainsStaged {image footprint : Type} (calls : RawWalStageCalls heap)
    (view : OpenCloseHeapView heap image) {directory : IO.Ref (Option IO.FS.Handle)}
    {active : IO.Ref (Option (FilePath × IO.FS.Handle))}
    {pending : IO.Ref (List (FilePath × IO.FS.Handle))} {path : FilePath} {bytes : ByteArray}
    {entry reached : heap} (observeProtected : heap → footprint) (binding : heap → FilePath → Option Nat)
    (inode : IO.FS.Handle → Nat)
    (staged : calls.run pending path bytes entry = .ok () reached)
    (opened : ∀ {file opened}, calls.acquire path entry = .ok file opened →
      view.literalCacheAt opened directory active pending = view.literalCacheAt entry directory active pending ∧
      observeProtected opened = observeProtected entry ∧ binding opened path = some (inode file))
    (written : ∀ {file before after}, calls.write file bytes before = .ok () after →
      view.literalCacheAt after directory active pending = view.literalCacheAt before directory active pending ∧
      observeProtected after = observeProtected before ∧ binding after path = binding before path)
    (flushed : ∀ {file before after}, calls.flush file before = .ok () after →
      view.literalCacheAt after directory active pending = view.literalCacheAt before directory active pending ∧
      observeProtected after = observeProtected before ∧ binding after path = binding before path)
    (stored : ∀ {file before}, calls.remember pending (pushPending path file) before = .ok () reached →
      view.literalCacheAt reached directory active pending = (view.literalCacheAt before directory active pending).remember path file ∧
      observeProtected reached = observeProtected before ∧ binding reached path = binding before path) :
    ∃ file, view.literalCacheAt reached directory active pending =
      (view.literalCacheAt entry directory active pending).remember path file ∧
      observeProtected reached = observeProtected entry ∧ binding reached path = some (inode file) := by
  obtain ⟨file, _, _, _, openedAt, wrote, flushedAt, saved⟩ := calls.returned staged
  obtain ⟨openCache, openProtected, openedInode⟩ := opened openedAt
  obtain ⟨writeCache, writeProtected, writeInode⟩ := written wrote
  obtain ⟨flushCache, flushProtected, flushInode⟩ := flushed flushedAt
  obtain ⟨storeCache, storeProtected, storeInode⟩ := stored saved
  exact ⟨file, by rw [storeCache, flushCache, writeCache, openCache],
    storeProtected.trans (flushProtected.trans (writeProtected.trans openProtected)),
    storeInode.trans (flushInode.trans (writeInode.trans openedInode))⟩

/-- An error means fresh staging did not produce a handle for the
infallible pending modification. The reached heap includes any release
after a failed write or flush. No pending entry was added. -/
theorem rejected {footprint : Type} (calls : RawWalStageCalls heap)
    {pending : IO.Ref (List (FilePath × IO.FS.Handle))} {path : FilePath} {bytes : ByteArray}
    {entry reached : heap} {cause : IO.Error} (observeProtected : heap → footprint)
    (failed : calls.run pending path bytes entry = .error cause reached)
    (rememberTotal : ∀ {file before}, calls.fresh path bytes entry = .ok file before →
      ∃ after, calls.remember pending (pushPending path file) before = .ok () after)
    (opened : observeProtected (reachedState (calls.acquire path entry)) = observeProtected entry)
    (written : ∀ {file before}, calls.acquire path entry = .ok file before →
      observeProtected (reachedState (calls.write file bytes before)) = observeProtected before)
    (flushed : ∀ {file opened before}, calls.acquire path entry = .ok file opened →
      calls.write file bytes opened = .ok () before →
      observeProtected (reachedState (calls.flush file before)) = observeProtected before)
    (dropped : ∀ {file opened cause failed}, calls.acquire path entry = .ok file opened →
      (calls.write file bytes >>= fun _ => calls.flush file) opened = .error cause failed →
      observeProtected (dataErrorDropState calls.drop file failed) = observeProtected failed) :
    calls.fresh path bytes entry = .error cause reached ∧ observeProtected reached = observeProtected entry := by
  have freshFailed : calls.fresh path bytes entry = .error cause reached := by
    simp only [run, Bind.bind, EStateM.bind] at failed
    cases fresh : calls.fresh path bytes entry with
    | error => simpa [fresh] using failed
    | ok file opened =>
      obtain ⟨after, remembered⟩ := rememberTotal fresh
      simp [fresh, remembered] at failed
  refine ⟨freshFailed, ?_⟩
  rw [fresh_effect] at freshFailed
  cases openResult : calls.acquire path entry with
  | error error atOpen =>
    simp only [openResult, EStateM.Result.error.injEq] at freshFailed
    rw [← freshFailed.2]
    simpa only [openResult, reachedState] using opened
  | ok file atOpen =>
    have writeProtected := written openResult
    rw [openResult] at opened
    cases writeResult : calls.write file bytes atOpen with
    | error error atWrite =>
      simp only [openResult, writeResult, EStateM.Result.error.injEq] at freshFailed
      have released := dropped (cause := error) (failed := atWrite) openResult (by
        simp only [Bind.bind, EStateM.bind, writeResult])
      rw [← freshFailed.2]
      rw [writeResult] at writeProtected
      exact released.trans (writeProtected.trans opened)
    | ok value atWrite =>
      cases value
      have flushProtected := flushed openResult writeResult
      cases flushResult : calls.flush file atWrite with
      | error error atFlush =>
        simp only [openResult, writeResult, flushResult, EStateM.Result.error.injEq] at freshFailed
        have released := dropped (cause := error) (failed := atFlush) openResult (by
          simp only [Bind.bind, EStateM.bind, writeResult, flushResult])
        rw [← freshFailed.2]
        rw [writeResult] at writeProtected
        rw [flushResult] at flushProtected
        exact released.trans (flushProtected.trans (writeProtected.trans opened))
      | ok value atFlush =>
        cases value
        simp [openResult, writeResult, flushResult] at freshFailed

end RawWalStageCalls
end Alvoki.Storage.DiskSession
