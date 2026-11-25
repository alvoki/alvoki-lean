import Alvoki.Storage.Disk.AppendHandleCustody
import Alvoki.Storage.Disk.NativeOpenClose

namespace Alvoki.Storage.DiskSession

open System SyncHandleRouting

/-- Interpret the callbacks of `OpenSyncFiles.appendCacheSchedule` on
one heap. File effects include the reaches of observed stream releases. -/
structure RawWalAppendCalls (heap : Type) where
  getActive : IO.Ref (Option (FilePath × IO.FS.Handle)) →
    EStateM IO.Error heap (Option (FilePath × IO.FS.Handle))
  setActive : IO.Ref (Option (FilePath × IO.FS.Handle)) →
    Option (FilePath × IO.FS.Handle) → EStateM IO.Error heap Unit
  openAppend : FilePath → EStateM IO.Error heap IO.FS.Handle
  write : IO.FS.Handle → ByteArray → EStateM IO.Error heap Unit
  flush : IO.FS.Handle → EStateM IO.Error heap Unit

/-- The literal cache keeps the OS handle objects from the observed
references. Descriptor and inode projections are separate observations. -/
def OpenCloseHeapView.literalCacheAt (view : OpenCloseHeapView heap image) (reached : heap)
    (directory : IO.Ref (Option IO.FS.Handle)) (active : IO.Ref (Option (FilePath × IO.FS.Handle)))
    (pending : IO.Ref (List (FilePath × IO.FS.Handle))) : Cache IO.FS.Handle :=
  ⟨view.directory reached directory, view.active reached active, view.pending reached pending⟩

namespace RawWalAppendCalls

variable {heap : Type}

abbrev run (calls : RawWalAppendCalls heap) (active : IO.Ref (Option (FilePath × IO.FS.Handle)))
    (path : FilePath) (bytes : ByteArray) : EStateM IO.Error heap Unit :=
  appendWithActive (calls.getActive active) (calls.setActive active) calls.openAppend calls.write calls.flush path bytes

/-- Invert the actual successful append. The same selected handle goes
through the reached write, flush and update of the original active cell. -/
theorem returned (calls : RawWalAppendCalls heap) {active : IO.Ref (Option (FilePath × IO.FS.Handle))}
    {path : FilePath} {bytes : ByteArray} {entry reached : heap} {cached : Option (FilePath × IO.FS.Handle)}
    (loaded : calls.getActive active entry = .ok cached entry)
    (appended : calls.run active path bytes entry = .ok () reached) :
    ∃ (handle : IO.FS.Handle) (opened written flushed : heap),
      selectAppendHandle cached calls.openAppend path entry = .ok handle opened ∧
      calls.write handle bytes opened = .ok () written ∧
      calls.flush handle written = .ok () flushed ∧
      calls.setActive active (some (path, handle)) flushed = .ok () reached := by
  rw [run, appendWithActive_effect, loaded] at appended
  cases selected : selectAppendHandle cached calls.openAppend path entry with
  | error cause atError => simp [selected] at appended
  | ok handle opened =>
    cases wrote : calls.write handle bytes opened with
    | error cause failed =>
      simp only [selected, Bind.bind, EStateM.bind, wrote] at appended
      cases cleared : calls.setActive active none failed <;> simp [cleared, EStateM.throw] at appended
    | ok value written =>
      cases value
      cases flushed : calls.flush handle written with
      | error cause failed =>
        simp only [selected, Bind.bind, EStateM.bind, wrote, flushed] at appended
        cases cleared : calls.setActive active none failed <;> simp [cleared, EStateM.throw] at appended
      | ok value atFlush =>
        cases value
        exact ⟨handle, opened, written, atFlush, rfl, wrote, flushed, by simpa [selected, Bind.bind,
          EStateM.bind, wrote, flushed] using appended⟩

/-- The successful store leaves the literal append handle under the
keeper name. A cache hit uses the existing name binding. A fallback
uses the binding observed by the actual open. Each reached callback
supplies its local binding law. -/
theorem retainsKeeper {image : Type} (calls : RawWalAppendCalls heap) (view : OpenCloseHeapView heap image)
    {directory : IO.Ref (Option IO.FS.Handle)} {active : IO.Ref (Option (FilePath × IO.FS.Handle))}
    {pending : IO.Ref (List (FilePath × IO.FS.Handle))} {dir path : FilePath} {bytes : ByteArray}
    {entry reached : heap} (bindings : heap → FilePath → Option Nat) (inode : IO.FS.Handle → Nat)
    (owned : (view.literalCacheAt entry directory active pending).Agrees dir inode (bindings entry))
    (fresh : ∀ {handle opened}, calls.openAppend path entry = .ok handle opened →
      bindings opened path = some (inode handle))
    (loaded : calls.getActive active entry = .ok (view.active entry active) entry)
    (appended : calls.run active path bytes entry = .ok () reached)
    (keepsWrite : ∀ {handle before after}, calls.write handle bytes before = .ok () after →
      bindings after path = bindings before path)
    (keepsFlush : ∀ {handle before after}, calls.flush handle before = .ok () after →
      bindings after path = bindings before path)
    (stored : ∀ {handle before}, calls.setActive active (some (path, handle)) before = .ok () reached →
      view.active reached active = some (path, handle) ∧ bindings reached path = bindings before path) :
    ∃ handle, view.active reached active = some (path, handle) ∧ bindings reached path = some (inode handle) := by
  obtain ⟨handle, _, _, _, selected, wrote, flushed, saved⟩ := calls.returned loaded appended
  have keeper := (view.literalCacheAt entry directory active pending).selectAppend_owned
    calls.openAppend bindings inode owned fresh selected
  obtain ⟨activeHandle, stillNamed⟩ := stored saved
  exact ⟨handle, activeHandle, stillNamed.trans ((keepsFlush flushed).trans ((keepsWrite wrote).trans keeper))⟩

/-- Follow the selected stream's bytes through the actual write, flush,
and active-cell store. A successful write can leave a suffix buffered.
The flush publishes that suffix before the selected stream is retained. -/
theorem appendsVisible {image : Type} (calls : RawWalAppendCalls heap) (view : OpenCloseHeapView heap image)
    {active : IO.Ref (Option (FilePath × IO.FS.Handle))} {path : FilePath} {bytes : ByteArray}
    {entry reached : heap} (bindings : heap → FilePath → Option Nat) (inode : IO.FS.Handle → Nat)
    (visible : heap → Nat → ByteArray) (buffered : heap → IO.FS.Handle → ByteArray) {keeper : Nat}
    (named : bindings entry path = some keeper)
    (loaded : calls.getActive active entry = .ok (view.active entry active) entry)
    (appended : calls.run active path bytes entry = .ok () reached)
    (cleanCached : ∀ handle, view.active entry active = some (path, handle) →
      inode handle = keeper ∧ buffered entry handle = ByteArray.empty)
    (openedExisting : ∀ {handle opened}, calls.openAppend path entry = .ok handle opened →
      inode handle = keeper ∧ bindings opened path = some keeper ∧
      visible opened keeper = visible entry keeper ∧ buffered opened handle = ByteArray.empty)
    (writeEffect : ∀ {handle before after}, calls.write handle bytes before = .ok () after →
      bindings after path = bindings before path ∧
      visible after (inode handle) ++ buffered after handle =
        (visible before (inode handle) ++ buffered before handle) ++ bytes)
    (flushEffect : ∀ {handle before after}, calls.flush handle before = .ok () after →
      bindings after path = bindings before path ∧
      visible after (inode handle) = visible before (inode handle) ++ buffered before handle ∧
      buffered after handle = ByteArray.empty)
    (storeEffect : ∀ {handle before}, calls.setActive active (some (path, handle)) before = .ok () reached →
      view.active reached active = some (path, handle) ∧ bindings reached path = bindings before path ∧
      visible reached (inode handle) = visible before (inode handle) ∧
      buffered reached handle = buffered before handle) :
    ∃ handle, view.active reached active = some (path, handle) ∧ inode handle = keeper ∧
      bindings reached path = some keeper ∧ visible reached keeper = visible entry keeper ++ bytes ∧
      buffered reached handle = ByteArray.empty := by
  obtain ⟨handle, opened, _, _, selected, wrote, flushed, saved⟩ := calls.returned loaded appended
  have initial : inode handle = keeper ∧ bindings opened path = some keeper ∧
      visible opened keeper = visible entry keeper ∧ buffered opened handle = ByteArray.empty := by
    cases cached : view.active entry active with
    | none => exact openedExisting (by simpa [selectAppendHandle, cached] using selected)
    | some value =>
      obtain ⟨name, file⟩ := value
      by_cases hit : path = name
      · simp [selectAppendHandle, cached, hit, Pure.pure, EStateM.pure] at selected
        obtain ⟨rfl, rfl⟩ := selected
        obtain ⟨same, clean⟩ := cleanCached file (by simpa [hit] using cached)
        exact ⟨same, named, rfl, clean⟩
      · exact openedExisting (by simpa [selectAppendHandle, cached, hit] using selected)
  obtain ⟨same, openName, openBytes, clean⟩ := initial
  obtain ⟨writeName, written⟩ := writeEffect wrote
  obtain ⟨flushName, flushedBytes, flushedBuffer⟩ := flushEffect flushed
  obtain ⟨activeHandle, storeName, storedBytes, storedBuffer⟩ := storeEffect saved
  have payload := storedBytes.trans (flushedBytes.trans written)
  rw [same, openBytes, clean, ByteArray.append_empty] at payload
  exact ⟨handle, activeHandle, same, storeName.trans (flushName.trans (writeName.trans openName)),
    payload, storedBuffer.trans flushedBuffer⟩

/-- Project the effect of the selected open or the hit on the original
active reference. A hit does not consult the append opener. -/
private theorem projectedSelect {heap files : Type}
    (calls : RawWalAppendCalls heap) (cache : heap → Cache IO.FS.Handle) (image : heap → files)
    (openAppend : FilePath → EStateM IO.Error files IO.FS.Handle) (path : FilePath) (entry : heap)
    (openLaw : (cache entry).active.map Prod.fst ≠ some path →
      projectResult image (calls.openAppend path entry) = openAppend path (image entry) ∧
        cache (reachedState (calls.openAppend path entry)) = cache entry) :
    projectResult image (selectAppendHandle (cache entry).active calls.openAppend path entry) =
      selectAppendHandle (cache entry).active openAppend path (image entry) ∧
    cache (reachedState (selectAppendHandle (cache entry).active calls.openAppend path entry)) = cache entry := by
  cases active : (cache entry).active with
  | none => exact openLaw (by simp [active])
  | some entry =>
    obtain ⟨name, handle⟩ := entry
    by_cases hit : path = name
    · simp [selectAppendHandle, hit, Pure.pure, EStateM.pure, projectResult, reachedState]
    · have misses : (cache entry).active.map Prod.fst ≠ some path := by
        simpa [active] using Ne.symm hit
      simpa [selectAppendHandle, hit] using openLaw misses

/-- Use one physical append interpreter with literal handles. Ref
operations are the reached read and store of the active cell. The file
callbacks supply the same result and file projection. On either data
error the actual clear happens before the original diagnostic returns.
The store law accounts for observed releases at that exact outcome. -/
theorem projects
    {heap files : Type} (calls : RawWalAppendCalls heap) (fileView : OpenCloseHeapView heap files)
    {directory : IO.Ref (Option IO.FS.Handle)} {active : IO.Ref (Option (FilePath × IO.FS.Handle))}
    {pending : IO.Ref (List (FilePath × IO.FS.Handle))}
    (image : heap → files) (path : FilePath) (bytes : ByteArray) (entry : heap)
    (openAppend : FilePath → EStateM IO.Error files IO.FS.Handle)
    (write : IO.FS.Handle → ByteArray → EStateM IO.Error files Unit)
    (flush : IO.FS.Handle → EStateM IO.Error files Unit)
    (loaded : calls.getActive active entry = .ok (fileView.active entry active) entry)
    (afterStore : Cache IO.FS.Handle → Option (FilePath × IO.FS.Handle) → files → files)
    (stored : ∀ {file opened outcome},
      selectAppendHandle (fileView.active entry active) calls.openAppend path entry = .ok file opened →
      (calls.write file bytes >>= fun _ => calls.flush file) opened = outcome →
      let (value, atStore) := match outcome with
        | .ok () reached => (some (path, file), reached)
        | .error _ reached => (none, reached)
      ∃ reached, calls.setActive active value atStore = .ok () reached ∧
        fileView.literalCacheAt reached directory active pending =
          { fileView.literalCacheAt atStore directory active pending with active := value } ∧
        image reached = afterStore (fileView.literalCacheAt atStore directory active pending) value (image atStore))
    (openLaw : (fileView.active entry active).map Prod.fst ≠ some path →
      projectResult image (calls.openAppend path entry) = openAppend path (image entry) ∧
      fileView.literalCacheAt (reachedState (calls.openAppend path entry)) directory active pending =
        fileView.literalCacheAt entry directory active pending)
    (writeLaw : ∀ {handle atWrite},
      selectAppendHandle (fileView.active entry active) calls.openAppend path entry = .ok handle atWrite →
      projectResult image (calls.write handle bytes atWrite) =
        write handle bytes (image atWrite) ∧
      fileView.literalCacheAt (reachedState (calls.write handle bytes atWrite)) directory active pending =
        fileView.literalCacheAt atWrite directory active pending)
    (flushLaw : ∀ {handle atWrite atFlush},
      selectAppendHandle (fileView.active entry active) calls.openAppend path entry = .ok handle atWrite →
      calls.write handle bytes atWrite = .ok () atFlush →
      projectResult image (calls.flush handle atFlush) = flush handle (image atFlush) ∧
      fileView.literalCacheAt (reachedState (calls.flush handle atFlush)) directory active pending =
        fileView.literalCacheAt atFlush directory active pending) :
    let cache := fun state => fileView.literalCacheAt state directory active pending
    projectResult (fun heap => (cache heap, image heap)) (calls.run active path bytes entry) =
      runAppendWithCacheEffects path bytes openAppend write flush afterStore (cache entry, image entry) := by
  intro cache
  have select := projectedSelect calls cache image openAppend path entry openLaw
  change calls.getActive active entry = .ok (cache entry).active entry at loaded
  change projectResult (fun heap => (cache heap, image heap)) (calls.run active path bytes entry) = _
  rw [runAppendWithCacheEffects_effect]
  simp only [RawWalAppendCalls.run, appendWithActive_effect, loaded]
  cases selected : selectAppendHandle (cache entry).active calls.openAppend path entry with
  | error cause reached =>
    have returned := select.1
    have kept := select.2
    rw [selected] at returned kept
    rw [← returned]
    simp [projectResult, reachedState] at kept ⊢
    exact kept
  | ok handle opened =>
    have returned := select.1
    have kept := select.2
    rw [selected] at returned kept
    rw [← returned]
    dsimp only [projectResult]
    change cache opened = cache entry at kept
    have actual : selectAppendHandle (fileView.active entry active) calls.openAppend path entry = .ok handle opened :=
      selected
    have wrote := writeLaw actual
    cases written : calls.write handle bytes opened with
    | error cause atError =>
      obtain ⟨after, cleared, frames, effects⟩ := stored (outcome := .error cause atError) actual (by
        simp only [Bind.bind, EStateM.bind, written])
      rw [written] at wrote
      rw [← wrote.1]
      have failedCache : cache atError = cache entry := wrote.2.trans kept
      change cache after = { cache atError with active := none } at frames
      change image after = afterStore (cache atError) none (image atError) at effects
      simp [projectResult, written, Bind.bind, EStateM.bind, EStateM.throw, cleared, frames, effects, failedCache]
    | ok value buffered =>
      cases value
      rw [written] at wrote
      rw [← wrote.1]
      dsimp only [projectResult]
      have bufferedCache : cache buffered = cache entry := wrote.2.trans kept
      have flushed := flushLaw actual written
      cases synced : calls.flush handle buffered with
      | error cause atError =>
        obtain ⟨after, cleared, frames, effects⟩ := stored (outcome := .error cause atError) actual (by
          simp only [Bind.bind, EStateM.bind, written, synced])
        rw [synced] at flushed
        rw [← flushed.1]
        have failedCache : cache atError = cache entry := flushed.2.trans bufferedCache
        change cache after = { cache atError with active := none } at frames
        change image after = afterStore (cache atError) none (image atError) at effects
        simp [projectResult, written, synced, Bind.bind, EStateM.bind, EStateM.throw, cleared, frames, effects, failedCache]
      | ok value flushedAt =>
        cases value
        obtain ⟨after, saved, frames, effects⟩ := stored (outcome := .ok () flushedAt) actual (by
          simp only [Bind.bind, EStateM.bind, written, synced])
        rw [synced] at flushed
        rw [← flushed.1]
        have flushedCache : cache flushedAt = cache entry := flushed.2.trans bufferedCache
        change cache after = { cache flushedAt with active := some (path, handle) } at frames
        change image after = afterStore (cache flushedAt) (some (path, handle)) (image flushedAt) at effects
        simp [projectResult, written, synced, Bind.bind, EStateM.bind, saved, frames, effects, flushedCache]


end RawWalAppendCalls
end Alvoki.Storage.DiskSession
