import Alvoki.Experiments.WAL.Segmented.Proofs.NativeRootIO

namespace WalRecoverySlice.Segmented.Native
open System Alvoki.NativePost

private theorem checkIO {op : F α} (h : Returns op w ok failed) :
    IOReturns (checked op) w ok failed := by
  unfold checked Returns IOReturns at *
  cases run : op.run w with
  | error => simpa [Bind.bind, instMonadEIO._aux_13, EST.bind, run, Pure.pure, instMonadEIO._aux_5, EST.pure, throw, throwThe, MonadExceptOf.throw, instMonadExceptOfEIO._aux_1, EST.throw] using h
  | ok r t =>
    cases r <;> rw [run] at h <;>
      simpa [Bind.bind, instMonadEIO._aux_13, EST.bind, run, Pure.pure, instMonadEIO._aux_5, EST.pure, throw, throwThe, MonadExceptOf.throw, instMonadExceptOfEIO._aux_1, EST.throw] using h

/-- Acquiring the exclusive WAL lock validates the name without following
symlinks. Its primitive postconditions refer to the descriptor returned by
the reached open; they may track the already opened directory. -/
theorem acquireRoot_io (root : FilePath) {P failed : W → Prop}
    {opened locked : IO.FS.Handle → W → Prop}
    (stat : IOReturns (root / "lock").symlinkMetadata w (fun _ t => P t) P)
    (bad : ∀ t, P t → failed t)
    (openLock : ∀ t, P t → IOReturns (IO.FS.Handle.mk (root / "lock") .append) t opened failed)
    (tryLock : ∀ h t, opened h t → IOReturns (h.tryLock true) t
      (fun yes u => if yes then locked h u else failed u) failed) :
    IOReturns (acquireRoot root) w locked failed := by
  apply checkIO
  unfold acquireRootWith
  let path := root / "lock"
  have md : IOReturns (metadata? path) w (fun _ t => P t) failed := by
    unfold IOReturns metadata? at *
    cases run : path.symlinkMetadata w with
    | ok m t =>
      simp only [path] at run
      rw [run] at stat
      simpa [tryCatchThe, MonadExceptOf.tryCatch, instMonadExceptOfEIO._aux_3, EST.tryCatch, path,
        Functor.map, instMonadEIO._aux_1, EST.bind, EST.pure, run] using stat
    | error e t =>
      simp only [path] at run
      rw [run] at stat
      cases e <;> simp [tryCatchThe, MonadExceptOf.tryCatch, instMonadExceptOfEIO._aux_3, EST.tryCatch, path,
        Functor.map, instMonadEIO._aux_1, EST.bind, run, throw, throwThe, MonadExceptOf.throw,
        instMonadExceptOfEIO._aux_1, EST.throw] <;> first | exact stat | exact bad _ stat
  apply Returns.bind (middle := fun _ t => P t)
  · apply Returns.bind (Returns.liftIO md)
    exact fun _ _ h => h
  intro valid t keep
  split
  · exact bad _ keep
  · apply Returns.bind (Returns.liftIO (openLock t keep))
    intro h u held
    apply Returns.bind (Returns.liftIO (tryLock h u held))
    intro yes v got
    cases yes <;> exact got

structure StoreAt (heap : PhaseMemory) (root : FilePath)
    (directory lock : IO.FS.Handle → W → Prop) (P : W → Prop) (s : Store) (w : W) : Prop where
  path : s.root = root
  directoryBound : directory s.directory w
  owns : lock s.lock w
  empty : heap.holds s.active none w
  frame : P w

/-- The empty slot, WAL lock and directory description in the returned
store are the ones allocated by the actual acquisition sequence. -/
theorem acquireStore_io (heap : PhaseMemory) (dir canonical : FilePath)
    {directory lock : IO.FS.Handle → W → Prop} {P : W → Prop}
    (resolve : IOReturns (IO.FS.realPath dir) w (fun r t => r = canonical ∧ P t) P)
    (openDir : ∀ t, P t → IOReturns (IO.FS.Handle.mk canonical .read) t
      (fun d u => directory d u ∧ P u) P)
    (stat : ∀ d t, directory d t → P t → IOReturns (canonical / "lock").symlinkMetadata t
      (fun _ u => directory d u ∧ P u) (fun u => directory d u ∧ P u))
    (opened : IO.FS.Handle → IO.FS.Handle → W → Prop)
    (openLock : ∀ d t, directory d t → P t → IOReturns (IO.FS.Handle.mk (canonical / "lock") .append) t
      (opened d) P)
    (acquire : ∀ d h t, opened d h t → IOReturns (h.tryLock true) t
      (fun yes u => if yes then directory d u ∧ lock h u ∧ P u else P u) P)
    (fresh : ∀ d h t, directory d t → lock h t → P t →
      let r := (IO.mkRef (none : Option (Nat × SingleFile.Handle)) : BaseIO _) t
      directory d r.state ∧ lock h r.state ∧ P r.state) :
    IOReturns (acquireStore dir) w (StoreAt heap canonical directory lock P) P := by
  unfold acquireStore acquireStoreWith
  apply IOReturns.bind (middle := fun pair t => pair.1 = canonical ∧ directory pair.2 t ∧ P t)
  · unfold openRootDirectoryWith
    apply IOReturns.bind resolve
    rintro _ t ⟨rfl, frame⟩
    apply IOReturns.bind (openDir t frame)
    exact fun d u post => ⟨rfl, post⟩
  rintro ⟨r, d⟩ t ⟨eq, bound, frame⟩
  change r = canonical at eq
  subst r
  apply IOReturns.bind (acquireRoot_io canonical (stat d t bound frame)
    (fun _ h => h.2) (fun u h => openLock d u h.1 h.2) (acquire d))
  rintro h u ⟨dirHeld, lockHeld, kept⟩
  let cell := (IO.mkRef (none : Option (Nat × SingleFile.Handle)) : BaseIO _) u
  obtain ⟨dirAfter, lockAfter, after⟩ := fresh d h u dirHeld lockHeld kept
  have allocated := heap.allocate (none : Option (Nat × SingleFile.Handle)) u
  have run : (IO.mkRef none : IO (IO.Ref (Option (Nat × SingleFile.Handle)))) u = .ok cell.val cell.state := by
    change BaseIO.toEIO _ u = _
    cases eq : (IO.mkRef (none : Option (Nat × SingleFile.Handle)) : BaseIO _) u
    simp [BaseIO.toEIO, cell, eq]
  simp only [IOReturns, Bind.bind, instMonadEIO._aux_13, EST.bind, run, Pure.pure, instMonadEIO._aux_5, EST.pure]
  exact ⟨rfl, dirAfter, lockAfter, allocated, after⟩

/-- The runtime lock stored in any successful acquisition is the description
returned by the canonical WAL lock pathname, and that same description
granted the lock on the immediately following world. -/
theorem acquireStore_rootLockAt (heap : PhaseMemory) (dir : FilePath)
    (returned : acquireStore dir w = .ok s finish) : RootLockAt s.root s.lock := by
  cases resolved : IO.FS.realPath dir w with
  | error e atPath =>
    simp [acquireStore, acquireStoreWith, openRootDirectoryWith, Bind.bind, instMonadEIO._aux_13,
      EST.bind, resolved] at returned
  | ok root t =>
    let opened := fun (_ : IO.FS.Handle) fd u =>
      ∃ begin, IO.FS.Handle.mk (root / "lock") .append begin = .ok fd u
    have result := acquireStore_io heap dir root
      (directory := fun _ _ => True) (lock := fun fd _ => RootLockAt root fd) (P := fun _ => True)
      (w := w) (by simp [IOReturns, resolved]) (by
        intro u _
        unfold IOReturns
        cases IO.FS.Handle.mk root .read u <;> simp)
      (by
        intro d u _ _
        unfold IOReturns
        cases (root / "lock").symlinkMetadata u <;> simp)
      opened (by
        intro d u _ _
        unfold IOReturns
        cases run : IO.FS.Handle.mk (root / "lock") .append u with
        | ok fd t => exact ⟨u, run⟩
        | error => trivial)
      (by
        rintro d fd u ⟨begin, file⟩
        unfold IOReturns
        cases granted : fd.tryLock true u with
        | error => trivial
        | ok yes v =>
          cases yes with
          | false => trivial
          | true => exact ⟨trivial, ⟨begin, u, v, file, granted⟩, trivial⟩)
      (fun d fd u _ held _ => ⟨trivial, held, trivial⟩)
    rw [IOReturns, returned] at result
    rw [result.path]
    exact result.owns

end WalRecoverySlice.Segmented.Native
