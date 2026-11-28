import Alvoki.Experiments.L0.Native
import Alvoki.Experiments.WAL.Segmented.Proofs.StoreAcquisition

namespace ExperimentalL0.HealthyRootAcquisition
open System

private theorem ioBind {a : IO α} {f : α → IO β} (one : a w = .ok x t)
    (next : f x t = .ok y u) : (a >>= f) w = .ok y u := by
  simp only [Bind.bind, instMonadEIO._aux_13, EST.bind, one, next]

private theorem checkDirectory {n : String}
    (stat : (root / n : FilePath).symlinkMetadata w = .ok md t)
    (valid : md.type = .dir) :
    Native.checkComponentDirectory root n w = .ok () t := by
  have guard : (md.type == .dir) = true := by rw [valid]; rfl
  unfold Native.checkComponentDirectory
  apply ioBind stat
  simp only [guard, eq_self, ite_true]
  rfl

/-- An initialized L0 root includes its existing lock name. Validation
performs separate metadata calls for existence and single-link/type. -/
theorem validatedRoot (path root : FilePath)
    (resolved : IO.FS.realPath path w = .ok root t)
    (wal : (root / "wal").symlinkMetadata t = .ok wmd u) (walDir : wmd.type = .dir)
    (manifest : (root / "manifest").symlinkMetadata u = .ok mmd v) (manifestDir : mmd.type = .dir)
    (tables : (root / "tables").symlinkMetadata v = .ok tmd x) (tablesDir : tmd.type = .dir)
    (existsLock : (root / "l0.lock").symlinkMetadata x = .ok first y)
    (lock : (root / "l0.lock").symlinkMetadata y = .ok lmd z)
    (regular : (lmd.type == .file && lmd.numLinks == 1) = true) :
    Native.validatedRoot path w = .ok root z := by
  have exists_ : Native.pathExists (root / "l0.lock") x = .ok true y := by
    simp [Native.pathExists, MonadExceptOf.tryCatch, instMonadExceptOfEIO._aux_3, EST.tryCatch,
      Bind.bind, instMonadEIO._aux_13, EST.bind, existsLock, Pure.pure, instMonadEIO._aux_5, EST.pure]
  have name : Native.checkLockName (root / "l0.lock") x = .ok () z := by
    unfold Native.checkLockName
    apply ioBind exists_
    change (do
      let md ← (root / "l0.lock").symlinkMetadata
      unless md.type == .file && md.numLinks == 1 do
        throw (IO.userError "expected a singly linked regular L0 lock file") : IO Unit) y = _
    apply ioBind lock
    simp only [regular, eq_self, ite_true]
    rfl
  simp only [Native.validatedRoot, Bind.bind, instMonadEIO._aux_13, EST.bind, resolved,
    checkDirectory wal walDir, checkDirectory manifest manifestDir, checkDirectory tables tablesDir, name,
    Pure.pure, instMonadEIO._aux_5, EST.pure]

open WalRecoverySlice.Segmented.Native

private theorem walLock (root : FilePath)
    (stat : (root / "lock").symlinkMetadata w = .ok md t)
    (valid : (md.type == .file && md.numLinks == 1) = true)
    (opened : IO.FS.Handle.mk (root / "lock") .append t = .ok lock u)
    (held : lock.tryLock true u = .ok true v) :
    acquireRoot root w = .ok lock v := by
  have mdRun : metadata? (root / "lock") w = .ok (some md) t := by
    simp [metadata?, tryCatchThe, MonadExceptOf.tryCatch, instMonadExceptOfEIO._aux_3,
      EST.tryCatch, Functor.map, instMonadEIO._aux_1, EST.bind, stat, EST.pure]
  have lift {α : Type} {a : IO α} {s t} {value : α} (run : a s = .ok value t) :
      (liftM a : ExceptT String IO α).run s = .ok (.ok value) t := by
    change (do return (Except.ok (← a) : Except String α) : IO _) s = _
    simp [Bind.bind, instMonadEIO._aux_13, EST.bind, run, Pure.pure, instMonadEIO._aux_5, EST.pure]
  have statRun := lift mdRun
  have openRun := lift opened
  have tryRun := lift held
  have bind {α β : Type} {a : ExceptT String IO α} {f : α → ExceptT String IO β} {w x t u y}
      (first : a.run w = .ok (.ok x) t) (next : (f x).run t = .ok (.ok y) u) :
      (a >>= f).run w = .ok (.ok y) u := by
    rw [ExceptT.run_bind]
    simp only [Bind.bind, instMonadEIO._aux_13, EST.bind, first, next]
  have checkedRun {α : Type} {a : ExceptT String IO α} {w x t} (run : a.run w = .ok (.ok x) t) :
      checked a w = .ok x t := by
    simp only [checked, Bind.bind, instMonadEIO._aux_13, EST.bind, run, Pure.pure, instMonadEIO._aux_5, EST.pure]
  unfold acquireRoot
  apply checkedRun
  unfold acquireRootWith
  apply bind (x := some true)
  · apply bind statRun
    change EST.Out.ok (Except.ok ((some md).map (fun item => item.type == .file && item.numLinks == 1))) t =
      .ok (.ok (some true)) t
    simp only [Option.map_some, valid]
  · change ((liftM (IO.FS.Handle.mk (root / "lock") .append) : ExceptT String IO _) >>= fun h =>
      (liftM (h.tryLock true) : ExceptT String IO _) >>= fun granted =>
        if granted then pure h else throw "segmented WAL already open").run t = _
    apply bind openRun
    apply bind tryRun
    rfl

/-- Healthy initial acquisition of the real segmented store. The state
continues at allocation of the empty slot, with exactly the directory and
lock handles returned by the indicated primitive calls. -/
theorem walStore (dir canonical : FilePath)
    (resolved : IO.FS.realPath dir w = .ok canonical t)
    (openDir : IO.FS.Handle.mk canonical .read t = .ok directory u)
    (stat : (canonical / "lock").symlinkMetadata u = .ok md v)
    (valid : (md.type == .file && md.numLinks == 1) = true)
    (openLock : IO.FS.Handle.mk (canonical / "lock") .append v = .ok lock x)
    (held : lock.tryLock true x = .ok true y) :
    let fresh := (IO.mkRef (none : Option (Nat × WalRecoverySlice.SingleFile.Handle)) : BaseIO _) y
    ∃ s, acquireStore dir w = .ok s fresh.state ∧ s.root = canonical ∧
      s.directory = directory ∧ s.lock = lock ∧ s.active = fresh.val := by
  let fresh := (IO.mkRef (none : Option (Nat × WalRecoverySlice.SingleFile.Handle)) : BaseIO _) y
  have allocated : (IO.mkRef none : IO (IO.Ref (Option (Nat × WalRecoverySlice.SingleFile.Handle)))) y =
      .ok fresh.val fresh.state := by
    change BaseIO.toEIO _ y = _
    cases eq : (IO.mkRef (none : Option (Nat × WalRecoverySlice.SingleFile.Handle)) : BaseIO _) y
    simp [fresh, BaseIO.toEIO, eq]
  have got := walLock canonical stat valid openLock held
  simp only [acquireStore, acquireStoreWith, openRootDirectoryWith, Bind.bind,
    instMonadEIO._aux_13, EST.bind, resolved, openDir, got, Pure.pure, instMonadEIO._aux_5, EST.pure, allocated]
  exact ⟨_, rfl, rfl, rfl, rfl, rfl⟩

end ExperimentalL0.HealthyRootAcquisition
