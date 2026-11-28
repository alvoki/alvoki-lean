import Alvoki.Experiments.WAL.Segmented.Proofs.RuntimeChild

namespace WalRecoverySlice.Segmented.Native
open Alvoki.NativePost System
open Model (Disk)

namespace HealthyEmpty

/-- A clean run of the single-file model transfers through the actual
descriptor operations, ref allocation and mutex construction. -/
theorem childOpen {id : Nat} (a : ChildAttempt store disk Q mem id policy w)
    (healthy : a.reports = {}) (prior : Child.Recoverable policy bs none ((disk w).segment id)) :
    ∃ h t, SingleFile.openExisting (segmentPath store.root id) w = .ok h t ∧
      mem.Owns h bs t ∧ Q t := by
  let dir := segmentPath store.root id
  obtain ⟨ready, after, model⟩ := SingleFile.openExisting_healthy dir policy _ prior.dirty
  have observed := SingleFile.ConcreteRecovery.openExisting a.steps a.recovery a.runtime
    {image := (disk w).segment id} a.boundaries
  rw [← healthy] at model
  rw [model] at observed
  cases run : SingleFile.openExisting dir w with
  | error e t => rw [run] at observed; contradiction
  | ok h t =>
    have safety := a.openExisting prior
    rw [IOReturns, run] at safety
    exact ⟨h, t, rfl, safety.2.2.1, safety.1⟩

theorem childScan (io : ChildUseIO mem Q) (owned : mem.Owns h bs w) (entry : Q w) :
    ∃ t, SingleFile.scan h w = .ok bs t ∧ Q t := by
  obtain ⟨id, p, ready, a, ref, m, rfl, pair, bound, cell, mutex, issued⟩ := owned
  obtain ⟨q0, _, m0, r0⟩ := io.lock _ _ _ _ issued entry mutex cell
  obtain ⟨got, q1, _, m1, r1⟩ := io.read _ _ _ _ issued q0 m0 r0
  have run := SingleFile.scan_active_run bound w (got.trans pair.phase)
  obtain ⟨q2, _, _, _⟩ := io.unlock _ _ _ _ issued q1 m1 r1
  exact ⟨_, pair.batches ▸ run, q2⟩

def control : Control := ⟨.logOnly, 1, 0, 0⟩
def session : Session := ⟨control, 0, ⟨0, []⟩⟩

theorem lift_ok {a : IO α} (ran : a w = .ok x t) :
    (liftM a : F α).run w = .ok (.ok x) t := by
  change (do return (Except.ok (← a) : Except String α) : IO _) w = _
  simp only [Bind.bind, instMonadEIO._aux_13, EST.bind, ran, Pure.pure, instMonadEIO._aux_5, EST.pure]

theorem checked_ok {a : F α} (ran : a.run w = .ok (.ok x) t) : checked a w = .ok x t := by
  simp [checked, Bind.bind, instMonadEIO._aux_13, EST.bind, ran, Pure.pure, instMonadEIO._aux_5, EST.pure]

theorem bind_ok {a : F α} {f : α → F β} (first : a.run w = .ok (.ok x) t)
    (next : (f x).run t = .ok (.ok y) u) : (a >>= f).run w = .ok (.ok y) u := by
  rw [ExceptT.run_bind]
  simp only [Bind.bind, instMonadEIO._aux_13, EST.bind, first, next]

theorem io_bind_ok {a : IO α} {f : α → IO β} (first : a w = .ok x t)
    (next : f x t = .ok y u) : (a >>= f) w = .ok y u := by
  simp only [Bind.bind, instMonadEIO._aux_13, EST.bind, first, next]

theorem readControl (s : Store)
    (stat : (s.root / "CONTROL").symlinkMetadata w = .ok md t)
    (regular : (md.type == .file && md.numLinks == 1) = true) (size : md.byteSize.toNat ≤ 80)
    (read : IO.FS.readBinFile (s.root / "CONTROL") t = .ok (ControlCodec.encode control) u) :
    s.callbacks.readControl.run w = .ok (.ok control) u := by
  change (readControlWith controlMetadata (fun p => (liftM (IO.FS.readBinFile p) : F ByteArray)) s.root).run w = _
  unfold readControlWith controlMetadata
  apply bind_ok (bind_ok (lift_ok stat) (by rfl))
  simp only [regular, ite_true, Nat.not_lt.mpr size, ite_false]
  apply bind_ok (lift_ok read)
  have decode := ControlCodec.decode_encode control (by decide) (by decide)
  simp only [decode]
  rfl

theorem acquireChecked (s : Store)
    (inspect : inspectChild (segmentPath s.root 0) w = .ok items t)
    (includes : (requiredChildNames .logOnly).all ((items.map (·.fileName)).contains) = true)
    (stat : (segmentPath s.root 0 / "policy").metadata t = .ok md u)
    (size : md.byteSize.toNat = (policyStamp .logOnly).utf8ByteSize)
    (read : IO.FS.readFile (segmentPath s.root 0 / "policy") u = .ok (policyStamp .logOnly) v)
    (opened : SingleFile.openExisting (segmentPath s.root 0) v = .ok h end_) :
    s.acquireChild .logOnly 0 w = .ok h end_ := by
  unfold Store.acquireChild
  apply io_bind_ok (x := ()) (f := fun _ : Unit => SingleFile.openExisting (segmentPath s.root 0)) _ opened
  apply checked_ok
  unfold validateChildWith
  apply bind_ok (bind_ok (lift_ok inspect) (by rfl))
  simp only [includes, ite_true]
  apply bind_ok (bind_ok (lift_ok stat) (by rfl))
  apply bind_ok (lift_ok read)
  simp [size]
  rfl

theorem recoverChild (s : Store)
    (ctrl : s.callbacks.readControl.run w = .ok (.ok control) t)
    (sync : syncHandle s.directory t = .ok () u)
    (acquire : s.acquireChild .logOnly 0 u = .ok h v)
    (scan : SingleFile.scan h v = .ok [] x)
    (list : entries s.root x = .ok items y)
    (names : listedIds (·.fileName) items = .ok [0])
    (settle : syncHandle s.directory y = .ok () z) :
    s.recoverChild w = .ok (session, h) z := by
  have prefixRun : (reopenPrefix s.callbacks).run w = .ok (.ok (control, #[])) u := by
    unfold reopenPrefix
    apply bind_ok ctrl
    change ((do
      s.callbacks.syncRoot
      let xs ← readSealed s.callbacks .logOnly 1 0 0 #[]
      pure (control, xs)) : F _).run t = _
    apply bind_ok (lift_ok sync)
    rfl
  have collected : (collect s.callbacks control).run x = .ok (.ok ()) z := by
    unfold collect
    have listed : s.callbacks.listSegments.run x = .ok (.ok [0]) y := by
      change (s.listIds).run x = _
      unfold Store.listIds
      apply bind_ok (lift_ok list)
      rw [names]
      rfl
    apply bind_ok listed
    apply bind_ok (by rfl : (removeRetired s.callbacks control.firstNeeded [0]).run y = .ok (.ok ()) y)
    exact lift_ok settle
  have finish : (finishReopen s.callbacks control #[] []).run x = .ok (.ok session) z := by
    unfold finishReopen
    change (collect s.callbacks control >>= fun _ => pure session).run x = _
    exact bind_ok collected rfl
  unfold Store.recoverChild
  apply checked_ok
  unfold reopenWith
  apply bind_ok prefixRun
  apply lift_ok
  unfold withActiveChild
  apply io_bind_ok acquire
  have resume : (checked ((finishReopen s.callbacks control #[] [] >>= fun session =>
      pure (session, h)) : F _) x) = .ok (session, h) z := checked_ok (bind_ok finish rfl)
  have body := io_bind_ok (f := fun batches => checked ((finishReopen s.callbacks control #[] batches >>= fun sess => pure (sess, h)) : F _)) scan resume
  unfold cleanupOnError
  simp [tryCatchThe, MonadExceptOf.tryCatch, instMonadExceptOfEIO._aux_3, EST.tryCatch, body]

/-- A successful small-file read follows the stdlib preallocation and EOF
operations. The latter is opaque in Lean 4.36. -/
structure FileBytes (path : FilePath) (w : W) (bs : ByteArray) (t : W) where
  md : IO.FS.Metadata
  file : IO.FS.Handle
  statWorld : W
  opened : W
  filled : W
  acc : ByteArray
  stat : path.metadata w = .ok md statWorld
  openFile : IO.FS.Handle.mk path .read statWorld = .ok file opened
  initial : (if md.byteSize.toUSize > 0 then file.read md.byteSize.toUSize
    else pure (ByteArray.emptyWithCapacity 0) : IO ByteArray) opened = .ok acc filled
  eof : file.readBinToEndInto acc filled = .ok bs t

theorem FileBytes.run (f : FileBytes path w bytes t) : IO.FS.readBinFile path w = .ok bytes t :=
  (FileRead.readBinFile_atEOF f.stat f.openFile f.initial).trans f.eof

theorem FileBytes.string {text : String} (f : FileBytes path w text.toUTF8 t) : IO.FS.readFile path w = .ok text t := by
  unfold IO.FS.readFile
  apply io_bind_ok f.run
  simp [String.fromUTF8?, String.toUTF8, text.isValidUTF8]
  rfl

inductive Members (dir : FilePath) : List IO.FS.DirEntry → W → W → Prop where
  | nil : Members dir [] w w
  | cons {entry : IO.FS.DirEntry} (known : childName entry.fileName = true)
      (stat : (dir / entry.fileName).symlinkMetadata w = .ok md t)
      (good : (md.type == .file && md.numLinks == 1) = true)
      (rest : Members dir xs t u) : Members dir (entry :: xs) w u

theorem inspect (dir : FilePath)
    (stat : dir.symlinkMetadata w = .ok md statWorld) (directory : (md.type == .dir) = true)
    (list : entries dir statWorld = .ok items listed)
    (members : Members dir items.toList listed after) :
    inspectChild dir w = .ok items after := by
  unfold inspectChild
  apply io_bind_ok stat
  simp only [directory, ite_true]
  apply io_bind_ok list
  rw [← Array.forIn_toList]
  apply io_bind_ok (x := ()) (t := after) _ (by rfl)
  generalize hv : items.toList = xs at *
  clear list hv
  induction members with
  | nil => rfl
  | cons known ran good rest ih =>
    simp only [List.forIn_cons]
    rw [known, ite_eq_left rfl]
    apply io_bind_ok (x := ForInStep.yield ()) (t := _) _ ih
    apply io_bind_ok ran
    unfold regular
    rw [good, ite_eq_left rfl]
    rfl

structure Inspected (s : Store) (start after : W) where
  md : IO.FS.Metadata
  statWorld : W
  listed : W
  items : Array IO.FS.DirEntry
  stat : (segmentPath s.root 0).symlinkMetadata start = .ok md statWorld
  directory : (md.type == .dir) = true
  list : entries (segmentPath s.root 0) statWorld = .ok items listed
  members : Members (segmentPath s.root 0) items.toList listed after
  includes : (requiredChildNames .logOnly).all ((items.map (·.fileName)).contains) = true

/-- Primitive success reports for CONTROL and the selected, settled child.
After that child's proved read, collection consumes its actual exit world. -/
structure Worker (s : Store) (disk : W → Disk) (P : W → Prop) (mem : ChildMemory disk) (w : W) where
  md : IO.FS.Metadata
  controlStat : W
  controlRead : W
  synced : W
  inspected : W
  policyStat : W
  policyRead : W
  stat : (s.root / "CONTROL").symlinkMetadata w = .ok md controlStat
  regular : (md.type == .file && md.numLinks == 1) = true
  bounded : md.byteSize.toNat ≤ 80
  bytes : FileBytes (s.root / "CONTROL") controlStat (ControlCodec.encode control) controlRead
  sync : syncHandle s.directory controlRead = .ok () synced
  names : Inspected s synced inspected
  policyMd : IO.FS.Metadata
  sizeStat : (segmentPath s.root 0 / "policy").metadata inspected = .ok policyMd policyStat
  size : policyMd.byteSize.toNat = (policyStamp .logOnly).utf8ByteSize
  stamp : FileBytes (segmentPath s.root 0 / "policy") policyStat (policyStamp .logOnly).toUTF8 policyRead
  child : ChildAttempt s disk P mem 0 .logOnly policyRead
  healthy : child.reports = {}
  prior : Child.Recoverable .logOnly [] none ((disk policyRead).segment 0)
  useChild : ChildUseIO mem P
  collect : ∀ h t u, SingleFile.openExisting (segmentPath s.root 0) policyRead = .ok h t →
    SingleFile.scan h t = .ok [] u →
    ∃ items v z, entries s.root u = .ok items v ∧ listedIds (·.fileName) items = .ok [0] ∧
      syncHandle s.directory v = .ok () z

theorem Worker.run (p : Worker s disk P mem w) : ∃ h u, s.recoverChild w = .ok (session, h) u := by
  have controlRun := readControl s p.stat p.regular p.bounded p.bytes.run
  have names := inspect _ p.names.stat p.names.directory p.names.list p.names.members
  obtain ⟨h, t, openChild, owned, frame⟩ := childOpen p.child p.healthy p.prior
  have acquired := acquireChecked s names p.names.includes p.sizeStat p.size p.stamp.string openChild
  obtain ⟨u, scanned, _⟩ := childScan p.useChild owned frame
  obtain ⟨_, _, z, list, ids, sync⟩ := p.collect h t u openChild scanned
  exact ⟨h, z, recoverChild s controlRun p.sync acquired scanned list ids sync⟩

/-- Install the actual recovered child and allocate the phase reference and
mutex. The resulting public handle is ready for its very first operation. -/
theorem Worker.openExisting (p : Worker s disk P mem w) (heap : PhaseMemory)
    (grant : acquireStore dir start = .ok s w) :
    ∃ h t, Native.openExisting dir start = .ok h t ∧ heap.Ready h session t := by
  obtain ⟨child, recovered, ran⟩ := p.run
  simp only [Native.openExisting_run, grant, ran]
  exact ⟨_, _, rfl, s, child, heap.fresh _ (heap.set _ _ _), heap.newMutex (heap.allocate _ _),
    heap.newMutex (heap.allocateFrame _ (heap.set _ _ _))⟩

end HealthyEmpty
end WalRecoverySlice.Segmented.Native
