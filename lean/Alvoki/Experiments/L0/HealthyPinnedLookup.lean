import Alvoki.Experiments.L0.HealthyPublishedRecovery
import Alvoki.Experiments.L0.NativeFlushRestart

namespace ExperimentalL0.HealthyPublishedRecovery
open System Lifecycle NativeFlushRestart
open NativeRead (Footprint tableNamespace Online HealthyChecks Frame Call publicCalls)
open NativeScope (W Ref Wal)

noncomputable def pin (physical : W → Footprint inode) (path : FilePath) (ident : inode)
    (bytes : ByteArray) (w : W) : Footprint inode := by
  classical
  exact {physical w with
    names := fun p => if p = path ∧ (physical w).names p ≠ some ident then none else (physical w).names p
    contents := fun i => if i = ident ∧ (physical w).contents i ≠ some bytes then none else (physical w).contents i}

private theorem pinNames {physical : W → Footprint inode}
    (existsName : (physical w).names path = some ident) (query : FilePath) (bytes : ByteArray) :
    (pin physical path ident bytes w).names query = (physical w).names query := by
  classical
  have good : ¬ (query = path ∧ (physical w).names query ≠ some ident) :=
    fun h => h.2 (h.1.symm ▸ existsName)
  simp only [pin,good,ite_false]

private theorem pinContents {physical : W → Footprint inode}
    (present : (physical w).contents ident = some bytes) (query : inode) (path : FilePath) :
    (pin physical path ident bytes w).contents query = (physical w).contents query := by
  classical
  have good : ¬ (query = ident ∧ (physical w).contents query ≠ some bytes) := fun h => h.2 (h.1.symm ▸ present)
  simp only [pin,good,ite_false]

theorem pinFiles (files : NativeReadScope.Files physical root img start)
    (named : (physical start).names path = some ident) (contents : (physical start).contents ident = some bytes) :
    NativeReadScope.Files (pin physical path ident bytes) root img start := by
  classical
  refine ⟨?_,files.manifest,files.disk⟩
  intro id rows found
  obtain ⟨i,b,n,c,format⟩ := files.catalog id rows found
  refine ⟨i,b,?_,?_,format⟩
  · exact (pinNames named _ bytes).trans n
  · exact (pinContents contents i path).trans c

theorem pinBinding (named : (pin physical path ident bytes w).names path = some i)
    (stored : (pin physical path ident bytes w).contents i = some b) :
    i = ident ∧ b = bytes ∧ (physical w).names path = some i ∧ (physical w).contents i = some b := by
  classical
  simp only [pin, true_and] at named
  split at named <;> try contradiction
  rename_i bound
  have eq := Classical.not_not.mp bound
  have same : i = ident := Option.some.inj (named.symm.trans eq)
  subst i
  simp only [pin,true_and] at stored
  split at stored <;> try contradiction
  rename_i live
  exact ⟨rfl,Option.some.inj (stored.symm.trans (Classical.not_not.mp live)),named,stored⟩

/-- The actual checked lookup borrows a descriptor on the inode retained by
the writer; both the raw bytes and the public return belong to that call. -/
theorem lookupPinned {physical : W → Footprint inode} {id : UInt64}
    (img : Selected) (s : Session) (key : UInt64) (value : Mutation)
    (fits : img.view.tail < UInt64.size) (hit : lookupRows s.mem.toList key = some value)
    (life : NativeRead.Lifetime) (ident : inode) (bytes : ByteArray)
    (ready : Online (pin physical (tablePath (root / "tables") id) ident bytes) root lock ref wal session (published img s id) history start)
    (binding : Native.Handle.AtRoot h root ref)
    (ops : WithOpenReads.Runtime (pin physical (tablePath (root / "tables") id) ident bytes) root lock ref (published img s id) life heap)
    (ok : HealthyChecks (ops.tables wal start ready.owned) (published img s id).version.tables) :
    ∃ w t, Native.get h key start = .ok value.value t ∧
      ∃ e : NativeRead.Exit ⟨root / "tables", id, .lookup key, w⟩,
        e.reached = t ∧ e.reply = .ok (some value) ∧
        (ops.tables wal start ready.owned).inodeOf e.handle e.entered = some ident ∧
        (physical e.checked).names (tablePath (root / "tables") id) = some ident ∧
        (physical e.checked).contents ident = some bytes ∧
        ¬ life.liveAtReturn e e.handle ∧ Online (pin physical (tablePath (root / "tables") id) ident bytes) root lock ref wal session (published img s id) history t := by
  let ph := pin physical (tablePath (root / "tables") id) ident bytes
  let image := published img s id
  let prim := ops.tables wal start ready.owned
  obtain ⟨w,phase,step⟩ := ops.phase.refRead wal start ready.owned (by rw [ready.phase]; rfl)
  rw [ready.phase] at phase
  obtain ⟨d,version,mem⟩ := ready.installed
  have replayed := d.replay_pending
  change (img.view.batches.drop (img.view.tail.toUInt64.toNat - img.view.base)).mapM decode = some d.pending at replayed
  rw [UInt64.toNat_ofNat_of_lt' fits] at replayed
  simp [WalRecoverySlice.Segmented.Contract.View.tail] at replayed
  have miss : session.mem[key]? = none := by rw [mem,replayed]; rfl
  have order : session.version.tables = id :: s.version.tables := by rw [version]; rfl
  have listed : id ∈ image.version.tables := .head _
  have rows : image.tables id = some s.mem.toList := by simp [image, published, stored, Selected.publish]
  have bound t (frame : Frame ph root wal image.tables start t) :=
    (ready.catalog.frame frame.tablesKept) id s.mem.toList rows
  obtain ⟨t,looked,frame⟩ := ok.lookup id listed bound key w step
  rw [hit] at looked
  have get : Native.get h key start = .ok value.value t := by
    rw [Native.get_atRoot binding phase (Native.callbackComponents root ref) rfl]
    have found : (ExperimentalL0.get (Native.callbackComponents root ref) session key).run w = .ok (.ok value.value) t := by
      unfold ExperimentalL0.get
      rw [miss,order]
      apply WalRecoverySlice.Segmented.Native.HealthyEmpty.bind_ok
      · unfold lookupTables
        exact WalRecoverySlice.Segmented.Native.HealthyEmpty.bind_ok looked rfl
      · rfl
    simp [Bind.bind, instMonadEIO._aux_13, EST.bind, found, Pure.pure, instMonadEIO._aux_5, EST.pure]
  obtain ⟨md,c,stat,regular⟩ := ok.stat id listed w step
  change (nativeTableStat (tablePath (root / "tables") id)).run w = _ at stat
  have cf := prim.stat (tablePath (root / "tables") id) w step
  rw [stat] at cf
  obtain ⟨i,b,n,contents,built⟩ := bound c cf.1
  obtain ⟨iEq,bEq,rawName,rawBytes⟩ := pinBinding (physical := physical) (ident := ident) (bytes := bytes) (path := tablePath (root / "tables") id) n contents
  obtain ⟨fd,u,opened⟩ := ok.acquire id listed c cf.1
  change IO.FS.Handle.mk (tablePath (root / "tables") id) .read c = _ at opened
  have borrowed := prim.openRead (tablePath (root / "tables") id) _ _ _ cf.1 n contents
  rw [opened] at borrowed
  let call : Call := ⟨root / "tables",id,.lookup key,w⟩
  let e := call.exitOfAcquire stat regular opened
  have consumed := EST.Out.ok.inj (e.returned.symm.trans looked)
  have free := (NativeRead.onlineGet ready binding (ops.phase.refRead wal) prim .refl key).1 _ (NativeRead.callsFirst phase miss order)
  exact ⟨w,t,get,e,consumed.2,consumed.1,borrowed.2.2.1.trans (congrArg some iEq),rawName.trans (congrArg some iEq),iEq ▸ rawBytes.trans (congrArg some bEq),free e,ready.frame frame⟩

end ExperimentalL0.HealthyPublishedRecovery
