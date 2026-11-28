import Alvoki.Experiments.L0.HealthyPinnedLookup
import Alvoki.Experiments.L0.HealthyMutation

namespace ExperimentalL0.HealthyPublishedRecovery
open System Lifecycle
open NativeScope (W Ref Wal Post)
open NativeRead (Footprint Online)
open NativeFlushRestart (published)
open WalRecoverySlice.Segmented.Native (PhaseMemory)

private theorem openingAt (p : HealthyReads.Entry path root start)
    (entry : NativeReadScope.Entry physical path root image) (files : NativeReadScope.Files physical root image start) :
    NativeRecoverAt.Opening physical root p.lock p.fresh.val image p.fresh.state ∧
      (physical p.fresh.state).manifest.active = L0Manifest.encode image.version := by
  have resolved := HealthyRootAcquisition.validatedRoot path root p.resolve p.walStat p.walDir p.manifestStat
    p.manifestDir p.tableStat p.tableDir p.existsLock p.lockStat p.regular
  have valid := NativeScope.validatedRoot_rule path (entry.resolve start files)
    (fun r w hr file => (entry.stat file w hr.2).weaken (fun _ _ f => ⟨hr.1,f⟩) (fun _ _ f => ⟨hr.1,f⟩))
    (fun _ _ hr _ => hr.2)
  rw [Post,resolved] at valid
  have opened := entry.openFile _ valid.2
  rw [Post,p.openLock] at opened
  have grant := entry.lock _ _ ⟨_,p.openLock⟩ opened.1 opened.2
  rw [Post,p.exclusive] at grant
  obtain ⟨owned,phase,fresh⟩ := entry.fresh _ _ ⟨_,⟨_,p.openLock⟩,p.exclusive⟩ (grant.2 rfl) grant.1
  exact ⟨⟨owned,phase,fresh.catalog,fresh.disk⟩,fresh.manifest⟩

noncomputable abbrev pinned (physical : W → Footprint inode) (root : FilePath) (id : UInt64) :=
  pin physical (tablePath (root / "tables") id)

structure ReadProgress (physical : W → Footprint inode) (life : NativeRead.Lifetime)
    (heap : PhaseMemory) (p : HealthyReads.Entry path root start) (image : Selected) where
  entry : NativeReadScope.Entry physical path root image
  runtime : WithOpenReads.Runtime physical root p.lock p.fresh.val image life heap
  recovery : Progress runtime p.fresh.state
  reading : ∀ wal session hist t (online : Online physical root p.lock p.fresh.val wal session image hist t),
    NativeRead.HealthyChecks (runtime.tables wal t online.owned) image.version.tables
  cleanup : HealthyMutation.Cleanup physical heap root p.lock p.fresh.val image none

structure ReadResult (physical : W → Footprint inode) (path root : FilePath) (key : UInt64)
    (value : Mutation) (id : UInt64) (ident : inode) (bytes : ByteArray)
    (life : NativeRead.Lifetime) (start : W) (heap : PhaseMemory) (p : HealthyReads.Entry path root start)
    (image : Selected) (io : ReadProgress (pinned physical root id ident bytes) life heap p image) : Prop where
  returned : ∃ wal callback handle t done, ∃ phaseReadAt, ∃ owner : NativeRead.Owned
      (pinned physical root id ident bytes callback) root p.lock p.fresh.val,
    Native.get handle key callback = .ok value.value t ∧
    Native.withOpen path (fun h => Native.get h key) start = .ok value.value done ∧
    ∃ e : NativeRead.Exit ⟨root / "tables",id,.lookup key,phaseReadAt⟩,
      e.reached = t ∧ e.reply = .ok (some value) ∧
      (io.runtime.tables wal callback owner).inodeOf e.handle e.entered = some ident ∧
      (physical e.checked).names (tablePath (root / "tables") id) = some ident ∧
      (physical e.checked).contents ident = some bytes ∧ ¬ life.liveAtReturn e e.handle

theorem withOpen {physical : W → Footprint inode} {id : UInt64}
    (p : HealthyReads.Entry path root start) (img : Selected) (s : Session) (key : UInt64) (value : Mutation)
    (fits : img.view.tail < UInt64.size) (hit : lookupRows s.mem.toList key = some value)
    (files : NativeReadScope.Files physical root (published img s id) start)
    (run : Execution.Run events none (published img s id))
    (ident : inode) (bytes : ByteArray) (name : (physical start).names (tablePath (root / "tables") id) = some ident)
    (content : (physical start).contents ident = some bytes) (heap : PhaseMemory)
    (io : ReadProgress (pinned physical root id ident bytes) life heap p (published img s id)) :
    ReadResult physical path root key value id ident bytes life start heap p (published img s id) io := by
  let ph := pinned physical root id ident bytes
  let image := published img s id
  obtain ⟨state,_,represented⟩ := run.refines
  obtain ⟨hist,⟨d⟩⟩ : ∃ history, Nonempty (Durable image history) := by
    cases state with
    | ready db => obtain ⟨_,_,impossible,_⟩ := represented; cases impossible
    | offline known pending => obtain ⟨_,h,_,dur⟩ := represented; exact ⟨_,dur⟩
  have files' := pinFiles files name content
  obtain ⟨opening,active⟩ := openingAt p io.entry files'
  obtain ⟨session,wal,t,ran,installed,attached⟩ := recover heap io.runtime d opening active io.recovery
  have recovered := attached.sessionAt installed
  obtain ⟨_,r,frame⟩ := io.runtime.phase.refRead wal _ recovered.owned (by rw [recovered.phase]; rfl)
  rw [NativeScope.read_io] at r
  let q : InterruptedMutation.Prefix path root start := {
    checked := p.checkedLock, opened := p.opened, granted := p.held, recovered := t, lock := p.lock, wal := wal,
    session := session, resolved := HealthyRootAcquisition.validatedRoot path root p.resolve p.walStat p.walDir
      p.manifestStat p.manifestDir p.tableStat p.tableDir p.existsLock p.lockStat p.regular,
    openFile := p.openLock, exclusive := p.exclusive, recovery := ran,
    phaseRead := (EST.Out.ok.inj r).1.trans recovered.phase }
  obtain ⟨_,hist,online⟩ := q.online io.entry files' heap io.runtime run
  obtain ⟨h,binding,scope⟩ := q.withOpen (fun h => Native.get h key)
  obtain ⟨w,u,got,e,endEq,reply,borrow,named,stored,dropped,after⟩ :=
    lookupPinned img s key value fits hit life ident bytes online binding io.runtime (io.reading _ _ _ _ online)
  obtain ⟨reg,slot,_,_,_⟩ := after.child
  have held : NativeWriteRelease.Held none ph root p.lock p.fresh.val image (.online wal session) u :=
    NativeWriteRelease.Held.ofRecover ⟨after.owned,after.phase,after.catalog,after.manifest⟩
      (NativeReadScope.filesOfOnline after).disk
  obtain ⟨detached,endWal,took,registered,closed,finish⟩ := HealthyMutation.release io.runtime.phase io.runtime.cleanup.cached
    held ((io.runtime.cleanup.cached _ after.owned wal reg).mp slot) (io.cleanup.child _ _ _ _ · held)
  have unlock := io.cleanup.rootUnlock _ _ _ _ _ _ held took registered closed
  unfold Post at unlock
  cases released : p.lock.unlock endWal with
  | error e t => rw [released] at unlock; contradiction
  | ok _ done =>
    have cleaned : Lifecycle.finish (ε := IO.Error) ((Native.phaseCell q.ref).close WalRecoverySlice.Segmented.Native.close) q.lock.unlock u = .ok () done :=
      finish.trans released
    refine ⟨wal,_,h,u,done,w,online.owned,got,?_,e,endEq,reply,borrow,named,stored,dropped⟩
    rw [scope, Lifecycle.finish_io]
    simp [EIO.toBaseIO,got,cleaned]

end ExperimentalL0.HealthyPublishedRecovery
