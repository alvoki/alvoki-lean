import Alvoki.Experiments.L0.MutationSequence
import Alvoki.Experiments.L0.HealthyMutation

namespace ExperimentalL0.MutationSequence
open NativeScope Lifecycle
open NativeRead (Footprint)
open WalRecoverySlice.Segmented.Native (PhaseMemory Registration ChildMemory)
open NativeWriteRelease (KeepsLive)
open InterruptedMutation (Prefix)

variable {physical : W → Footprint inode} {heap : PhaseMemory} {image : Selected}

structure HealthyOperations (physical : W → Footprint inode) (heap : PhaseMemory)
    (p : Prefix path root start) (reg : Registration) (mem : ChildMemory (fun w => (physical w).disk))
    (image : Selected) (key value : UInt64) where
  steps : PairIO physical heap mem root p.lock p.ref p.wal reg p.session image
    (key,.put value) (key,.delete) p.callback
  healthy : steps.Healthy
  get : ∀ (r : Registration) w t, r.store = reg.store →
    After physical heap mem root p.lock p.ref p.wal r (next p.session (key,.put value))
      (extend image (key,.put value)) (key,.delete) w →
    (p.ref.get : IO (Phase Wal)) w = .ok (.online p.wal (next (next p.session (key,.put value)) (key,.delete))) t →
    KeepsLive mem r w t

/-- Successful primitive reports for a fresh initialized root produce the
same recovered prefix and registration consumed by the two public writes. -/
theorem initialized {disk : W → WalRecoverySlice.Segmented.Model.Disk} {mem : ChildMemory disk}
    (p : HealthyReads.Entry path root start) (manifest : HealthyReads.Manifest root p.fresh.state t)
    (opening : (p.fresh.val.get : IO (Phase Wal)) t = .ok .opening u)
    (grant : HealthyReads.WalRoot (root / "wal") u)
    (worker : ∀ s, WalRecoverySlice.Segmented.Native.acquireStore (root / "wal") u = .ok s (HealthyReads.storeEntry grant) →
      s.root = grant.canonical → s.directory = grant.directory → s.lock = grant.lock →
      WalRecoverySlice.Segmented.Native.HealthyEmpty.Worker s disk Q mem (HealthyReads.storeEntry grant))
    (attach : ∀ wal v reg, WalRecoverySlice.Segmented.Native.Origin (root / "wal") wal reg u v →
      heap.Registered wal reg v → heap.Registered wal reg (HealthyReads.attached p.fresh.val wal v))
    (publishRead : ∀ wal v reg, WalRecoverySlice.Segmented.Native.Origin (root / "wal") wal reg u v →
      heap.Registered wal reg (HealthyReads.scanned p.fresh.val wal v) →
      (HealthyReads.phaseRead p.fresh.val (HealthyReads.scanned p.fresh.val wal v)).val = .recovering wal)
    (publishSwap : ∀ wal v reg, WalRecoverySlice.Segmented.Native.Origin (root / "wal") wal reg u v →
      heap.Registered wal reg (HealthyReads.phaseRead p.fresh.val (HealthyReads.scanned p.fresh.val wal v)).state →
      heap.Registered wal reg (HealthyReads.online p.fresh.val wal v)) :
    ∃ q : Prefix path root start, ∃ reg, heap.Registered q.wal reg q.callback ∧ reg.session = HealthyReads.specSession := by
  obtain ⟨wal,v,reg,opened,shape,origin,held,_⟩ := grant.open heap worker
  have attached := attach wal v reg origin held
  have recovered := HealthyReads.recover manifest p.fresh.val heap opening opened (shape ▸ attached.ready)
  have scanned : heap.Registered wal reg (HealthyReads.scanned p.fresh.val wal v) :=
    ⟨attached.1,heap.unlock _ (heap.readFrame _ (heap.lock _ attached.2.1)),
      heap.unlock _ (heap.readFrame _ (heap.lock _ attached.2.2))⟩
  let q : Prefix path root start := {
    checked := p.checkedLock, opened := p.opened, granted := p.held, recovered := HealthyReads.scanned p.fresh.val wal v,
    lock := p.lock, wal := wal, session := HealthyReads.empty,
    resolved := HealthyRootAcquisition.validatedRoot path root p.resolve p.walStat p.walDir p.manifestStat
      p.manifestDir p.tableStat p.tableDir p.existsLock p.lockStat p.regular,
    openFile := p.openLock, exclusive := p.exclusive, recovery := recovered, phaseRead := publishRead _ _ _ origin scanned }
  exact ⟨q,reg,publishSwap _ _ _ origin (HealthyReads.readFrame heap p.fresh.val scanned),shape⟩

def events (before : List Event) (key value : UInt64) :=
  before ++ [.reopened, .written (key,.put value), .written (key,.delete), .got key none, .stop]

private theorem reported (run : Execution.Run (before ++ [.reopened]) (some session) image) (key value : UInt64) :
    Execution.Run (events before key value) none (extend (extend image (key,.put value)) (key,.delete)) := by
  let first : Change := (key,.put value)
  let second : Change := (key,.delete)
  have s₁ := run.written (fun _ i => i.append first)
  have s₂ := s₁.written (fun _ i => i.append second)
  have s₃ := s₂.got (key := key) (value := none) (by
    intro history installed
    obtain ⟨d, _, mem⟩ := installed
    have hit : (next (next session first) second).mem[key]? = some .delete := by simp [second,insert]
    change (next (next session first) second).mem = _ at mem
    rw [mem, replay_lookup] at hit
    rw [denote, d.split, latest_append, hit]
    rfl)
  simpa [events,first,second,List.append_assoc] using s₃.stop

/-- The recovered child supplies the first write authority. The returned
registration supplies the second, and its successor is still active during
the get. Cleanup closes this last registration and releases the root lock. -/
theorem withOpen (p : Prefix path root start) (key value : UInt64)
    (entry : NativeReadScope.Entry physical path root image) (files : NativeReadScope.Files physical root image start)
    (ops : WithOpenReads.Runtime physical root p.lock p.ref image life heap) (prior : Execution.Run before none image)
    (initial : ∃ reg, heap.Registered p.wal reg p.callback ∧ reg.session = HealthyReads.specSession)
    (localIO : ∀ (reg : Registration) (pathEq : reg.store.root = ops.wal.acquire.canonical), (physical p.callback).readyWal p.wal = some reg →
      HealthyOperations physical heap p reg (ops.wal.worker reg.store pathEq).children.memory image key value)
    (cleanup : HealthyMutation.Cleanup physical heap root p.lock p.ref (extend (extend image (key,.put value)) (key,.delete)) none)
    (linux : System.Platform.isWindows = false) :
    let first := (key, Mutation.put value)
    let second := (key, Mutation.delete)
    Execution.Run (events before key value) none (extend (extend image first) second) ∧
      ∃ (h : Native.Handle), ∃ u v t detached endWal done, ∃ one two : Registration,
        h.AtRoot root p.ref ∧ Native.put h key value p.callback = .ok () u ∧ Native.delete h key u = .ok () v ∧
        Native.get h key v = .ok none t ∧ two.store = one.store ∧ two.session.control.active = one.session.control.active + 1 ∧
        heap.Registered p.wal two detached ∧ WalRecoverySlice.Segmented.Native.close p.wal detached = .ok () endWal ∧
        p.lock.unlock endWal = .ok () done ∧ Native.withOpen path (fun h => program h first second key) start = .ok none done := by
  intro first second
  obtain ⟨trace,_,online⟩ := p.online entry files heap ops prior
  obtain ⟨reg,pathEq,slot,view,active⟩ := NativeMutationScope.atIssue ops online
  obtain ⟨r,registered,shape⟩ := initial
  have same : reg = r := Option.some.inj (slot.symm.trans ((ops.cleanup.cached _ online.owned p.wal r).mpr registered))
  subst r
  have fits : image.view.tail + 2 < UInt64.size := by rw [← view,shape]; decide
  have cap : reg.session.control.capacity = 1 := shape ▸ rfl
  have count : reg.session.activeCount = 0 := shape ▸ rfl
  obtain ⟨h,bound,scope⟩ := p.withOpen (fun h => program h first second key)
  let inputs := localIO reg pathEq slot
  obtain ⟨u,v,t,one,two,put,del,get,callback,_,rotation,store₁,store₂,_,final⟩ :=
    putDeleteGet ⟨⟨online.owned,online.phase,online.catalog,online.manifest⟩,active,view⟩ bound ops.cleanup.cached
      ops.phase key value cap count fits inputs.steps inputs.healthy linux inputs.get
  obtain ⟨_,_,_,_,_,ready⟩ := final.active
  have held := NativeWriteRelease.Held.ofRecover final.held (ready.installed.offline (request := none) (.inl final.view))
  obtain ⟨detached,endWal,took,registered,closed,finishEq⟩ := HealthyMutation.release (image := extend (extend image first) second)
    ⟨ops.phase.read,ops.phase.swap⟩ ops.cleanup.cached held final.active.2.1 (cleanup.child _ _ _ _ · held)
  have unlock := cleanup.rootUnlock _ _ _ _ _ _ held took registered closed
  unfold Post at unlock
  cases released : p.lock.unlock endWal with
  | error e done => rw [released] at unlock; contradiction
  | ok _ done =>
    refine ⟨reported trace key value,h,u,v,t,detached,endWal,done,one,two,bound,put,del,get,
      store₂.trans store₁.symm,rotation,registered,closed,released,?_⟩
    rw [scope, Lifecycle.finish_io]
    simp [EIO.toBaseIO, first, second, callback, finishEq, released]

end ExperimentalL0.MutationSequence
