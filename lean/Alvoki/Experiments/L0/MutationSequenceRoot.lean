import Alvoki.Experiments.L0.MutationSequence
import Alvoki.Experiments.L0.HealthyMutation

namespace ExperimentalL0.MutationSequence
open NativeScope Lifecycle
open NativeRead (Footprint)
open WalRecoverySlice.Segmented.Native (PhaseMemory Registration ChildMemory)
open WalRecoverySlice.Segmented.Native.HealthyEmpty (control)
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

private theorem emptyCounts {disk : W → WalRecoverySlice.Segmented.Model.Disk}
    {mem : ChildMemory disk} {reg : Registration}
    (active : WalRecoverySlice.Segmented.Native.AppendIO.Active mem heap wal reg w)
    (control : (disk w).liveControl = some WalRecoverySlice.Segmented.Native.HealthyEmpty.control)
    (empty : reg.session.view = ⟨0,[]⟩) : reg.session.control.capacity = 1 ∧ reg.session.activeCount = 0 := by
  obtain ⟨_,_,_,_,_,history,shape,_,observed,_,_⟩ := active
  have cfg := Option.some.inj (observed.symm.trans control)
  have view := congrArg WalRecoverySlice.Segmented.Session.view shape
  rw [empty, cfg] at view
  have nil : history = [] := by
    simpa [WalRecoverySlice.Segmented.sessionOf, WalRecoverySlice.Segmented.historyView, WalRecoverySlice.Segmented.Native.HealthyEmpty.control] using
      (congrArg WalRecoverySlice.Segmented.Contract.View.batches view).symm
  exact ⟨cfg ▸ rfl, by rw [shape, cfg, nil]; rfl⟩

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
    (control : (physical p.callback).disk.liveControl = some WalRecoverySlice.Segmented.Native.HealthyEmpty.control) (empty : image.view = ⟨0,[]⟩)
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
  obtain ⟨cap,count⟩ := emptyCounts active control (view.trans empty)
  have fits : image.view.tail + 2 < UInt64.size := by rw [empty]; decide
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
