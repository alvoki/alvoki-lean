import Alvoki.Experiments.L0.HealthyTableRead
import Alvoki.Experiments.L0.HealthyReads
import Alvoki.Experiments.L0.InterruptedMutation

namespace ExperimentalL0.HealthyPublishedRecovery
open System Lifecycle NativeRecoverAt
open NativeRead (Footprint HealthyChecks checkTables_healthy Frame)
open NativeScope (swap_io)
open WalRecoverySlice.Segmented.Native (PhaseMemory ChildMemory Registration Origin)
open WalRecoverySlice.Segmented.Native.HealthyEmpty (bind_ok lift_ok checked_ok FileBytes)
open Alvoki.NativePost (Returns W)

structure Progress {physical : W → Footprint inode} {heap : PhaseMemory} {image : Selected}
    (ops : WithOpenReads.Runtime physical root lock ref image life heap) (start : W) where
  manifestAt : W
  walAt : W
  manifest : HealthyReads.Manifest root start manifestAt image.version
  opening : (ref.get : IO (Phase Wal)) manifestAt = .ok .opening walAt
  grant : HealthyReads.WalRoot (root / "wal") walAt
  memory : ChildMemory (fun w => (physical w).disk)
  worker : ∀ s, WalRecoverySlice.Segmented.Native.acquireStore (root / "wal") walAt = .ok s (HealthyReads.storeEntry grant) →
    s.root = grant.canonical → s.directory = grant.directory → s.lock = grant.lock →
    WalRecoverySlice.Segmented.Native.HealthyEmpty.Reports s (fun w => (physical w).disk) (fun _ => True)
      memory (HealthyReads.storeEntry grant) image.view.batches
  attach : ∀ wal reg v, Origin (root / "wal") wal reg walAt v → heap.Registered wal reg v →
    heap.Registered wal reg (HealthyReads.attached ref wal v)
  tables : ∀ wal w (a : Attached physical root lock ref image wal w),
    HealthyChecks (ops.tables wal w a.1.owned) image.version.tables

private theorem Progress.openWal {physical : W → Footprint inode} {heap : PhaseMemory}
    {ops : WithOpenReads.Runtime physical root lock ref image life heap} (io : Progress ops start)
    (input : ManifestReady physical root lock ref image io.walAt none) :
    ∃ wal t reg, WalRecoverySlice.Segmented.Native.openExisting (root / "wal") io.walAt = .ok wal t ∧
      Origin (root / "wal") wal reg io.walAt t ∧ heap.Registered wal reg t := by
  let grant := io.grant
  obtain ⟨s,acquired,path,dir,lockEq,_⟩ := HealthyRootAcquisition.walStore (root / "wal") grant.canonical
    grant.resolve grant.openDir grant.stat grant.valid grant.openLock grant.held
  let p := io.worker s acquired path dir lockEq
  let a := ops.wal.acquire
  have start := WalRecoverySlice.Segmented.Native.acquireStore_io heap _ a.canonical
    (a.resolve io.walAt ⟨input.2,input.1⟩) a.openDir a.stat a.opened a.openLock a.tryLock a.fresh
  rw [Alvoki.NativePost.IOReturns,acquired] at start
  have worker := ops.wal.worker s start.path
  obtain ⟨prior,fits⟩ := p.selected worker ⟨start.directoryBound,start.owns,start.empty,start.frame.2⟩ start.frame.1
  let derived : WalRecoverySlice.Segmented.Native.HealthyEmpty.Worker s _ _ _ _ image.view.batches := ⟨p,prior⟩
  have locked : WalRecoverySlice.Segmented.Native.RootLockAt s.root s.lock := by
    rw [path,lockEq]
    exact ⟨grant.statWorld,grant.lockWorld,grant.heldWorld,grant.openLock,grant.held⟩
  obtain ⟨wal,t,reg,run,_,origin,registered,_⟩ := derived.openExisting fits heap acquired locked
  exact ⟨wal,t,reg,run,origin,registered⟩

theorem recover {physical : W → Footprint inode} (heap : PhaseMemory)
    (ops : WithOpenReads.Runtime physical root lock ref image life heap) (d : Durable image history)
    (opening : Opening physical root lock ref image start)
    (bytes : (physical start).manifest.active = L0Manifest.encode image.version) (io : Progress ops start) :
    ∃ session wal t, Native.recoverAt root ref start = .ok session t ∧ Installed session image history ∧
      Attached physical root lock ref image wal t := by
  have manifest := io.manifest.runVersion ref d.unique
  have ready := manifestOpening d opening bytes (ops.manifest _ opening)
  rw [Returns, manifest] at ready
  have input := readOpening (failed := fun _ => False) ops.phase ready.2
  rw [Returns,show (Native.componentCell ref).read.run io.manifestAt = .ok (.ok .opening) io.walAt from lift_ok io.opening] at input
  obtain ⟨wal,v,reg,opened,origin,held⟩ := io.openWal input.2
  have called := HealthyReads.walRan io.opening opened heap (io.attach _ _ _ origin held).ready
  have same v (p : WalRecoverySlice.Segmented.PermittedView image.view none v) : v = image.view := by
    simpa [WalRecoverySlice.Segmented.PermittedView] using p
  have selected := reopenWal_selected ready.2 heap ops.cleanup.cached ops.wal.toOpenIO ops.childCache ops.phase
    (fun v wal w p => by cases same v p; exact ops.scan wal w)
  rw [Returns,called] at selected
  obtain ⟨permitted,child,attached⟩ := selected
  have choice := same _ permitted
  rw [choice] at called attached
  let prim := ops.tables child _ attached.1.owned
  obtain ⟨t,checks,frame⟩ := checkTables_healthy prim (Native.callbackComponents root ref).tables rfl d
    (fun _ step => attached.1.catalog.frame step.tablesKept) (io.tables child _ attached) _ Frame.refl
  have ran : Native.recoverAt root ref start = .ok ⟨image.version,replay d.pending⟩ t := by
    unfold Native.recoverAt
    apply checked_ok
    unfold ExperimentalL0.recover
    apply bind_ok manifest
    apply bind_ok called
    simp only [d.bounds, and_self, ite_true, d.replay_pending]
    exact bind_ok checks rfl
  exact ⟨_,child,t,ran,⟨d,rfl,rfl⟩,attached.1.frame frame,attached.2.frame frame⟩

end ExperimentalL0.HealthyPublishedRecovery
