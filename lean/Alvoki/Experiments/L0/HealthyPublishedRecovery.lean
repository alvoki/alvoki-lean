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
  bs : List WalRecoverySlice.Bytes
  small : bs.length ≤ 1
  manifestAt : W
  walAt : W
  manifest : HealthyReads.Manifest root start manifestAt image.version
  opening : (ref.get : IO (Phase Wal)) manifestAt = .ok .opening walAt
  grant : HealthyReads.WalRoot (root / "wal") walAt
  memory : ChildMemory (fun w => (physical w).disk)
  worker : ∀ s, WalRecoverySlice.Segmented.Native.acquireStore (root / "wal") walAt = .ok s (HealthyReads.storeEntry grant) →
    s.root = grant.canonical → s.directory = grant.directory → s.lock = grant.lock →
    WalRecoverySlice.Segmented.Native.HealthyEmpty.Worker s (fun w => (physical w).disk) (fun _ => True)
      memory (HealthyReads.storeEntry grant) bs
  attach : ∀ wal reg v, Origin (root / "wal") wal reg walAt v → heap.Registered wal reg v →
    heap.Registered wal reg (HealthyReads.attached ref wal v)
  tables : ∀ wal w (a : Attached physical root lock ref image wal w),
    HealthyChecks (ops.tables wal w a.1.owned) image.version.tables

theorem recover {physical : W → Footprint inode} (heap : PhaseMemory)
    (ops : WithOpenReads.Runtime physical root lock ref image life heap) (d : Durable image history)
    (opening : Opening physical root lock ref image start)
    (bytes : (physical start).manifest.active = L0Manifest.encode image.version) (io : Progress ops start) :
    ∃ session wal t, Native.recoverAt root ref start = .ok session t ∧ Installed session image history ∧
      Attached physical root lock ref image wal t := by
  have manifest := io.manifest.runVersion ref d.unique
  have ready := manifestOpening d opening bytes (ops.manifest _ opening)
  rw [Returns, manifest] at ready
  obtain ⟨wal,v,reg,opened,shape,origin,held,_⟩ := io.grant.openBatches heap io.small io.worker
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
