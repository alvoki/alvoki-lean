import Alvoki.Experiments.L0.NativeFlushInterrupted

namespace ExperimentalL0.NativeFlushInterrupted
open NativeScope (W)
open NativeRead (Footprint tableNamespace)
open NativeFlushRestart (published stored)
open MutationExitCut (Frames Cut afterStore)
open NativeFlushExit (Edge)
open WalRecoverySlice.Segmented.Native (returnedWorld)

theorem Ingress.pinAtReturn {p : InterruptedMutation.Prefix path root start}
    (entered : Ingress p physical media image events) {id : UInt64}
    (nonempty : p.session.mem.isEmpty = false) (fits : image.view.tail < UInt64.size)
    (file : NativeFlushStore.SameFile media id p.session.mem.toList made
      (returnedWorld (NativeFlush.store root image p.session (storeWorld p))))
    (leaves : Frames (Edge physical root media (stored image p.session id).tables) stop
      (afterStore p.ref p.lock p.session (result p image)) (returnedWorld (result p image))) :
    NativeFlushStore.SameFile media id p.session.mem.toList made
      (returnedWorld (Native.withOpen path Native.flush start)) := by
  have resultEq : result p image = NativeFlush.store root image p.session (storeWorld p) := by
    simp [result,NativeFlushExit.resultAt,nonempty,fits]
  rw [← resultEq] at file
  let tail := afterStore p.ref p.lock p.session (result p image)
  have ended := Cut.boundary (stop := stop) (MutationExitCut.Tail.Prefix.finish tail (returnedWorld (result p image)))
  have edge := ended.accumulate leaves (fun _ => Edge.same ..) Edge.trans
  rw [entered.exitState] at edge
  obtain ⟨i,bytes,built,durable,imageAt,ready,synced⟩ := file
  have row : (stored image p.session id).tables id = some p.session.mem.toList := by simp [stored]
  obtain ⟨ln,live⟩ := edge.catalog id _ i bytes row ready.named ready.visible
  obtain ⟨dn,disk⟩ := edge.stable id _ i bytes row synced ready.synced
  exact ⟨i,bytes,built,durable,imageAt,⟨ln,live,disk⟩,dn⟩

end ExperimentalL0.NativeFlushInterrupted
