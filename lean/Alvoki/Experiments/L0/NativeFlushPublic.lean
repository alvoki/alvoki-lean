import Alvoki.Experiments.L0.NativeFlushStore
import Alvoki.Experiments.L0.NativeFlushCatalog

namespace ExperimentalL0.NativeFlush
open NativeRead (Footprint SessionAt tableNamespace Lifetime)
open NativeReadScope (Files)
open NativeScope (W Ref Wal Post)
open NativeReadRelease (RootScope RootLifetime RootCall)
open NativeFlushCatalog (joint)
open WalRecoverySlice.Segmented.Native (PhaseMemory)

/-- A second public scope starts on the exact world left by the first scope,
including after the manifest rename reported an error. -/
def ReadAt (physical : W → Footprint inode) (path root : System.FilePath) (life : Lifetime)
    (rootLife : RootLifetime) (keys : List UInt64) (events : List Event) (img : Selected) (w : W) :=
  let call : RootCall := ⟨path,keys,w⟩
  Execution.Run events none img ∧ (∃ state, Client.Allows events state ∧ Execution.Represents none img state) ∧
  Post call.run w (WithOpenReads.Finished physical root img life events call rootLife)
    (WithOpenReads.Failure physical root img life events call rootLife)

structure ReadRuntime (physical : W → Footprint inode) (path root : System.FilePath) (life : Lifetime) (heap : PhaseMemory) where
  entry : ∀ img, NativeReadScope.Entry physical path root img
  runtime : ∀ img lock ref, WithOpenReads.Runtime physical root lock ref img life heap

private theorem readAt (io : ReadRuntime physical path root life heap) (rootLife : RootLifetime)
    (files : Files physical root img w) (trace : Execution.Run events none img) (keys : List UInt64) :
    ReadAt physical path root life rootLife keys events img w :=
  ⟨trace, trace.refines, WithOpenReads.withOpen (io.entry img) files heap (io.runtime img) trace keys rootLife⟩

def Reopens (physical : W → Footprint inode) (path root : System.FilePath) (life : Lifetime)
    (rootLife : RootLifetime) (keys : List UInt64) (before : List Event) (img : Selected) (w : W) :=
  ∃ s next after, Selection img s next after ∧
    ReadAt physical path root life rootLife keys ((before ++ [.flushed]) ++ [.stop]) after w ∧
    ReadAt physical path root life rootLife keys ((before ++ [.flushUncertain]) ++ [.stop]) after w

private theorem Finished.reopens (out : Finished physical root events img w)
    (io : ReadRuntime physical path root life heap) (keys : List UInt64) (rootLife : RootLifetime) :
    Reopens physical path root life rootLife keys events img w := by
  obtain ⟨s,next,after,_,_,sel,closed,delivered,lost⟩ := out.outcome
  exact ⟨s,next,after,sel,readAt io rootLife closed.files delivered keys,readAt io rootLife closed.files lost keys⟩

def Retry (physical : W → Footprint inode) (path root : System.FilePath) (life : Lifetime)
    (rootLife : RootLifetime) (keys : List UInt64) (before : List Event) (img : Selected) (w : W) :=
  ReadAt physical path root life rootLife keys (before ++ [.openFailed]) img w ∨
  ∃ s next after, Selection img s next after ∧ ReadAt physical path root life rootLife keys
    (((before ++ [.reopened]) ++ [.flushUncertain]) ++ [.stop]) after w

private theorem Failed.retry (out : Failed physical root before img w)
    (io : ReadRuntime physical path root life heap) (keys : List UInt64) (rootLife : RootLifetime) :
    Retry physical path root life rootLife keys before img w := by
  cases out with
  | openFailed files run => exact .inl (readAt io rootLife files run keys)
  | flushFailed sel closed run => exact .inr ⟨_,_,_,sel,readAt io rootLife closed.files run keys⟩
  | cleanup finished =>
    obtain ⟨s,next,after,sel,_,lost⟩ := finished.reopens io keys rootLife
    exact .inr ⟨s,next,after,sel,lost⟩

theorem withOpen {physical : W → Footprint inode} {media : NativeTableCreate.Media (tableNamespace physical root)}
    (entry : NativeReadScope.Entry (joint physical root media) path root image)
    (files : Files physical root image start) (saved : NativeFlushCatalog.Saved physical root media image.tables start)
    (heap : PhaseMemory) (runtime : ∀ lock ref, WithOpenReads.Runtime (joint physical root media) root lock ref image life heap)
    (prior : Execution.Run before none image)
    (scans : ∀ lock ref wal s history u, SessionAt (joint physical root media) root lock ref wal s image history u (.updating wal) →
      NativeRecoverAt.ScanPrimitives (joint physical root media) root wal image.tables u)
    (phase : ∀ lock ref img, NativeRecoverAt.PhasePrimitives physical root lock ref img)
    (cleanup : ∀ lock ref img, NativeReadRelease.Laws heap physical root lock ref img)
    (release : ∀ lock ref img, NativeWriteRelease.Laws heap none physical root lock ref img)
    (manifest : NativeManifestPublish.Media inode) (stop : NativeManifestPublish.Stop)
    (storage : ∀ lock ref wal s t, NativeFlushStore.Runtime physical root lock ref wal image s media manifest stop t)
    (reader : ReadRuntime physical path root life heap) (keys : List UInt64) (rootLife : RootLifetime) :
    let call : RootScope := ⟨path,.flush,start⟩
    Post (Native.withOpen path Native.flush) start
      (fun _ w => call.Released rootLife ∧ Finished physical root (before ++ [.reopened]) image w ∧
        Reopens physical path root life rootLife keys (before ++ [.reopened]) image w)
      (fun _ w => call.Released rootLife ∧ Failed physical root before image w ∧
        Retry physical path root life rootLife keys before image w) := by
  let scope : RootScope := ⟨path,.flush,start⟩
  apply Post.weaken (before := fun _ => Finished physical root (before ++ [.reopened]) image)
    (failure := fun _ => Failed physical root before image)
  · apply NativeFlushCatalog.withOpen entry files saved heap runtime prior scans
    · exact fun _ _ kept trace => .openFailed kept trace
    intro lock ref wal s history handle entered t grant binding run reached durable called
    apply callback reached called grant heap (cleanup lock ref image).cached (phase lock ref)
      (cleanup lock ref) (release lock ref) run
    intro _ fits
    have produced := NativeFlushStore.produce (storage lock ref wal s t)
      ⟨⟨reached.owned,reached.phase,reached.child⟩,reached.manifest,reached.catalog,durable⟩ reached.installed fits
    have selected := produced.1
    cases ran : store root image s t <;> rw [ran] at selected <;> simpa only [Post, ran] using selected
  · exact fun _ _ finished => ⟨scope.released rootLife,finished,finished.reopens reader keys rootLife⟩
  · exact fun _ _ failure => ⟨scope.released rootLife,failure,failure.retry reader keys rootLife⟩

end ExperimentalL0.NativeFlush
