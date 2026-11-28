import Alvoki.Experiments.L0.MutationExitCut
import Alvoki.Experiments.L0.NativeFlush

namespace ExperimentalL0.NativeFlushExit
open NativeScope (W Ref Post)
open NativeRead (Footprint tableNamespace SessionAt)
open NativeReadScope (Files)
open NativeFlushRestart (stored published proposal Survivor)
open MutationExitCut (afterStore Cut Frames Frame)
open WalRecoverySlice.Segmented (Recoverable)
open WalRecoverySlice.Segmented.Native (returnedWorld)
open System

abbrev Result := EST.Out IO.Error IO.RealWorld Session

/-- These are the visible media at return from the store, before the update
publishes its session or tries to close. In the admitted case a later power
loss can still choose different bytes from the current active manifest. -/
inductive Media (physical : W → Footprint inode) (root : FilePath) (before : Selected) (s : Session)
    (w : W) : Catalog → Prop where
  | original (catalog : (tableNamespace physical root).Represents w before.tables)
      (stable : (physical w).manifest.Stable (L0Manifest.encode before.version)) :
      Media physical root before s w before.tables
  | published (id : UInt64) (fresh : before.tables id = none) (fits : before.view.tail < UInt64.size)
      (catalog : (tableNamespace physical root).Represents w (stored before s id).tables)
      (stable : (physical w).manifest.Stable (L0Manifest.encode (proposal before s id))) :
      Media physical root before s w (stored before s id).tables
  | admitted (id : UInt64) (fresh : before.tables id = none) (fits : before.view.tail < UInt64.size)
      (catalog : (tableNamespace physical root).Represents w (stored before s id).tables)
      (allowed : (physical w).manifest.Admits (L0Manifest.encode before.version)
        (some (L0Manifest.encode (proposal before s id)))) :
      Media physical root before s w (stored before s id).tables

/-- Frame only the physical observations read by reboot. No phase, descriptor
or lock is assumed to survive the updating callback's finalizers. -/
theorem Media.restart (source : Media physical root before s w tables)
    (wal : Recoverable before.view none (physical w).disk) (edge : Frame physical root tables w cut)
    (restart : NativeAppendCut.Restarted physical root tables cut (physical cut).disk mode after) :
    ∃ img, Survivor physical root before s after img ∧ Files physical root img after := by
  cases source with
  | original catalog stable =>
    have files := edge.files stable catalog wal restart
    exact ⟨_, .old files.manifest, files⟩
  | published id fresh fits catalog stable =>
    have files := edge.files (image := NativeFlushRestart.published before s id) stable catalog wal restart
    have row := files.catalog id s.mem.toList (by simp [NativeFlushRestart.published, stored, Selected.publish])
    exact ⟨_, .newTable id fresh fits row files.manifest, files⟩
  | admitted id fresh fits catalog allowed =>
    have retained := catalog.frame edge.catalog
    have old : (tableNamespace physical root).Represents cut before.tables := by
      intro k rows bound
      have ne : k ≠ id := by rintro rfl; simp [fresh] at bound
      exact retained k rows (by simpa [stored, ne] using bound)
    have admitted : (physical cut).manifest.Admits (L0Manifest.encode before.version)
        (some (L0Manifest.encode (proposal before s id))) := by
      simpa only [DurableBlob.Image.Admits, edge.manifest, edge.survivors] using allowed
    exact NativeFlushRestart.ofRestart restart old fresh fits
      (retained id s.mem.toList (by simp [stored])) admitted (edge.disk.recoverable wal)

def resultAt (root : FilePath) (image : Selected) (s : Session) (w : W) : Result :=
  if s.mem.isEmpty then .ok s w
  else if image.view.tail < UInt64.size then NativeFlush.store root image s w
  else .error (IO.userError "absolute WAL position exhausted") w

/-- Project the native public flush from the callback invoked by this open. The
tail is indexed by its actual store return (including a thrown IO error). -/
theorem dispatch (p : InterruptedMutation.Prefix path root start)
    (entry : NativeReadScope.Entry physical path root image) (files : Files physical root image start)
    (heap : WithOpenReads.Heap) (ops : WithOpenReads.Runtime physical root p.lock p.ref image life heap)
    (run : Execution.Run events none image)
    (scan : ∀ history w, SessionAt physical root p.lock p.ref p.wal p.session image history w (.updating p.wal) →
      NativeRecoverAt.ScanPrimitives physical root p.wal image.tables w) :
    Execution.Run (events ++ [.reopened]) (some p.session) image ∧ ∃ history w,
      SessionAt physical root p.lock p.ref p.wal p.session image history w (.updating p.wal) ∧
      let out := resultAt root image p.session w
      ∃ h, Native.Handle.AtRoot h root p.ref ∧
      Native.withOpen path Native.flush start = Lifecycle.finish (ε := IO.Error) (Native.flush h)
        (Lifecycle.finish (ε := IO.Error) ((Native.phaseCell p.ref).close WalRecoverySlice.Segmented.Native.close)
          p.lock.unlock) p.callback ∧
      Native.flush h p.callback = NativeWrite.afterWrite p.ref out ∧
      ((afterStore p.ref p.lock p.session out).run (returnedWorld out)).state =
        returnedWorld (Native.withOpen path Native.flush start) := by
  obtain ⟨opened, history, online⟩ := p.online entry files heap ops run
  obtain ⟨h, binds, invoked⟩ := p.withOpen Native.flush
  obtain ⟨w, reached, executed⟩ := NativeFlush.dispatch online binds heap ops.cleanup.cached ops.phase (scan history)
  exact ⟨opened, history, w, reached, h, binds, invoked, executed, invoked ▸ MutationExitCut.afterWrite_state _ executed p.lock p.session⟩

/-- Under a stop after store return and before reply, even a successful publication
has an uncertain client acknowledgement. The physical catalog and manifest still
decide exactly which image the subsequent concrete open/check/get/cleanup consumes. -/
theorem readAfterReturn {physical : W → Footprint inode} (out : Result)
    (source : Media physical root image s (returnedWorld out) tables)
    (wal : Recoverable image.view none (physical (returnedWorld out)).disk)
    (position : Cut stop (afterStore ref lock s out) (returnedWorld out) cut)
    (frames : Frames (Frame physical root tables) stop (afterStore ref lock s out) (returnedWorld out))
    (restart : NativeAppendCut.Restarted physical root tables cut (physical cut).disk mode after)
    (run : Execution.Run events (some s) image)
    (entry : ∀ img, NativeReadScope.Entry physical path root img) (heap : WithOpenReads.Heap)
    (runtime : ∀ img lock ref, WithOpenReads.Runtime physical root lock ref img life heap)
    (keys : List UInt64) (rootLife : NativeReadRelease.RootLifetime) :
    let stopped := (events ++ [.flushUncertain]) ++ [.stop]
    ∃ img, Survivor physical root image s after img ∧ Files physical root img after ∧
      Execution.Run stopped none img ∧
      Post (Native.withOpen path (fun h => (NativeRead.readMany h keys : IO (List NativeRead.Reply)))) after
        (WithOpenReads.Finished physical root img life stopped ⟨path, keys, after⟩ rootLife)
        (WithOpenReads.Failure physical root img life stopped ⟨path, keys, after⟩ rootLife) := by
  obtain ⟨img, selected, files⟩ := source.restart wal (position.frame frames) restart
  exact ⟨img, selected, files, (selected.uncertain run).stop,
    NativeFlushRestart.uncertainReopen selected files run (entry img) heap (runtime img) keys rootLife⟩

end ExperimentalL0.NativeFlushExit
