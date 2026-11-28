import Alvoki.Experiments.L0.NativeFlush
import Alvoki.Experiments.L0.NativeWriteRelease

namespace ExperimentalL0.NativeFlush

open NativeRead (Footprint SessionAt Online RegisteredChild tableNamespace)
open NativeScope (W Ref Wal Post Callback)
open NativeReadScope (Files Grant)
open NativeReadRelease (Closed)
open NativeFlushRestart (published proposal)
open WalRecoverySlice.Segmented.Native (PhaseMemory)

/-- A completed store either skipped an empty memtable or durably published
the actual table identifier and scan watermark. -/
inductive Selection (before : Selected) (s : Session) : Session → Selected → Prop where
  | unchanged : Selection before s s before
  | newTable (id : UInt64) : before.tables id = none → before.view.tail < UInt64.size →
      Selection before s ⟨proposal before s id, ∅⟩ (published before s id)

theorem Selection.install (sel : Selection before s next img) (valid : Installed s before history) :
    Installed next img history := by
  cases sel with
  | unchanged => exact valid
  | newTable _ fresh fits => exact NativeFlushRestart.installedPublished valid fresh fits

theorem Selection.durable (sel : Selection before s next img) (valid : Installed s before history) :
    Nonempty (Durable img history) := by
  obtain ⟨d, _⟩ := sel.install valid
  exact ⟨d⟩

structure Finished (physical : W → Footprint inode) (root : System.FilePath)
    (before : List Event) (image : Selected) (w : W) : Prop where
  outcome : ∃ s next img lock ref, Selection image s next img ∧ Closed physical root lock ref img w ∧
    Execution.Run ((before ++ [.flushed]) ++ [.stop]) none img ∧
    Execution.Run ((before ++ [.flushUncertain]) ++ [.stop]) none img

inductive Failed (physical : W → Footprint inode) (root : System.FilePath)
    (before : List Event) (image : Selected) (w : W) : Prop where
  | openFailed : Files physical root image w → Execution.Run (before ++ [.openFailed]) none image →
      Failed physical root before image w
  | flushFailed : Selection image s next img → Closed physical root lock ref img w →
      Execution.Run (((before ++ [.reopened]) ++ [.flushUncertain]) ++ [.stop]) none img →
      Failed physical root before image w
  | cleanup : Finished physical root (before ++ [.reopened]) image w → Failed physical root before image w

def Stored (physical : W → Footprint inode) (root : System.FilePath) (lock : IO.FS.Handle)
    (ref : Ref) (wal : Wal) (s : Session) (image : Selected) (history : Rows) (next : Session) (w : W) :=
  ∃ img, Selection image s next img ∧ SessionAt physical root lock ref wal next img history w (.updating wal)

def Uncertain (physical : W → Footprint inode) (root : System.FilePath) (lock : IO.FS.Handle)
    (ref : Ref) (wal : Wal) (s : Session) (image : Selected) (w : W) :=
  ∃ next img, Selection image s next img ∧ NativeWriteRelease.Held none physical root lock ref img (.updating wal) w ∧
    RegisteredChild physical root img wal w

theorem SessionAt.uncertain {physical : W → Footprint inode}
    (entry : SessionAt physical root lock ref wal s image history t (.updating wal)) :
    Uncertain physical root lock ref wal s image t :=
  ⟨s, image, .unchanged, ⟨entry.owned, entry.phase, NativeReadScope.filesOfChild entry.child entry.catalog entry.manifest.1⟩, entry.child⟩

private theorem accepted {physical : W → Footprint inode}
    (grant : Grant root lock ref) (phase : ∀ img, NativeRecoverAt.PhasePrimitives physical root lock ref img)
    (cleanup : ∀ img, NativeReadRelease.Laws heap physical root lock ref img)
    (run : Execution.Run (before ++ [.reopened]) (some s) image)
    (entry : Stored physical root lock ref wal s image history next t)
    (returned : Native.flush handle start = NativeWrite.afterWrite ref (.ok next t)) :
    Callback ref lock (Native.flush handle) start
      (fun _ => Finished physical root (before ++ [.reopened]) image) (fun _ => Failed physical root before image) := by
  obtain ⟨img, sel, reached⟩ := entry
  obtain ⟨_, u, _, _, read, swap, _, published⟩ := NativeWrite.afterWrite_publish
    ⟨reached.owned, reached.phase, reached.catalog, reached.manifest⟩ (phase img) next
  have reading := reached.advance read
  have online := reading.advance swap
  have done v (closed : Closed physical root lock ref img v) :
      Finished physical root (before ++ [.reopened]) image v :=
    ⟨s, next, img, lock, ref, sel, closed, (run.flushed fun _ valid => sel.install valid).stop,
      (run.flushUncertain fun _ valid => sel.durable valid).stop⟩
  unfold Callback Post
  rw [returned, published]
  exact NativeReadRelease.onlineTo (cleanup img) grant online done (fun _ _ h => .cleanup (done _ h))

private theorem failed {physical : W → Footprint inode}
    (grant : Grant root lock ref) (phase : ∀ img, NativeRecoverAt.PhasePrimitives physical root lock ref img)
    (cache : NativeRecoverAt.Cached heap physical root lock ref)
    (release : ∀ img, NativeWriteRelease.Laws heap none physical root lock ref img)
    (run : Execution.Run (before ++ [.reopened]) (some s) image)
    (entry : Uncertain physical root lock ref wal s image t)
    (returned : Native.flush handle start = NativeWrite.afterWrite ref (.error error t)) :
    Callback ref lock (Native.flush handle) start
      (fun _ => Finished physical root (before ++ [.reopened]) image) (fun _ => Failed physical root before image) := by
  obtain ⟨next, img, sel, held, reg, slot, origin, _, _⟩ := entry
  have ready := (cache t held.owned wal reg).mp slot
  obtain ⟨_, closed, custody⟩ := NativeWriteRelease.afterError (release img) grant (phase img) held
    (.ofRegistered ready origin.2) error
  have done u (c : Closed physical root lock ref img u) : Failed physical root before image u :=
    .flushFailed sel c (run.flushUncertain fun _ valid => sel.durable valid).stop
  unfold Callback Post
  rw [returned, closed]
  exact NativeWriteRelease.outerOffline wal (release img).toRootUnlock grant (phase img) custody done (fun _ => done)

/-- The component consumer on the actually reserved and scanned world.
The concrete filesystem producer supplies the store postcondition. -/
theorem callback {physical : W → Footprint inode}
    (reached : SessionAt physical root lock ref wal s image history t (.updating wal))
    (called : Native.flush handle start = NativeWrite.afterWrite ref
      (if s.mem.isEmpty then .ok s t else if image.view.tail < UInt64.size then store root image s t
       else .error (IO.userError "absolute WAL position exhausted") t))
    (grant : Grant root lock ref)
    (heap : PhaseMemory) (cached : NativeRecoverAt.Cached heap physical root lock ref)
    (phase : ∀ img, NativeRecoverAt.PhasePrimitives physical root lock ref img)
    (cleanup : ∀ img, NativeReadRelease.Laws heap physical root lock ref img)
    (release : ∀ img, NativeWriteRelease.Laws heap none physical root lock ref img)
    (run : Execution.Run (before ++ [.reopened]) (some s) image)
    (storage :
      s.mem.isEmpty = false → image.view.tail < UInt64.size →
      Post (store root image s) t (Stored physical root lock ref wal s image history)
        (fun _ => Uncertain physical root lock ref wal s image)) :
    Callback ref lock (Native.flush handle) start
      (fun _ => Finished physical root (before ++ [.reopened]) image) (fun _ => Failed physical root before image) := by
  cases empty : s.mem.isEmpty with
  | true =>
    simp only [empty, ↓reduceIte] at called
    exact accepted grant phase cleanup run ⟨image, .unchanged, reached⟩ called
  | false =>
    simp only [empty, Bool.false_eq_true, ↓reduceIte] at called
    by_cases fits : image.view.tail < UInt64.size
    · simp only [fits, ↓reduceIte] at called
      have post := storage empty fits
      cases ret : store root image s t with
      | ok next u =>
        rw [ret] at called
        exact accepted grant phase cleanup run (by simpa only [Post, ret] using post) called
      | error e u =>
        rw [ret] at called
        exact failed grant phase cached release run (by simpa only [Post, ret] using post) called
    · simp only [fits, ↓reduceIte] at called
      exact failed grant phase cached release run (SessionAt.uncertain reached) called


end ExperimentalL0.NativeFlush
