import Alvoki.Experiments.L0.NativeReadRelease

namespace ExperimentalL0.WithOpenReads
open System Lifecycle NativeRead
open NativeReadScope (Entry Files)
open NativeScope (Post)
abbrev W := NativeScope.W
abbrev Ref := NativeScope.Ref
abbrev Wal := NativeScope.Wal
abbrev Heap := WalRecoverySlice.Segmented.Native.PhaseMemory

/-- Primitives on the storage and runtime owned by this invocation. The
table operations cover either recovery validation or online lookup. -/
structure Runtime (physical : W → Footprint inode) (root : FilePath) (lock : IO.FS.Handle)
    (ref : Ref) (image : Selected) (life : Lifetime) (heap : Heap) where
  manifest : ∀ start, NativeRecoverAt.Opening physical root lock ref image start →
    NativeManifest.Primitives (root / "manifest") (NativeRecoverAt.ManifestFrame physical root image.tables start)
      (fun w => (physical w).manifest)
  wal : WalRecoverySlice.Segmented.Native.LocalOpenIO heap (root / "wal") (fun w => (physical w).disk)
    image.view (NativeRecoverAt.Held physical root lock ref image .opening)
  phase : NativeRecoverAt.PhasePrimitives physical root lock ref image
  scan : ∀ wal w, NativeRecoverAt.Attached physical root lock ref image wal w →
    NativeRecoverAt.ScanPrimitives physical root wal image.tables w
  tables : ∀ wal w, Owned (physical w) root lock ref →
    Primitives (tableNamespace physical root) life (Frame physical root wal image.tables w)
  cleanup : NativeReadRelease.Laws heap physical root lock ref image

def eventsAfter (events : List Event) (keys : List UInt64) (replies : List Reply) :=
  ((events ++ [.reopened]) ++ readEvents keys replies) ++ [.stop]

/-- A returned callback and cleanup. Even when cleanup fails, its reached
world and the actual callback replies identify the observed client trace. -/
structure Finished (physical : W → Footprint inode) (root : FilePath) (image : Selected)
    (life : Lifetime) (events : List Event) (keys : List UInt64) (replies : List Reply) (w : W) : Prop where
  trace : Execution.Run (eventsAfter events keys replies) none image
  client : ∃ state, Client.Allows (eventsAfter events keys replies) state ∧ Execution.Represents none image state
  callback : ∃ lock ref wal session history handle entered, Native.Handle.AtRoot handle root ref ∧
    Online physical root lock ref wal session image history entered ∧
    (readMany handle keys entered).val = replies ∧
    Online physical root lock ref wal session image history (readMany handle keys entered).state ∧
    allReleased life ref (root / "tables") handle keys entered ∧
    NativeReadRelease.Closed physical root lock ref image w

inductive Failure (physical : W → Footprint inode) (root : FilePath) (image : Selected)
    (life : Lifetime) (events : List Event) (keys : List UInt64) (w : W) : Prop where
  | before : Files physical root image w →
    Execution.Run (events ++ [.openFailed]) none image → Failure physical root image life events keys w
  | recovery : NativeReadRelease.Closed physical root lock ref image w →
    Execution.Run (events ++ [.openFailed]) none image → Failure physical root image life events keys w
  | cleanup : Finished physical root image life events keys replies w → Failure physical root image life events keys w

/-- A reported scope failure retains the entry files for a retry and the
client trace appropriate to the point where the failure occurred. -/
theorem Failure.refines (failure : Failure physical root image life events keys w) :
    Files physical root image w ∧ ∃ observed state,
      (observed = events ++ [.openFailed] ∨ ∃ replies, observed = eventsAfter events keys replies) ∧
      Client.Allows observed state ∧ Execution.Represents none image state := by
  cases failure with
  | before files run =>
    obtain ⟨state, allowed, off⟩ := run.refines
    exact ⟨files, _, state, .inl rfl, allowed, off⟩
  | recovery closed run =>
    obtain ⟨state, allowed, off⟩ := run.refines
    exact ⟨closed.files, _, state, .inl rfl, allowed, off⟩
  | cleanup finished =>
    obtain ⟨state, allowed, off⟩ := finished.client
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, closed⟩ := finished.callback
    exact ⟨closed.files, _, state, .inr ⟨_, rfl⟩, allowed, off⟩

theorem withOpen (entry : Entry physical path root image) (files : Files physical root image start)
    (heap : Heap) (runtime : ∀ lock ref, Runtime physical root lock ref image life heap)
    (prior : Execution.Run events none image) (keys : List UInt64) :
    Post (Native.withOpen path (fun h => (readMany h keys : IO (List Reply)))) start
      (Finished physical root image life events keys) (fun _ => Failure physical root image life events keys) := by
  have failedTrace := prior.openFailed (fun _ h => ⟨h⟩)
  obtain ⟨state, _, represented⟩ := prior.refines
  obtain ⟨history, durable⟩ : ∃ history, Nonempty (Durable image history) := by
    cases state with
    | ready db => obtain ⟨_, _, impossible, _⟩ := represented; cases impossible
    | offline known pending =>
      obtain ⟨_, history, _, d⟩ := represented
      exact ⟨_, d⟩
  obtain ⟨d⟩ := durable
  apply entry.withOpen files _ (fun _ _ before => .before before failedTrace)
  intro lock ref w opening bytes handle binding
  let ops := runtime lock ref
  have safe (actual) (D : Durable image actual) :=
    NativeRecoverAt.recoverAt D opening bytes (ops.manifest _ opening) heap ops.cleanup.cached
      ops.wal.toOpenIO ops.phase ops.scan (fun wal t a => ops.tables wal t a.1.owned)
  unfold Post
  cases recovery : Native.recoverAt root ref w with
  | error e t =>
    have exit := safe history d
    rw [Post, recovery] at exit
    exact NativeReadRelease.failedTo ops.cleanup exit
      (fun _ closed => .recovery closed failedTrace) (fun _ _ closed => .recovery closed failedTrace)
  | ok session t =>
    have installed actual (D : Durable image actual) := by
      have r := safe actual D
      rw [Post, recovery] at r
      exact r
    obtain ⟨valid, wal, attached⟩ := installed history d
    have reopened := prior.reopened (fun actual D => (installed actual D).1)
    apply publishOnline (attached.sessionAt valid) (ops.phase.refRead wal) (ops.phase.refSwap wal)
    intro entered online
    let result := readMany handle keys entered
    have read := readMany_run online binding (ops.phase.refRead wal) (ops.tables wal entered online.owned) Frame.refl reopened keys
    obtain ⟨trace, _, reached, released⟩ := read
    have stopped := trace.stop
    have finish (u) (closed : NativeReadRelease.Closed physical root lock ref image u) :
        Finished physical root image life events keys result.val u :=
      ⟨stopped, stopped.refines, lock, ref, wal, session, history, handle, entered, binding, online, rfl, reached, released, closed⟩
    have release := NativeReadRelease.onlineTo ops.cleanup reached finish (fun _ u h => Failure.cleanup (finish u h))
    unfold NativeScope.Callback Post
    change (match readMany handle keys entered with | ⟨xs, v⟩ => _)
    dsimp only [result] at release
    generalize eq : readMany handle keys entered = r at *
    cases r
    exact release

/-- The two-read callback used in the fault witness is the two-element
instance of the public client, including the world after the second get. -/
theorem readMany_two (handle : Native.Handle) (a b : UInt64) (w : W) :
    let r := readTwice handle a b w
    readMany handle [a, b] w = ⟨[r.val.1, r.val.2], r.state⟩ := rfl

/-- The first read's caught error leaves the observed trace unchanged. The
next result is recorded, and the public scope has finished cleanup. -/
theorem caught_then_got {finish : W} (entry : Entry physical path root image) (files : Files physical root image start)
    (heap : Heap) (runtime : ∀ lock ref, Runtime physical root lock ref image life heap)
    (prior : Execution.Run events none image)
    (returned : Native.withOpen path (fun h => (readMany h [first, second] : IO (List Reply))) start =
      .ok [.error e, .ok value] finish) :
    Execution.Run (((events ++ [.reopened]) ++ [.got second value]) ++ [.stop]) none image ∧
    ∃ lock ref, NativeReadRelease.Closed physical root lock ref image finish := by
  have observed := withOpen entry files heap runtime prior [first, second]
  rw [Post, returned] at observed
  obtain ⟨lock, ref, _, _, _, _, _, _, _, _, _, _, closed⟩ := observed.callback
  exact ⟨by simpa [eventsAfter, readEvents, readEvent] using observed.trace, lock, ref, closed⟩

end ExperimentalL0.WithOpenReads
