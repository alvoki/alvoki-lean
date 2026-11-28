import Alvoki.Experiments.L0.NativeRecoverSelected
import Alvoki.Experiments.L0.WithOpenReads
import Alvoki.Experiments.L0.AppendRecovery

namespace ExperimentalL0.PendingReadScope
open System Lifecycle NativeRead NativeScope NativeReadRelease
open NativeReadScope (RestartFiles RestartEntry Grant)
open WalRecoverySlice.Segmented (PermittedView)
abbrev WalView := WalRecoverySlice.Segmented.Contract.View
abbrev W := NativeScope.W
abbrev Ref := NativeScope.Ref
abbrev Wal := NativeScope.Wal
abbrev Heap := WithOpenReads.Heap

abbrev choose := NativeRecoverAt.selectedAt

def Admitted (events : List Event) (image : Selected) (req : Option WalRecoverySlice.Segmented.Contract.Request) :=
  ∀ view, PermittedView image.view req view → Execution.Run events none (choose image view)

theorem Admitted.failed (prior : Admitted events image req) : Admitted (events ++ [.openFailed]) image req :=
  fun view h => (prior view h).openFailed (fun _ d => ⟨d⟩)

/-- The public uncertain-write event carries the very mutation encoded in
the pending WAL request; failed opens leave the same alternatives available. -/
theorem afterWrite (run : Execution.Run events (some session) image) (change : Change) :
    Admitted ((events ++ [.writeUncertain change]) ++ [.stop]) image (some (.append (encode change))) := by
  intro view allowed
  have trace := run.uncertainRetries 0 allowed
  simp only [List.replicate_zero, List.append_nil] at trace
  exact trace.stop

/-- When the native append returned success before acknowledgement was
lost, the established disk has a single survivor although the client
observes the same uncertain-write event. -/
theorem afterLostAck (run : Execution.Run events (some session) image) (change : Change) :
    Admitted ((events ++ [.writeUncertain change]) ++ [.stop]) (image.append (encode change)) none := by
  intro view allowed
  have same : view = (image.append (encode change)).view := allowed.elim id (by simp)
  subst view
  exact (run.uncertainAtView (Or.inr rfl)).stop

private theorem installed_eq (valid : Installed session image history) : session = image.replaySession := by
  obtain ⟨d, version, mem⟩ := valid
  cases session
  simp_all [Selected.replaySession, d.replay_pending]

private theorem historyAt (prior : Execution.Run events none image) : ∃ h, Nonempty (Durable image h) := by
  obtain ⟨state, _, represented⟩ := prior.refines
  cases state with
  | ready => obtain ⟨_, _, impossible, _⟩ := represented; cases impossible
  | offline =>
    obtain ⟨_, h, _, d⟩ := represented
    exact ⟨h, d⟩

/-- An early failure swaps the fresh opening cell offline without an attached
WAL. The root descriptor remains owned until the single outer unlock. -/
structure Stopped (req : Option WalRecoverySlice.Segmented.Contract.Request)
    (physical : W → Footprint inode) (root : FilePath) (ref : Ref) (image : Selected) (w : W) : Prop where
  files : RestartFiles req physical root image w
  refBound : (physical w).phaseRef = some ref
  offline : (physical w).phase = .offline

structure EmptyRelease (req : Option WalRecoverySlice.Segmented.Contract.Request)
    (physical : W → Footprint inode) (root : FilePath) (lock : IO.FS.Handle) (ref : Ref)
    (image : Selected) : Prop where
  swap : ∀ w, Owned (physical w) root lock ref → (physical w).phase = .opening →
    RestartFiles req physical root image w →
    let taken := (ref.swap .offline : BaseIO _) w
    taken.val = .opening ∧ Stopped req physical root ref image taken.state ∧
      (physical taken.state).rootLock = some (root, lock)
  unlock : ∀ u, Grant root lock ref → Stopped req physical root ref image u →
    (physical u).rootLock = some (root, lock) →
    Post lock.unlock u (fun _ t => Stopped req physical root ref image t ∧ (physical t).rootLock = none)
      (fun _ t => Stopped req physical root ref image t)

structure ClosedBeforeSelection (req : Option WalRecoverySlice.Segmented.Contract.Request)
    (physical : W → Footprint inode) (root : FilePath) (lock : IO.FS.Handle) (ref : Ref)
    (image : Selected) (t : W) : Prop extends Stopped req physical root ref image t where
  report : ∃ u, Grant root lock ref ∧ (physical u).rootLock = some (root, lock) ∧
    ((lock.unlock u = .ok () t ∧ (physical t).rootLock = none) ∨ ∃ e, lock.unlock u = .error e t)

theorem EmptyRelease.release (laws : EmptyRelease req physical root lock ref image)
    (grant : Grant root lock ref) (owned : Owned (physical w) root lock ref)
    (phase : (physical w).phase = .opening) (files : RestartFiles req physical root image w)
    (finish : ∀ t, ClosedBeforeSelection req physical root lock ref image t → result t) :
    Release ref lock w result (fun _ t => result t) := by
  obtain ⟨opening, off, held⟩ := laws.swap w owned phase files
  unfold Release
  dsimp only
  rw [opening]
  let u := ((ref.swap .offline : BaseIO _) w).state
  change Post lock.unlock u (fun _ t => result t) (fun _ t => result t)
  have returned := laws.unlock u grant off held
  unfold Post at *
  cases ran : lock.unlock u with
  | ok val t =>
    cases val
    rw [ran] at returned
    exact finish t ⟨returned.1, u, grant, held, .inl ⟨ran, returned.2⟩⟩
  | error e t =>
    rw [ran] at returned
    exact finish t ⟨returned, u, grant, held, .inr ⟨e, ran⟩⟩

/-- The first public restart can fail before granting its root, return
before WAL selection, or select a view and then report a validation or cleanup error. -/
inductive Failure (req : Option WalRecoverySlice.Segmented.Contract.Request) (physical : W → Footprint inode)
    (root : FilePath) (image : Selected) (life : Lifetime) (events : List Event)
    (call : RootCall) (rootLife : RootLifetime) (err : IO.Error) (w : W) : Prop where
  | before : call.Released rootLife → RestartFiles req physical root image w →
      Admitted (events ++ [.openFailed]) image req → Failure req physical root image life events call rootLife err w
  | early : call.Released rootLife → ClosedBeforeSelection req physical root lock ref image w →
      Native.recoverAt root ref start = .error err reached →
      (∀ view, NativeRecoverAt.NoChecks root ref (choose image view) start) →
      Admitted (events ++ [.openFailed]) image req → Failure req physical root image life events call rootLife err w
  | selected (view : WalView) : PermittedView image.view req view →
      WithOpenReads.Failure physical root (choose image view) life events call rootLife err w →
      Failure req physical root image life events call rootLife err w

def Finished (req : Option WalRecoverySlice.Segmented.Contract.Request) (physical : W → Footprint inode)
    (root : FilePath) (image : Selected) (life : Lifetime) (events : List Event)
    (call : RootCall) (rootLife : RootLifetime) (replies : List Reply) (w : W) : Prop :=
  ∃ view, PermittedView image.view req view ∧
    WithOpenReads.Finished physical root (choose image view) life events call rootLife replies w


structure Runtime (req : Option WalRecoverySlice.Segmented.Contract.Request) (physical : W → Footprint inode)
    (root : FilePath) (lock : IO.FS.Handle) (ref : Ref) (image : Selected)
    (life : Lifetime) (heap : Heap) where
  manifest : ∀ start, NativeRecoverAt.Opening physical root lock ref image start req →
    NativeManifest.Primitives (root / "manifest") (NativeRecoverAt.ManifestFrame physical root image.tables start)
      (fun w => (physical w).manifest)
  wal : WalRecoverySlice.Segmented.Native.LocalOpenIO heap (root / "wal") (fun w => (physical w).disk)
    image.view (NativeRecoverAt.Held physical root lock ref image .opening) req
  cached : NativeRecoverAt.Cached heap physical root lock ref
  phase : NativeRecoverAt.PhasePrimitives physical root lock ref image
  scan : ∀ view wal w, PermittedView image.view req view →
    NativeRecoverAt.Attached physical root lock ref (choose image view) wal w →
    NativeRecoverAt.ScanPrimitives physical root wal image.tables w
  tables : ∀ wal w, Owned (physical w) root lock ref →
    Primitives (tableNamespace physical root) life (Frame physical root wal image.tables w)
  empty : EmptyRelease req physical root lock ref image
  attached : ∀ view, PermittedView image.view req view →
    NativeReadRelease.Laws heap physical root lock ref (choose image view)

/-- The first public open after an uncertain append chooses its own view.
Only a successful WAL acquisition enables publication and the read callback. -/
theorem withOpen (entry : RestartEntry req physical path root image) (files : RestartFiles req physical root image start)
    (heap : Heap) (runtime : ∀ lock ref, Runtime req physical root lock ref image life heap)
    (prior : Admitted events image req) (keys : List UInt64) (rootLife : RootLifetime) :
    Post (Native.withOpen path (fun h => (readMany h keys : IO (List Reply)))) start
      (Finished req physical root image life events ⟨path, keys, start⟩ rootLife)
      (Failure req physical root image life events ⟨path, keys, start⟩ rootLife) := by
  classical
  let call : RootCall := ⟨path, keys, start⟩
  let hist (v : WalView) := if h : PermittedView image.view req v then (historyAt (prior v h)).choose else []
  have durable (v : WalView) (h : PermittedView image.view req v) :
      Durable (choose image v) (hist v) := by
    simp only [hist, h, dite_true]
    exact Classical.choice (historyAt (prior v h)).choose_spec
  apply entry.withOpen files _ (fun _ _ retry => .before (call.released rootLife) retry prior.failed)
  intro lock ref w grant owned phase persistent handle binding
  let ops := runtime lock ref
  let opening : NativeRecoverAt.Opening physical root lock ref image w req :=
    ⟨owned, phase, persistent.catalog, persistent.disk⟩
  have post := NativeRecoverAt.recoverAt_selected_checks durable opening persistent.manifest
    (ops.manifest w opening) heap ops.cached ops.wal.toOpenIO ops.phase ops.scan
    (fun _ wal t _ a => ops.tables wal t a.1.owned)
  unfold Post
  cases ran : Native.recoverAt root ref w with
  | error e t =>
    rw [Post, ran] at post
    rcases post with ⟨⟨early, manifest⟩, noChecks⟩ | ⟨v, choice, ⟨wal, attached⟩, receipt⟩
    · exact ops.empty.release grant early.owned early.phase ⟨early.catalog, manifest, early.disk⟩
        fun _ closed => .early (call.released rootLife) closed ran noChecks prior.failed
    · have failure : NativeRecoverAt.Failed physical root lock ref (choose image v) t := .inr ⟨wal, attached⟩
      have done u (closed : Closed physical root lock ref (choose image v) u) :
          Failure req physical root image life events call rootLife e u :=
        .selected v choice (.recovery (call.released rootLife) closed ran (.inr receipt) (prior.failed v choice))
      exact NativeReadRelease.failedTo (ops.attached v choice) grant failure done (fun _ => done)
  | ok session t =>
    rw [Post, ran] at post
    obtain ⟨v, choice, installed, ⟨wal, attached⟩, checked⟩ := post
    have replay := (prior v choice).reopenSelected
    have identity : session = (choose image v).replaySession := installed_eq installed
    rw [← identity] at replay
    exact WithOpenReads.finishRecovery call rootLife grant binding ran installed attached checked
      (ops.phase.refRead wal) (ops.phase.refSwap wal) (ops.tables wal) (ops.attached v choice) replay
      (fun _ _ finished => ⟨v, choice, finished⟩) (fun _ _ {_} finished => .selected v choice (.cleanup finished))


private theorem Failure.restartSelected (f : WithOpenReads.Failure physical root image life events call rootLife err w) :
    NativeReadScope.Files physical root image w ∧ ∃ observed,
      (observed = events ++ [.openFailed] ∨ ∃ replies, observed = WithOpenReads.eventsAfter events call.keys replies) ∧
      Execution.Run observed none image := by
  cases f with
  | before _ files trace => exact ⟨files, _, .inl rfl, trace⟩
  | recovery _ closed _ _ trace => exact ⟨closed.files, _, .inl rfl, trace⟩
  | cleanup finished =>
    obtain ⟨_, _, closed, _⟩ := finished.callback
    exact ⟨closed.files, _, .inr ⟨_, rfl⟩, finished.trace⟩

def PinnedPost (physical : W → Footprint inode) (root : FilePath) (image : Selected) (life : Lifetime)
    (events : List Event) (call : RootCall) (rootLife : RootLifetime) :=
  Post call.run call.start (WithOpenReads.Finished physical root image life events call rootLife)
    (WithOpenReads.Failure physical root image life events call rootLife)

/-- On an earlier reported failure the next public open either consumes the
same unresolved request or the survivor pinned by the first WAL acquisition. -/
inductive Retry (req : Option WalRecoverySlice.Segmented.Contract.Request) (physical : W → Footprint inode)
    (root : FilePath) (image : Selected) (life : Lifetime) (events : List Event)
    (first second : RootCall) (rootLife : RootLifetime) (err : IO.Error) : Prop where
  | unresolved : RestartFiles req physical root image second.start →
      Admitted (events ++ [.openFailed]) image req →
      Post second.run second.start (Finished req physical root image life (events ++ [.openFailed]) second rootLife)
        (Failure req physical root image life (events ++ [.openFailed]) second rootLife) →
      Retry req physical root image life events first second rootLife err
  | pinned (view : WalView) (selected : PermittedView image.view req view) :
      WithOpenReads.Failure physical root (choose image view) life events first rootLife err second.start →
      NativeReadScope.Files physical root (choose image view) second.start →
      (observed = events ++ [.openFailed] ∨ ∃ replies, observed = WithOpenReads.eventsAfter events first.keys replies) →
      Execution.Run observed none (choose image view) →
      PinnedPost physical root (choose image view) life observed second rootLife →
      Retry req physical root image life events first second rootLife err

/-- Postcondition for two actual opens. Every second call starts at the
world returned by the first, including after an unsuccessful first open. -/
def TwoReads (req : Option WalRecoverySlice.Segmented.Contract.Request) (physical : W → Footprint inode)
    (path root : FilePath) (image : Selected) (life : Lifetime) (events : List Event) (start : W)
    (firstKeys secondKeys : List UInt64) (rootLife : RootLifetime) : Prop :=
    let first : RootCall := ⟨path, firstKeys, start⟩
    Post first.run first.start
      (fun replies w => ∃ view, PermittedView image.view req view ∧
        WithOpenReads.Finished physical root (choose image view) life events first rootLife replies w ∧
        PinnedPost physical root (choose image view) life (WithOpenReads.eventsAfter events firstKeys replies)
          ⟨path, secondKeys, w⟩ rootLife)
      (fun e w => Failure req physical root image life events first rootLife e w ∧
        Retry req physical root image life events first ⟨path, secondKeys, w⟩ rootLife e)

/-- The two public calls share the actual return world of the first call,
including after a validation failure or a cleanup error. Once a survivor
has been selected, the second public call uses the ordinary closed-file
invariant with the same WAL view. -/
theorem twice (entry : RestartEntry req physical path root image)
    (files : RestartFiles req physical root image start)
    (heap : Heap) (runtime : ∀ lock ref, Runtime req physical root lock ref image life heap)
    (pinnedEntry : ∀ v, PermittedView image.view req v → NativeReadScope.Entry physical path root (choose image v))
    (pinnedRuntime : ∀ v, PermittedView image.view req v → ∀ lock ref,
      WithOpenReads.Runtime physical root lock ref (choose image v) life heap)
    (prior : Admitted events image req) (firstKeys secondKeys : List UInt64) (rootLife : RootLifetime) :
    TwoReads req physical path root image life events start firstKeys secondKeys rootLife := by
  unfold TwoReads
  intro first
  have fixed v (choice : PermittedView image.view req v) w ev
      (disk : NativeReadScope.Files physical root (choose image v) w)
      (trace : Execution.Run ev none (choose image v)) :
      PinnedPost physical root (choose image v) life ev ⟨path, secondKeys, w⟩ rootLife :=
    WithOpenReads.withOpen (pinnedEntry v choice) disk heap (pinnedRuntime v choice) trace secondKeys rootLife
  apply (withOpen entry files heap runtime prior firstKeys rootLife).weaken
  · rintro replies w ⟨v, choice, finish⟩
    obtain ⟨_, _, closed, _⟩ := finish.callback
    exact ⟨v, choice, finish, fixed v choice w _ closed.files finish.trace⟩
  · intro e w failure
    refine ⟨failure, ?_⟩
    have retry (disk : RestartFiles req physical root image w) (trace : Admitted (events ++ [.openFailed]) image req) :
        Retry req physical root image life events first ⟨path, secondKeys, w⟩ rootLife e := by
      apply Retry.unresolved (events := events) disk trace
      unfold RootCall.run
      exact withOpen (events := events ++ [Event.openFailed]) entry disk heap runtime trace secondKeys rootLife
    cases failure with
    | before _ disk trace => exact retry disk trace
    | early _ closed _ _ trace => exact retry closed.files trace
    | selected v choice f =>
      obtain ⟨disk, ev, observed, trace⟩ := Failure.restartSelected f
      exact .pinned v choice f disk observed trace (fixed v choice w ev disk trace)

end ExperimentalL0.PendingReadScope
