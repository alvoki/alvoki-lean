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

def choose (image : Selected) (view : WalView) : Selected := {image with view}

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

end ExperimentalL0.PendingReadScope
