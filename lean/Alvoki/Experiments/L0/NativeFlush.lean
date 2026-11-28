import Alvoki.Experiments.L0.NativeWrite
import Alvoki.Experiments.L0.NativeFlushRestart

namespace ExperimentalL0.NativeFlush

open NativeScope (W Wal Ref)
open NativeWrite (checked_bind checked_pure checked_throw)
open NativeFlushRestart (proposal published)

abbrev createTable (root : System.FilePath) (rows : Rows) : IO UInt64 :=
  Native.checked (Native.createTable (root / "tables") rows)

abbrev publish (root : System.FilePath) (version : L0Manifest.Version) : IO Unit :=
  Native.checked ((NativeManifest.backend (root / "manifest")).publish version)

/-- The checked native operation preserves both typed guard errors and IO errors.
The empty memtable completes before the first WAL borrow. -/
theorem atRoot (root : System.FilePath) (ref : Ref) (s : Session) :
    Native.checked (flush (Native.callbackComponents root ref) s) =
      (do
        if s.mem.isEmpty then return s
        let view ← Native.checked (Native.callbackComponents root ref).scan
        unless view.tail < UInt64.size do throw (IO.userError "absolute WAL position exhausted")
        let id ← createTable root s.mem.toList
        let version : L0Manifest.Version := ⟨id :: s.version.tables, view.tail.toUInt64⟩
        publish root version
        return ⟨version, ∅⟩ : IO Session) := by
  unfold flush flushTableWith
  split
  · rfl
  · rw [checked_bind]
    apply congrArg (Bind.bind _)
    funext view
    by_cases fits : view.tail < UInt64.size <;>
      simp only [fits, ↓reduceIte, checked_bind, checked_throw, checked_pure] <;> rfl

open NativeRead (Online SessionAt Footprint)
open WalRecoverySlice.Segmented.Native (PhaseMemory)

def store (root : System.FilePath) (image : Selected) (s : Session) : IO Session :=
  flushTableWith (createTable root) (publish root) s image.view.tail

theorem store_eq (root : System.FilePath) (image : Selected) (s : Session) :
    store root image s = (do
      let id ← createTable root s.mem.toList
      let version := proposal image s id
      publish root version
      return ⟨version, ∅⟩) := rfl

def hidden (ref : Ref) (wal : Wal) (start : W) : W :=
  ((ref.swap (.updating wal) : BaseIO _) ((ref.get : BaseIO _) start).state).state

def origin (ref : Ref) (wal : Wal) (s : Session) (start : W) : W :=
  if s.mem.isEmpty then hidden ref wal start else NativeWrite.guardWorld ref wal start

/-- Primitive receipts fix the scan world independently of the return value of
the storage action. The empty branch never borrows the WAL. -/
structure Issued (root : System.FilePath) (ref : Ref) (wal : Wal) (s : Session) (image : Selected) (start : W) : Prop where
  read : (ref.get : IO (Lifecycle.Phase Wal)) start =
    .ok (.online wal s) ((ref.get : BaseIO _) start).state
  swap : (ref.swap (.updating wal) : IO _) ((ref.get : BaseIO _) start).state =
    .ok (.online wal s) (hidden ref wal start)
  scan : s.mem.isEmpty ≠ true →
    let w := hidden ref wal start
    (ref.get : IO (Lifecycle.Phase Wal)) w = .ok (.updating wal) ((ref.get : BaseIO _) w).state ∧
      Native.checked (Native.callbackComponents root ref).scan w =
        .ok image.view (NativeWrite.guardWorld ref wal start)

/-- Reserve the actual online phase. Only a nonempty memtable reaches
the WAL scan. Its exact rows and the observed tail determine the proposal. -/
theorem dispatchAt {physical : W → Footprint inode}
    (online : Online physical root lock ref wal s image history start)
    (binding : Native.Handle.AtRoot handle root ref)
    (heap : PhaseMemory) (cached : NativeRecoverAt.Cached heap physical root lock ref)
    (phase : NativeRecoverAt.PhasePrimitives physical root lock ref image)
    (scan : ∀ w, SessionAt physical root lock ref wal s image history w (.updating wal) →
      NativeRecoverAt.ScanPrimitives physical root wal image.tables w) :
    let t := origin ref wal s start
    Issued root ref wal s image start ∧ SessionAt physical root lock ref wal s image history t (.updating wal) ∧
      Native.flush handle start = NativeWrite.afterWrite ref
        (if s.mem.isEmpty then .ok s t
         else if image.view.tail < UInt64.size then store root image s t
         else .error (IO.userError "absolute WAL position exhausted") t) := by
  obtain ⟨entered, hiddenAt, read, swap, updating⟩ := NativeWrite.reserve online phase
  have run := NativeWrite.update_started ref (fun s => Native.checked (flush (Native.callbackComponents root ref) s)) read swap
  rw [← Native.flush_atRoot binding, atRoot] at run
  have r := read
  have u := swap
  rw [NativeScope.read_io] at r
  rw [NativeScope.swap_io] at u
  have eqEntered := (EST.Out.ok.inj r).2
  have eqHidden : hidden ref wal start = hiddenAt := by
    unfold hidden
    rw [eqEntered, (EST.Out.ok.inj u).2]
  have swapRead : (ref.swap (.updating wal) : IO _) ((ref.get : BaseIO _) start).state =
      .ok (.online wal s) (hidden ref wal start) := by rw [eqEntered, eqHidden]; exact swap
  dsimp only
  by_cases empty : s.mem.isEmpty = true
  · simp only [origin, empty, ↓reduceIte, eqHidden]
    exact ⟨⟨by rw [eqEntered]; exact read, swapRead, fun nonempty => False.elim (nonempty empty)⟩,
      updating, by simpa only [empty, ↓reduceIte, Pure.pure, instMonadEIO._aux_5, EST.pure] using run⟩
  obtain ⟨borrowed, scanned, kept⟩ := NativeWrite.scanAt updating heap cached phase scan
  have eqGuard : NativeWrite.guardWorld ref wal start =
      WalRecoverySlice.Segmented.Native.scanWorld wal ((ref.get : BaseIO _) hiddenAt).state := by
    change _ = WalRecoverySlice.Segmented.Native.scanWorld wal ((ref.get : BaseIO _) hiddenAt).state
    change WalRecoverySlice.Segmented.Native.scanWorld wal ((ref.get : BaseIO _) (hidden ref wal start)).state = _
    rw [eqHidden]
  simp only [origin, empty, eqGuard]
  refine ⟨⟨by rw [eqEntered]; exact read, swapRead, fun _ => by rw [eqHidden, eqGuard]; exact ⟨borrowed,scanned⟩⟩,
    kept, run.trans ?_⟩
  apply congrArg (NativeWrite.afterWrite ref)
  by_cases fit : image.view.tail < UInt64.size <;>
    simp [empty, fit, Bind.bind, instMonadEIO._aux_13, EST.bind, scanned, store, flushTableWith, proposal] <;> rfl

/-- Reserve the actual online phase. Only a nonempty memtable reaches
the WAL scan. Its exact rows and the observed tail determine the proposal. -/
theorem dispatch {physical : W → Footprint inode}
    (online : Online physical root lock ref wal s image history start)
    (binding : Native.Handle.AtRoot handle root ref)
    (heap : PhaseMemory) (cached : NativeRecoverAt.Cached heap physical root lock ref)
    (phase : NativeRecoverAt.PhasePrimitives physical root lock ref image)
    (scan : ∀ w, SessionAt physical root lock ref wal s image history w (.updating wal) →
      NativeRecoverAt.ScanPrimitives physical root wal image.tables w) :
    ∃ t, SessionAt physical root lock ref wal s image history t (.updating wal) ∧
      Native.flush handle start = NativeWrite.afterWrite ref
        (if s.mem.isEmpty then .ok s t
         else if image.view.tail < UInt64.size then store root image s t
         else .error (IO.userError "absolute WAL position exhausted") t) := by
  obtain ⟨_, reached, ran⟩ := dispatchAt online binding heap cached phase scan
  exact ⟨_, reached, ran⟩

end ExperimentalL0.NativeFlush
