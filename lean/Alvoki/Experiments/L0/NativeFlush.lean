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
  unfold flush
  split
  · rfl
  · rw [checked_bind]
    apply congrArg (Bind.bind _)
    funext view
    by_cases fits : view.tail < UInt64.size <;>
      simp only [fits, ↓reduceIte, checked_bind, checked_throw, checked_pure] <;> rfl

open NativeRead (Online SessionAt Footprint)
open WalRecoverySlice.Segmented.Native (PhaseMemory)

def store (root : System.FilePath) (image : Selected) (s : Session) : IO Session := do
  let id ← createTable root s.mem.toList
  let next := proposal image s id
  publish root next
  return ⟨next, ∅⟩

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
  obtain ⟨_, hidden, read, swap, updating⟩ := NativeWrite.reserve online phase
  have run := NativeWrite.update_started ref (fun s => Native.checked (flush (Native.callbackComponents root ref) s)) read swap
  rw [← Native.flush_atRoot binding, atRoot] at run
  by_cases empty : s.mem.isEmpty = true
  · exact ⟨hidden, updating, by simpa only [empty, ↓reduceIte, Pure.pure, instMonadEIO._aux_5, EST.pure] using run⟩
  obtain ⟨t, scanned, kept⟩ := NativeWrite.scan updating heap cached phase scan
  refine ⟨t, kept, run.trans ?_⟩
  apply congrArg (NativeWrite.afterWrite ref)
  by_cases fit : image.view.tail < UInt64.size <;>
    simp [empty, fit, Bind.bind, instMonadEIO._aux_13, EST.bind, scanned, store, proposal] <;> rfl

end ExperimentalL0.NativeFlush
