import Alvoki.Experiments.WAL.Proofs.NativePost
import Alvoki.Experiments.L0.Trace
import Alvoki.Experiments.L0.Native

namespace ExperimentalL0.NativeRecovery
open Lifecycle

open Alvoki.NativePost

/-- Open failures occur with an opening L0 phase. As soon as open succeeds,
the exact Wal handle is attached before its first scan can fail. -/
theorem reopenWal {Wal : Type} (cell : Cell F Wal) (invalid : String)
    (openWal : F Wal) (scan : Wal → F α)
    {canOpen failed : W → Prop} {acquired attached : Wal → W → Prop}
    (read : Returns cell.read start (fun phase w => phase = .opening ∧ canOpen w) failed)
    (openStep : ∀ w, canOpen w → Returns openWal w acquired failed)
    (swap : ∀ h w, acquired h w →
      Returns (cell.swap (.recovering h)) w (fun _ t => attached h t) failed)
    (scanStep : ∀ h w, attached h w → Returns (scan h) w done failed) :
    Returns (cell.reopenWal invalid openWal scan) start done failed := by
  unfold Cell.reopenWal
  apply read.bind
  intro phase w pre
  obtain ⟨rfl, opening⟩ := pre
  apply (openStep w opening).bind
  intro h u held
  apply (swap h u held).bind
  intro _ t owns
  exact scanStep h t owns

/-- The concrete L0 check reads no mutation callbacks. The selected manifest
and returned WAL view determine the replay suffix. Failed checks preserve
the reached recovery custody for the outer cleanup. -/
theorem recover {manifestReady attached failed : W → Prop} (ops : Components F) (selected : Selected)
    (d : Durable selected history)
    (manifest : Returns ops.manifest.reopen start
      (fun version t => version = selected.version ∧ manifestReady t) failed)
    (wal : ∀ w, manifestReady w → Returns ops.reopenWal w
      (fun view t => view = selected.view ∧ attached t) failed)
    (tables : ∀ w, attached w → Returns (checkTables ops.tables selected.version.tables) w
      (fun _ t => attached t) failed) :
    Returns (ExperimentalL0.recover ops) start
      (fun session t => Installed session selected history ∧ attached t) failed := by
  unfold ExperimentalL0.recover
  apply manifest.bind
  intro version w ready
  obtain ⟨rfl, ready⟩ := ready
  apply (wal w ready).bind
  intro view t valid
  obtain ⟨rfl, valid⟩ := valid
  simp only [d.bounds, and_self, ite_true, d.replay_pending]
  apply (tables t valid).bind
  intro _ u finish
  exact ⟨⟨d, rfl, rfl⟩, finish⟩

end ExperimentalL0.NativeRecovery
