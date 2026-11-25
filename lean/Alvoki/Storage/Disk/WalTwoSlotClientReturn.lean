import Alvoki.Storage.Disk.WalTwoSlot
import Alvoki.Storage.Disk.DiskTable
import Alvoki.Storage.Disk.DiskSession

namespace Alvoki.WAL.TwoSlot

open Alvoki.Storage

private def setPhase {α σ : Type} (phase : DiskSession.Phase α) :
    EStateM ε (DiskSession.Phase α × σ) Unit :=
  fun (_, files) => .ok () (phase, files)

private def commitReports {α σ : Type} (publish : EStateM IO.Error σ Unit) :
    EStateM DiskWriteError (DiskSession.Phase α × σ) Unit :=
  fun (phase, files) =>
    match publish files with
    | .ok _ after => .ok () (phase, after)
    | .error cause after => .error (.commitUnknown cause) (phase, after)

/-- Interpret the returned branch of the actual session publication wrapper
over the exact ordered marker effect reports. A publication error retains
the reached files and leaves no ready table or acknowledged sequence. -/
theorem prepared_write_reports {α σ : Type}
    (next : α) (sequence : UInt64) (prior : DiskSession.Phase α) (files : σ)
    (append syncWal writeSlot syncSlot install : EStateM IO.Error σ Unit) :
    DiskSession.publishPreparedWrite next sequence setPhase
      (commitReports (publish append syncWal writeSlot syncSlot install)) (prior, files) =
      match publish append syncWal writeSlot syncSlot install files with
      | .ok _ after => .ok sequence (.ready next, after)
      | .error cause after => .error (.commitUnknown cause) (.poisoned, after) := by
  cases result : publish append syncWal writeSlot syncSlot install files <;>
  simp only [DiskSession.publishPreparedWrite, DiskSession.publishPrepared, setPhase,
    commitReports, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure, result]

end Alvoki.WAL.TwoSlot
