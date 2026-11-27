import Alvoki.Storage.Disk.Proofs.Append.AppendLockHandoff

namespace Alvoki.Storage.DiskSession

open System

/-- Interpret the complete single-write schedule. The phase and active-file
metadata reports are read-only. Publication uses the existing exact reached
write tail, keeping any effects of a failed callback. -/
def runSingleWrite {image : Type} (directory : DiskDirectory) (key : UInt64) (value : Option UInt64)
    (lookup : FilePath → Except IO.Error IO.FS.Metadata)
    (commit : Installed → WAL.Write → Nat → EStateM IO.Error image Unit) :
    EStateM DiskWriteError (Phase Installed × LockedFileState image) UInt64 :=
  withPreparedSingleWrite key value
    (fun state => match (state.1.installed : Except IO.Error Installed) with
      | .ok installed => .ok installed state
      | .error cause => .error (.rejected cause) state)
    DiskWriteError.rejected
    (fun prepared => match prepared with
      | some pair => pure pair
      | none => throw (.rejected (IO.userError "write sequence space exhausted")))
    (fun installed state => match (checkActiveSegmentWith directory installed lookup : Except IO.Error Unit) with
      | .ok () => .ok () state
      | .error cause => .error (.rejected cause) state)
    (fun installed event table bytes =>
      runPreparedWrite { installed with table, walBytes := bytes } event.sequence (commit installed event bytes))

section

variable {image : Type} {directory : DiskDirectory} {key : UInt64} {value : Option UInt64}
  {lookup : FilePath → Except IO.Error IO.FS.Metadata}
  {commit : Installed → WAL.Write → Nat → EStateM IO.Error image Unit}
  {before : LockedFileState image} {installed : Installed}

theorem runSingleWrite_rejectedPhase {phase : Phase Installed} {cause : IO.Error}
    (rejected : (phase.installed : Except IO.Error Installed) = .error cause) :
    runSingleWrite directory key value lookup commit (phase, before) = .error (.rejected cause) (phase, before) := by
  simp only [runSingleWrite, withPreparedSingleWrite, Bind.bind, EStateM.bind, rejected]

/-- Sequence exhaustion wins before the WAL count or metadata is checked. -/
theorem runSingleWrite_rejectedSequence (exhausted : prepareWrite installed.table key value = none) :
    runSingleWrite directory key value lookup commit (.ready installed, before) =
      .error (.rejected (IO.userError "write sequence space exhausted")) (.ready installed, before) := by
  simp [runSingleWrite, withPreparedSingleWrite, Phase.installed, Bind.bind, EStateM.bind,
    exhausted, Pure.pure, Except.pure, throw, throwThe, MonadExceptOf.throw, EStateM.throw]

theorem runSingleWrite_rejectedWalCount {event : WAL.Write} {table : PackedTable}
    (prepared : prepareWrite installed.table key value = some (event, table))
    (overflow : UInt64.size ≤ installed.walBytes + WAL.frameSize) :
    runSingleWrite directory key value lookup commit (.ready installed, before) =
      .error (.rejected (IO.userError "WAL byte count is too large")) (.ready installed, before) := by
  simp [runSingleWrite, withPreparedSingleWrite, Phase.installed, Bind.bind, EStateM.bind, prepared,
    Nat.not_lt.mpr overflow, Pure.pure, Except.pure, EStateM.pure, throw, throwThe, MonadExceptOf.throw, EStateM.throw]

/-- Forward the exact active-file error with the original ready state and
no append, phase assignment, cache mutation or lock handoff. -/
theorem runSingleWrite_rejectedActive {event : WAL.Write} {table : PackedTable} {cause : IO.Error}
    (prepared : prepareWrite installed.table key value = some (event, table))
    (fits : installed.walBytes + WAL.frameSize < UInt64.size)
    (rejected : (checkActiveSegmentWith directory installed lookup : Except IO.Error Unit) = .error cause) :
    runSingleWrite directory key value lookup commit (.ready installed, before) =
      .error (.rejected cause) (.ready installed, before) := by
  simp [runSingleWrite, withPreparedSingleWrite, Phase.installed, Bind.bind, EStateM.bind,
    prepared, fits, Pure.pure, Except.pure, EStateM.pure, rejected]

/-- Successful preflight reaches exactly the existing tail. Its success and
unknown-commit results therefore have the same reached file image and owner
as the whole single write. -/
theorem runSingleWrite_of_preflight {event : WAL.Write} {table : PackedTable}
    (prepared : prepareWrite installed.table key value = some (event, table))
    (fits : installed.walBytes + WAL.frameSize < UInt64.size)
    (active : (checkActiveSegmentWith directory installed lookup : Except IO.Error Unit) = .ok ()) :
    runSingleWrite directory key value lookup commit (.ready installed, before) =
      runPreparedWrite { installed with table, walBytes := installed.walBytes + WAL.frameSize } event.sequence
        (commit installed event (installed.walBytes + WAL.frameSize)) (.ready installed, before) := by
  simp [runSingleWrite, withPreparedSingleWrite, Phase.installed, Bind.bind, EStateM.bind,
    prepared, fits, Pure.pure, Except.pure, EStateM.pure, active]

end

end Alvoki.Storage.DiskSession
