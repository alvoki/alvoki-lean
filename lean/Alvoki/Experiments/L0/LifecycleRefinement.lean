import Alvoki.Experiments.L0.Lifecycle
import Alvoki.Experiments.L0.NativeBridge
import Alvoki.Experiments.L0.ScheduleSteps

namespace ExperimentalL0.Lifecycle
open Proof

variable {W S : Type}
variable {ops : Components (StorageM (Phase W × S))}
variable {selected : S → Selected}
variable {fileBytes : S → UInt64 → Option ByteArray}

/-- One reached recovery result justifies both the actual scope's publication
of the recovered session and the client trace step. Phase writes leave the
storage carrier untouched. -/
theorem recovery_online
    (prior : Execution.Run events none (selected before))
    (evidence : NativeBridge.CallbackEvidence ops (selected ∘ Prod.snd) (fileBytes ∘ Prod.snd))
    (ran : recover ops (.opening, before) = .ok session (.recovering handle, after))
    (use : StorageM (Phase W × S) α)
    (invalid : String) (closeWal : W → StorageM (Phase W × S) Unit) (unlock : StorageM (Phase W × S) Unit) :
    Execution.Run (events ++ [.reopened]) (some session) (selected after) ∧
      Cell.withSession stateCell invalid (recover ops) use closeWal unlock (.opening, before) =
        finish (ε := String) use (finish (ε := String) (Cell.close stateCell closeWal) unlock)
          (.online handle session, after) :=
  ⟨Execution.Run.recoverOk (s := (.opening, before)) prior evidence.laws ran,
    successful_recovery_publishes (recover ops) use invalid closeWal unlock handle session
      before after ran⟩

/-- Failed recovery records only an offline client step. Phase cleanup
detaches the handle even when closing the WAL or releasing the lock fails. -/
theorem recovery_offline
    (prior : Execution.Run events none (selected before))
    (evidence : NativeBridge.CallbackEvidence ops (selected ∘ Prod.snd) (fileBytes ∘ Prod.snd))
    (ran : recover ops (.opening, before) = .error error after)
    (use : StorageM (Phase W × S) α)
    (invalid : String) (closeWal : W → StorageM (Phase W × S) Unit) (unlock : StorageM (Phase W × S) Unit)
    (closeFrame : ∀ handle storage, reached (closeWal handle (.offline, storage)) = (.offline, storage))
    (unlockFrame : ∀ storage, reached (unlock (.offline, storage)) = (.offline, storage)) :
    Execution.Run (events ++ [.openFailed]) none (selected after.2) ∧
      Cell.withSession stateCell invalid (recover ops) use closeWal unlock (.opening, before) =
        .error error (.offline, after.2) :=
  ⟨Execution.Run.recoverError (s := (.opening, before)) prior evidence.laws ran,
    failed_recovery_closes (recover ops) use invalid error closeWal unlock before after ran
      closeFrame unlockFrame⟩

/-- Put and delete use this same write schedule. Publication changes only
phase custody, as does hiding the previous session before the call. -/
theorem write_online
    (prior : Execution.Run events (some old) (selected before))
    (evidence : NativeBridge.CallbackEvidence ops (selected ∘ Prod.snd) (fileBytes ∘ Prod.snd))
    (change : Change)
    (ran : write ops old change (.updating handle, before) = .ok next (.updating handle, after))
    (invalid : String) (closeWal : W → StorageM (Phase W × S) Unit) :
    Execution.Run (events ++ [.written change]) (some next) (selected after) ∧
      Cell.update stateCell invalid (fun session => write ops session change) closeWal
        (.online handle old, before) = .ok () (.online handle next, after) :=
  ⟨Execution.Run.writeOk (s := (.updating handle, before)) prior evidence.laws ran,
    update_success _ invalid closeWal handle old next before after ran⟩

theorem write_offline
    (prior : Execution.Run events (some old) (selected before))
    (evidence : NativeBridge.CallbackEvidence ops (selected ∘ Prod.snd) (fileBytes ∘ Prod.snd))
    (change : Change)
    (ran : write ops old change (.updating handle, before) = .error error after)
    (invalid : String) (closeWal : W → StorageM (Phase W × S) Unit)
    (closeFrame : ∀ handle storage, reached (closeWal handle (.offline, storage)) = (.offline, storage)) :
    Execution.Run (events ++ [.writeUncertain change]) none (selected after.2) ∧
      Cell.update stateCell invalid (fun session => write ops session change) closeWal
        (.online handle old, before) = .error error (.offline, after.2) :=
  ⟨Execution.Run.writeInterrupted (s := (.updating handle, before)) prior evidence.laws ran,
    update_error _ invalid error closeWal handle old before after ran closeFrame⟩

theorem flush_online
    (prior : Execution.Run events (some old) (selected before))
    (evidence : NativeBridge.CallbackEvidence ops (selected ∘ Prod.snd) (fileBytes ∘ Prod.snd))
    (ran : flush ops old (.updating handle, before) = .ok next (.updating handle, after))
    (invalid : String) (closeWal : W → StorageM (Phase W × S) Unit) :
    Execution.Run (events ++ [.flushed]) (some next) (selected after) ∧
      Cell.update stateCell invalid (flush ops) closeWal
        (.online handle old, before) = .ok () (.online handle next, after) :=
  ⟨Execution.Run.flushOk (s := (.updating handle, before)) prior evidence.laws ran,
    update_success _ invalid closeWal handle old next before after ran⟩

theorem flush_offline
    (prior : Execution.Run events (some old) (selected before))
    (evidence : NativeBridge.CallbackEvidence ops (selected ∘ Prod.snd) (fileBytes ∘ Prod.snd))
    (ran : flush ops old (.updating handle, before) = .error error after)
    (invalid : String) (closeWal : W → StorageM (Phase W × S) Unit)
    (closeFrame : ∀ handle storage, reached (closeWal handle (.offline, storage)) = (.offline, storage)) :
    Execution.Run (events ++ [.flushUncertain]) none (selected after.2) ∧
      Cell.update stateCell invalid (flush ops) closeWal
        (.online handle old, before) = .error error (.offline, after.2) :=
  ⟨Execution.Run.flushInterrupted (s := (.updating handle, before)) prior evidence.laws ran,
    update_error _ invalid error closeWal handle old before after ran closeFrame⟩


theorem get_online
    (prior : Execution.Run events (some session) (selected before))
    (evidence : NativeBridge.CallbackEvidence ops (selected ∘ Prod.snd) (fileBytes ∘ Prod.snd))
    (ran : get ops session key (.online handle session, before) =
      .ok value (.online handle session, after)) (invalid : String) :
    Execution.Run (events ++ [.got key value]) (some session) (selected after) ∧
      Cell.useSession stateCell invalid (fun live => get ops live key)
        (.online handle session, before) = .ok value (.online handle session, after) :=
  ⟨Execution.Run.getOk (s := (.online handle session, before)) prior evidence.laws ran,
    (useSession_online _ invalid handle session before).trans ran⟩

theorem get_online_error
    (prior : Execution.Run events (some session) (selected before))
    (evidence : NativeBridge.CallbackEvidence ops (selected ∘ Prod.snd) (fileBytes ∘ Prod.snd))
    (ran : get ops session key (.online handle session, before) =
      .error error (.online handle session, after)) (invalid : String) :
    Execution.Run events (some session) (selected after) ∧
      Cell.useSession stateCell invalid (fun live => get ops live key)
        (.online handle session, before) = .error error (.online handle session, after) :=
  ⟨Execution.Run.getError (s := (.online handle session, before)) prior evidence.laws ran,
    (useSession_online _ invalid handle session before).trans ran⟩

end ExperimentalL0.Lifecycle
