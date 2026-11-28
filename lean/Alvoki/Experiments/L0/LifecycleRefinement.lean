import Alvoki.Experiments.L0.Lifecycle
import Alvoki.Experiments.L0.NativeBridge
import Alvoki.Experiments.L0.ScheduleSteps

namespace ExperimentalL0.Lifecycle
open Proof

variable {W S : Type}
variable {callbacks : Callbacks (EStateM String S) W}
variable {unavailable : String}
local notation "ops" => callbacksWithPhase callbacks unavailable
variable {selected : S → Selected}
variable {namespaceState : TableNamespace (Phase W × S)}

/-- One reached recovery result justifies both the actual scope's publication
of the recovered session and the client trace step. Phase writes leave the
storage carrier untouched. -/
theorem recovery_online
    (prior : Execution.Run events none (selected before))
    (evidence : NativeBridge.CallbackEvidence ops (selected ∘ Prod.snd) namespaceState)
    (ran : recover ops (.opening, before) = .ok session after)
    (use : StorageM (Phase W × S) α)
    (invalid : String) (closeWal : W → StorageM (Phase W × S) Unit) (unlock : StorageM (Phase W × S) Unit) :
    ∃ handle, after.1 = .recovering handle ∧
      Execution.Run (events ++ [.reopened]) (some session) (selected after.2) ∧
      Cell.withSession stateCell invalid (recover ops) use closeWal unlock (.opening, before) =
        finish (ε := String) use (finish (ε := String) (Cell.close stateCell closeWal) unlock)
          (.online handle session, after.2) := by
  obtain ⟨handle, attached⟩ := recover_attached callbacks unavailable before session after ran
  obtain ⟨phase, storage⟩ := after
  change phase = .recovering handle at attached
  subst phase
  exact ⟨handle, rfl,
    Execution.Run.recoverOk (s := (.opening, before)) prior evidence.effects ran,
    successful_recovery_publishes (recover ops) use invalid closeWal unlock handle session
      before storage ran⟩

/-- Failed recovery records only an offline client step. Phase cleanup
detaches the handle even when closing the WAL or releasing the lock fails. -/
theorem recovery_offline
    (prior : Execution.Run events none (selected before))
    (evidence : NativeBridge.CallbackEvidence ops (selected ∘ Prod.snd) namespaceState)
    (ran : recover ops (.opening, before) = .error error after)
    (use : StorageM (Phase W × S) α)
    (invalid : String) (closeWal : W → StorageM (Phase W × S) Unit) (unlock : StorageM (Phase W × S) Unit)
    (closeFrame : ∀ handle storage, reached (closeWal handle (.offline, storage)) = (.offline, storage))
    (unlockFrame : ∀ storage, reached (unlock (.offline, storage)) = (.offline, storage)) :
    Execution.Run (events ++ [.openFailed]) none (selected after.2) ∧
      Cell.withSession stateCell invalid (recover ops) use closeWal unlock (.opening, before) =
        .error error (.offline, after.2) :=
  ⟨Execution.Run.recoverError (s := (.opening, before)) prior evidence.effects ran,
    failed_recovery_closes (recover ops) use invalid error closeWal unlock before after ran
      closeFrame unlockFrame⟩

/-- Put and delete use this same write schedule. Publication changes only
phase custody, as does hiding the previous session before the call. -/
theorem write_online
    (prior : Execution.Run events (some old) (selected before))
    (evidence : NativeBridge.CallbackEvidence ops (selected ∘ Prod.snd) namespaceState)
    (change : Change)
    (ran : write ops old change (.updating handle, before) = .ok next after)
    (invalid : String) (closeWal : W → StorageM (Phase W × S) Unit) :
    Execution.Run (events ++ [.written change]) (some next) (selected after.2) ∧
      Cell.update stateCell invalid (fun session => write ops session change) closeWal
        (.online handle old, before) = .ok () (.online handle next, after.2) := by
  have frame := write_keepsPhase callbacks unavailable old change (.updating handle, before)
  rw [ran] at frame
  rcases after with ⟨phase, storage⟩
  change phase = .updating handle at frame
  subst phase
  exact ⟨Execution.Run.writeOk (s := (.updating handle, before)) prior evidence.effects ran,
    update_success _ invalid closeWal handle old next before storage ran⟩

theorem write_offline
    (prior : Execution.Run events (some old) (selected before))
    (evidence : NativeBridge.CallbackEvidence ops (selected ∘ Prod.snd) namespaceState)
    (change : Change)
    (ran : write ops old change (.updating handle, before) = .error error after)
    (invalid : String) (closeWal : W → StorageM (Phase W × S) Unit)
    (closeFrame : ∀ handle storage, reached (closeWal handle (.offline, storage)) = (.offline, storage)) :
    Execution.Run (events ++ [.writeUncertain change]) none (selected after.2) ∧
      Cell.update stateCell invalid (fun session => write ops session change) closeWal
        (.online handle old, before) = .error error (.offline, after.2) :=
  ⟨Execution.Run.writeInterrupted (s := (.updating handle, before)) prior evidence.effects ran,
    update_error _ invalid error closeWal handle old before after ran closeFrame⟩

theorem flush_online
    (prior : Execution.Run events (some old) (selected before))
    (evidence : NativeBridge.CallbackEvidence ops (selected ∘ Prod.snd) namespaceState)
    (ran : flush ops old (.updating handle, before) = .ok next after)
    (invalid : String) (closeWal : W → StorageM (Phase W × S) Unit) :
    Execution.Run (events ++ [.flushed]) (some next) (selected after.2) ∧
      Cell.update stateCell invalid (flush ops) closeWal
        (.online handle old, before) = .ok () (.online handle next, after.2) := by
  have frame := flush_keepsPhase callbacks unavailable old (.updating handle, before)
  rw [ran] at frame
  rcases after with ⟨phase, storage⟩
  change phase = .updating handle at frame
  subst phase
  exact ⟨Execution.Run.flushObserved (s := (.updating handle, before)) prior evidence.effects ran .delivered,
    update_success _ invalid closeWal handle old next before storage ran⟩

theorem flush_offline
    (prior : Execution.Run events (some old) (selected before))
    (evidence : NativeBridge.CallbackEvidence ops (selected ∘ Prod.snd) namespaceState)
    (ran : flush ops old (.updating handle, before) = .error error after)
    (invalid : String) (closeWal : W → StorageM (Phase W × S) Unit)
    (closeFrame : ∀ handle storage, reached (closeWal handle (.offline, storage)) = (.offline, storage)) :
    Execution.Run (events ++ [.flushUncertain]) none (selected after.2) ∧
      Cell.update stateCell invalid (flush ops) closeWal
        (.online handle old, before) = .error error (.offline, after.2) :=
  ⟨Execution.Run.flushObserved (s := (.updating handle, before)) prior evidence.effects ran .reportedError,
    update_error _ invalid error closeWal handle old before after ran closeFrame⟩


theorem get_online
    (prior : Execution.Run events (some session) (selected before))
    (evidence : NativeBridge.CallbackEvidence ops (selected ∘ Prod.snd) namespaceState)
    (catalog : namespaceState.Represents (.online handle session, before) (selected before).tables)
    (ran : get ops session key (.online handle session, before) =
      .ok value after) (invalid : String) :
    Execution.Run (events ++ [.got key value]) (some session) (selected after.2) ∧
      Cell.useSession stateCell invalid (fun live => get ops live key)
        (.online handle session, before) = .ok value (.online handle session, after.2) := by
  have frame := get_keepsPhase callbacks unavailable session key (.online handle session, before)
  rw [ran] at frame
  rcases after with ⟨phase, storage⟩
  change phase = .online handle session at frame
  subst phase
  exact ⟨Execution.Run.getOk (s := (Phase.online handle session, before)) prior (fun _ installed => evidence.get catalog installed key) ran,
    (useSession_online _ invalid handle session before).trans ran⟩

theorem get_online_error
    (prior : Execution.Run events (some session) (selected before))
    (evidence : NativeBridge.CallbackEvidence ops (selected ∘ Prod.snd) namespaceState)
    (catalog : namespaceState.Represents (.online handle session, before) (selected before).tables)
    (ran : get ops session key (.online handle session, before) =
      .error error after) (invalid : String) :
    Execution.Run events (some session) (selected after.2) ∧
      Cell.useSession stateCell invalid (fun live => get ops live key)
        (.online handle session, before) = .error error (.online handle session, after.2) := by
  have frame := get_keepsPhase callbacks unavailable session key (.online handle session, before)
  rw [ran] at frame
  rcases after with ⟨phase, storage⟩
  change phase = .online handle session at frame
  subst phase
  exact ⟨Execution.Run.getError (s := (Phase.online handle session, before)) prior (fun _ installed => evidence.get catalog installed key) ran,
    (useSession_online _ invalid handle session before).trans ran⟩

end ExperimentalL0.Lifecycle
