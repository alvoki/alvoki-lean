import Alvoki.Experiments.L0.Lifecycle
import Alvoki.Experiments.L0.DurableCatalog
import Alvoki.Experiments.L0.Trace

namespace ExperimentalL0.Lifecycle
open Proof

variable {W S : Type}
variable {callbacks : Callbacks (EStateM String S) W}
variable {unavailable : String}
local notation "ops" => callbacksWithPhase callbacks unavailable
variable {selected : S → Selected}
variable {namespaceState : TableNamespace S}

/-- An initialized empty table catalog needs no inode witnesses. The
durable logical state is the same one that starts the client trace. -/
theorem initialCatalog (image : S)
    (empty : (selected image).tables = fun _ => none)
    (initial : Durable (selected image) []) :
    Execution.Run [] none (selected image) ∧
      namespaceState.Represents image (selected image).tables :=
  ⟨.initial ⟨initial⟩, empty.symm ▸ namespaceState.empty image⟩

/-- The callback's finite trace is already observed when outer cleanup runs.
A cleanup error ends the scope with the same client history and reached storage. -/
theorem scope_refines
    (use : StorageM (Phase W × S) α)
    (invalid : String) (closeWal : W → StorageM (Phase W × S) Unit)
    (unlock : StorageM (Phase W × S) Unit)
    (ran : recover ops (.opening, before) = .ok session (.recovering handle, after))
    (closeFrame : ∀ h storage, reached (closeWal h (.offline, storage)) = (.offline, storage))
    (unlockFrame : ∀ storage, reached (unlock (.offline, storage)) = (.offline, storage))
    (client : Execution.Run events visible (selected (reached (use (.online handle session, after))).2))
    (catalog : namespaceState.Represents (reached (use (.online handle session, after))).2
      (selected (reached (use (.online handle session, after))).2).tables) :
    let final := reached (Cell.withSession stateCell invalid (recover ops) use closeWal unlock
      (.opening, before))
    final.1 = .offline ∧ namespaceState.Represents final.2 (selected final.2).tables ∧
      ∃ state, Client.Allows (events ++ [.stop]) state ∧
        Execution.Represents none (selected final.2) state := by
  dsimp only
  rw [successful_recovery_cleanup (recover ops) use invalid closeWal unlock handle session before after
    ran closeFrame unlockFrame]
  exact ⟨rfl, catalog, (Execution.Run.stop client).refines⟩

end ExperimentalL0.Lifecycle
