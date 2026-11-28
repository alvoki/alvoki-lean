import Alvoki.Experiments.L0.Trace
import Alvoki.Experiments.WAL.Segmented.Proofs.Invariant

namespace ExperimentalL0

open WalRecoverySlice.Segmented (Contract.View PermittedView)

/-- The concrete recovery returns this replay when the selected bytes are durable. -/
def Selected.replaySession (image : Selected) : Session :=
  let suffix := image.view.batches.drop (image.version.flushedThrough.toNat - image.view.base)
  ⟨image.version, replay ((suffix.mapM decode).getD [])⟩

theorem Durable.replaySession (d : Durable image history) : Installed image.replaySession image history :=
  ⟨d, rfl, by simp [Selected.replaySession, d.replay_pending]⟩

namespace Execution

theorem Run.uncertainAtView (run : Run events (some session) image)
    (choice : view = image.view ∨ view = image.view.append (encode change)) :
    Run (events ++ [.writeUncertain change]) none {image with view := view} := by
  apply run.writeUncertain
  intro history installed
  obtain ⟨d, _, _⟩ := installed
  rcases choice with rfl | rfl
  · exact .inl ⟨d⟩
  · exact .inr ⟨d.append change⟩

theorem Run.reopenSelected (run : Run events none image) :
    Run (events ++ [.reopened]) (some image.replaySession) image :=
  run.reopened fun _ d => d.replaySession

theorem Run.uncertainPermitted (run : Run events (some session) image)
    (allowed : PermittedView image.view (some (.append (encode change))) view) :
    Run (events ++ [.writeUncertain change]) none
      {image with view := view} := by
  have choice : view = image.view ∨ view = image.view.append (encode change) := by
    rcases allowed with old | applied
    · exact .inl old
    · right
      by_cases room : image.view.tail < WalRecoverySlice.Segmented.Contract.maxPosition <;>
        simp_all [WalRecoverySlice.Segmented.Contract.Request.apply]
  exact run.uncertainAtView choice

end Execution
end ExperimentalL0
