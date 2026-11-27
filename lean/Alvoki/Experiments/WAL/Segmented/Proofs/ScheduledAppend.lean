import Alvoki.Experiments.WAL.Segmented.Proofs.Model
import Alvoki.Experiments.WAL.Proofs.ScheduledExecution

namespace WalRecoverySlice.Segmented.Model

/-- The exact append callback retains the submitted batch as the sole
    uncertainty. Ordinary scheduled writes may ACK. The first torn data write
    aborts, so neither a data barrier nor a marker publication follows it. -/
theorem Effects.appendRun_refines (effects : Effects) (clock id : Nat) (policy : Policy)
    (image : Persistence.Image) (history : List Bytes) (p : Bytes)
    (entry : Persistence.Ready policy image history) (clean : image.powerLoss = image)
    (bounded : ∀ b ∈ history, b.length ≤ 32) (fits : history.length < 255) (size : p.length ≤ 32) :
    let r := (effects.appendRun clock id policy (Persistence.historyCursor history) p).run image
    Persistence.Dirty policy history (some p) (Persistence.reached r) ∧
    (policy = .logOnly → (Persistence.reached r).MarkersSettled) ∧
    ∀ c, Persistence.acknowledged r = some c →
      c = Persistence.historyCursor (history ++ [p]) ∧
      Persistence.Ready policy (Persistence.reached r) (history ++ [p]) ∧
      (Persistence.reached r).powerLoss = Persistence.reached r := by
  exact Persistence.appendPrimitive_refines (effects.appendSegment clock id)
    (effects.appendWritebacks clock id) policy image history p
    (effects.tornAppend clock id policy (Persistence.historyCursor history) p)
    entry clean bounded fits size

end WalRecoverySlice.Segmented.Model
