import Alvoki.Experiments.L0.NativeRead
import Alvoki.Experiments.L0.NativeScope
import Alvoki.Experiments.WAL.Proofs.NativePost

open ExperimentalL0 Alvoki.NativePost

example (p : W → Prop) (q : α → Prop) (a : F α) :
    NativeRead.FilePost p q a ↔
      ∀ w, p w → Returns a w (fun x t => p t ∧ q x) p := by
  constructor <;> intro h w hw <;> have step := h w hw <;>
    unfold NativeRead.FilePost Returns at * <;>
    cases run : a.run w with
    | error => simpa [run] using step
    | ok r t => cases r <;> simpa [run] using step

example (a : IO α) (w : W) (q : α → W → Prop) (p : W → Prop) :
    IOReturns a w q p ↔ NativeScope.Post a w q (fun _ => p) := Iff.rfl
