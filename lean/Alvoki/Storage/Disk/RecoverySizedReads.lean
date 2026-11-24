import Alvoki.Storage.Disk.WalSegmentReplay

namespace Alvoki.Storage

open System
open WAL (frameSize)

/-- Admit an exact-size recovery payload before requesting any bytes.
The metadata callback observes the file under the held lock. The payload
callback is a prefix read of at most the requested size. -/
def readExactRecoveryFileWith [Monad m] [MonadExceptOf IO.Error m] (path : FilePath) (expected : Nat)
    (mismatch : IO.Error) (readSize : FilePath → m Nat) (readPrefix : FilePath → Nat → m ByteArray) : m ByteArray := do
  let actual ← readSize path
  unless actual = expected ∧ expected < USize.size do throw mismatch
  let bytes ← readPrefix path expected
  unless bytes.size = expected do throw mismatch
  pure bytes

/-- An oversized file, a short file, or an unrepresentable request stops
at metadata admission. The supplied payload callback has no effect. -/
theorem readExactRecoveryFileWith_rejectsSize {state : Type} (path : FilePath) (expected : Nat)
    (mismatch : IO.Error) (readSize : FilePath → EStateM IO.Error state Nat)
    (readPrefix : FilePath → Nat → EStateM IO.Error state ByteArray)
    {initial observed : state} {actual : Nat}
    (sized : readSize path initial = .ok actual observed)
    (wrong : ¬ (actual = expected ∧ expected < USize.size)) :
    readExactRecoveryFileWith path expected mismatch readSize readPrefix initial = .error mismatch observed := by
  simp only [readExactRecoveryFileWith, Bind.bind, EStateM.bind, sized, wrong, ite_false]
  rfl

/-- The successful branch reaches exactly the admitted prefix request.
The returned extent still has to match the expected size. -/
theorem readExactRecoveryFileWith_accepts {state : Type} (path : FilePath) (expected : Nat)
    (mismatch : IO.Error) (readSize : FilePath → EStateM IO.Error state Nat)
    (readPrefix : FilePath → Nat → EStateM IO.Error state ByteArray)
    {initial observed final : state} {bytes : ByteArray} (fits : expected < USize.size)
    (sized : readSize path initial = .ok expected observed)
    (read : readPrefix path expected observed = .ok bytes final)
    (exactSize : bytes.size = expected) :
    readExactRecoveryFileWith path expected mismatch readSize readPrefix initial = .ok bytes final := by
  simp only [readExactRecoveryFileWith, Bind.bind, EStateM.bind, sized, fits, exactSize, read,
    and_self, ite_true, Pure.pure, EStateM.pure]

structure WalReadExtent where
  first : Nat
  bytes : Nat

structure WalRecoveryReadPlan where
  sealed : List WalReadExtent
  keeper : WalReadExtent

/-- Compute the exact sealed lengths from adjacent selected offsets. The
keeper is the last selected file and is read only through the marker. -/
def walRecoveryReadPlan (through : Nat) : List Nat → Option WalRecoveryReadPlan
  | [] => none
  | [keeper] =>
    if keeper ≤ through then some ⟨[], ⟨keeper, (through - keeper) * frameSize⟩⟩ else none
  | first :: rest@(next :: _) => do
    if first < next then
      let plan ← walRecoveryReadPlan through rest
      return { plan with sealed := ⟨first, (next - first) * frameSize⟩ :: plan.sealed }
    else none

/-- An admitted plan requests exactly the marker-covered byte interval
from the first selected start, including the keeper prefix. -/
theorem walRecoveryReadPlan_bytes {through first : Nat} {rest : List Nat} {plan : WalRecoveryReadPlan}
    (planned : walRecoveryReadPlan through (first :: rest) = some plan) :
    first ≤ through ∧
      (plan.sealed.map WalReadExtent.bytes).sum + plan.keeper.bytes = (through - first) * frameSize := by
  induction rest generalizing first plan with
  | nil =>
    simp only [walRecoveryReadPlan] at planned
    split at planned
    · rename_i covered
      cases planned
      exact ⟨covered, Nat.zero_add _⟩
    · contradiction
  | cons next tail ih =>
    simp only [walRecoveryReadPlan] at planned
    split at planned
    · rename_i forward
      cases later : walRecoveryReadPlan through (next :: tail) with
      | none => simp [later, Bind.bind, Option.bind] at planned
      | some rest =>
        simp only [later, Bind.bind, Option.bind, Pure.pure, Option.some.injEq] at planned
        subst plan
        obtain ⟨covered, bytes⟩ := ih later
        have count : next - first + (through - next) = through - first := by omega
        refine ⟨by omega, ?_⟩
        simp only [List.map_cons, List.sum_cons, Nat.add_assoc, bytes, ← Nat.add_mul, count]
    · contradiction

private theorem WalSegmentSpans.exactReadPlan {through : Nat} {files : List (Nat × ByteArray)}
    (spans : WalSegmentSpans through files) (listed : ∀ file ∈ files, file.1 ≤ through) :
    ∃ keeper payload, files.getLast? = some (keeper, payload) ∧
      walRecoveryReadPlan through (files.map Prod.fst) =
        some ⟨files.dropLast.map (fun file => ⟨file.1, file.2.size⟩), ⟨keeper, (through - keeper) * frameSize⟩⟩ ∧
      (through - keeper) * frameSize ≤ payload.size := by
  induction spans with
  | @active keeper bytes covered =>
    have keeperWithin : keeper ≤ through := listed (keeper, bytes) (by simp)
    exact ⟨keeper, bytes, rfl, by simp [walRecoveryReadPlan, keeperWithin], covered⟩
  | @sealed first next bytes nextBytes tail forward size remaining ih =>
    obtain ⟨keeper, payload, last, planned, covered⟩ :=
      ih (fun file found => listed file (List.mem_cons_of_mem _ found))
    refine ⟨keeper, payload, ?_, ?_, covered⟩
    · simpa only [List.getLast?_cons_cons] using last
    · simp only [List.dropLast_cons_cons, List.map_cons, walRecoveryReadPlan, forward, ite_true]
      simp only [List.map_cons] at planned
      simp [Bind.bind, Option.bind, planned, Pure.pure, size]

/-- Every accepted old span check supplies this same ordered read plan.
Its sealed lengths are exact, while its keeper read may omit an
unselected tail. -/
theorem walRecoveryReadPlan_ofCheckedSpans {through : Nat} {files : List (Nat × ByteArray)}
    (checked : checkSelectedWalSegmentSpans through files = true) :
    ∃ keeper payload, files.getLast? = some (keeper, payload) ∧
      walRecoveryReadPlan through (files.map Prod.fst) =
        some ⟨files.dropLast.map (fun file => ⟨file.1, file.2.size⟩), ⟨keeper, (through - keeper) * frameSize⟩⟩ ∧
      (through - keeper) * frameSize ≤ payload.size := by
  obtain ⟨bounded, spans⟩ := Bool.and_eq_true_iff.mp checked
  exact ((checkWalSegmentSpans_iff through files).mp spans).2.exactReadPlan
    (fun file found => of_decide_eq_true (List.all_eq_true.mp bounded file found))

end Alvoki.Storage
