import Alvoki.Experiments.L0.Basic

namespace ExperimentalL0

/-- Probe occupied names, including orphans. The exclusive writer still
uses exclusive creation, even after a successful probe. -/
def freeTableId [Monad m] [MonadExceptOf String m] (occupied : UInt64 → m Bool)
    (next : Nat) : m UInt64 :=
  if full : next ≥ UInt64.size then throw "table IDs exhausted"
  else do
    let id := next.toUInt64
    if ← occupied id then freeTableId occupied (next + 1) else return id
termination_by UInt64.size - next
decreasing_by omega

/-- Return the ID only after both the file and directory barriers. -/
def createTableAt [Monad m] [MonadExceptOf String m] (occupied : UInt64 → m Bool)
    (buildSynced : UInt64 → Rows → m Unit) (syncDirectory : m Unit) (rows : Rows) : m UInt64 := do
  let id ← freeTableId occupied 0
  buildSynced id rows
  syncDirectory
  return id

end ExperimentalL0
