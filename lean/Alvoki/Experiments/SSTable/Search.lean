import Alvoki.Experiments.SSTable.Contract

namespace ImmutableSSTable

/-- Search the half-open interval of row indices. Each comparison requests
exactly one row, so the reader can fail at the point it needs that row. -/
def seekBetween [Monad m] (read : Nat → m Entry) (key : ByteArray) (lo hi : Nat) : m Nat := do
  if lo < hi then
    let mid := lo + (hi - lo) / 2
    let row ← read mid
    if row.key < key then
      seekBetween read key (mid + 1) hi
    else
      seekBetween read key lo mid
  else
    return lo
termination_by hi - lo
decreasing_by all_goals omega

end ImmutableSSTable
