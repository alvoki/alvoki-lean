import Alvoki.Experiments.L0.Codecs

namespace ExperimentalL0

/-- Supply the next typed row's encoding and advance the cursor by exactly
one element. End of input leaves the cursor unchanged. -/
def nextTableRow [Monad m] (read : m Rows) (write : Rows → m Unit) :
    m (Option ImmutableSSTable.Entry) := do
  match ← read with
  | [] => return none
  | row :: remaining =>
    write remaining
    return some (ImmutableSSTable.Entry.encode keyCodec mutationCodec row)

end ExperimentalL0
