import Alvoki.Experiments.L0.Execution

open ExperimentalL0 ExperimentalL0.Model

private def check (ok : Bool) (message : String) : M Unit :=
  unless ok do throw message

private def expectFailure (action : M α) : M Unit :=
  fun image => match action image with
  | .error _ after => .ok () after
  | .ok _ after => .error "expected interruption" after

private def scenario (publication : Outcome) : M Unit := do
  let ops := components {}
  let session ← recover ops
  let session ← write ops session (7, .put 10)
  let session ← flush ops session
  let session ← write ops session (7, .delete)
  let session ← write ops session (8, .put 21)
  check ((← get ops session 7).isNone) "memtable tombstone hid no value"
  expectFailure (flush (components {create := .afterEffect}) session)
  let session ← recover ops
  expectFailure (flush (components {publish := publication}) session)
  expectFailure (recover (components {openWal := false}))
  let session ← recover ops
  check ((← get ops session 7).isNone) "recovered tombstone hid no value"
  check ((← get ops session 8) == some 21) "recovery lost acknowledged put"
  check (session.version.tables.length == (if publication == .beforeEffect then 1 else 2))
    "wrong manifest selected"
  check (session.mem.isEmpty == (publication == .afterEffect)) "wrong replay suffix"
  expectFailure (write (components {append := .afterEffect}) session (7, .put 44))
  let session ← recover ops
  check ((← get ops session 7) == some 44) "lost committed uncertain put"
  let reopened ← recover ops
  check ((← get ops reopened 7) == some 44) "second recovery changed result"
  check ((← get ops reopened 8) == some 21) "second recovery lost acknowledged put"

private def expectError (action : M α) (expected : String) : M Unit :=
  fun image => match action image with
  | .error error after =>
    if error == expected then .ok () after else .error error after
  | .ok _ after => .error "expected a reported error" after

private def readErrors : M Unit := do
  let ops := components {}
  let session ← recover ops
  let session ← write ops session (7, .put 10)
  let session ← flush ops session
  let session ← write ops session (7, .put 20)
  let session ← flush ops session
  let some newer := session.version.tables.head? | throw "expected a newer table"
  let faulty := { ops with tables := { ops.tables with
    lookup := fun id key => if id == newer then throw "lookup failed" else ops.tables.lookup id key
    check := fun id => if id == newer then throw "table open failed" else ops.tables.check id
  }}
  expectError (get faulty session 7) "lookup failed"
  expectError (recover faulty) "table open failed"
  let recovered ← recover ops
  check ((← get ops recovered 7) == some 20) "retry lost newest value"

def main : IO Unit := do
  for outcome in [Outcome.beforeEffect, Outcome.afterEffect] do
    match scenario outcome ({} : Image) with
    | .ok _ _ => pure ()
    | .error err _ => throw (IO.userError err)
  match readErrors ({} : Image) with
  | .ok _ _ => pure ()
  | .error err _ => throw (IO.userError err)
