import Init

@[noinline] private def destination (capacity : Nat) : ByteArray :=
  ((ByteArray.emptyWithCapacity capacity).push 7).markLinear

@[noinline] private def overwrite (out : ByteArray) (offset : Nat) : ByteArray :=
  (ByteArray.empty.push 9).copySlice 0 out offset 1 false

def main (args : List String) : IO Unit := do
  let [mode, size] := args | throw (IO.userError "expected mode and capacity")
  -- A runtime capacity keeps the destination out of the compiler's closed values.
  let some capacity := size.toNat? | throw (IO.userError "invalid capacity")
  match mode with
  | "shared" | "shared-growth" =>
    let offset := if mode == "shared" then 0 else 1
    let before := destination capacity
    let after := overwrite before offset
    IO.println s!"{before[0]!} -> {after[offset]!}"
  | "unique" => IO.println (overwrite (destination capacity) 0)[0]!
  | "growth" =>
    let out := overwrite (destination capacity) 1
    IO.println s!"size {out.size}, appended {out[1]!}"
  | _ => throw (IO.userError "unknown mode")
