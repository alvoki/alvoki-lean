import Compaction
import Optimizations

open Alvoki Alvoki.Opt

-- Benchmark-only externs. The validated run lengths and the output allocation
-- determine every window. Safe verification and ordinary builds use stock Lean.
@[extern "lean_byte_array_uget_uint64le"]
private unsafe opaque wideLoad (bytes : @& ByteArray) (offset : USize) : UInt64

@[extern "lean_byte_array_uset_uint64le"]
private unsafe opaque wideStore (bytes : ByteArray) (offset : USize) (value : UInt64) : ByteArray

@[inline] private def storeRow
    (load : ByteArray → USize → UInt64) (store : ByteArray → USize → UInt64 → ByteArray)
    (src : @& ByteArray) (srcPos : USize) (out : ByteArray) (dstPos : USize) : ByteArray :=
  let out := store out dstPos (load src srcPos)
  let out := store out (dstPos + 8) (load src (srcPos + 8))
  let out := store out (dstPos + 16) (load src (srcPos + 16))
  store out (dstPos + 24) (load src (srcPos + 24))

@[specialize] private partial def freshFrom
    (load : ByteArray → USize → UInt64) (store : ByteArray → USize → UInt64 → ByteArray)
    (src : @& ByteArray) (limit offset : USize) (out : ByteArray) : ByteArray :=
  if offset < limit then
    freshFrom load store src limit (offset + 32) (storeRow load store src offset out offset)
  else out

@[inline] private def fresh
    (load : ByteArray → USize → UInt64) (store : ByteArray → USize → UInt64 → ByteArray)
    (src : @& ByteArray) (out : ByteArray) : ByteArray :=
  let out := store (store out 0 (load src 0)) 8 3
  freshFrom load store src src.usize 16 out

@[specialize] private partial def denseFrom
    (load : ByteArray → USize → UInt64) (store : ByteArray → USize → UInt64 → ByteArray)
    (src : @& ByteArray) (limit offset : USize) (out : ByteArray) : ByteArray :=
  if offset < limit then
    let out := if load src (offset + 16) == 0 then
      store out (offset + 24) (load src (offset + 24) ^^^ 0xfedcba9876543210)
    else out
    denseFrom load store src limit (offset + 32) out
  else out

@[inline] private def dense
    (load : ByteArray → USize → UInt64) (store : ByteArray → USize → UInt64 → ByteArray)
    (src : @& ByteArray) (out : ByteArray) : ByteArray :=
  denseFrom load store src src.usize 16 out

@[specialize] private partial def alternateFrom
    (copyRow : ByteArray → USize → ByteArray → USize → ByteArray)
    (left right : @& ByteArray) (rightLimit source target : USize) (out : ByteArray) : ByteArray :=
  if source < rightLimit then
    let out := copyRow left source out target
    let out := copyRow right source out (target + 32)
    alternateFrom copyRow left right rightLimit (source + 32) (target + 64) out
  else if source < left.usize then copyRow left source out target
  else out

@[inline] private def alternate
    (copyRow : ByteArray → USize → ByteArray → USize → ByteArray)
    (left right : @& ByteArray) (out : ByteArray) : ByteArray :=
  let out := storeWord (storeWord out 0 ((out.size - 16) / 32).toUInt64) 8 3
  alternateFrom copyRow left right right.usize 16 16 out

private abbrev Row := Alvoki.Compaction.Model.Entry (UInt64 × UInt64)

@[specialize] private partial def encodeOwnedFrom (store : ByteArray → USize → UInt64 → ByteArray)
    (rows : @& Array Row) (index offset : USize) (out : ByteArray) : ByteArray :=
  if hit : index < rows.usize then
    have outer : rows.usize.toNat ≤ rows.size := USize.toNat_ofNat_le
    let row := rows.uget index (Nat.lt_of_lt_of_le (USize.lt_iff_toNat_lt.mp hit) outer)
    let out := store (store (store (store out offset row.key) (offset + 8) row.sequence)
      (offset + 16) row.payload.1) (offset + 24) row.payload.2
    encodeOwnedFrom store rows (index + 1) (offset + 32) out
  else out

@[inline] private def encodeOwned (store : ByteArray → USize → UInt64 → ByteArray)
    (rows : @& Array Row) (out : ByteArray) : ByteArray :=
  encodeOwnedFrom store rows 0 16 (store (store out 0 rows.size.toUInt64) 8 3)

@[noinline] unsafe def wideFresh (src : @& ByteArray) (out : ByteArray) : ByteArray :=
  fresh wideLoad wideStore src out
@[noinline] unsafe def wideDense (src : @& ByteArray) (out : ByteArray) : ByteArray :=
  dense wideLoad wideStore src out
@[noinline] unsafe def wideAlternate (left right : @& ByteArray) (out : ByteArray) : ByteArray :=
  alternate (storeRow wideLoad wideStore) left right out
@[noinline] unsafe def wideOwned (rows : @& Array Row) (out : ByteArray) : ByteArray :=
  encodeOwned wideStore rows out

@[noinline] def stockFresh (src : @& ByteArray) (out : ByteArray) : ByteArray :=
  fresh wordMachine storeWord src out
@[noinline] def stockDense (src : @& ByteArray) (out : ByteArray) : ByteArray :=
  dense wordMachine storeWord src out
@[noinline] def stockAlternate (left right : @& ByteArray) (out : ByteArray) : ByteArray :=
  alternate (fun src srcPos out dstPos => src.copySlice srcPos.toNat out dstPos.toNat 32 false) left right out
@[noinline] def stockOwned (rows : @& Array Row) (out : ByteArray) : ByteArray :=
  encodeOwned storeWord rows out

@[noinline] unsafe def sharedFinalWord (before : ByteArray) : ByteArray :=
  let index := (before.size - 8).toUSize
  let updated := wideStore before index 0xfedcba9876543210
  pushWordFast (before ++ updated) (wideLoad updated index)

private def checkRun (bytes : ByteArray) : IO Unit :=
  match Alvoki.Compaction.parse bytes with
  | .ok _ => pure ()
  | .error why => throw (IO.userError why)

private def prepareOutput (mode : String) (left right : @& ByteArray) : ByteArray :=
  if mode.endsWith "dense" then left.extract 0 left.size
  else if mode.endsWith "alternating" then zeroedBytes (left.size + right.size - 16)
  else if mode == "alias" then ByteArray.empty
  else zeroedBytes left.size

unsafe def main (args : List String) : IO Unit := do
  let [requestedMode, leftPath, rightPath, output, trialText] := args
    | throw (IO.userError "expected MODE LEFT RIGHT_OR_DASH OUT_OR_DASH TRIALS")
  let some trials := trialText.toNat? | throw (IO.userError "invalid trials")
  let kernel := requestedMode.startsWith "kernel-"
  let mode := if kernel then (requestedMode.drop 7).toString else requestedMode
  let left ← IO.FS.readBinFile leftPath
  let right ← if rightPath == "-" then pure ByteArray.empty else IO.FS.readBinFile rightPath
  if mode == "alias" then
    unless 8 ≤ left.size && left.size < USize.size do throw (IO.userError "short alias fixture")
  else
    checkRun left
  if mode.endsWith "alternating" then
    checkRun right
    unless left.size + right.size < USize.size &&
        (left.size == right.size || left.size == right.size + 32) do
      throw (IO.userError "incompatible alternating run lengths")
  let rows := if mode.endsWith "owned" then
    (Array.range ((left.size - 16) / 32)).map (Alvoki.Compaction.rawRow left)
  else #[]
  let inputs ← IO.mkRef (left, right, rows)
  for _ in [0:trials] do
    let (a, b, rows) ← inputs.get
    let initial := if kernel then some (prepareOutput mode a b) else none
    let start ← IO.monoNanosNow
    let out := match initial with
      | .some bytes => bytes
      | .none => prepareOutput mode a b
    let bytes ← match mode with
      | "fresh" => pure (wideFresh a out)
      | "dense" => pure (wideDense a out)
      | "alternating" => pure (wideAlternate a b out)
      | "owned" => pure (wideOwned rows out)
      | "stock-fresh" => pure (stockFresh a out)
      | "stock-dense" => pure (stockDense a out)
      | "stock-alternating" => pure (stockAlternate a b out)
      | "stock-owned" => pure (stockOwned rows out)
      | "alias" => pure (sharedFinalWord a)
      | _ => throw (IO.userError "unknown mode")
    let elapsed := (← IO.monoNanosNow) - start
    let tag := word bytes 0 ^^^ word bytes (bytes.size - 8) ^^^ bytes.size.toUInt64
    if output != "-" then IO.FS.writeBinFile output bytes
    IO.println s!"{elapsed} {tag}"
