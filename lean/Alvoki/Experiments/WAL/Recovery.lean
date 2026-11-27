/-! An experimental, one-segment model. This is not the production WAL format. -/
namespace WalRecoverySlice

inductive Policy where | logOnly | boundary deriving BEq, Repr

abbrev Bytes := List UInt8

private def maxPayload := 32
private def frameOverhead := 6 -- four header fields and two check bytes

private def checksum (xs : Bytes) : Nat := xs.foldl (fun a b => (a * 31 + b.toNat) % 251) 7

def frame (seq : Nat) (payload : Bytes) : Bytes :=
  let header : Bytes := [42, 1, seq.toUInt8, payload.length.toUInt8]
  header ++ [(checksum header).toUInt8] ++ payload ++ [(checksum (header ++ payload)).toUInt8]

/-- Append position established by a successful append or open, for this segment only. -/
structure Cursor where
  endPos : Nat := 0
  nextSeq : Nat := 1
  deriving Repr, BEq

structure Decoded where
  batches : List Bytes
  cursor : Cursor
  deriving Repr

/-- A bad final frame may be torn. A complete header with the wrong generation or
sequence is a gap, not a tail. The bounded format admits at most 32 payload units. -/
def scan (bytes : Bytes) (limit : Nat) (policy : Policy) : Except String Decoded := do
  let rec loop (fuel pos seq : Nat) (rest : Bytes) (acc : List Bytes) : Except String Decoded := do
    let fuel + 1 := fuel | throw "scan fuel exhausted"
    let complete := fun () => Decoded.mk acc.reverse ⟨pos, seq⟩
    let torn := fun (reason : String) (maxLength : Nat) =>
      if policy == .logOnly && rest.length ≤ maxLength then Except.ok (complete ())
      else Except.error reason
    match rest with
    | [] => return complete ()
    | magic :: gen :: seqByte :: lenByte :: headerCheck :: tail =>
      let header := [magic, gen, seqByte, lenByte]
      if headerCheck != (checksum header).toUInt8 then
        return ← torn "damaged header" (maxPayload + frameOverhead)
      if magic != 42 || gen != 1 || seqByte.toNat != seq then throw "gap or generation mismatch"
      let len := lenByte.toNat
      if len > maxPayload then throw "invalid batch length"
      let (payload, trailer) := tail.splitAt len
      let total := len + frameOverhead
      let check :: remaining := trailer | return ← torn "short batch" total
      if check != (checksum (header ++ payload)).toUInt8 then
        return ← torn "damaged batch" total
      loop fuel (pos + total) (seq + 1) remaining (payload :: acc)
    | _ => return ← torn "short header" frameOverhead
  let selected := bytes.take limit
  if selected.length != limit then throw "missing bytes"
  loop (limit + 1) 0 1 selected []

structure Ops (m : Type → Type) where
  append : Bytes → m Unit
  syncData : m Unit
  replaceMarker : Nat → Nat → m Unit
  syncDirectory : m Unit
  readData : m Bytes
  readMarker : m (Nat × Nat)
  truncate : Nat → m Unit

/-- All successful returns from append follow the data barrier and, if selected,
the marker barrier. The caller must abandon the session on any error. -/
def appendBatch [Monad m] [MonadExceptOf String m] (ops : Ops m) (policy : Policy) (cursor : Cursor)
    (payload : Bytes) : m Cursor := do
  let seq := cursor.nextSeq
  if payload.length > maxPayload || seq == 0 || seq > 255 then throw "batch out of bounds"
  let bytes := frame seq payload
  ops.append bytes
  ops.syncData
  let next := cursor.endPos + bytes.length
  if policy == .boundary then
    ops.replaceMarker next seq
    ops.syncDirectory
  return ⟨next, seq + 1⟩

/-- Recovery synchronizes even an unchanged end: process exit can leave a valid
frame visible only in cache. The marker is read before the segment. -/
def reopen [Monad m] [MonadExceptOf String m] (ops : Ops m) (policy : Policy) : m Decoded := do
  let marker ← if policy == .boundary then some <$> ops.readMarker else pure none
  let bytes ← ops.readData
  let endPos := marker.map Prod.fst |>.getD bytes.length
  let decoded ← match scan bytes endPos policy with
    | .ok d => pure d
    | .error e => throw e
  if let some (_, lastSeq) := marker then
    if decoded.cursor.nextSeq != lastSeq + 1 then throw "marker sequence mismatch"
    -- A previous process may have renamed this visible marker without syncing its directory.
    ops.syncDirectory
  if decoded.cursor.endPos < bytes.length then ops.truncate decoded.cursor.endPos
  ops.syncData
  return decoded

end WalRecoverySlice
