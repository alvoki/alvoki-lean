/-! An experimental, one-segment model. This is not the production WAL format. -/
namespace WalRecoverySlice

inductive Policy where | logOnly | boundary deriving BEq, Repr

abbrev Bytes := List UInt8

def maxPayload := 32
private def frameOverhead := 20 -- four header bytes and two eight-byte checksums

/-- Eight little-endian bytes of Lean's standard 64-bit list hash. -/
def checksumBytes (xs : Bytes) : Bytes :=
  let h : UInt64 := hash xs
  [h.toUInt8, (h >>> 8).toUInt8, (h >>> 16).toUInt8, (h >>> 24).toUInt8,
   (h >>> 32).toUInt8, (h >>> 40).toUInt8, (h >>> 48).toUInt8, (h >>> 56).toUInt8]

@[simp] theorem checksumBytes_length (xs : Bytes) : (checksumBytes xs).length = 8 := rfl

def frame (seq : Nat) (payload : Bytes) : Bytes :=
  let header : Bytes := [42, 1, seq.toUInt8, payload.length.toUInt8]
  header ++ checksumBytes header ++ payload ++ checksumBytes (header ++ payload)

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
    | magic :: gen :: seqByte :: lenByte :: tail =>
      let header := [magic, gen, seqByte, lenByte]
      let headerCheck := tail.take 8
      let body := tail.drop 8
      if headerCheck != checksumBytes header then
        return ← torn "damaged header" (maxPayload + frameOverhead)
      if magic != 42 || gen != 1 || seqByte.toNat != seq then throw "gap or generation mismatch"
      let len := lenByte.toNat
      if len > maxPayload then throw "invalid batch length"
      let (payload, trailer) := body.splitAt len
      let total := len + frameOverhead
      if trailer.take 8 != checksumBytes (header ++ payload) then
        return ← torn "damaged batch" total
      loop fuel (pos + total) (seq + 1) (trailer.drop 8) (payload :: acc)
    | _ => return ← torn "short header" frameOverhead
  let selected := bytes.take limit
  if selected.length != limit then throw "missing bytes"
  loop (limit + 1) 0 1 selected []

def markerSize : Nat := 14

/-- Six cursor fields followed by an eight-byte little-endian checksum. -/
def encodeMarker (endPos lastSeq : Nat) : Bytes :=
  let fields : Bytes := [77, 2, 1, lastSeq.toUInt8, (endPos / 256).toUInt8, (endPos % 256).toUInt8]
  fields ++ checksumBytes fields

structure Marker where
  endPos : Nat
  lastSeq : Nat

/-- A short record or invalid checksum may be a torn slot. A checksum-valid record with
wrong format, generation, slot, or empty-cursor fields is a protocol error. -/
def decodeMarker (slot : Nat) (bytes : Bytes) : Except String (Option Marker) := do
  if bytes.length > markerSize then throw "oversized marker file"
  if bytes.length < markerSize then return none
  match bytes with
  | magic :: format :: generation :: seq :: hi :: lo :: check =>
    let fields : Bytes := [magic, format, generation, seq, hi, lo]
    if check != checksumBytes fields then return none
    let n := seq.toNat
    let offset := hi.toNat * 256 + lo.toNat
    if magic != 77 || format != 2 || generation != 1 || n % 2 != slot ||
        !((n == 0 && offset == 0) || (n > 0 && offset > 0)) then
      throw "invalid marker fields"
    return some ⟨offset, n⟩
  | _ => return none

/-- Both reads are required, including when the first record is valid. -/
def selectMarker (a b : Bytes) : Except String Marker := do
  let a ← decodeMarker 0 a
  let b ← decodeMarker 1 b
  match a, b with
  | none, none => throw "no valid marker"
  | some m, none | none, some m => return m
  | some left, some right => return if left.lastSeq > right.lastSeq then left else right

structure Ops (m : Type → Type) where
  append : Bytes → m Unit
  syncData : m Unit
  writeMarker : Nat → Bytes → m Unit
  syncMarker : Nat → m Unit
  readData : m Bytes
  readMarker : Nat → m Bytes
  truncate : Nat → m Unit

/-- All successful returns from append follow the data barrier and, if selected,
the marker barrier. The caller must abandon the session on any error. -/
def appendBatch [Monad m] [MonadExceptOf String m] (ops : Ops m) (policy : Policy) (cursor : Cursor)
    (payload : Bytes) : m Cursor := do
  let seq := cursor.nextSeq
  if payload.length > maxPayload || seq == 0 || seq > 255 then throw "batch out of bounds"
  let bytes := frame seq payload
  let next := cursor.endPos + bytes.length
  if policy == .boundary && next > 65535 then throw "marker offset out of bounds"
  ops.append bytes
  ops.syncData
  if policy == .boundary then
    let slot := seq % 2
    ops.writeMarker slot (encodeMarker next seq)
    ops.syncMarker slot
  return ⟨next, seq + 1⟩

/-- Recovery synchronizes even an unchanged end: process exit can leave a valid
frame visible only in cache. The marker is read before the segment. -/
def reopen [Monad m] [MonadExceptOf String m] (ops : Ops m) (policy : Policy) : m Decoded := do
  let marker ← if policy == .boundary then do
    let a ← ops.readMarker 0
    let b ← ops.readMarker 1
    match selectMarker a b with
    | .ok marker => pure (some marker)
    | .error e => throw e
    else pure none
  let bytes ← ops.readData
  let endPos := marker.map Marker.endPos |>.getD bytes.length
  let decoded ← match scan bytes endPos policy with
    | .ok d => pure d
    | .error e => throw e
  if let some selected := marker then
    if decoded.cursor.nextSeq != selected.lastSeq + 1 then throw "marker sequence mismatch"
    -- Settle both visible slots before truncation. The other slot may
    -- still hold a newer durable record behind a torn visible overwrite.
    let slot := selected.lastSeq % 2
    ops.syncMarker slot
    ops.syncMarker (1 - slot)
  if decoded.cursor.endPos < bytes.length then ops.truncate decoded.cursor.endPos
  ops.syncData
  return decoded

end WalRecoverySlice
