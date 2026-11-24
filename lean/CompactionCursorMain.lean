import CompactionCodec
import CodecVariants

open Alvoki Alvoki.Compaction

private abbrev Buffer (size : Nat) := { bytes : ByteArray // bytes.size = size }

@[inline] private def putWord (out : Buffer size) (offset : USize) (value : UInt64)
    (extent : offset.toNat + 7 < size) : Buffer size :=
  let written := Opt.storeWordAt out.val offset value (by simpa only [out.property] using extent)
  ⟨written.val, written.property.trans out.property⟩

@[inline] private def putRow (out : Buffer size) (offset : USize)
    (key sequence kind value : UInt64) (extent : offset.toNat + 31 < size) : Buffer size :=
  have lane (n : Nat) (small : n ≤ 24) : (offset + n.toUSize).toNat + 7 < size := by
    rw [USize.toNat_add]
    have le := Nat.mod_le (offset.toNat + n.toUSize.toNat) (2 ^ System.Platform.numBits)
    have laneSize : n.toUSize.toNat ≤ n := USize.toNat_ofNat_le
    omega
  let out := putWord out offset key (by omega)
  let out := putWord out (offset + 8) sequence (lane 8 (by decide))
  let out := putWord out (offset + 16) kind (lane 16 (by decide))
  putWord out (offset + 24) value (lane 24 (by decide))

private def zeroChunk : ByteArray := Opt.zeroedBytes 4096

/-- Extend from an immutable zero chunk. This keeps the new destination distinct
from the source of every copy during initialization. -/
private def preextend (out : ByteArray) (size : Nat) (bounded : out.size ≤ size) : Buffer size :=
  if more : out.size < size then
    let width := min zeroChunk.size (size - out.size)
    let next := zeroChunk.copySlice 0 out out.size width false
    have step : next.size = out.size + width := by
      let builder := ScopedBytes.Builder.ofPrefix out
      change (builder.copyToTail zeroChunk 0 width).finish.size = _
      rw [ScopedBytes.copyToTail_refines, ByteArray.size_append, ByteArray.size_extract,
        Nat.zero_add, Nat.min_eq_left (Nat.min_le_left ..), Nat.sub_zero]
      rfl
    preextend next size (by
      have space : width ≤ size - out.size := Nat.min_le_right ..
      rw [step]
      omega)
  else ⟨out, by omega⟩
termination_by size - out.size
decreasing_by
  change size - next.size < size - out.size
  have chunkSize : zeroChunk.size = 4096 := Opt.zeroedBytes_size _
  have positive : 0 < width := by
    dsimp only [width]
    rw [chunkSize]
    exact Nat.lt_min.mpr ⟨by decide, by omega⟩
  omega

private def exactBuffer (size : Nat) : Buffer size :=
  preextend (ByteArray.emptyWithCapacity size) size (by
    change 0 ≤ size
    exact Nat.zero_le size)

private def encodeAppend (rows : @& Array RawEntry) : ByteArray :=
  let out := ByteArray.emptyWithCapacity (16 + 32 * rows.size)
  rows.foldl appendV3Row (pushWordFast (pushWordFast out rows.size.toUInt64) 3)

private def writeFrom (rows : @& Array RawEntry) (count i : USize)
    (countExact : count.toNat = rows.size) (out : Buffer (16 + 32 * rows.size)) :
    Buffer (16 + 32 * rows.size) :=
  if h : i < count then
    have hit : i.toNat < rows.size := by rwa [USize.lt_iff_toNat_lt, countExact] at h
    let offset : USize := 16 + 32 * i
    have extent : offset.toNat + 31 < 16 + 32 * rows.size := by
      have offsetLe : offset.toNat ≤ 16 + 32 * i.toNat := by
        dsimp [offset]
        rw [USize.toNat_add, USize.toNat_mul]
        have sixteen : (16 : USize).toNat = 16 := USize.toNat_ofNat_of_lt_32 (by decide)
        have thirtyTwo : (32 : USize).toNat = 32 := USize.toNat_ofNat_of_lt_32 (by decide)
        rw [sixteen, thirtyTwo]
        exact Nat.le_trans (Nat.mod_le ..) (Nat.add_le_add_left (Nat.mod_le ..) 16)
      omega
    let row := rows[i]'hit
    let next := putRow out offset row.key row.sequence row.payload.1 row.payload.2 extent
    writeFrom rows count (i + 1) countExact next
  else out
termination_by count.toNat - i.toNat
decreasing_by
  have step := Opt.addOne i count (USize.lt_iff_toNat_lt.mp h)
  omega

private def encodeCursor (rows : @& Array RawEntry) : ByteArray :=
  let size := 16 + 32 * rows.size
  if fits : size < USize.size then
    have countExact : rows.usize.toNat = rows.size :=
      USize.toNat_ofNat_of_lt (by dsimp [size] at fits; omega)
    let out := putWord (exactBuffer size) 0 rows.size.toUInt64 (by dsimp [size]; simp; omega)
    let out := putWord out 8 3 (by dsimp [size]; simp; omega)
    (writeFrom rows rows.usize 0 countExact out).val
  else encodeAppend rows

private def encodeListAppend (rows : @& List RawEntry) : ByteArray :=
  let count := rows.length
  let out := ByteArray.emptyWithCapacity (16 + 32 * count)
  rows.foldl appendV3Row (pushWordFast (pushWordFast out count.toUInt64) 3)

private def writeListFrom (rows : @& List RawEntry) (offset : USize) (out : Buffer size)
    (extent : offset.toNat + 32 * rows.length ≤ size) : Buffer size :=
  match rows with
  | [] => out
  | row :: rest =>
    have headFits : offset.toNat + 31 < size := by
      simp only [List.length_cons] at extent
      omega
    have restFits : (offset + 32).toNat + 32 * rest.length ≤ size := by
      simp only [List.length_cons] at extent
      rw [USize.toNat_add, show (32 : USize).toNat = 32 from USize.toNat_ofNat_of_lt_32 (by decide)]
      have le := Nat.mod_le (offset.toNat + 32) (2 ^ System.Platform.numBits)
      omega
    let next := putRow out offset row.key row.sequence row.payload.1 row.payload.2 headFits
    writeListFrom rest (offset + 32) next restFits

private def encodeListCursor (rows : @& List RawEntry) : ByteArray :=
  let count := rows.length
  let size := 16 + 32 * count
  if size < USize.size then
    let out := putWord (exactBuffer size) 0 count.toUInt64 (by dsimp [size]; simp; omega)
    let out := putWord out 8 3 (by dsimp [size]; simp; omega)
    (writeListFrom rows 16 out (by
      simp [size, count, show (16 : USize).toNat = 16 from USize.toNat_ofNat_of_lt_32 (by decide)])).val
  else encodeListAppend rows

private structure Cursor (size : Nat) where
  out : Buffer size
  offset : USize

private theorem overwriteKeepsSize (source out : ByteArray) (start dest width : Nat)
    (fits : dest + width ≤ out.size) :
    (source.copySlice start out dest width false).size = out.size := by
  rw [ByteArray.copySlice_eq_append]
  have startIn : dest ≤ out.size := by omega
  rw [ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract]
  simp only [ByteArray.size_data, Nat.min_eq_left startIn, Nat.sub_zero, Nat.min_self]
  by_cases inSource : start + width ≤ source.size
  · rw [Nat.min_eq_left inSource, Nat.min_eq_left (by omega : width ≤ source.size - start)]
    omega
  · rw [Nat.min_eq_right (by omega : source.size ≤ start + width),
      Nat.min_eq_right (by omega : source.size - start ≤ width)]
    omega

@[inline] private def cursorWrite (packedCopy : Bool) (source : @& Run) (i : USize)
    (key sequence : UInt64) (state : Cursor size) (limit failed : USize)
    (limitBound : limit.toNat + 31 ≤ size) : Cursor size :=
  if inside : state.offset < limit then
    have extent : state.offset.toNat + 31 < size := by
      have offset := USize.lt_iff_toNat_lt.mp inside
      omega
    let written :=
      if packedCopy then
        let start := 16 + 32 * i.toNat
        ⟨source.bytes.copySlice start state.out.val state.offset.toNat 32 false, by
          rw [overwriteKeepsSize _ _ _ _ _ (by simpa only [state.out.property] using (by omega :
            state.offset.toNat + 32 ≤ size)), state.out.property]⟩
      else
        let kind := Opt.wordMachine source.bytes (32 + 32 * i)
        let value := Opt.wordMachine source.bytes (40 + 32 * i)
        putRow state.out state.offset key sequence kind value extent
    ⟨written, state.offset + 32⟩
  else ⟨state.out, failed⟩

/-- Count with the original selector, then write at offsets in an exact-sized
buffer. The original span route covers sizes outside machine offset range. -/
@[inline] private def compactCursor (packedCopy : Bool) (left right : @& Run) (floor : UInt64) :
    ByteArray :=
  let count : Nat := visit left right floor 0 fun n _ _ _ _ => n + 1
  let size := 16 + 32 * count
  if fits : size < USize.size then
    let out := putWord (exactBuffer size) 0 count.toUInt64 (by dsimp [size]; simp; omega)
    let out := putWord out 8 3 (by dsimp [size]; simp; omega)
    if nonempty : 0 < count then
      let limit : USize := (size - 31).toUSize
      have bound : limit.toNat + 31 ≤ size := by
        have le : limit.toNat ≤ size - 31 := USize.toNat_ofNat_le
        dsimp [size] at le ⊢
        omega
      let failed := (size - 1).toUSize
      let done := visit left right floor (⟨out, 16⟩ : Cursor size) fun state rightward i key seq =>
        cursorWrite packedCopy (if rightward then right else left) i key seq state limit failed bound
      if done.offset == size.toUSize then done.out.val else compactSpans left right floor
    else out.val
  else compactSpans left right floor

private def decode (run : @& Run) : Array RawEntry := Id.run do
  let mut rows := Array.emptyWithCapacity run.count.toNat
  for i in [0:run.count.toNat] do rows := rows.push (rawRow run.bytes i)
  return rows

private def checked (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error message => throw (IO.userError message)

def main (args : List String) : IO Unit := do
  let [mode, leftPath, rightPath, floorText, snapshotText, output, trialsText] := args
    | throw (IO.userError "expected mode left right floor snapshot output trials")
  let some floor := floorText.toNat? | throw (IO.userError "invalid floor")
  let some snapshot := snapshotText.toNat? | throw (IO.userError "invalid snapshot")
  let some trials := trialsText.toNat? | throw (IO.userError "invalid trial count")
  if snapshot < floor || snapshot >= 2^64 then throw (IO.userError "invalid snapshot bounds")
  let left ← checked (Compaction.parse (← IO.FS.readBinFile leftPath))
  let right ← checked (Compaction.parse (← IO.FS.readBinFile rightPath))
  let rows := if mode.startsWith "encode-" || mode.startsWith "check-encode-" then
    decode left
  else #[]
  let (rows, rowList) := if mode.startsWith "encode-list-" || mode.startsWith "check-encode-list-" then
    (#[], rows.toList)
  else (rows, [])
  let inputs ← IO.mkRef (left, right, rows, rowList, floor.toUInt64, snapshot.toUInt64)
  for _ in [0:trials] do
    let (left, right, rows, rowList, floor, snapshot) ← inputs.get
    let start ← IO.monoNanosNow
    let (bytes, sum) ← match mode with
      | "cursor-copy" | "check-cursor-copy" => pure (compactCursor true left right floor, 0)
      | "cursor-store" | "check-cursor-store" => pure (compactCursor false left right floor, 0)
      | "cursor-pipeline" =>
        let parsed ← checked (Compaction.parse (compactCursor true left right floor))
        pure (ByteArray.empty, parsed.scan snapshot)
      | "encode-append" | "check-encode-append" => pure (encodeAppend rows, 0)
      | "encode-cursor" | "check-encode-cursor" => pure (encodeCursor rows, 0)
      | "encode-list-append" | "check-encode-list-append" => pure (encodeListAppend rowList, 0)
      | "encode-list-cursor" | "check-encode-list-cursor" => pure (encodeListCursor rowList, 0)
      | _ => throw (IO.userError "invalid cursor mode")
    let elapsed := (← IO.monoNanosNow) - start
    if mode.startsWith "check-" then IO.FS.writeBinFile output bytes
    else
      let tag := if bytes.size >= 16 then
        word bytes 0 ^^^ word bytes (bytes.size - 8) ^^^ bytes.size.toUInt64 else sum
      IO.println s!"{elapsed} {tag}"
