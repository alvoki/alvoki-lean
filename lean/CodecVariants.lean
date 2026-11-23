import RunProofs
import Optimizations
import Init.Internal.Order.While

namespace Alvoki
open Packed Opt Alvoki.ByteWords

theorem pushWord_eq_fast (bytes : ByteArray) (value : UInt64) :
    pushWord bytes value = pushWordFast bytes value := by
  unfold pushWord
  dsimp only
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  rfl

/-- Both baseline encoder modes emit the canonical v1 bytes. -/
theorem encode_eq_v1 (records : Array Record) (fast : Bool) :
    encode records fast = encodeV1 records := by
  cases fast <;> simp [encode, pushWord_eq_fast, encodeV1, Nat.mul_comm] <;> rfl

theorem Opt.encodeScalar_eq_v1 (records : Array ScalarRecord) :
    encodeScalar records = encodeV1 (records.map fun row => (row.key, row.value)) := by
  unfold encodeV1
  rw [Array.foldl_map]
  simp [encodeScalar, Nat.mul_comm]
  rfl

theorem Block.read_eq_word (block : Block) (offset : Nat) :
    block.read offset = word block.bytes offset := by
  cases h : block.fast <;> simp [Block.read, h, wordFast_eq_word]

private theorem toList_foldPush (indices : List Nat) (init : Array α) (f : Nat → α) :
    (indices.foldl (fun out i => out.push (f i)) init).toList =
      init.toList ++ indices.map f := by
  induction indices generalizing init with
  | nil => simp
  | cons i is ih => simp

private theorem Block.record_eq (block : Block) (run : Run)
    (bytes : block.bytes = run.view.bytes) (i : Nat) :
    block.record i = run.view.logicalRecord i := by
  simp [Block.record, Block.key, block.read_eq_word, View.logicalRecord,
    run.interleaved.1, run.interleaved.2, bytes]

/-- The baseline materializer reads the same v1 records as the validated run
when both describe the same bytes and count. -/
theorem Block.decode_eq_v1 (block : Block) (run : Run) (bytes : block.bytes = run.view.bytes)
    (count : block.count = run.count.toNat) : block.decode = run.decodeV1 := by
  unfold Block.decode
  dsimp only
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  rw [List.forIn_pure_yield_eq_foldl]
  simp only [pure_bind, Id.run_pure, Std.Legacy.Range.size, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one]
  change (List.range' 0 block.count).foldl (fun out i => out.push (block.record i))
    (Array.emptyWithCapacity block.count) = run.decodeV1
  apply Array.toList_inj.mp
  rw [toList_foldPush, ← List.range_eq_range', count]
  simp only [Array.emptyWithCapacity, Array.toList_empty, List.nil_append]
  apply List.ext_getElem (by simp)
  intro i _ _
  simpa using block.record_eq run bytes i

/-- The scalar materializer projects to precisely the same records as the baseline. -/
theorem Opt.decodeScalar_eq_v1 (block : Block) (run : Run) (bytes : block.bytes = run.view.bytes)
    (count : block.count = run.count.toNat) :
    (decodeScalar block).map (fun row => (row.key, row.value)) = run.decodeV1 := by
  rw [← block.decode_eq_v1 run bytes count]
  unfold decodeScalar Block.decode
  dsimp only
  rw [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.forIn_eq_forIn_range']
  simp only [List.forIn_pure_yield_eq_foldl, pure_bind, Id.run_pure,
    Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
  apply Array.toList_inj.mp
  rw [Array.toList_map, toList_foldPush, toList_foldPush]
  simp [List.map_map, Function.comp_def, Block.record]

/-- The streaming baseline decoder folds precisely the decoded v1 records. -/
theorem Opt.decodeFold_eq_v1 (block : Block) (run : Run) (bytes : block.bytes = run.view.bytes)
    (count : block.count = run.count.toNat) :
    decodeFold block =
      run.decodeV1.toList.foldl (fun sum row => sum + (row.1 ^^^ row.2)) 0 := by
  rw [← block.decode_eq_v1 run bytes count]
  unfold decodeFold Block.decode
  dsimp only
  rw [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.forIn_eq_forIn_range']
  simp only [List.forIn_pure_yield_eq_foldl, pure_bind, Id.run_pure,
    Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
  change _ = ((List.range' 0 block.count).foldl (fun out i => out.push (block.record i))
    (Array.emptyWithCapacity block.count)).toList.foldl _ 0
  rw [toList_foldPush]
  simp [List.foldl_map, Block.record]

theorem Opt.View.decode_eq_v1 (run : Run) :
    run.view.decode.map (fun row => (row.key, row.value)) = run.decodeV1 := by
  apply Array.toList_inj.mp
  rw [Array.toList_map, View.decode_records]
  apply List.ext_getElem (by simp [Run.count])
  intro i _ _
  simp

private theorem zeroLoop_size (size : Nat) (bytes : ByteArray)
    (positive : 0 < bytes.size) (bounded : bytes.size ≤ size) :
    (({} : Lean.Loop).forIn (m := Id) bytes (fun _ current =>
      if current.size < size then pure (.yield (current.copySlice 0 current current.size
        (min current.size (size - current.size)))) else pure (.done current))).run.size = size := by
  rw [Lean.Loop.forIn_eq_of_monadTail]
  by_cases more : bytes.size < size
  · simp only [ite_eq_left more, pure_bind]
    let step := min bytes.size (size - bytes.size)
    have le : step ≤ bytes.size := Nat.min_le_left ..
    have fits : step ≤ size - bytes.size := Nat.min_le_right ..
    have grows : 0 < step := by dsimp [step]; omega
    let next := bytes.copySlice 0 bytes bytes.size step
    have width : next.size = bytes.size + step := by
      unfold next
      rw [ByteArray.copySlice_eq_append]
      simp only [Nat.sub_zero, Nat.zero_add]
      change (bytes.extract 0 bytes.size ++ bytes.extract 0 step ++
        bytes.extract (bytes.size + min step bytes.size) bytes.size).size = _
      rw [Nat.min_eq_left le, ByteArray.extract_zero_size]
      have empty : bytes.extract (bytes.size + step) bytes.size = ByteArray.empty := by
        rw [ByteArray.extract_eq_empty_iff]
        omega
      rw [empty, ByteArray.append_empty, ByteArray.size_append, ByteArray.size_extract,
        Nat.min_eq_left le, Nat.sub_zero]
    exact zeroLoop_size size next (by omega) (by omega)
  · simp only [ite_eq_right more, pure_bind, Id.run_pure]
    omega
termination_by size - bytes.size
decreasing_by
  change size - next.size < size - bytes.size
  omega

theorem Opt.zeroedBytes_size (size : Nat) : (zeroedBytes size).size = size := by
  unfold zeroedBytes
  by_cases empty : size = 0
  · simp [empty]
  · have h : ¬ (size == 0) = true := by simpa using empty
    rw [ite_eq_right h]
    change ((({} : Lean.Loop).forIn (m := Id) ((ByteArray.emptyWithCapacity size).push 0)
      (fun _ current => if current.size < size then pure (.yield (current.copySlice 0 current
        current.size (min current.size (size - current.size)))) else pure (.done current))).run).size = size
    have fresh : (ByteArray.emptyWithCapacity size).size = 0 := rfl
    apply zeroLoop_size <;> rw [ByteArray.size_push, fresh] <;> omega

private theorem pushWord_byte (prefixBytes : ByteArray) (v : UInt64) (j : Nat)
    (within : j < prefixBytes.size + 8) :
    (pushWordFast prefixBytes v).data[j]? =
      if j < prefixBytes.size then prefixBytes.data[j]? else some (splitByte v (j - prefixBytes.size)) := by
  rw [pushWordFast_append, ByteArray.data_append]
  by_cases before : j < prefixBytes.size
  · rw [ite_eq_left before, Array.getElem?_append_left before]
  · have le : prefixBytes.data.size ≤ j := by
      change prefixBytes.size ≤ j
      omega
    rw [ite_eq_right before, Array.getElem?_append_right le]
    change (pushWordFast ByteArray.empty v).data[j - prefixBytes.size]? = _
    have hit : j - prefixBytes.size < 8 := by omega
    generalize j - prefixBytes.size = k at *
    have small : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 := by omega
    rcases small with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [pushWordFast, ByteArray.data_push]

private def WrittenPrefix (prefixBytes buffer : ByteArray) : Prop :=
  prefixBytes.size ≤ buffer.size ∧ ∀ j < prefixBytes.size, buffer.data[j]? = prefixBytes.data[j]?

private theorem storeWord_extends {prefixBytes buffer : ByteArray} (existing : WrittenPrefix prefixBytes buffer)
    {offset : USize} (position : offset.toNat = prefixBytes.size) (v : UInt64)
    (fits : buffer.size < USize.size) (extent : prefixBytes.size + 8 ≤ buffer.size) :
    WrittenPrefix (pushWordFast prefixBytes v) (storeWord buffer offset v) := by
  refine ⟨by simpa [pushWordFast_size] using extent, ?_⟩
  intro j within
  rw [pushWordFast_size] at within
  rw [storeWord_byte buffer offset v fits (by omega) j, pushWord_byte prefixBytes v j within, position]
  by_cases prior : j < prefixBytes.size
  · have no : ¬ (prefixBytes.size ≤ j ∧ j < prefixBytes.size + 8) := by omega
    rw [ite_eq_right no, ite_eq_left prior]
    exact existing.2 j prior
  · have yes : prefixBytes.size ≤ j ∧ j < prefixBytes.size + 8 := ⟨by omega, within⟩
    rw [ite_eq_left yes, ite_eq_right prior]

private theorem prefix_eq {p buffer : ByteArray} (existing : WrittenPrefix p buffer)
    (size : p.size = buffer.size) : buffer = p := by
  ext1
  apply Array.ext_getElem?
  intro j
  by_cases hit : j < p.size
  · exact existing.2 j hit
  · rw [Array.getElem?_eq_none (show buffer.data.size ≤ j by change buffer.size ≤ j; omega),
      Array.getElem?_eq_none (show p.data.size ≤ j by change p.size ≤ j; omega)]

private def storeRow (state : ByteArray × USize) (row : ScalarRecord) : ByteArray × USize :=
  (storeWord (storeWord state.1 state.2 row.key) (state.2 + 8) row.value, state.2 + 16)

private def appendRow (prefixBytes : ByteArray) (row : ScalarRecord) : ByteArray :=
  pushWordFast (pushWordFast prefixBytes row.key) row.value

private theorem indexedFold (rows : List ScalarRecord) (prefixBytes buffer : ByteArray) (offset : USize)
    (existing : WrittenPrefix prefixBytes buffer) (position : offset.toNat = prefixBytes.size)
    (capacity : prefixBytes.size + 16 * rows.length = buffer.size) (fits : buffer.size < USize.size) :
    (rows.foldl storeRow (buffer, offset)).1 = rows.foldl appendRow prefixBytes := by
  induction rows generalizing prefixBytes buffer offset with
  | nil =>
    simp only [List.foldl_nil, List.length_nil, Nat.mul_zero, Nat.add_zero] at capacity ⊢
    exact prefix_eq existing capacity
  | cons row rows ih =>
    simp only [List.length_cons] at capacity
    have key := storeWord_extends existing position row.key fits (by omega)
    have noWrapKey : prefixBytes.size + 8 < USize.size := by omega
    have noWrapRow : prefixBytes.size + 16 < USize.size := by omega
    have afterKey : (offset + 8).toNat = (pushWordFast prefixBytes row.key).size := by
      rw [USize.toNat_add, show (8 : USize).toNat = 8 from USize.toNat_ofNat_of_lt_32 (by decide),
        position, pushWordFast_size, Nat.mod_eq_of_lt noWrapKey]
    have value := storeWord_extends key afterKey row.value
      (by simpa using fits) (by simp only [pushWordFast_size, storeWord_size]; omega)
    have afterRow : (offset + 16).toNat = (appendRow prefixBytes row).size := by
      rw [USize.toNat_add, show (16 : USize).toNat = 16 from USize.toNat_ofNat_of_lt_32 (by decide),
        position, Nat.mod_eq_of_lt noWrapRow]
      simp only [appendRow, pushWordFast_size]
    rw [List.foldl_cons, List.foldl_cons]
    apply ih _ _ _ value afterRow
    · simp only [pushWordFast_size, storeWord_size]
      omega
    · simpa [storeRow] using fits

set_option maxHeartbeats 500000 in
/-- The indexed encoder writes the canonical bytes, including through its scalar fallback.
Its offset invariant and machine-width guard cover every indexed store. -/
theorem Opt.encodeIndexed_eq_v1 (records : Array ScalarRecord) :
    encodeIndexed records = encodeV1 (records.map fun row => (row.key, row.value)) := by
  let length := 16 + records.size * 16
  by_cases fits : length < USize.size
  · let fresh := zeroedBytes length
    let header := pushWordFast (pushWordFast ByteArray.empty records.size.toUInt64) 1
    let buffer := storeWord (storeWord fresh 0 records.size.toUInt64) 8 1
    have size : fresh.size = length := zeroedBytes_size _
    have key := storeWord_extends (prefixBytes := ByteArray.empty) (buffer := fresh)
      ⟨by simp, fun j h => by simp at h⟩
      (offset := 0) (USize.toNat_ofNat_of_lt_32 (by decide)) records.size.toUInt64
      (by rwa [size]) (by rw [size]; simp [length]; omega)
    have value := storeWord_extends key (offset := 8)
      (by simp only [pushWordFast_size, ByteArray.size_empty]; exact USize.toNat_ofNat_of_lt_32 (by decide)) 1
      (by simpa only [storeWord_size, size] using fits)
      (by simp only [pushWordFast_size, storeWord_size, size, ByteArray.size_empty]; simp [length])
    unfold encodeIndexed encodeV1
    dsimp only
    rw [ite_eq_right (show ¬ USize.size ≤ length by omega)]
    simp only [Array.forIn_pure_yield_eq_foldl, pure_bind, Id.run_pure]
    rw [Array.foldl_map, ← Array.foldl_toList, ← Array.foldl_toList]
    simp only [Array.size_map]
    have headerSize : header.size = 16 := by simp only [header, pushWordFast_size, ByteArray.size_empty]
    have start : (16 : USize).toNat = header.size := by
      rw [headerSize]
      exact USize.toNat_ofNat_of_lt_32 (by decide)
    have space : header.size + 16 * records.toList.length = buffer.size := by
      simp only [headerSize, buffer, storeWord_size, size, length, Array.length_toList]
      omega
    have bufferFits : buffer.size < USize.size := by simpa only [buffer, storeWord_size, size] using fits
    exact indexedFold records.toList header buffer 16 value start space bufferFits
  · have wide : USize.size ≤ length := by omega
    unfold encodeIndexed
    dsimp only
    rw [ite_eq_left wide]
    exact encodeScalar_eq_v1 records

end Alvoki
