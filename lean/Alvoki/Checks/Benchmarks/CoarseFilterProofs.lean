import Alvoki.Checks.Benchmarks.CoarseFilter
import Alvoki.Experiments.SSTable.Recursive.Image

namespace ImmutableSSTable.Recursive.CoarseFilter

open Alvoki (word)
open Alvoki.ByteWords
open Unified (Ref)

theorem MaskView.maybe_eq (view : MaskView) (key : ByteArray) (positive : 0 < view.logical.size) :
    view.maybe key = Bloom.mayContain view.logical key := by
  cases view with
  | decoded => rfl
  | packed bytes start =>
    unfold MaskView.maybe MaskView.logical Bloom.mayContain
    have size : (bytes.extract start bytes.size).size = bytes.size - start := by simp
    rw [size]
    have equal (p : Nat) (member : p ∈ Bloom.positions (bytes.size - start) key) :
        bytes[start + p / 8]!.toNat.testBit (p % 8) =
          Bloom.bit (bytes.extract start bytes.size) p := by
      have bound : p / 8 < (bytes.extract start bytes.size).size := by
        simp only [Bloom.positions, List.mem_map] at member
        obtain ⟨i, _, rfl⟩ := member
        have nonempty : 0 < bytes.size - start := by
          simpa [MaskView.logical, size] using positive
        rw [size]
        exact Nat.div_lt_of_lt_mul (Nat.mod_lt _ (by omega))
      unfold Bloom.bit
      let inPacket : start + p / 8 < bytes.size := ByteArray.getElem_extract_aux bound
      rw [getElem!_pos bytes _ inPacket, getElem!_pos (bytes.extract start bytes.size) _ bound,
          ByteArray.getElem_extract]
    apply Bool.eq_iff_iff.mpr
    simp only [List.all_eq_true]
    constructor
    · intro h p mem
      rw [← equal p mem]
      exact h p mem
    · intro h p mem
      rw [equal p mem]
      exact h p mem

theorem decodeRegion_encode (format : Representation) (ref : Ref)
    (upper : ByteArray) (first count total : Nat) (lower : Option ByteArray) (bits : ByteArray)
    (nonempty : 0 < count) (limits : count ≤ partitionRows ∧ first + count ≤ total)
    (indicesFit : first < UInt64.size)
    (lowerFits : (lower.elim 0 (fun key => key.size + 1)) < UInt64.size)
    (starts : lower = none ↔ first = 0) (fences : lower.all (· < upper) = true)
    (maskSize : bits.size = Bloom.bytesFor count) :
    ∃ decoded, decodeRegion format total ref ⟨upper, encodeRegion first count lower bits⟩ = .ok decoded ∧
      decoded.ref = ref ∧ decoded.first = first ∧ decoded.count = count ∧ decoded.lower = lower ∧
      decoded.upper = upper ∧ decoded.view.logical = bits := by
  let header := encodeWords (regionWords first count lower)
  let prefixBytes := lower.getD ByteArray.empty
  let payload := (header ++ prefixBytes) ++ bits
  let lowerLength := lower.elim 0 (fun key => key.size + 1)
  have headerSize : header.size = 24 := by simp [header, regionWords]
  have size : payload.size = 24 + prefixBytes.size + bits.size := by simp [payload, headerSize]
  have width (i : Nat) (inside : i < 3) :
      word payload (8 * i) = (regionWords first count lower)[i]'(by simpa [regionWords]) := by
    change word ((header ++ prefixBytes) ++ bits) (8 * i) = _
    rw [ByteArray.append_assoc, word_left header _ _ (by omega)]
    exact word_encodeWords (regionWords first count lower) i (by simpa [regionWords])
  have firstWord : (word payload 0).toNat = first := by
    rw [show word payload 0 = first.toUInt64 from width 0 (by decide)]
    exact UInt64.toNat_ofNat_of_lt' indicesFit
  have countWord : (word payload 8).toNat = count := by
    rw [show word payload 8 = count.toUInt64 from width 1 (by decide)]
    exact UInt64.toNat_ofNat_of_lt' (Nat.lt_of_le_of_lt limits.1 (by decide))
  have lowerWord : (word payload 16).toNat = lowerLength := by
    have same : (regionWords first count lower)[2]'(by simp [regionWords]) = lowerLength.toUInt64 := by
      cases lower <;> rfl
    rw [show word payload 16 = lowerLength.toUInt64 from (width 2 (by decide)).trans same]
    exact UInt64.toNat_ofNat_of_lt' lowerFits
  have beginMask : 24 + (lowerLength - 1) = (header ++ prefixBytes).size := by
    cases lower <;> simp [lowerLength, prefixBytes, headerSize]
  have lowerSlice : payload.extract 24 (24 + (lowerLength - 1)) = prefixBytes := by
    change ((header ++ prefixBytes) ++ bits).extract 24 (24 + (lowerLength - 1)) = _
    rw [beginMask, ByteArray.extract_append_size_left]
    exact ByteArray.extract_append_eq_right headerSize.symm (by simp)
  have maskSlice : payload.extract (24 + (lowerLength - 1)) payload.size = bits := by
    change ((header ++ prefixBytes) ++ bits).extract (24 + (lowerLength - 1))
      ((header ++ prefixBytes) ++ bits).size = _
    rw [beginMask]
    exact ByteArray.extract_append_eq_right rfl (by simp)
  have recovered : (if lowerLength = 0 then none else
      some (payload.extract 24 (24 + (lowerLength - 1)))) = lower := by
    cases lower with
    | none => simp [lowerLength]
    | some low =>
      have slice : payload.extract 24 (24 + low.size) = low := by
        simpa [lowerLength, prefixBytes] using lowerSlice
      simp [lowerLength, slice]
  have linkedStart : lowerLength = 0 ↔ first = 0 := by
    cases lower
    · have head := starts.mp rfl
      simp [lowerLength, head]
    · have interior : first ≠ 0 := fun zero => by simpa using (starts.mpr zero)
      simp [lowerLength, interior]
  have extent : 0 < count ∧ count ≤ partitionRows ∧ first + count ≤ total ∧
      24 + (lowerLength - 1) + Bloom.bytesFor count = payload.size := by
    refine ⟨nonempty, limits.1, limits.2, ?_⟩
    rw [beginMask, ← maskSize]
    simp [payload]
  have padded : 24 ≤ payload.size := by omega
  have recovered' : (if first = 0 then none else
      some (payload.extract 24 (24 + (lowerLength - 1)))) = lower := by
    simpa only [linkedStart] using recovered
  change ∃ decoded, decodeRegion format total ref ⟨upper, payload⟩ = .ok decoded ∧ _
  simp only [decodeRegion, padded, firstWord, countWord, lowerWord, extent, linkedStart,
    recovered', fences, ↓reduceIte, and_self]
  cases format
  · exact ⟨_, rfl, rfl, rfl, rfl, rfl, rfl, maskSlice⟩
  · exact ⟨_, rfl, rfl, rfl, rfl, rfl, rfl, maskSlice⟩

theorem packedWordBuild_onlyKey (rows : Array Entry) :
    BloomPlacement.packedWordBuild (rows.map onlyKey) = BloomPlacement.packedWordBuild rows := by
  unfold BloomPlacement.packedWordBuild
  rw [← Array.foldl_toList, ← Array.foldl_toList]
  simp [List.foldl_map, onlyKey]

/-- The serialized companion entry is the mask for one contiguous slice of
the primary writer's rows. This promise belongs in the paired producer Image. -/
def WireRegion (rows : List Entry) (entry : Entry) : Prop :=
  ∃ before : List Entry, ∃ part : Array Entry, ∃ after : List Entry,
    rows = before ++ part.toList ++ after ∧ 0 < part.size ∧ part.size ≤ partitionRows ∧
    part.back?.map Entry.key = some entry.key ∧
    (before.getLast?.map Entry.key |>.elim 0 (fun key => key.size + 1)) < UInt64.size ∧
    entry.value = encodeRegion before.length part.size (before.getLast?.map Entry.key)
      (BloomPlacement.packedWordBuild part)

/-- A proof-only association retained across cached queries. The masks are
private to a session holding the descriptor that supplied them. -/
def RegionBinding (rows : List Entry) (mask : CheckedMask) : Prop :=
  ∃ before : List Entry, ∃ part : Array Entry, ∃ after : List Entry,
    rows = before ++ part.toList ++ after ∧ mask.first = before.length ∧
    mask.count = part.size ∧ mask.lower = before.getLast?.map Entry.key ∧
    part.back?.map Entry.key = some mask.upper ∧ mask.view.logical = Bloom.build part

theorem WireRegion.admits {rows : List Entry} {entry : Entry}
    (wire : WireRegion rows entry) (ordered : Ordered rows) (limit : rows.length ≤ maxFileSize)
    (format : Representation) (ref : Ref) :
    ∃ decoded, decodeRegion format rows.length ref entry = .ok decoded ∧
      decoded.ref = ref ∧ RegionBinding rows decoded := by
  obtain ⟨before, part, after, joined, nonempty, partLimit, lastKey, lowerFits, payload⟩ := wire
  have ends : before.length + part.size ≤ rows.length := by rw [joined]; simp
  have fit : before.length < UInt64.size :=
    Nat.lt_of_le_of_lt (by omega : before.length ≤ maxFileSize) (by decide)
  let lower := before.getLast?.map Entry.key
  have starts : lower = none ↔ before.length = 0 := by simp [lower]
  have fences : lower.all (· < entry.key) = true := by
    obtain ⟨upper, last, key⟩ : ∃ upper, part.back? = some upper ∧ upper.key = entry.key := by
      cases found : part.back? with
      | none => simp [found] at lastKey
      | some old => exact ⟨old, rfl, by simpa [found] using lastKey⟩
    have upperMember : upper ∈ part.toList := by
      apply List.mem_of_getLast?
      simpa only [Array.getLast?_toList] using last
    rw [joined] at ordered
    cases prev : before.getLast? with
    | none => simp [lower, prev]
    | some previous =>
      -- Split at the cut between the prefix and the partition.
      have within : Ordered (before ++ part.toList) :=
        (List.pairwise_append.mp ordered).1
      have earlier := within.rel_of_mem_append (List.mem_of_getLast? prev) upperMember
      simpa [lower, prev, key] using earlier
  have wordFits : 8 * Bloom.bytesFor part.size < UInt64.size := by
    unfold Bloom.bytesFor partitionRows at *
    have : UInt64.size = 18446744073709551616 := rfl
    omega
  have buildEq := BloomPlacement.packedWordBuild_eq part wordFits
  rw [buildEq] at payload
  obtain ⟨decoded, admitted, whereAt, first, count, decodedLower, upper, bits⟩ :=
    decodeRegion_encode format ref entry.key before.length part.size rows.length lower (Bloom.build part)
      nonempty ⟨partLimit, ends⟩ fit lowerFits starts fences (Bloom.build_size part)
  have exactEntry : Entry.mk entry.key (encodeRegion before.length part.size lower (Bloom.build part)) = entry :=
    by cases entry; congr 1; exact payload.symm
  rw [exactEntry] at admitted
  rw [← upper] at lastKey
  exact ⟨decoded, admitted, whereAt, before, part, after, joined, first, count, decodedLower, lastKey, bits⟩

theorem RegionBinding.accepts (binding : RegionBinding rows mask) (ordered : Ordered rows)
    (row : Entry) (member : row ∈ rows) (covered : mask.covers row.key = true) :
    mask.view.maybe row.key = true := by
  obtain ⟨before, part, after, joined, _, _, lower, upper, bits⟩ := binding
  have positive : 0 < mask.view.logical.size := by rw [bits, Bloom.build_size]; unfold Bloom.bytesFor; omega
  rw [MaskView.maybe_eq _ _ positive, bits]
  apply Bloom.build_covers
  have upperBound : row.key ≤ mask.upper := by
    simpa [CheckedMask.covers] using (Bool.and_eq_true_iff.mp covered).2
  have lowerBound : mask.lower.all (· < row.key) = true := (Bool.and_eq_true_iff.mp covered).1
  rw [joined] at member ordered
  rcases List.mem_append.mp member with earlier | later
  · rcases List.mem_append.mp earlier with prior | here
    · cases prev : before.getLast? with
      | none => simp [List.getLast?_eq_none_iff.mp prev] at prior
      | some previous =>
        have greater : previous.key < row.key := by simpa [lower, prev] using lowerBound
        obtain ⟨head, shape⟩ := List.getLast?_eq_some_iff.mp prev
        rw [shape] at prior
        rcases List.mem_append.mp prior with inHead | last
        · have orderedBefore : Ordered (head ++ [previous]) := by
            simpa only [Ordered, shape] using (List.pairwise_append.mp (List.pairwise_append.mp ordered).1).1
          have less := orderedBefore.rel_of_mem_append inHead (by simp : previous ∈ [previous])
          exact False.elim (Std.not_lt_of_ge (Std.le_of_lt less) greater)
        · simp at last
          subst row
          exact False.elim (Std.lt_irrefl greater)
    · exact here
  · obtain ⟨fence, key, mem⟩ : ∃ fence, fence.key = mask.upper ∧ fence ∈ part.toList := by
      cases found : part.back? with
      | none => simp [found] at upper
      | some fence =>
        have key : fence.key = mask.upper := by simpa [found] using upper
        have member : fence ∈ part.toList :=
          List.mem_of_getLast? (by simpa only [Array.getLast?_toList] using found)
        exact ⟨fence, key, member⟩
    have greater := ordered.rel_of_mem_append (List.mem_append.mpr (.inr mem)) later
    rw [key] at greater
    exact False.elim (Std.not_lt_of_ge upperBound greater)

/-- A checked load from the immutable companion image locates the exact
serialized entry in the exact data packet used to admit the mask. -/
theorem load_binding {filters : Handle (EStateM String σ)}
    (observed : filters.Observes image filterRows)
    (orderedFilters : Ordered filterRows) (orderedRows : Ordered rows)
    (regions : ∀ entry ∈ filterRows, WireRegion rows entry) (limit : rows.length ≤ maxFileSize)
    (success : load filters format rows.length query start = .ok (some mask) reached) :
    ∃ ref data index entry, filters.locate query = pure (some (ref, data, index)) ∧
      data.readRow index = .ok entry ∧ mask.ref = ref ∧ RegionBinding rows mask := by
  obtain ⟨i, lowerBound⟩ := Unified.exists_lowerBound orderedFilters query
  by_cases inside : i < filterRows.length
  · obtain ⟨ref, data, route, _, read⟩ := observed.locate lowerBound inside
    obtain ⟨decoded, parsed, boundRef, binding⟩ :=
      (regions filterRows[i] (by simp)).admits orderedRows limit format ref
    have schedule : load filters format rows.length query =
        if decoded.covers query then pure (some decoded)
        else throw "key routed outside its coarse filter interval" := by
      simp only [load, route, pure_bind, read, parsed, liftDecode]
      split <;> rfl
    rw [schedule] at success
    split at success
    · cases success
      exact ⟨ref, data, i - ref.firstRow, filterRows[i], route, read, boundRef, binding⟩
    · cases success
  · have atEnd : i = filterRows.length := by have := lowerBound.1; omega
    subst i
    have route : filters.locate query = pure none := by
      simp [Handle.locate, observed.root.noKey lowerBound]
    simp [load, route] at success
    cases success

theorem load_locate_error {filters : Handle (EStateM String σ)}
    (failed : filters.locate query start = .error error reached) :
    load filters format count query start = .error error reached := by
  simp [load, Bind.bind, EStateM.bind, failed]

theorem RegionBinding.excludes (binding : RegionBinding rows mask) (ordered : Ordered rows)
    (covered : mask.covers key = true) (negative : mask.view.maybe key = false) :
    Contents.lookup rows key = none := by
  have absent : (rows.find? fun row => row.key == key) = none := by
    apply List.find?_eq_none.mpr
    intro row member
    intro hit
    have same := beq_iff_eq.mp hit
    have positive := binding.accepts ordered row member (by simpa only [same] using covered)
    rw [same, negative] at positive
    contradiction
  simp [Contents.lookup, absent]

/-- The resident mask has already been admitted by a checked load for the
same immutable session. The negative fast path is pure and keeps that session. -/
theorem Session.probe_resident_negative [Monad m] [LawfulMonad m] [MonadExceptOf String m]
    {session : Session m} (cached : session.resident.masks.find? (·.covers key) = some mask)
    (negative : mask.view.maybe key = false) :
    session.probe key = pure (⟨none, true, some false⟩, session) := by
  simp [Session.probe, cached, negative]

/-- Replacing the latest mask keeps the byte budget and each retained mask's
binding to the same primary rows. The load theorem supplies the incoming binding. -/
theorem Resident.latest_preserves (resident : Resident) (limit : Nat) (incoming : CheckedMask)
    (fits : resident.bytes ≤ limit)
    (old : ∀ mask ∈ resident.masks, RegionBinding rows mask)
    (fresh : RegionBinding rows incoming) :
    let state := resident.latest limit incoming
    state.bytes ≤ limit ∧ ∀ mask ∈ state.masks, RegionBinding rows mask := by
  unfold Resident.latest
  split
  · rename_i admitted
    refine ⟨admitted, ?_⟩
    intro mask member
    have same : mask = incoming := by simpa using member
    simpa only [same] using fresh
  · exact ⟨fits, old⟩

theorem Session.probe_resident_correct [Monad m] [LawfulMonad m] [MonadExceptOf String m]
    {session : Session m} (primary : session.base.table.Represents rows)
    (bound : ∀ mask ∈ session.resident.masks, RegionBinding rows mask)
    (cached : session.resident.masks.find? (·.covers key) = some mask) :
    session.probe key =
      pure (⟨Contents.lookup rows key, true, some (mask.view.maybe key)⟩, session) := by
  cases bit : mask.view.maybe key
  · have selected := Array.mem_of_find?_eq_some cached
    have excludes := (bound mask selected).excludes primary.ordered (Array.find?_some (p := fun item : CheckedMask => item.covers key) cached) bit
    rw [excludes, Session.probe_resident_negative cached bit]
  · have value : session.base.lookup key = pure (Contents.lookup rows key) := primary.lookup key
    simp [Session.probe, cached, bit, value]

end ImmutableSSTable.Recursive.CoarseFilter
