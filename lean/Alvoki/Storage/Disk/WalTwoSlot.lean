import Alvoki.Storage.Disk.WalBoundary
import Alvoki.Storage.Disk.WalOrderedTwoSlot

namespace Alvoki.WAL.TwoSlot

open Alvoki.ByteWords

def stride : Nat := 4096
def containerSize : Nat := 2 * stride

private def magic : UInt64 := 0x32544f4c534c4157

structure Selection where
  slot : Nat
  epoch : UInt64
  frontier : UInt64
  deriving DecidableEq

def Selection.encode (selected : Selection) : ByteArray :=
  let fields := [magic, selected.slot.toUInt64, selected.epoch, selected.frontier]
  encodeWords (fields ++ [checksumWords fields])

def initialSelection : Selection := ⟨0, 0, 0⟩

def initial : ByteArray :=
  initialSelection.encode ++ ⟨Array.replicate (containerSize - 40) 0⟩

def decodeSlot (bytes : ByteArray) (slot : Nat) : Option Selection := do
  let offset := slot * stride
  let epoch := word bytes (offset + 16)
  let frontier := word bytes (offset + 24)
  let fields := [magic, slot.toUInt64, epoch, frontier]
  if word bytes offset == magic && word bytes (offset + 8) == slot.toUInt64 &&
      word bytes (offset + 32) == checksumWords fields && epoch.toNat % 2 == slot &&
      frontier.toNat % frameSize == 0 && epoch.toNat ≤ frontier.toNat / frameSize then
    return ⟨slot, epoch, frontier⟩
  else
    none

/-- A complete, well-formed encoding at the reported byte offset is
accepted as that exact record. The bytes of the other slot are irrelevant. -/
theorem decodeSlot_exact {bytes : ByteArray} (selected : Selection)
    (inside : selected.slot * stride + 40 ≤ bytes.size)
    (written : bytes.extract (selected.slot * stride) (selected.slot * stride + 40) = selected.encode)
    (parity : selected.epoch.toNat % 2 = selected.slot)
    (aligned : selected.frontier.toNat % frameSize = 0)
    (counts : selected.epoch.toNat ≤ selected.frontier.toNat / frameSize) :
    decodeSlot bytes selected.slot = some selected := by
  let fields := [magic, selected.slot.toUInt64, selected.epoch, selected.frontier]
  let words := fields ++ [checksumWords fields]
  have lane (i : Nat) (small : i < 5) :
      word bytes (selected.slot * stride + 8 * i) = words[i]! := by
    have exactWord := word_extract bytes (selected.slot * stride)
      (selected.slot * stride + 40) (8 * i) (by omega) inside
    rw [written] at exactWord
    have bounded : i < words.length := by simpa [words, fields] using small
    rw [getElem!_pos words i bounded]
    exact exactWord.symm.trans (word_encodeWords words i bounded)
  have tag : word bytes (selected.slot * stride) = magic := by simpa [words, fields] using lane 0 (by decide)
  have slot : word bytes (selected.slot * stride + 8) = selected.slot.toUInt64 := by
    simpa [words, fields] using lane 1 (by decide)
  have epoch : word bytes (selected.slot * stride + 16) = selected.epoch := by
    simpa [words, fields] using lane 2 (by decide)
  have frontier : word bytes (selected.slot * stride + 24) = selected.frontier := by
    simpa [words, fields] using lane 3 (by decide)
  have checksum : word bytes (selected.slot * stride + 32) = checksumWords fields := by
    simpa [words, fields] using lane 4 (by decide)
  cases selected
  simp_all [decodeSlot, fields, pure]

/-- A positional write in the other slot's range preserves every byte
observed by the active decoder. This is the byte-range consequence of the
write report. Crash failure isolation remains a storage premise. -/
theorem decodeSlot_unchanged {before after : ByteArray} {slot : Nat} (valid : slot < 2)
    (unchanged : ∀ position, (position < (1 - slot) * stride ∨ (1 - slot) * stride + 40 ≤ position) →
      after.get! position = before.get! position) :
    decodeSlot after slot = decodeSlot before slot := by
  have sameWord (offset : Nat) (small : offset ≤ 32) :
      word after (slot * stride + offset) = word before (slot * stride + offset) := by
    have sameByte (lane : Nat) (inWord : lane ≤ 7) :
        after.get! (slot * stride + offset + lane) = before.get! (slot * stride + offset + lane) := by
      apply unchanged
      have slots : slot = 0 ∨ slot = 1 := by omega
      rcases slots with rfl | rfl <;> simp [stride] at * <;> omega
    simp only [word, joinBytes, sameByte 0 (by decide), sameByte 1 (by decide),
      sameByte 2 (by decide), sameByte 3 (by decide), sameByte 4 (by decide),
      sameByte 5 (by decide), sameByte 6 (by decide), sameByte 7 (by decide)]
  have magicWord : word after (slot * stride) = word before (slot * stride) := by
    simpa using sameWord 0 (by decide)
  simp only [decodeSlot, magicWord, sameWord 8 (by decide), sameWord 16 (by decide),
    sameWord 24 (by decide), sameWord 32 (by decide)]

/-- Select the latest valid slot. Two valid slots must be consecutive and
advance the frontier. Validation of the selected WAL is the caller's
responsibility, with no fallback if the selected WAL is invalid. -/
private def select (left right : Option Selection) : Except String Selection :=
  match left, right with
  | none, none => .error "no valid two-slot WAL marker"
  | some selected, none | none, some selected => .ok selected
  | some zero, some one =>
    let (older, newer) := if zero.epoch < one.epoch then (zero, one) else (one, zero)
    if older.epoch.toNat + 1 = newer.epoch.toNat ∧ older.frontier < newer.frontier then
      .ok newer
    else
      .error "inconsistent two-slot WAL markers"

def decode (bytes : ByteArray) : Except String Selection :=
  if bytes.size == containerSize then
    select (decodeSlot bytes 0) (decodeSlot bytes 1)
  else
    .error "invalid two-slot WAL marker length"

/-- The bytes published at bootstrap select an empty WAL. -/
theorem decode_initial : decode initial = .ok initialSelection := by
  let padding : ByteArray := ⟨Array.replicate (containerSize - 40) 0⟩
  have encodedSize : initialSelection.encode.size = 40 := by
    simp [Selection.encode]
  have paddingSize : padding.size = containerSize - 40 := by
    change (Array.replicate (containerSize - 40) (0 : UInt8)).size = _
    simp
  have joined : initial = initialSelection.encode ++ padding := rfl
  have size : initial.size = containerSize := by
    rw [joined, ByteArray.size_append, encodedSize, paddingSize]
    decide
  have encodedPrefix : initial.extract 0 40 = initialSelection.encode := by
    rw [joined, ByteArray.extract_append_eq_left encodedSize.symm]
  have first : decodeSlot initial 0 = some initialSelection :=
    decodeSlot_exact initialSelection (by rw [size]; decide) encodedPrefix (by decide) (by decide) (by decide)
  have zeroByte (offset : Nat) (within : offset < padding.size) : padding.get! offset = 0 := by
    rw [getBang_eq_index, getElem!_pos padding offset within]
    exact Array.getElem_replicate _
  have zeroWord : word padding (stride - 40) = 0 := by
    simp only [word, joinBytes]
    repeat rw [zeroByte _ (by rw [paddingSize]; decide)]
    decide
  have otherWord : word initial stride = 0 := by
    rw [joined, ← zeroWord]
    have offset : stride = initialSelection.encode.size + (stride - 40) := by rw [encodedSize]; decide
    refine (congrArg (word (initialSelection.encode ++ padding)) offset).trans ?_
    exact word_right _ _ _ (by rw [paddingSize]; decide)
  have second : decodeSlot initial 1 = none := by
    simp [decodeSlot, otherWord, magic]
  simp [decode, size, first, second, select]

private theorem decodeSlot_valid {bytes : ByteArray} {slot : Nat} {selected : Selection}
    (accepted : decodeSlot bytes slot = some selected) :
    selected.slot = slot ∧ selected.epoch.toNat % 2 = slot ∧
      selected.frontier.toNat % frameSize = 0 ∧
      selected.epoch.toNat ≤ selected.frontier.toNat / frameSize := by
  unfold decodeSlot at accepted
  dsimp only at accepted
  split at accepted
  · rename_i checked
    have fields := Option.some.inj accepted
    subst selected
    simp_all
  · contradiction

private theorem selectedSlot {left right : Option Selection} {selected : Selection}
    (accepted : select left right = .ok selected) : left = some selected ∨ right = some selected := by
  cases left <;> cases right <;> simp_all [select]
  rename_i a b
  by_cases order : a.epoch < b.epoch <;> simp only [order, ite_true, ite_false] at accepted
  · split at accepted <;> simp_all
  · split at accepted <;> simp_all

/-- Successful decode identifies the physical slot containing the record
and supplies the format invariants required to make a successor. -/
theorem decode_valid {bytes : ByteArray} {selected : Selection} (accepted : decode bytes = .ok selected) :
    decodeSlot bytes selected.slot = some selected ∧ selected.slot < 2 ∧
      selected.epoch.toNat % 2 = selected.slot ∧ selected.frontier.toNat % frameSize = 0 ∧
      selected.epoch.toNat ≤ selected.frontier.toNat / frameSize := by
  unfold decode at accepted
  split at accepted
  · rcases selectedSlot accepted with first | second
    · obtain ⟨slot, parity, aligned, count⟩ := decodeSlot_valid first
      exact ⟨slot ▸ first, by rw [slot]; decide, slot ▸ parity, aligned, count⟩
    · obtain ⟨slot, parity, aligned, count⟩ := decodeSlot_valid second
      exact ⟨slot ▸ second, by rw [slot]; decide, slot ▸ parity, aligned, count⟩
  · contradiction

/-- Read one byte beyond the fixed container to witness oversized files. -/
abbrev acquisitionLimit : Nat := containerSize + 1

theorem decode_acquisitionPrefix (bytes : ByteArray) :
    decode (bytes.extract 0 (min acquisitionLimit bytes.size)) = decode bytes := by
  by_cases covered : bytes.size ≤ acquisitionLimit
  · simp [Nat.min_eq_right covered]
  · have original : bytes.size ≠ containerSize := by
      unfold acquisitionLimit at covered
      omega
    have capped : min acquisitionLimit bytes.size ≠ containerSize := by
      rw [Nat.min_eq_left (Nat.le_of_not_ge covered)]
      simp [acquisitionLimit]
    simp [decode, original, capped]

def Selection.toRecord (selected : Selection) :
    Alvoki.WAL.OrderedTwoSlot.Record UInt64 :=
  ⟨selected.epoch.toNat, selected.frontier⟩

/-- Every concrete selection accepted by the consistency checks agrees with
the protocol's latest-record rule. -/
private theorem select_agrees_with_protocol {left right : Option Selection} {chosen : Selection}
    (h : select left right = .ok chosen) :
    Alvoki.WAL.OrderedTwoSlot.selectNewest
      (left.map Selection.toRecord) (right.map Selection.toRecord) = .ok chosen.toRecord := by
  cases left <;> cases right <;>
    simp_all [select, Alvoki.WAL.OrderedTwoSlot.selectNewest, Selection.toRecord]
  next zero one =>
    by_cases lt : zero.epoch.toNat < one.epoch.toNat
    · have ltWord : zero.epoch < one.epoch := lt
      simp only [ltWord, lt, ite_true] at *
      split at h <;> simp_all
    · have nltWord : ¬zero.epoch < one.epoch := lt
      simp only [nltWord, lt, ite_false] at *
      split at h
      · rename_i valid
        have ltNat : one.epoch.toNat < zero.epoch.toNat := by omega
        simp_all
      · simp_all

/-- A successful decode chooses the abstract protocol's newest record. -/
theorem decode_agrees_with_protocol {bytes : ByteArray} {chosen : Selection}
    (h : decode bytes = .ok chosen) :
    Alvoki.WAL.OrderedTwoSlot.selectNewest
      ((decodeSlot bytes 0).map Selection.toRecord)
      ((decodeSlot bytes 1).map Selection.toRecord) = .ok chosen.toRecord := by
  unfold decode at h
  split at h
  · exact select_agrees_with_protocol h
  · contradiction

def slotIndex : OrderedTwoSlot.Slot → Nat
  | .first => 0
  | .second => 1

def decodedSlots (bytes : ByteArray) : OrderedTwoSlot.Slots UInt64 :=
  fun slot => (decodeSlot bytes (slotIndex slot)).map Selection.toRecord

/-- A successful decode supplies the active record and proves every
other decodable record has an older epoch. -/
theorem decodedSlots_active {bytes : ByteArray} {current : Selection}
    (accepted : decode bytes = .ok current) (active : OrderedTwoSlot.Slot)
    (offset : current.slot = slotIndex active) :
    decodedSlots bytes active = some current.toRecord ∧
      ∀ stale, decodedSlots bytes active.other = some stale → stale.epoch < current.toRecord.epoch := by
  have found := (decode_valid accepted).1
  rw [offset] at found
  have currentRead : decodedSlots bytes active = some current.toRecord :=
    congrArg (Option.map Selection.toRecord) found
  have latest := decode_agrees_with_protocol accepted
  change OrderedTwoSlot.selectNewest (decodedSlots bytes .first) (decodedSlots bytes .second) =
    .ok current.toRecord at latest
  refine ⟨currentRead, ?_⟩
  intro stale other
  cases active with
  | first =>
    change decodedSlots bytes .second = some stale at other
    rw [currentRead, other] at latest
    simp only [OrderedTwoSlot.selectNewest] at latest
    split at latest
    · rename_i order
      have eq := congrArg OrderedTwoSlot.Record.epoch (Except.ok.inj latest)
      omega
    · split at latest
      · assumption
      · contradiction
  | second =>
    change decodedSlots bytes .first = some stale at other
    rw [currentRead, other] at latest
    simp only [OrderedTwoSlot.selectNewest] at latest
    split at latest
    · assumption
    · split at latest
      · rename_i order
        have eq := congrArg OrderedTwoSlot.Record.epoch (Except.ok.inj latest)
        omega
      · contradiction

private theorem decodedSlots_eq_writeTarget {before after : ByteArray}
    (active : OrderedTwoSlot.Slot)
    (unchanged : ∀ position,
      (position < slotIndex active.other * stride ∨ slotIndex active.other * stride + 40 ≤ position) →
        after.get! position = before.get! position) :
    OrderedTwoSlot.writeTarget (decodedSlots before) active
      (decodedSlots after active.other) = decodedSlots after := by
  have preserved : decodedSlots after active = decodedSlots before active := by
    have bounded : slotIndex active < 2 := by cases active <;> decide
    have offset : slotIndex active.other = 1 - slotIndex active := by cases active <;> rfl
    rw [offset] at unchanged
    exact congrArg (Option.map Selection.toRecord) (decodeSlot_unchanged bounded unchanged)
  funext slot
  have choices : slot = active ∨ slot = active.other := by cases active <;> cases slot <;> decide
  rcases choices with rfl | rfl
  · rw [OrderedTwoSlot.writeTarget_keepsActive, preserved]
  · exact OrderedTwoSlot.writeTarget_updatesOther ..

/-- Project a raw inactive-slot update to the crash protocol. The storage
premises are byte isolation outside the target and an old, invalid, or
exact-new decode at the target. -/
theorem uncertainSurvivor_of_bytes {before after : ByteArray}
    (active : OrderedTwoSlot.Slot) (next : Selection)
    (unchanged : ∀ position,
      (position < slotIndex active.other * stride ∨ slotIndex active.other * stride + 40 ≤ position) →
        after.get! position = before.get! position)
    (target : decodedSlots after active.other = decodedSlots before active.other ∨
      decodedSlots after active.other = none ∨ decodedSlots after active.other = some next.toRecord) :
    OrderedTwoSlot.Survivor (decodedSlots before) active next.toRecord .slotWriteUncertain
      (decodedSlots after) := by
  rw [← decodedSlots_eq_writeTarget active unchanged]
  rcases target with old | invalid | exactNew
  · rw [old]
    exact .uncertainOld
  · rw [invalid]
    exact .uncertainInvalid
  · rw [exactNew]
    exact .uncertainNew

/-- A successful slot sync supplies the exact target bytes in the admitted
crash image. Decode them using the ordinary codec roundtrip. -/
theorem syncedSurvivor_of_bytes {before after : ByteArray}
    (active : OrderedTwoSlot.Slot) (next : Selection)
    (targetSlot : next.slot = slotIndex active.other)
    (unchanged : ∀ position,
      (position < next.slot * stride ∨ next.slot * stride + 40 ≤ position) →
        after.get! position = before.get! position)
    (inside : next.slot * stride + 40 ≤ after.size)
    (written : after.extract (next.slot * stride) (next.slot * stride + 40) = next.encode)
    (parity : next.epoch.toNat % 2 = next.slot)
    (aligned : next.frontier.toNat % frameSize = 0)
    (counts : next.epoch.toNat ≤ next.frontier.toNat / frameSize) :
    OrderedTwoSlot.Survivor (decodedSlots before) active next.toRecord .slotSynced
      (decodedSlots after) := by
  have complete := decodeSlot_exact next inside written parity aligned counts
  have target : decodedSlots after active.other = some next.toRecord := by
    simp [decodedSlots, ← targetSlot, complete]
  rw [targetSlot] at unchanged
  rw [← decodedSlots_eq_writeTarget active unchanged, target]
  exact .synced

def advance (before : Selection) (frontier : Nat) : Except String Selection := do
  unless before.epoch.toNat + 1 < UInt64.size do throw "two-slot WAL marker epoch exhausted"
  unless before.frontier.toNat < frontier && frontier < UInt64.size && frontier % frameSize == 0 do
    throw "invalid next two-slot WAL frontier"
  return ⟨1 - before.slot, (before.epoch.toNat + 1).toUInt64, frontier.toUInt64⟩

/-- A prepared write advances the epoch and targets the opposite record. -/
theorem advance_fields {before next : Selection} {frontier : Nat}
    (step : advance before frontier = .ok next) :
    next.slot = 1 - before.slot ∧ next.epoch.toNat = before.epoch.toNat + 1 ∧
      next.frontier.toNat = frontier ∧ before.frontier < next.frontier ∧
      next.frontier.toNat % frameSize = 0 := by
  by_cases room : before.epoch.toNat + 1 < UInt64.size
  · by_cases bounds : before.frontier.toNat < frontier ∧ frontier < UInt64.size ∧
        frontier % frameSize = 0
    · obtain ⟨increases, fits, aligned⟩ := bounds
      simp [advance, room, increases, fits, aligned, Pure.pure, Except.pure] at step
      subst next
      have epochExact : (before.epoch.toNat + 1).toUInt64.toNat = before.epoch.toNat + 1 := by
        exact Nat.mod_eq_of_lt room
      have lengthExact : frontier.toUInt64.toNat = frontier := Nat.mod_eq_of_lt fits
      have increasesWord : before.frontier < frontier.toUInt64 := by
        change before.frontier.toNat < frontier.toUInt64.toNat
        rwa [lengthExact]
      exact ⟨rfl, epochExact, lengthExact, increasesWord, by simpa [lengthExact] using aligned⟩
    · simp [advance, room, bounds, and_assoc, throw, throwThe,
        MonadExceptOf.throw, Bind.bind, Except.bind] at step
  · simp [advance, room, throw, throwThe,
      MonadExceptOf.throw, Bind.bind, Except.bind] at step

/-- Advancing a valid marker gives a valid slot index and an epoch bounded
by the number of frames. The absolute frontier grows by at least one frame. -/
theorem advance_valid {before next : Selection} {frontier : Nat}
    (step : advance before frontier = .ok next)
    (parity : before.epoch.toNat % 2 = before.slot)
    (aligned : before.frontier.toNat % frameSize = 0)
    (counts : before.epoch.toNat ≤ before.frontier.toNat / frameSize) :
    next.epoch.toNat % 2 = next.slot ∧ next.frontier.toNat % frameSize = 0 ∧
      next.epoch.toNat ≤ next.frontier.toNat / frameSize := by
  obtain ⟨slot, epoch, _, increases, nextAligned⟩ := advance_fields step
  change before.frontier.toNat < next.frontier.toNat at increases
  unfold frameSize at *
  exact ⟨by omega, nextAligned, by omega⟩

/-- A complete successor and the preserved older slot admit the complete new
frontier, regardless of which offset was updated. -/
theorem decode_newer {bytes : ByteArray} {before next : Selection}
    (size : bytes.size = containerSize)
    (epoch : before.epoch.toNat + 1 = next.epoch.toNat)
    (frontier : before.frontier < next.frontier)
    (slots : (decodeSlot bytes 0 = some before ∧ decodeSlot bytes 1 = some next) ∨
      (decodeSlot bytes 0 = some next ∧ decodeSlot bytes 1 = some before)) :
    decode bytes = .ok next := by
  have newer : before.epoch < next.epoch := by
    change before.epoch.toNat < next.epoch.toNat
    omega
  rcases slots with ⟨zero, one⟩ | ⟨zero, one⟩
  · simp [decode, size, zero, one, select, newer, epoch, frontier]
  · have notOlder : ¬next.epoch < before.epoch := by
      change ¬next.epoch.toNat < before.epoch.toNat
      omega
    simp [decode, size, zero, one, select, notOlder, epoch, frontier]

/-- With a complete container and an isolated active slot, every admitted
inactive-slot outcome decodes. The old outcome reuses the previous accepted
container's consistency check. The invalid outcome uses only the active slot. -/
theorem decode_interruptedWrite {before after : ByteArray} {active : OrderedTwoSlot.Slot}
    {current next : Selection}
    (prior : decode before = .ok current)
    (size : after.size = containerSize)
    (observed : decodeSlot before (slotIndex active) = some current)
    (unchanged : ∀ position,
      (position < slotIndex active.other * stride ∨ slotIndex active.other * stride + 40 ≤ position) →
        after.get! position = before.get! position)
    (target : decodeSlot after (slotIndex active.other) = decodeSlot before (slotIndex active.other) ∨
      decodeSlot after (slotIndex active.other) = none ∨
      decodeSlot after (slotIndex active.other) = some next)
    (epoch : current.epoch.toNat + 1 = next.epoch.toNat)
    (frontier : current.frontier < next.frontier) :
    decode after = .ok current ∨ decode after = .ok next := by
  have bounded : slotIndex active < 2 := by cases active <;> decide
  have offset : slotIndex active.other = 1 - slotIndex active := by cases active <;> rfl
  rw [offset] at unchanged
  have kept := decodeSlot_unchanged bounded unchanged
  rcases target with old | invalid | written
  · left
    have previousSize : before.size = containerSize := by
      by_cases h : before.size = containerSize
      · exact h
      · simp [decode, h] at prior
    cases active <;> simp only [slotIndex, OrderedTwoSlot.Slot.other] at kept old <;>
      simpa [decode, size, previousSize, kept, old] using prior
  · left
    cases active <;> simp_all [slotIndex, OrderedTwoSlot.Slot.other, decode, select]
  · right
    apply decode_newer size epoch frontier
    cases active with
    | first => exact .inl ⟨kept.trans observed, written⟩
    | second => exact .inr ⟨written, kept.trans observed⟩

/-- Exact bytes at the synced target and an isolated active slot suffice
for the native decoder to accept the just-published successor. -/
theorem decode_syncedWrite {before after : ByteArray} {active : OrderedTwoSlot.Slot}
    {current next : Selection}
    (size : after.size = containerSize)
    (observed : decodeSlot before (slotIndex active) = some current)
    (targetSlot : next.slot = slotIndex active.other)
    (unchanged : ∀ position,
      (position < next.slot * stride ∨ next.slot * stride + 40 ≤ position) →
        after.get! position = before.get! position)
    (inside : next.slot * stride + 40 ≤ after.size)
    (written : after.extract (next.slot * stride) (next.slot * stride + 40) = next.encode)
    (parity : next.epoch.toNat % 2 = next.slot)
    (aligned : next.frontier.toNat % frameSize = 0)
    (counts : next.epoch.toNat ≤ next.frontier.toNat / frameSize)
    (epoch : current.epoch.toNat + 1 = next.epoch.toNat)
    (frontier : current.frontier < next.frontier) :
    decode after = .ok next := by
  have target := decodeSlot_exact next inside written parity aligned counts
  rw [targetSlot] at target unchanged
  have bounded : slotIndex active < 2 := by cases active <;> decide
  have offset : slotIndex active.other = 1 - slotIndex active := by cases active <;> rfl
  rw [offset] at unchanged
  have kept := (decodeSlot_unchanged bounded unchanged).trans observed
  apply decode_newer size epoch frontier
  cases active with
  | first => exact .inl ⟨kept, target⟩
  | second => exact .inr ⟨target, kept⟩

/-- A successful advance from an accepted container decodes as the new
selection once its encoded bytes are durable and the other slot is intact. -/
theorem decode_afterAdvance {before after : ByteArray} {current next : Selection} {frontier : Nat}
    (prior : decode before = .ok current) (advanced : advance current frontier = .ok next)
    (size : after.size = containerSize)
    (unchanged : ∀ position,
      (position < next.slot * stride ∨ next.slot * stride + 40 ≤ position) →
        after.get! position = before.get! position)
    (written : after.extract (next.slot * stride) (next.slot * stride + 40) = next.encode) :
    decode after = .ok next := by
  obtain ⟨found, bounded, oldParity, oldAligned, oldCounts⟩ := decode_valid prior
  obtain ⟨slot, epoch, _, increases, _⟩ := advance_fields advanced
  obtain ⟨parity, aligned, counts⟩ := advance_valid advanced oldParity oldAligned oldCounts
  have inside : next.slot * stride + 40 ≤ after.size := by
    rw [size, slot]
    change (1 - current.slot) * 4096 + 40 ≤ 8192
    omega
  obtain initial | alternate : current.slot = 0 ∨ current.slot = 1 := by omega
  · apply decode_syncedWrite (active := .first) size (by simpa only [initial, slotIndex] using found)
      (by simp [initial, slot, slotIndex, OrderedTwoSlot.Slot.other]) unchanged inside written
      parity aligned counts epoch.symm increases
  · apply decode_syncedWrite (active := .second) size (by simpa only [alternate, slotIndex] using found)
      (by simp [alternate, slot, slotIndex, OrderedTwoSlot.Slot.other]) unchanged inside written
      parity aligned counts epoch.symm increases

/-- The native marker decoder and WAL boundary reader agree on the exact
batch prefix when a crash interrupts an isolated inactive-slot update.
The WAL barrier supplies the whole encoded batch before the slot write. -/
theorem interruptedBytes_selectBatch
    {before after physical : ByteArray} {active : OrderedTwoSlot.Slot} {current next : Selection}
    {history batch : List WAL.Write}
    (prior : decode before = .ok current)
    (activeOffset : current.slot = slotIndex active)
    (advanced : advance current (WAL.encode (history ++ batch)).size = .ok next)
    (size : after.size = containerSize)
    (unchanged : ∀ position,
      (position < slotIndex active.other * stride ∨ slotIndex active.other * stride + 40 ≤ position) →
        after.get! position = before.get! position)
    (target : decodeSlot after (slotIndex active.other) = decodeSlot before (slotIndex active.other) ∨
      decodeSlot after (slotIndex active.other) = none ∨
      decodeSlot after (slotIndex active.other) = some next)
    (oldCount : current.frontier.toNat = (WAL.encode history).size)
    (durable : ∃ tail, physical = WAL.encode (history ++ batch) ++ tail) :
    ∃ chosen events, decode after = .ok chosen ∧
      (events = history ∨ events = history ++ batch) ∧
      Boundary.select chosen.frontier physical = .ok (WAL.encode events) := by
  obtain ⟨tail, rfl⟩ := durable
  have observed := (decode_valid prior).1
  rw [activeOffset] at observed
  obtain ⟨_, epoch, nextCount, increasing, _⟩ := advance_fields advanced
  rcases decode_interruptedWrite prior size observed unchanged target epoch.symm increasing with old | new
  · refine ⟨current, history, old, .inl rfl, ?_⟩
    have fits : (WAL.encode history).size < UInt64.size := by
      rw [← oldCount]
      exact current.frontier.toNat_lt
    have count : current.frontier = (WAL.encode history).size.toUInt64 := by
      rw [← oldCount]
      simp
    rw [count, WAL.encode_append, ByteArray.append_assoc]
    exact Boundary.select_encoded history _ fits
  · refine ⟨next, history ++ batch, new, .inr rfl, ?_⟩
    have fits : (WAL.encode (history ++ batch)).size < UInt64.size := by
      rw [← nextCount]
      exact next.frontier.toNat_lt
    have count : next.frontier = (WAL.encode (history ++ batch)).size.toUInt64 := by
      rw [← nextCount]
      simp
    rw [count]
    exact Boundary.select_encoded (history ++ batch) tail fits

/-- Successful ordered barriers recover the complete batch from the
same marker and WAL images. -/
theorem syncedBytes_selectBatch
    {before after physical : ByteArray} {current next : Selection}
    (history batch : List WAL.Write)
    (prior : decode before = .ok current)
    (advanced : advance current (WAL.encode (history ++ batch)).size = .ok next)
    (size : after.size = containerSize)
    (unchanged : ∀ position,
      (position < next.slot * stride ∨ next.slot * stride + 40 ≤ position) →
        after.get! position = before.get! position)
    (written : after.extract (next.slot * stride) (next.slot * stride + 40) = next.encode)
    (durable : ∃ tail, physical = WAL.encode (history ++ batch) ++ tail) :
    decode after = .ok next ∧
      Boundary.select next.frontier physical = .ok (WAL.encode (history ++ batch)) := by
  refine ⟨decode_afterAdvance prior advanced size unchanged written, ?_⟩
  obtain ⟨tail, rfl⟩ := durable
  have count := (advance_fields advanced).2.2.1
  have fits : (WAL.encode (history ++ batch)).size < UInt64.size := by
    rw [← count]
    exact next.frontier.toNat_lt
  have frontier : next.frontier = (WAL.encode (history ++ batch)).size.toUInt64 := by
    rw [← count]
    simp
  rw [frontier]
  exact Boundary.select_encoded (history ++ batch) tail fits

/-- Schedule used by the native writer. On a reported failure the remaining
operations are skipped, including the installation of the cached slot. -/
@[macro_inline] def publish [Monad m] (append syncWal writeSlot syncSlot install : m Unit) :
    m Unit := do
  append
  syncWal
  writeSlot
  syncSlot
  install

theorem publish_reports {ε σ : Type}
    (append syncWal writeSlot syncSlot install : EStateM ε σ Unit) (initial : σ) :
    publish append syncWal writeSlot syncSlot install initial =
      match append initial with
      | .ok _ appended =>
        match syncWal appended with
        | .ok _ walSynced =>
          match writeSlot walSynced with
          | .ok _ slotWritten =>
            match syncSlot slotWritten with
            | .ok _ slotSynced => install slotSynced
            | .error cause after => .error cause after
          | .error cause after => .error cause after
        | .error cause after => .error cause after
      | .error cause after => .error cause after := by
  simp only [publish, Bind.bind, EStateM.bind]
  split <;> simp_all
  split <;> simp_all
  split <;> simp_all
  split <;> simp_all

/-- An observed marker must be settled before any destructive finish,
after the selected WAL and checkpoint have been validated. -/
@[macro_inline] def reopenWith [Monad m] (prepare : m (α × β × Nat))
    (stabilize : m Unit) (finish : α → Nat → m Unit) : m β := do
  let (plan, opened, size) ← prepare
  stabilize
  finish plan size
  return opened

theorem reopenWith_reports {ε σ α β : Type} (prepare : EStateM ε σ (α × β × Nat))
    (stabilize : EStateM ε σ Unit) (finish : α → Nat → EStateM ε σ Unit) (initial : σ) :
    reopenWith prepare stabilize finish initial =
      match prepare initial with
      | .error cause after => .error cause after
      | .ok (plan, opened, size) prepared =>
        match stabilize prepared with
        | .error cause after => .error cause after
        | .ok _ settled =>
          match finish plan size settled with
          | .error cause after => .error cause after
          | .ok _ after => .ok opened after := by
  cases first : prepare initial with
  | error => simp [reopenWith, Bind.bind, EStateM.bind, first]
  | ok result prepared =>
    obtain ⟨plan, opened, size⟩ := result
    cases second : stabilize prepared with
    | error => simp [reopenWith, Bind.bind, EStateM.bind, first, second]
    | ok _ settled =>
      cases last : finish plan size settled <;>
        simp [reopenWith, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure, first, second, last]

/-- Keep the acquired marker alongside the returned table. Preparation uses
its decoded frontier and stabilization uses the very same handle. -/
@[macro_inline] def reopenAcquiredWith [Monad m]
    (acquire : m (handle × Selection)) (prepare : Selection → m (plan × opened × Nat))
    (stabilize : handle → m Unit) (finish : plan → Nat → m Unit) :
    m (opened × handle × Selection) := do
  let (marker, selection) ← acquire
  let table ← reopenWith (prepare selection) (stabilize marker) finish
  return (table, marker, selection)

theorem reopenAcquiredWith_reports {ε σ handle plan opened : Type}
    (acquire : EStateM ε σ (handle × Selection))
    (prepare : Selection → EStateM ε σ (plan × opened × Nat))
    (stabilize : handle → EStateM ε σ Unit) (finish : plan → Nat → EStateM ε σ Unit)
    (initial : σ) :
    reopenAcquiredWith acquire prepare stabilize finish initial =
      match acquire initial with
      | .error cause after => .error cause after
      | .ok (marker, selection) acquired =>
        match reopenWith (prepare selection) (stabilize marker) finish acquired with
        | .error cause after => .error cause after
        | .ok table after => .ok (table, marker, selection) after := by
  cases first : acquire initial with
  | error => simp [reopenAcquiredWith, Bind.bind, EStateM.bind, first]
  | ok result acquired =>
    obtain ⟨marker, selection⟩ := result
    cases second : reopenWith (prepare selection) (stabilize marker) finish acquired <;>
      simp [reopenAcquiredWith, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure, first, second]

end Alvoki.WAL.TwoSlot
