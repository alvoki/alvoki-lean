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
  ⟨initialSelection.encode.data ++ Array.replicate (containerSize - 40) 0⟩

private def decodeSlot (bytes : ByteArray) (slot : Nat) : Option Selection := do
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

def advance (before : Selection) (frontier : Nat) : Except String Selection := do
  unless before.epoch.toNat + 1 < UInt64.size do throw "two-slot WAL marker epoch exhausted"
  unless before.frontier.toNat < frontier && frontier < UInt64.size && frontier % frameSize == 0 do
    throw "invalid next two-slot WAL frontier"
  return ⟨1 - before.slot, (before.epoch.toNat + 1).toUInt64, frontier.toUInt64⟩

/-- A prepared write advances the epoch and targets the opposite record. -/
theorem advance_fields {before next : Selection} {frontier : Nat}
    (step : advance before frontier = .ok next) :
    next.slot = 1 - before.slot ∧ next.epoch.toNat = before.epoch.toNat + 1 ∧
      next.frontier.toNat = frontier ∧ before.frontier < next.frontier := by
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
      exact ⟨rfl, epochExact, lengthExact, increasesWord⟩
    · simp [advance, room, bounds, and_assoc, throw, throwThe,
        MonadExceptOf.throw, Bind.bind, Except.bind] at step
  · simp [advance, room, throw, throwThe,
      MonadExceptOf.throw, Bind.bind, Except.bind] at step

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

end Alvoki.WAL.TwoSlot
