import Lean.Elab.Tactic.Cbv
import Alvoki.Checks.Tests.SSTableProducer
import Alvoki.Experiments.SSTable.Recursive.NativeReadProofs

namespace ImmutableSSTable.Recursive.Vertical

set_option maxRecDepth 2000
set_option maxHeartbeats 800000

open SSTableProducerCheck (State name primitives supplier)

def layout : Unified.Layout := ⟨some 1, some 0, 905⟩
def crc : Unified.Checksum := fun _ _ => 0

def a : Entry := ⟨⟨#[0]⟩, .empty⟩
def b : Entry := ⟨⟨#[2]⟩, .empty⟩
def c : Entry := ⟨⟨#[4]⟩, .empty⟩
def rows : List Entry := [a, b, c]

def ra : Unified.Ref := ⟨a.key, 0, 5, 0, 1⟩
def rb : Unified.Ref := ⟨b.key, 5, 5, 1, 1⟩
def rc : Unified.Ref := ⟨c.key, 10, 5, 2, 1⟩
def left : Unified.Ref := ⟨b.key, 15, 86, 0, 2⟩
def right : Unified.Ref := ⟨c.key, 101, 45, 2, 1⟩
def leafRefs : Array Unified.Ref := #[ra, rb]
def fringeRefs : Array Unified.Ref := #[rc]
def rootRefs : Array Unified.Ref := #[left, right]
def footer : Footer := ⟨⟨layout, 3, 146, 86⟩, 2⟩

def packet (kind : UInt64) (offset : Nat) (payload : ByteArray) : ByteArray :=
  Unified.encodePacket crc layout.tableId kind offset payload

def packetA := packet dataKind 0 (Unified.encodeData layout #[a])
def packetB := packet dataKind 5 (Unified.encodeData layout #[b])
def packetC := packet dataKind 10 (Unified.encodeData layout #[c])
def packetLeft := packet (indexKind 1) 15 (Unified.encodeIndex leafRefs)
def packetRight := packet (indexKind 1) 101 (Unified.encodeIndex fringeRefs)
def packetRoot := packet (indexKind 2) 146 (Unified.encodeIndex rootRefs)
def packetFooter := Unified.encodePacket crc 0 footerKind 0 (encodeFooter footer)

def bytes : ByteArray :=
  (((((packetA ++ packetB) ++ packetC) ++ packetLeft) ++ packetRight) ++ packetRoot) ++ packetFooter

def published : State :=
  { binding := some (name, 17), description := some ((), 17), appended := bytes,
    flushed := true, durable := some (17, bytes) }

theorem writes :
    buildFileWith primitives crc name layout supplier id ⟨1, 1⟩ ({ rows } : State) = .ok 3 published := by
  cbv

open Unified (Ref RefCovers ValidRefsAfter)

private theorem packetSlice (beforeBytes body suffix : ByteArray) :
    ((beforeBytes ++ body) ++ suffix).extract beforeBytes.size (beforeBytes.size + body.size) = body := by
  have extract := ByteArray.extract_append_size_left (a := beforeBytes ++ body) (b := suffix) (i := beforeBytes.size)
  rw [ByteArray.size_append] at extract
  rw [extract, ByteArray.extract_append_eq_right rfl rfl]

private theorem sliceA : bytes.extract 0 5 = packetA := by
  have good := packetSlice ByteArray.empty packetA (packetB ++ packetC ++ packetLeft ++ packetRight ++ packetRoot ++ packetFooter)
  simpa only [bytes, ByteArray.empty_append, ByteArray.size_empty, Nat.zero_add, ByteArray.append_assoc,
    show packetA.size = 5 by rfl] using good

private theorem sliceB : bytes.extract 5 10 = packetB := by
  have good := packetSlice packetA packetB (packetC ++ packetLeft ++ packetRight ++ packetRoot ++ packetFooter)
  simpa only [bytes, ByteArray.append_assoc, show packetA.size = 5 by rfl,
    show packetB.size = 5 by rfl] using good

private theorem sliceC : bytes.extract 10 15 = packetC := by
  have good := packetSlice (packetA ++ packetB) packetC (packetLeft ++ packetRight ++ packetRoot ++ packetFooter)
  simpa only [bytes, ByteArray.append_assoc, show (packetA ++ packetB).size = 10 by rfl,
    show packetC.size = 5 by rfl] using good

private theorem sliceLeft : bytes.extract 15 101 = packetLeft := by
  have good := packetSlice (packetA ++ packetB ++ packetC) packetLeft (packetRight ++ packetRoot ++ packetFooter)
  simpa only [bytes, ByteArray.append_assoc, ByteArray.size_append,
    show packetA.size = 5 by rfl, show packetB.size = 5 by rfl, show packetC.size = 5 by rfl,
    show packetLeft.size = 86 by rfl, show packetRight.size = 45 by rfl,
    show packetRoot.size = 86 by rfl] using good

private theorem sliceRight : bytes.extract 101 146 = packetRight := by
  have good := packetSlice (packetA ++ packetB ++ packetC ++ packetLeft) packetRight (packetRoot ++ packetFooter)
  simpa only [bytes, ByteArray.append_assoc, ByteArray.size_append,
    show packetA.size = 5 by rfl, show packetB.size = 5 by rfl, show packetC.size = 5 by rfl,
    show packetLeft.size = 86 by rfl, show packetRight.size = 45 by rfl,
    show packetRoot.size = 86 by rfl] using good

private theorem sliceRoot : bytes.extract 146 232 = packetRoot := by
  have good := packetSlice (packetA ++ packetB ++ packetC ++ packetLeft ++ packetRight) packetRoot packetFooter
  simpa only [bytes, ByteArray.append_assoc, ByteArray.size_append,
    show packetA.size = 5 by rfl, show packetB.size = 5 by rfl, show packetC.size = 5 by rfl,
    show packetLeft.size = 86 by rfl, show packetRight.size = 45 by rfl,
    show packetRoot.size = 86 by rfl] using good

private theorem sliceFooter : bytes.extract 232 300 = packetFooter := by
  unfold bytes
  exact ByteArray.extract_append_eq_right rfl rfl

private theorem single (ref : Ref) (pos : ref.Valid) :
    ValidRefsAfter none [ref] :=
  ⟨pos, by simp, trivial⟩

private theorem pair (l r : Ref) (lv : l.Valid) (rv : r.Valid) (ordered : l.Precedes r) :
    ValidRefsAfter none [l,r] :=
  ⟨lv, by simp, rv, by simpa, trivial⟩

private theorem fencedOne (ref : Ref) (positive : 0 < ref.count)
    (extent : ref.firstRow + ref.count ≤ rows.length)
    (key : ref.lastKey = (rowAt rows (ref.firstRow + ref.count - 1)).key) :
    RefCovers rows ref.firstRow ref.count #[ref] := by
  refine ⟨extent, ?_, ?_, ?_⟩
  · intro i inside
    simp at inside
    have first : i = 0 := by omega
    subst i
    exact ⟨positive, Nat.le_refl _, Nat.le_refl _, key⟩
  · intro i j hi hj ordered
    simp at hi hj
    omega
  · intro index lo hi
    exact ⟨0, by simp, lo, hi⟩

private theorem fencedPair (l r : Ref) (adjacent : l.firstRow + l.count = r.firstRow)
    (lp : 0 < l.count) (rp : 0 < r.count)
    (extent : r.firstRow + r.count ≤ rows.length)
    (leftKey : l.lastKey = (rowAt rows (l.firstRow + l.count - 1)).key)
    (rightKey : r.lastKey = (rowAt rows (r.firstRow + r.count - 1)).key) :
    RefCovers rows l.firstRow (l.count + r.count) #[l,r] := by
  refine ⟨by omega, ?_, ?_, ?_⟩
  · intro i inside
    simp at inside
    rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl
    · change 0 < l.count ∧ l.firstRow ≤ l.firstRow ∧
        l.firstRow + l.count ≤ l.firstRow + (l.count + r.count) ∧ _
      exact ⟨lp, Nat.le_refl _, by omega, leftKey⟩
    · change 0 < r.count ∧ l.firstRow ≤ r.firstRow ∧
        r.firstRow + r.count ≤ l.firstRow + (l.count + r.count) ∧ _
      exact ⟨rp, by omega, by omega, rightKey⟩
  · intro i j hi hj ordered
    simp at hi hj
    have leftIndex : i = 0 := by omega
    have rightIndex : j = 1 := by omega
    subst i j
    exact Nat.le_of_eq adjacent
  · intro index lo hi
    by_cases inLeft : index < l.firstRow + l.count
    · exact ⟨0, by simp, lo, inLeft⟩
    · refine ⟨1, by simp, ?_⟩
      change r.firstRow ≤ index ∧ index < r.firstRow + r.count
      omega

private theorem dataA : DataAt layout crc bytes rows ra left.offset := by
  refine ⟨by decide, by decide, by decide, rfl, #[a], rfl, by decide, ?_, ?_,
    ⟨rfl, by decide, by decide, sliceA⟩⟩
  all_goals
    intro i inside
    have first : i = 0 := by simpa using inside
    subst i
    rfl

private theorem dataB : DataAt layout crc bytes rows rb left.offset := by
  refine ⟨by decide, by decide, by decide, rfl, #[b], rfl, by decide, ?_, ?_,
    ⟨rfl, by decide, by decide, sliceB⟩⟩
  all_goals
    intro i inside
    have first : i = 0 := by simpa using inside
    subst i
    rfl

private theorem dataC : DataAt layout crc bytes rows rc right.offset := by
  refine ⟨by decide, by decide, by decide, rfl, #[c], rfl, by decide, ?_, ?_,
    ⟨rfl, by decide, by decide, sliceC⟩⟩
  all_goals
    intro i inside
    have first : i = 0 := by simpa using inside
    subst i
    rfl

private theorem leftNode :
    TreeInImage layout crc bytes rows left 146 true 1 := by
  refine ⟨leafRefs, ⟨⟨⟨by decide, by decide, by decide, by cbv, ?_⟩, by decide, by decide,
    rfl, sliceLeft⟩, fencedPair ra rb rfl (by decide) (by decide) (by decide) rfl rfl,
    rfl, fun _ => rfl⟩, ?_⟩
  · exact pair ra rb (by unfold Ref.Valid; decide) (by unfold Ref.Valid; decide)
      (by unfold Ref.Precedes; decide)
  · intro ref member
    simp [leafRefs] at member
    rcases member with rfl | rfl
    · exact dataA
    · exact dataB

private theorem rightNode :
    TreeInImage layout crc bytes rows right 146 true 1 := by
  refine ⟨fringeRefs, ⟨⟨⟨by decide, by decide, by decide, by cbv, ?_⟩, by decide, by decide,
    rfl, sliceRight⟩, fencedOne rc (by decide) (by decide) rfl, rfl, fun _ => rfl⟩, ?_⟩
  · exact single rc (by unfold Ref.Valid; decide)
  · intro ref member
    have same : ref = rc := by simpa [fringeRefs] using member
    subst ref
    exact dataC

theorem writtenImage : Image layout crc bytes rows := by
  constructor
  · simp only [rows, Ordered, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false]
    refine ⟨?_, ?_, ?_⟩
    · intro row member
      rcases member with rfl | rfl <;> decide
    · intro row same
      subst row
      decide
    · simp
  · decide
  · refine ⟨footer, ⟨?_, by decide, ?_⟩, rfl, rfl, by decide, sliceFooter, ?_⟩
    · unfold Unified.Footer.Valid Unified.Layout.Valid
      decide
    · change 2 = 0 ↔ 3 = 0
      decide
    · change 146 + 86 = bytes.size - footerPacketSize ∧
        TreeInImage layout crc bytes rows footer.rootRef (bytes.size - footerPacketSize) false 2
      refine ⟨rfl, rootRefs, ⟨⟨⟨by decide, by decide, by decide, by cbv, ?_⟩, by decide,
        by decide, rfl, sliceRoot⟩, fencedPair left right rfl (by decide) (by decide) (by decide) rfl rfl,
        rfl, by intro impossible; contradiction⟩, ?_⟩
      · exact pair left right (by unfold Ref.Valid; decide) (by unfold Ref.Valid; decide)
          (by unfold Ref.Precedes; decide)
      · intro ref member
        simp [rootRefs] at member
        rcases member with rfl | rfl
        · exact leftNode
        · exact rightNode

/-- The actual streaming writer runs with a two-level index and syncs the
exact bytes. Local read primitive contracts for that inode suffice for a
correct public get and preservation of the frame on either outcome. -/
theorem durableMultiLevelLookup {ops : ReadPrimitives (ReadM world) handle}
    (effects : ReadEffects ops name frame pinned bytes) (key : ByteArray) :
    ∃ state : State, buildFileWith primitives crc name layout supplier id ⟨1, 1⟩
        ({ rows } : State) = .ok 3 state ∧
      state.durable = some (17, bytes) ∧
      ReadPost frame
        (openCheckedWith ops crc name layout.tableId >>= fun table => table.table.lookup key)
        (· = Contents.lookup rows key) :=
  ⟨published, writes, rfl, checkedNativeLookup effects writtenImage key⟩

/-- For healthy reads the writer bytes also give a non-vacuous open and
all three operations of the public table contract. -/
theorem durableMultiLevelOpens :
    ∃ state : State, buildFileWith primitives crc name layout supplier id ⟨1, 1⟩
        ({ rows } : State) = .ok 3 state ∧
      state.durable = some (17, bytes) ∧
      ∃ table, openChecked (exactSource bytes) crc layout.tableId = pure table ∧
        table.table.Represents rows :=
  ⟨published, writes, rfl, writtenImage.open_represents (Source.memory_serves bytes)⟩

end ImmutableSSTable.Recursive.Vertical
