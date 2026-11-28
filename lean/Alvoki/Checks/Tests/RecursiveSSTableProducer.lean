import Lean.Elab.Tactic.Cbv
import Alvoki.Checks.Tests.SSTableProducer
import Alvoki.Experiments.SSTable.Recursive.NativeWriteProofs

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

theorem writtenImage : Image layout crc bytes rows := by
  obtain ⟨_, _, _, image, _⟩ := buildFileWith_refines SSTableProducerCheck.effects writes
  exact image

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
