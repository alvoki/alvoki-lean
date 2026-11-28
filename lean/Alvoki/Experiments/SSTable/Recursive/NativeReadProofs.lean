import Alvoki.Experiments.SSTable.Recursive.Native
import Alvoki.Experiments.SSTable.Recursive.Image
import Alvoki.Experiments.SSTable.Recursive.ReadSafety

namespace ImmutableSSTable.Recursive

open Unified (Layout Checksum)
variable {world handle : Type} {ops : ReadPrimitives (ReadM world) handle}

structure ReadEffects (ops : ReadPrimitives (ReadM world) handle) (path : System.FilePath)
    (frame : world → Prop) (pinned : handle → world → Prop) (image : ByteArray) : Prop where
  openRead : ReadPost frame (ops.openFile path .read) (fun _ => True)
  bindRead : ∀ start held after, frame start →
    ops.openFile path .read start = .ok held after → pinned held after
  size : ∀ held, ReadPost (fun s => frame s ∧ pinned held s) (ops.size held) (· = image.size)
  pread : ∀ held offset count, ReadPost (fun s => frame s ∧ pinned held s)
    (ops.pread held offset count) (· = image.extract offset.toNat (offset.toNat + count.toNat))

private theorem source_reads (effects : ReadEffects ops path frame pinned image) (held : handle) :
    ImageReads (fun s => frame s ∧ pinned held s) (ops.source held) image := by
  refine ⟨effects.size held, ?_⟩
  intro offset count start atDescriptor
  by_cases bounds : count ≤ maxRowSize ∧ offset + count ≤ maxFileSize
  · have offsetEq : offset.toUInt64.toNat = offset :=
      UInt64.toNat_ofNat_of_lt' (Nat.lt_of_le_of_lt (by omega : offset ≤ maxFileSize) (by decide))
    have packetFits : maxRowSize < USize.size := by
      rcases System.Platform.numBits_eq with bits | bits <;> simp [USize.size, bits, maxRowSize]
    have countEq : count.toUSize.toNat = count :=
      USize.toNat_ofNat_of_lt' (Nat.lt_of_le_of_lt bounds.1 packetFits)
    have observed := effects.pread held offset.toUInt64 count.toUSize start atDescriptor
    rw [offsetEq, countEq] at observed
    simpa [ReadPrimitives.source, Nat.not_lt_of_ge bounds.1, Nat.not_lt_of_ge bounds.2]
      using observed
  · have outside : maxRowSize < count ∨ maxFileSize < offset + count := by omega
    have rejected : (ops.source held).readAt offset count start =
        .error "SSTable read outside positional I/O bounds" start := by
      rcases outside with tooLarge | tooFar
      · simp only [ReadPrimitives.source, tooLarge, decide_true, Bool.true_or, ↓reduceIte]
        rfl
      · simp only [ReadPrimitives.source, tooFar, decide_true, Bool.or_true, ↓reduceIte]
        rfl
    rw [rejected]
    exact atDescriptor

/-- The public lookup schedule uses the acquired descriptor. On a returned
error only the frame is required. A successful lookup has the public
exact-match value, including a successful miss. -/
theorem checkedNativeLookup (effects : ReadEffects ops path frame pinned image)
    (produced : Image layout crc image rows) (key : ByteArray) :
    ReadPost frame
      (openCheckedWith ops crc path layout.tableId >>= fun handle => handle.table.lookup key)
      (· = Contents.lookup rows key) := by
  unfold openCheckedWith
  rw [bind_assoc]
  intro start before
  have openedFrame := effects.openRead start before
  cases acquired : ops.openFile path .read start with
  | error error after =>
    have kept : frame after := by simpa [acquired] using openedFrame
    simpa [openCheckedWith, Bind.bind, EStateM.bind, acquired] using kept
  | ok held after =>
    have kept : frame after := by simpa [acquired] using openedFrame
    have sameInode := effects.bindRead start held after before acquired
    have read := checkedLookup_framed (source_reads effects held) crc layout.tableId key after
      ⟨kept, sameInode⟩
    have exact : (exactSource image).Serves image := Source.memory_serves image
    obtain ⟨table, opened, semantics⟩ := produced.open_represents exact
    have expected :
        (openChecked (exactSource image) crc layout.tableId >>= (·.lookup key)) () =
          .ok (Contents.lookup rows key) () := by
      change (openChecked (exactSource image) crc layout.tableId >>= fun h => h.table.lookup key) () = _
      rw [opened, pure_bind, semantics.lookup]
      rfl
    simp only [Bind.bind, EStateM.bind, acquired, Handle.table]
    cases ran : (openChecked (ops.source held) crc layout.tableId >>= (·.lookup key)) after with
    | error error reached =>
      rw [ran] at read
      simp only [Bind.bind, EStateM.bind] at ran
      rw [ran]
      exact read.1
    | ok result reached =>
      rw [ran] at read
      simp only [Bind.bind, EStateM.bind] at ran
      rw [ran]
      exact ⟨read.1.1, (EStateM.Result.ok.inj (read.2.symm.trans expected)).1⟩

end ImmutableSSTable.Recursive
