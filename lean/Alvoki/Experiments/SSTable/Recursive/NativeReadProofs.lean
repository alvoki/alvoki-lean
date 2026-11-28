import Alvoki.Experiments.SSTable.Recursive.Native
import Alvoki.Experiments.SSTable.Recursive.FilterImageProofs
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

private theorem ReadEffects.withSource (effects : ReadEffects ops path frame pinned image)
    (onSource : Source (ReadM world) → ReadM world α) (result : α → Prop)
    (safe : ∀ held, ImageReads (fun s => frame s ∧ pinned held s) (ops.source held) image →
      ReadPost (fun s => frame s ∧ pinned held s) (onSource (ops.source held)) result) :
    ReadPost frame (ops.openFile path .read >>= fun held => onSource (ops.source held)) result := by
  intro start before
  have openedFrame := effects.openRead start before
  cases acquired : ops.openFile path .read start with
  | error error after =>
    have kept : frame after := by simpa [acquired] using openedFrame
    simpa [Bind.bind, EStateM.bind, acquired] using kept
  | ok held after =>
    have kept : frame after := by simpa [acquired] using openedFrame
    have sameInode := effects.bindRead start held after before acquired
    have read := safe held (source_reads effects held) after ⟨kept, sameInode⟩
    simp only [Bind.bind, EStateM.bind, acquired]
    cases ran : onSource (ops.source held) after with
    | error error reached =>
      rw [ran] at read
      exact read.1
    | ok value reached =>
      rw [ran] at read
      exact ⟨read.1.1, read.2⟩

private theorem ReadPost.weaken (safe : ReadPost frame (world := world) action pre)
    (implies : ∀ value, pre value → post value) : ReadPost frame action post := by
  intro start initial
  have observed := safe start initial
  cases ran : action start with
  | error _ _ => simpa [ran] using observed
  | ok value _ =>
    rw [ran] at observed
    exact ⟨observed.1, implies value observed.2⟩

/-- The checked schedule uses the acquired descriptor. On a returned
error the frame is preserved. A successful lookup has the exact public value. -/
theorem checkedNativeLookup (effects : ReadEffects ops path frame pinned image)
    (produced : Image layout crc image rows) (key : ByteArray) :
    ReadPost frame
      (openCheckedWith ops crc path layout.tableId >>= fun handle => handle.table.lookup key)
      (· = Contents.lookup rows key) := by
  unfold openCheckedWith
  rw [bind_assoc]
  apply effects.withSource (fun source => openChecked source crc layout.tableId >>= (·.lookup key))
  intro held sourceSafe
  have exact : (exactSource image).Serves image := Source.memory_serves image
  obtain ⟨table, opened, semantics⟩ := produced.open_represents exact
  apply (checkedLookup_framed sourceSafe crc layout.tableId key).weaken
  intro value agreed
  change (openChecked (exactSource image) crc layout.tableId >>= fun h => h.table.lookup key) () = _ at agreed
  rw [opened, pure_bind, semantics.lookup] at agreed
  exact (EStateM.Result.ok.inj agreed).1.symm

theorem checkedNativeFilteredLookup (effects : ReadEffects ops path frame pinned image)
    (produced : Image layout crc image rows) (key : ByteArray) :
    ReadPost frame
      (openCheckedWith ops crc path layout.tableId >>= fun handle => handle.filteredTable.lookup key)
      (· = Contents.lookup rows key) := by
  unfold openCheckedWith
  rw [bind_assoc]
  apply effects.withSource (fun source => openChecked source crc layout.tableId >>= (·.filteredLookup key))
  intro held sourceSafe
  have exact : (exactSource image).Serves image := Source.memory_serves image
  obtain ⟨table, opened, semantics⟩ := produced.open_filtered_represents exact
  apply (checkedFilteredLookup_framed sourceSafe crc layout.tableId key).weaken
  intro value agreed
  change (openChecked (exactSource image) crc layout.tableId >>= fun h => h.filteredTable.lookup key)
    () = _ at agreed
  rw [opened, pure_bind, semantics.lookup] at agreed
  exact (EStateM.Result.ok.inj agreed).1.symm

end ImmutableSSTable.Recursive
