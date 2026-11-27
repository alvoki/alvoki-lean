import Alvoki.Experiments.SSTable.Proofs.UnifiedEndToEnd
import Alvoki.Experiments.SSTable.UnifiedNative

namespace ImmutableSSTable

/-- Successful primitive observations at an already acquired file description.
The caller supplies its binding to the expected immutable file and keeps the
file contents stable for as long as the description is used. -/
structure ReadPrimitives.ReadsExactly [Monad m] (ops : ReadPrimitives m handle)
    (held : handle) (image : ByteArray) : Prop where
  size : ops.size held = pure image.size
  pread : ∀ (offset : UInt64) (count : USize), count.toNat ≤ maxRowSize →
    offset.toNat + count.toNat ≤ image.size →
    ops.pread held offset count = pure (image.extract offset.toNat (offset.toNat + count.toNat))

/-- A fixed healthy snapshot of the files reachable by open descriptions.
There is no pathname lookup after acquisition. An unlinked inode can still
be present in `contents` while an open description retains it. -/
structure ReadSnapshot (handle inode : Type) where
  inodeAt : handle → Option inode
  contents : inode → Option ByteArray

private def ReadSnapshot.bytesFor (snapshot : ReadSnapshot handle inode) (held : handle) :
    Option ByteArray :=
  (snapshot.inodeAt held).bind snapshot.contents

/-- Interpret fstat and pread at the inode of the supplied description.
The caller interprets acquisition, including path resolution and failure. -/
def ReadSnapshot.primitives [Monad m] [MonadExceptOf String m]
    (snapshot : ReadSnapshot handle inode) (openFile : System.FilePath → IO.FS.Mode → m handle) :
    ReadPrimitives m handle where
  openFile := openFile
  size held := match snapshot.bytesFor held with
    | none => throw "missing SSTable read description"
    | some bytes => pure bytes.size
  pread held offset count := do
    if count.toNat > maxRowSize || offset.toNat + count.toNat > maxFileSize then
      throw "SSTable read outside positional I/O bounds"
    match snapshot.bytesFor held with
    | none => throw "missing SSTable read description"
    | some bytes => pure (bytes.extract offset.toNat (offset.toNat + count.toNat))

theorem ReadSnapshot.readsExactly [Monad m] [MonadExceptOf String m]
    (snapshot : ReadSnapshot handle inode) (openFile : System.FilePath → IO.FS.Mode → m handle)
    {file : inode} (bound : snapshot.inodeAt held = some file)
    (contents : snapshot.contents file = some image)
    (extent : image.size ≤ maxFileSize) :
    (snapshot.primitives openFile).ReadsExactly held image := by
  have bytesFor : snapshot.bytesFor held = some image := by
    simp [ReadSnapshot.bytesFor, bound, contents]
  refine ⟨by simp [ReadSnapshot.primitives, bytesFor], ?_⟩
  intro offset count countFits inImage
  have readFits := Nat.le_trans inImage extent
  simp [ReadSnapshot.primitives, bytesFor, Nat.not_lt_of_ge countFits, Nat.not_lt_of_ge readFits]

private theorem packetSize_fitsUSize : maxRowSize < USize.size := by
  rcases System.Platform.numBits_eq with bits | bits <;> simp [USize.size, bits, maxRowSize]

/-- The checked adapter does not narrow admitted offsets or counts. Both
callbacks use the exact description to which the observations apply. -/
theorem ReadPrimitives.ReadsExactly.source_serves [Monad m] [MonadExceptOf String m]
    {ops : ReadPrimitives m handle} {held : handle} {image : ByteArray}
    (observed : ops.ReadsExactly held image) (extent : image.size ≤ maxFileSize) :
    (ops.source held).Serves image := by
  refine ⟨observed.size, ?_⟩
  intro offset count countFits inImage
  have readFits := Nat.le_trans inImage extent
  have offsetCast : offset.toUInt64.toNat = offset :=
    UInt64.toNat_ofNat_of_lt' (Nat.lt_of_le_of_lt (by omega : offset ≤ maxFileSize) (by decide))
  have countCast : count.toUSize.toNat = count :=
    USize.toNat_ofNat_of_lt' (Nat.lt_of_le_of_lt countFits packetSize_fitsUSize)
  have read := observed.pread offset.toUInt64 count.toUSize
  rw [offsetCast, countCast] at read
  simpa [ReadPrimitives.source, Nat.not_lt_of_ge countFits, Nat.not_lt_of_ge readFits]
    using read countFits inImage

/-- The signed-offset and packet-size checks run before the primitive.
Within those bounds a read error keeps the primitive's error and state. -/
theorem ReadPrimitives.source_pread_error
    {ops : ReadPrimitives (EStateM String σ) handle} {held : handle}
    {offset count : Nat} {before reached : σ} {message : String}
    (countFits : count ≤ maxRowSize) (readFits : offset + count ≤ maxFileSize)
    (failed : ops.pread held offset.toUInt64 count.toUSize before = .error message reached) :
    (ops.source held).readAt offset count before = .error message reached := by
  simpa [ReadPrimitives.source, Nat.not_lt_of_ge countFits, Nat.not_lt_of_ge readFits] using failed

namespace Unified

/-- Opening the immutable image uses the description returned by the
shared acquisition schedule directly. No path lookup occurs in either
callback retained by the public table. -/
theorem Image.openCheckedWith_represents [Monad m] [LawfulMonad m] [MonadExceptOf String m]
    {ops : ReadPrimitives m handle} {held : handle} {path : System.FilePath}
    (built : Image crc layout rows image)
    (opened : ops.openFile path .read = pure held)
    (observed : ops.ReadsExactly held image) :
    ∃ table, openCheckedWith ops crc path layout.tableId = pure table ∧ table.Represents rows := by
  obtain ⟨table, checked, represents⟩ := built.open_represents (observed.source_serves built.extent)
  exact ⟨table, by simp [openCheckedWith, opened, checked], represents⟩

/-- Connect the successful writer model to the actual checked-open schedule,
conditional on native acquisition and primitive observations for its output. -/
theorem openCheckedWith_built_table [Monad m] [LawfulMonad m] [MonadExceptOf String m]
    {ops : ReadPrimitives m handle} {held : handle} {path : System.FilePath}
    {crc : Checksum} {layout : Layout} {rows : List Entry} {options : BuildOptions}
    {count : Nat} {image : ByteArray}
    (built : modelBuild crc layout rows options = .ok (count, image))
    (opened : ops.openFile path .read = pure held)
    (observed : ops.ReadsExactly held image) :
    count = rows.length ∧
      ∃ table, openCheckedWith ops crc path layout.tableId = pure table ∧ table.Represents rows := by
  obtain ⟨rowCount, imageFacts⟩ := modelBuild_ok built
  exact ⟨rowCount, imageFacts.openCheckedWith_represents opened observed⟩

/-- A successful acquisition may change the modeled state. The file operations
in the healthy interpretation leave that acquired state unchanged. -/
theorem Image.openCheckedWith_represents_at
    {ops : ReadPrimitives (EStateM String σ) handle} {held : handle} {path : System.FilePath}
    {crc : Checksum} {layout : Layout} {rows : List Entry}
    {image : ByteArray} {before acquired : σ}
    (built : Image crc layout rows image)
    (opened : ops.openFile path .read before = .ok held acquired)
    (observed : ops.ReadsExactly held image) :
    ∃ table, openCheckedWith ops crc path layout.tableId before = .ok table acquired ∧
      table.Represents rows := by
  obtain ⟨table, checked, represents⟩ := built.open_represents
    (observed.source_serves built.extent)
  exact ⟨table, by simp [openCheckedWith, Bind.bind, EStateM.bind, opened, checked,
    Pure.pure, EStateM.pure], represents⟩

theorem openCheckedWith_acquire_error {ops : ReadPrimitives (EStateM String σ) handle}
    {path : System.FilePath} {before reached : σ} {message : String}
    (failed : ops.openFile path .read before = .error message reached) :
    openCheckedWith ops crc path expectedId before = .error message reached := by
  simp [openCheckedWith, Bind.bind, EStateM.bind, failed]

theorem openCheckedWith_size_error {ops : ReadPrimitives (EStateM String σ) handle}
    {path : System.FilePath} {held : handle} {before acquired reached : σ} {message : String}
    (opened : ops.openFile path .read before = .ok held acquired)
    (failed : ops.size held acquired = .error message reached) :
    openCheckedWith ops crc path expectedId before = .error message reached := by
  simp [openCheckedWith, opened, openTableChecked, openChecked, readFooter,
    ReadPrimitives.source, Bind.bind, EStateM.bind, failed]

end Unified
end ImmutableSSTable
