import Init.System.IO

namespace Alvoki.Storage
open System

/-- Canonical basename shared by checkpoint publication and run-name parsing. -/
@[macro_inline] def renderRunFileName (generation : UInt64) (index : Nat) : String := s!"run-{generation}-{index}.v3"

/-- Segment names identify the number of complete frames before the segment. -/
def renderWalSegmentName (first : Nat) : String := "WAL-segment-" ++ first.repr

/-- The files the Linux disk protocol addresses within a database directory. -/
inductive DiskFile where
  | lock | wal | stagedWal | manifest | stagedManifest
  | walBoundary | stagedWalBoundary
  | run (generation : UInt64) (index : Nat)
  | walSegment (first : Nat)

private def DiskFile.name : DiskFile → String
  | .lock => "LOCK"
  | .wal => "WAL"
  | .stagedWal => "WAL.next"
  | .manifest => "MANIFEST"
  | .stagedManifest => "MANIFEST.next"
  | .walBoundary => "WAL.commit"
  | .stagedWalBoundary => "WAL.commit.next"
  | .run generation index => renderRunFileName generation index
  | .walSegment first => renderWalSegmentName first

/-- A fixed absolute directory path for all operations in an open session. -/
structure DiskDirectory where
  private mk ::
  path : FilePath
  absolute : path.toString.startsWith '/'

def DiskDirectory.file (dir : DiskDirectory) (file : DiskFile) : FilePath :=
  ⟨dir.path.toString ++ "/" ++ file.name⟩

theorem DiskDirectory.walSegment_path (dir : DiskDirectory) (first : Nat) :
    dir.file (.walSegment first) = ⟨dir.path.toString ++ "/" ++ renderWalSegmentName first⟩ := rfl

private theorem DiskDirectory.name_eq_of_file_eq {dir : DiskDirectory} {left right : DiskFile}
    (same : dir.file left = dir.file right) : left.name = right.name := by
  have names := congrArg FilePath.toString same
  exact (String.append_right_inj (dir.path.toString ++ "/")).mp names

/-- Segment names have a separate prefix from all existing database files. -/
theorem DiskDirectory.walSegment_exclusive {dir : DiskDirectory} {file : DiskFile} {first : Nat}
    (same : dir.file file = dir.file (.walSegment first)) : ∃ start, file = .walSegment start := by
  have samePrefix := congrArg (fun name : String => name.toList.take 4) (name_eq_of_file_eq same)
  cases file with
  | walSegment start => exact ⟨start, rfl⟩
  | run generation index =>
    change ("run-" ++ generation.toNat.repr ++ "-" ++ index.repr ++ ".v3").toList.take 4 =
      (renderWalSegmentName first).toList.take 4 at samePrefix
    simp [renderWalSegmentName, String.toList_append] at samePrefix
  | lock | wal | stagedWal | manifest | stagedManifest | walBoundary | stagedWalBoundary =>
    simp [DiskFile.name, renderWalSegmentName, String.toList_append] at samePrefix

theorem DiskDirectory.file_absolute (dir : DiskDirectory) (file : DiskFile) :
    (dir.file file).toString.startsWith '/' := by
  obtain ⟨rest, pathEq⟩ := String.startsWith_char_iff_exists_append.mp dir.absolute
  apply String.startsWith_char_iff_exists_append.mpr
  exact ⟨rest ++ "/" ++ file.name, by simp [DiskDirectory.file, pathEq, String.append_assoc]⟩

/-- POSIX interpretation of an argument with respect to the working directory. -/
def resolveDiskPath (cwd path : FilePath) : FilePath :=
  if path.toString.startsWith '/' then path else cwd / path

theorem DiskDirectory.paths_independent_of_cwd (dir : DiskDirectory) (cwd : FilePath) :
    resolveDiskPath cwd dir.path = dir.path ∧
      ∀ file, resolveDiskPath cwd (dir.file file) = dir.file file := by
  exact ⟨by simp [resolveDiskPath, dir.absolute],
    fun file => by simp [resolveDiskPath, dir.file_absolute file]⟩

/-- Resolve the database root once and require an absolute canonical path. -/
def DiskDirectory.open (input : FilePath) : IO DiskDirectory := do
  let path ← IO.FS.realPath input
  if absolute : path.toString.startsWith '/' then
    return ⟨path, absolute⟩
  else
    throw (IO.userError s!"database path is not absolute: {path}")

end Alvoki.Storage
