import Init.System.IO

namespace Alvoki.Storage
open System

/-- Canonical basename shared by checkpoint publication and run-name parsing. -/
@[macro_inline] def renderRunFileName (generation : UInt64) (index : Nat) : String := s!"run-{generation}-{index}.v3"

/-- The files the Linux disk protocol addresses within a database directory. -/
inductive DiskFile where
  | lock | wal | stagedWal | manifest | stagedManifest
  | walBoundary | stagedWalBoundary
  | run (generation : UInt64) (index : Nat)

private def DiskFile.name : DiskFile → String
  | .lock => "LOCK"
  | .wal => "WAL"
  | .stagedWal => "WAL.next"
  | .manifest => "MANIFEST"
  | .stagedManifest => "MANIFEST.next"
  | .walBoundary => "WAL.commit"
  | .stagedWalBoundary => "WAL.commit.next"
  | .run generation index => renderRunFileName generation index

/-- A fixed absolute directory path for all operations in an open session. -/
structure DiskDirectory where
  private mk ::
  path : FilePath
  absolute : path.toString.startsWith '/'

def DiskDirectory.file (dir : DiskDirectory) (file : DiskFile) : FilePath :=
  ⟨dir.path.toString ++ "/" ++ file.name⟩

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
