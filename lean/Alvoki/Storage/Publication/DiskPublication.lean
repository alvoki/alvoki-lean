namespace Alvoki.Storage.Publication

/-- Replace one directory entry with a synced temporary file in the same directory. -/
inductive Step where
  | writeStaged
  | syncStaged
  | renameStaged
  | syncDirectory
  deriving DecidableEq, Repr

def steps : List Step := [.writeStaged, .syncStaged, .renameStaged, .syncDirectory]

@[inline] def run [Monad m] (perform : Step → m Unit) : m Unit := steps.forM perform

variable {m : Type → Type u} {path : Type v}

/-- Interpret a replacement step in terms of file operations. The extra sync
targets share the staged file's sync, and the destination is needed only at rename. -/
@[inline] def performReplacement (write : path → m Unit) (sync : Array path → m Unit)
    (renameFile : path → path → m Unit) (staged directory : path) (active : Unit → path)
    (alsoSync : Array path) : Step → m Unit
  | .writeStaged => write staged
  | .syncStaged => sync (alsoSync.push staged)
  | .renameStaged => renameFile staged (active ())
  | .syncDirectory => sync #[directory]

/-- The exact sequence of callbacks, including the terminal `pure ()` of `run`.
This equation applies to native `IO` without making any claim about what its
file operations persist. -/
theorem run_performReplacement [Monad m] (write : path → m Unit)
    (sync : Array path → m Unit) (renameFile : path → path → m Unit)
    (staged directory : path) (active : Unit → path) (alsoSync : Array path) :
    run (performReplacement write sync renameFile staged directory active alsoSync) = (do
      write staged
      sync (alsoSync.push staged)
      renameFile staged (active ())
      sync #[directory]
      pure ()) := rfl

/-- Choose how to settle a validated WAL before making the session available.
Delay both actions so the aligned path need not construct a staging path. -/
@[inline] def runReopen (walSize selectedSize : Nat) (repair syncAligned : Unit → m Unit) : m Unit :=
  if selectedSize < walSize then repair () else syncAligned ()

theorem runReopen_repair {walSize selectedSize : Nat} (repair syncAligned : Unit → m Unit)
    (shorter : selectedSize < walSize) :
    runReopen walSize selectedSize repair syncAligned = repair () := by
  simp [runReopen, shorter]

theorem runReopen_aligned {walSize selectedSize : Nat} (repair syncAligned : Unit → m Unit)
    (notShorter : ¬ selectedSize < walSize) :
    runReopen walSize selectedSize repair syncAligned = syncAligned () := by
  simp [runReopen, notShorter]

end Alvoki.Storage.Publication
