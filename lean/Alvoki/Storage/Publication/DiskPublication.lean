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

variable {m : Type → Type u}

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
