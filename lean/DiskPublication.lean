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

end Alvoki.Storage.Publication
