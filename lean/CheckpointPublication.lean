import DiskPublication

namespace Alvoki.Storage.CheckpointPublication

/-- A run's contents are synced before its generation can appear in the manifest. -/
inductive Step where
  | writeRun (index : Nat)
  | syncRun (index : Nat)
  | syncRunsDirectory
  | manifest (step : Publication.Step)
  deriving DecidableEq, Repr

def runSteps (runCount : Nat) : List Step :=
  (List.range runCount).flatMap fun index => [.writeRun index, .syncRun index]

def steps (runCount : Nat) : List Step :=
  runSteps runCount ++ [.syncRunsDirectory] ++ Publication.steps.map Step.manifest

@[inline] def run [Monad m] (runCount : Nat) (perform : Step → m Unit) : m Unit :=
  (steps runCount).forM perform

end Alvoki.Storage.CheckpointPublication
