import Alvoki.Storage.Disk.Proofs.Read.NativeOpenReadTrace

namespace Alvoki.Storage.DiskSession

open System
open Sequential (SnapshotPin)

-- The interpreted callbacks track the phase heap. File and cache effects
-- remain in the reached native execution position.
structure NativeOpenedHandle (heap : Type) where
  table : DiskTable
  directory : DiskDirectory
  lock : IO.FS.Handle
  files : DiskTable.OpenSyncFiles
  phase : IO.Ref (Phase Installed)
  token : IO.Ref Unit
  uses : table.UsesOpenReferences directory lock files phase token
  contents : heap → IO.Ref (Phase Installed) → Option (Phase Installed)
  get : IO.Ref (Phase Installed) → EStateM IO.Error heap (Phase Installed)
  set : IO.Ref (Phase Installed) → Phase Installed → EStateM IO.Error heap Unit
  phaseEffects : OpenPhaseCellEffects contents get set
  ptrEq : IO.Ref Unit → IO.Ref Unit → EStateM IO.Error heap Bool

variable {heap : Type} {opened : NativeOpenedHandle heap}

/-- Keep the actual issued pin alongside its model handle and sequence. -/
structure NativeOpenedPin (opened : NativeOpenedHandle heap) where
  raw : DiskSnapshotPin
  localPin : SnapshotPin
  issued : raw.UsesOpenToken opened.token localPin

/-- The same opened handle supplies the phase cell at every reached
position. The common position carries the exact modeled file state,
synchronization cache and owner. -/
structure NativeOpenedPosition (opened : NativeOpenedHandle heap) where
  current : NativeExecutionPosition
  reached : heap
  directory : current.ready.state.session.directory = opened.directory
  stored : opened.contents reached opened.phase = some current.ready.state.session.phase
  pins : List (NativeOpenedPin opened)

/-- Seed a trace from a reached ready open before any snapshot pin has
been issued. Later reads then use pins issued inside the trace. -/
def NativeOpenedPosition.fromOpen (opened : NativeOpenedHandle heap) (start : NativeExecutionPosition)
    (reached : heap) (directory : start.ready.state.session.directory = opened.directory)
    (stored : opened.contents reached opened.phase = some start.ready.state.session.phase) :
    NativeOpenedPosition opened :=
  ⟨start, reached, directory, stored, []⟩

theorem NativeOpenedPosition.uses (position : NativeOpenedPosition opened) :
    opened.table.UsesOpenReferences position.current.ready.state.session.directory opened.lock opened.files
      opened.phase opened.token :=
  position.directory.symm ▸ opened.uses

end Alvoki.Storage.DiskSession
