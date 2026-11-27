import Alvoki.Storage.Disk.Proofs.Native.Recovery.NativeRawFlockOutcome

namespace Alvoki.Storage.DiskSession

open System

variable {heap α : Type}

/-- The same append handle and its reached heap feed the successful flock. -/
structure RawOpenLockedAt (calls : RawOpenAdmissionCallbacks heap) (input : FilePath) (entry : heap)
    (directory : DiskDirectory) (lock : IO.FS.Handle) (afterFlock : heap) : Prop where
  appended : ∃ afterAppend,
    calls.beforeFlock input entry = .ok (directory, lock) afterAppend ∧
    calls.flock lock afterAppend = .ok true afterFlock

/-- The held part of open stops at the first error. It either fails to
initialize the cache or passes the exact initialized record to recovery. -/
inductive RawOpenHeldError (openCache : DiskDirectory → EStateM IO.Error heap DiskTable.OpenSyncFiles)
    (recover : DiskDirectory → IO.FS.Handle → DiskTable.OpenSyncFiles → EStateM IO.Error heap α)
    (directory : DiskDirectory) (lock : IO.FS.Handle) (afterFlock : heap) : IO.Error → heap → Prop where
  | initializing {cause : IO.Error} {reached : heap}
      (failed : openCache directory afterFlock = .error cause reached) :
      RawOpenHeldError openCache recover directory lock afterFlock cause reached
  | recovering {cache : DiskTable.OpenSyncFiles} {initialized reached : heap} {cause : IO.Error}
      (opened : openCache directory afterFlock = .ok cache initialized)
      (failed : recover directory lock cache initialized = .error cause reached) :
      RawOpenHeldError openCache recover directory lock afterFlock cause reached

/-- Classify a native open return by the first failing stage and its
actual cleanup outcome, or the exact value returned by the held work. -/
inductive RawOpenReturn (calls : RawOpenAdmissionCallbacks heap) (input : FilePath) (entry : heap)
    (openCache : DiskDirectory → EStateM IO.Error heap DiskTable.OpenSyncFiles)
    (recover : DiskDirectory → IO.FS.Handle → DiskTable.OpenSyncFiles → EStateM IO.Error heap α) :
    EStateM.Result IO.Error heap α → Prop where
  | beforeFlock {cause : IO.Error} {reached : heap}
      (whereFailed : RawOpenPrefixReturn calls input entry (.error cause reached)) :
      RawOpenReturn calls input entry openCache recover (.error cause reached)
  | flockError {directory : DiskDirectory} {lock : IO.FS.Handle} {afterAppend reached : heap} {cause : IO.Error}
      (appended : calls.beforeFlock input entry = .ok (directory, lock) afterAppend)
      (failed : calls.flock lock afterAppend = .error cause reached) :
      RawOpenReturn calls input entry openCache recover (.error cause reached)
  | contended {directory : DiskDirectory} {lock : IO.FS.Handle} {afterAppend reached : heap}
      (appended : calls.beforeFlock input entry = .ok (directory, lock) afterAppend)
      (busy : calls.flock lock afterAppend = .ok false reached) :
      RawOpenReturn calls input entry openCache recover
        (.error (IO.userError s!"database already open: {directory.path}") reached)
  | returned {directory : DiskDirectory} {lock : IO.FS.Handle} {afterFlock initialized reached : heap}
      {cache : DiskTable.OpenSyncFiles} {value : α}
      (held : RawOpenLockedAt calls input entry directory lock afterFlock)
      (opened : openCache directory afterFlock = .ok cache initialized)
      (recovered : recover directory lock cache initialized = .ok value reached) :
      RawOpenReturn calls input entry openCache recover (.ok value reached)
  | unlocked {directory : DiskDirectory} {lock : IO.FS.Handle} {afterFlock failed reached : heap} {cause : IO.Error}
      (held : RawOpenLockedAt calls input entry directory lock afterFlock)
      (reported : RawOpenHeldError openCache recover directory lock afterFlock cause failed)
      (unlocked : calls.unlock lock failed = .ok () reached) :
      RawOpenReturn calls input entry openCache recover (.error cause reached)
  | unlockError {directory : DiskDirectory} {lock : IO.FS.Handle} {afterFlock failed reached : heap}
      {cause cleanup : IO.Error}
      (held : RawOpenLockedAt calls input entry directory lock afterFlock)
      (reported : RawOpenHeldError openCache recover directory lock afterFlock cause failed)
      (unlock : calls.unlock lock failed = .error cleanup reached) :
      RawOpenReturn calls input entry openCache recover (.error cleanup reached)

/-- Under one fixed interpretation of the native callbacks, classify
all ordinary returns with the exact intermediate arguments and heaps. -/
theorem RawOpenAdmissionCallbacks.classifiesOpenReturn (calls : RawOpenAdmissionCallbacks heap) (input : FilePath)
    (init : OpenSyncCacheCallbacks heap)
    (makeCache : IO.Ref (Option IO.FS.Handle) → IO.Ref (Option (FilePath × IO.FS.Handle)) →
      IO.Ref (List (FilePath × IO.FS.Handle)) → DiskTable.OpenSyncFiles)
    (recover : DiskDirectory → IO.FS.Handle → DiskTable.OpenSyncFiles → EStateM IO.Error heap α) (entry : heap) :
    let openCache := fun directory : DiskDirectory =>
      openSyncFilesWith (init.openDirectory directory.path) init.newRef init.newRef init.newRef makeCache
    RawOpenReturn calls input entry openCache recover (calls.runOpen input init makeCache recover entry) := by
  intro openCache
  have cleanup {directory : DiskDirectory} {lock : IO.FS.Handle} {afterFlock failed : heap} {cause : IO.Error}
      (held : RawOpenLockedAt calls input entry directory lock afterFlock)
      (reported : RawOpenHeldError openCache recover directory lock afterFlock cause failed) :
      RawOpenReturn calls input entry openCache recover
        ((do calls.unlock lock; throw cause : EStateM IO.Error heap α) failed) := by
    simp only [Bind.bind, EStateM.bind, throw, throwThe, MonadExceptOf.throw, EStateM.throw]
    cases result : calls.unlock lock failed with
    | ok value reached =>
      cases value
      exact .unlocked held reported result
    | error diagnostic reached => exact .unlockError held reported result
  cases prepared : calls.beforeFlock input entry with
  | error cause reached =>
    rw [calls.runsAfterPrefix, prepared]
    exact .beforeFlock (prepared ▸ calls.classifiesBeforeFlock input entry)
  | ok resolved afterAppend =>
    obtain ⟨directory, lock⟩ := resolved
    rw [calls.runsAfterFlock input prepared init makeCache recover]
    cases flock : calls.flock lock afterAppend with
    | error cause reached => exact .flockError prepared flock
    | ok granted afterFlock =>
      cases granted
      · exact .contended prepared flock
      · have held : RawOpenLockedAt calls input entry directory lock afterFlock := ⟨afterAppend, prepared, flock⟩
        dsimp only
        change RawOpenReturn calls input entry openCache recover
          ((tryCatchThe IO.Error (do
            let cache ← openCache directory
            recover directory lock cache) fun cause => do
              calls.unlock lock
              throw cause) afterFlock)
        simp only [tryCatchThe, MonadExceptOf.tryCatch, EStateM.tryCatch,
          EStateM.Backtrackable.restore, EStateM.dummyRestore, Bind.bind, EStateM.bind]
        cases opened : openCache directory afterFlock with
        | error cause failed => exact cleanup held (.initializing opened)
        | ok cache initialized =>
          dsimp only
          cases recovered : recover directory lock cache initialized with
          | ok value reached => exact .returned held opened recovered
          | error cause failed => exact cleanup held (.recovering opened recovered)

end Alvoki.Storage.DiskSession
