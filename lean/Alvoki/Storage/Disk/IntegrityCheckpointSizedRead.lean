import Alvoki.Storage.Disk.DiskPaths
import Alvoki.Storage.Disk.IntegrityCheckpointRead
import Alvoki.Storage.Disk.RecoverySizedReads
import Alvoki.Storage.Disk.RecoveryRequestCount

namespace Alvoki.Storage

open System Manifest

private def runExtentError : IO.Error := IO.userError checkpointIntegrityMismatch

private def readStampedRun [Monad m] [MonadExceptOf IO.Error m] (dir : DiskDirectory)
    (stamps : Array RunIntegrity) (readSize : FilePath → m Nat)
    (readPrefix : FilePath → Nat → m ByteArray) (generation : UInt64) (index : Nat) : m ByteArray := do
  let some stamp := stamps[index]? | throw runExtentError
  readExactRecoveryFileWith (dir.file (.run generation index)) stamp.byteCount.toNat
    runExtentError readSize readPrefix

/-- The existing increasing-index loop checks the observed file extent
against its decoded integrity stamp before requesting payload bytes.
Index a single array of stamps so the traversal takes linear work. -/
def readIntegrityRunBytesSized [Monad m] [MonadExceptOf IO.Error m] (dir : DiskDirectory)
    (manifest : IntegrityCheckpoint) (readSize : FilePath → m Nat)
    (readPrefix : FilePath → Nat → m ByteArray) : m (List ByteArray) :=
  let stamps := manifest.runs.toArray
  readCheckpointRunBytes (readStampedRun dir stamps readSize readPrefix) manifest.header

/-- Read the strict manifest and its selected runs. Integrity checks and
structural restoration consume the same ordered bytes as the older route. -/
def readIntegrityCheckpointSized [Monad m] [MonadExceptOf IO.Error m] (dir : DiskDirectory)
    (readManifest : m (Option ByteArray)) (readSize : FilePath → m Nat)
    (readPrefix : FilePath → Nat → m ByteArray) : m (Option (PackedTable × UInt64)) := do
  let some bytes ← readManifest | return none
  let manifest ← liftExcept ((IntegrityCheckpoint.decode bytes).mapError IO.userError)
  let files ← readIntegrityRunBytesSized dir manifest readSize readPrefix
  let table ← liftExcept ((loadIntegrityRunSet manifest files).mapError IO.userError)
  return some (table, manifest.header.generation)

private theorem mapM_eq_of_mem [Monad m] [LawfulMonad m] {α β : Type} {left right : α → m β}
    (indices : List α) (equivalent : ∀ index ∈ indices, left index = right index) :
    indices.mapM left = indices.mapM right := by
  induction indices with
  | nil => rfl
  | cons head rest ih =>
    simp only [List.mapM_cons, equivalent head (by simp)]
    rw [ih (fun index found => equivalent index (List.mem_cons_of_mem _ found))]

/-- Healthy exact observations read exactly the old bytes at every
selected generation/index, in the same order. The checkpoint loader
therefore sees the same checksums, structure and restore input. -/
private theorem readIntegrityRunBytesSized_eq_of_reports [Monad m] [LawfulMonad m] [MonadExceptOf IO.Error m]
    (dir : DiskDirectory) {manifest : IntegrityCheckpoint}
    (count : manifest.runs.length = manifest.header.runCount.toNat)
    (readSize : FilePath → m Nat) (readPrefix : FilePath → Nat → m ByteArray)
    (readRun : UInt64 → Nat → m ByteArray)
    (reported : ∀ index stamp, manifest.runs[index]? = some stamp → ∃ payload,
      stamp.byteCount.toNat < USize.size ∧ payload.size = stamp.byteCount.toNat ∧
      readSize (dir.file (.run manifest.header.generation index)) = pure stamp.byteCount.toNat ∧
      readPrefix (dir.file (.run manifest.header.generation index)) stamp.byteCount.toNat = pure payload ∧
      readRun manifest.header.generation index = pure payload) :
    readIntegrityRunBytesSized dir manifest readSize readPrefix = readCheckpointRunBytes readRun manifest.header := by
  rw [readIntegrityRunBytesSized, readCheckpointRunBytes_eq_mapM, readCheckpointRunBytes_eq_mapM]
  apply mapM_eq_of_mem
  intro index member
  have within : index < manifest.runs.length := count.symm ▸ List.mem_range.mp member
  let stamp := manifest.runs[index]'within
  have atIndex : manifest.runs[index]? = some stamp := List.getElem?_eq_getElem within
  obtain ⟨payload, fits, exactSize, size, payloadRead, old⟩ := reported index stamp atIndex
  simp [readStampedRun, atIndex, readExactRecoveryFileWith, size, fits, payloadRead, exactSize, old]

theorem readIntegrityRunBytesSized_compatible (dir : DiskDirectory) {manifest : IntegrityCheckpoint}
    (count : manifest.runs.length = manifest.header.runCount.toNat)
    (readSize : FilePath → Except IO.Error Nat) (readPrefix : FilePath → Nat → Except IO.Error ByteArray)
    (readRun : UInt64 → Nat → Except IO.Error ByteArray)
    (reported : ∀ index stamp, manifest.runs[index]? = some stamp → ∃ payload,
      stamp.byteCount.toNat < USize.size ∧ payload.size = stamp.byteCount.toNat ∧
      readSize (dir.file (.run manifest.header.generation index)) = .ok stamp.byteCount.toNat ∧
      readPrefix (dir.file (.run manifest.header.generation index)) stamp.byteCount.toNat = .ok payload ∧
      readRun manifest.header.generation index = .ok payload) :
    readIntegrityRunBytesSized dir manifest readSize readPrefix = readCheckpointRunBytes readRun manifest.header :=
  readIntegrityRunBytesSized_eq_of_reports dir count readSize readPrefix readRun reported

/-- Successful reads can be interpreted in a stateful monad. The manifest
and every selected run callback preserve the state on their reported success. -/
theorem readIntegrityCheckpointSized_eq_of_reports [Monad m] [LawfulMonad m] [MonadExceptOf IO.Error m]
    (dir : DiskDirectory) (readManifest : m (Option ByteArray))
    (readSize : FilePath → m Nat) (readPrefix : FilePath → Nat → m ByteArray)
    (readRun : UInt64 → Nat → m ByteArray)
    {bytes : ByteArray} (manifestRead : readManifest = pure (some bytes)) {manifest : IntegrityCheckpoint}
    (decoded : IntegrityCheckpoint.decode bytes = .ok manifest)
    (reported : ∀ index stamp, manifest.runs[index]? = some stamp → ∃ payload,
      stamp.byteCount.toNat < USize.size ∧ payload.size = stamp.byteCount.toNat ∧
      readSize (dir.file (.run manifest.header.generation index)) = pure stamp.byteCount.toNat ∧
      readPrefix (dir.file (.run manifest.header.generation index)) stamp.byteCount.toNat = pure payload ∧
      readRun manifest.header.generation index = pure payload) :
    readIntegrityCheckpointSized dir readManifest readSize readPrefix =
      readIntegrityCheckpoint readManifest readRun (fun report => liftExcept (report.mapError IO.userError)) := by
  have same := readIntegrityRunBytesSized_eq_of_reports dir (IntegrityCheckpoint.decode_spec decoded).2.2
    readSize readPrefix readRun reported
  simp [readIntegrityCheckpointSized, readIntegrityCheckpoint, manifestRead, decoded, same,
    liftExcept, Except.mapError]

theorem readIntegrityCheckpointSized_compatible (dir : DiskDirectory)
    (readManifest : Except IO.Error (Option ByteArray))
    (readSize : FilePath → Except IO.Error Nat) (readPrefix : FilePath → Nat → Except IO.Error ByteArray)
    (readRun : UInt64 → Nat → Except IO.Error ByteArray)
    {bytes : ByteArray} (manifestRead : readManifest = .ok (some bytes)) {manifest : IntegrityCheckpoint}
    (decoded : IntegrityCheckpoint.decode bytes = .ok manifest)
    (reported : ∀ index stamp, manifest.runs[index]? = some stamp → ∃ payload,
      stamp.byteCount.toNat < USize.size ∧ payload.size = stamp.byteCount.toNat ∧
      readSize (dir.file (.run manifest.header.generation index)) = .ok stamp.byteCount.toNat ∧
      readPrefix (dir.file (.run manifest.header.generation index)) stamp.byteCount.toNat = .ok payload ∧
      readRun manifest.header.generation index = .ok payload) :
    readIntegrityCheckpointSized dir readManifest readSize readPrefix =
      readIntegrityCheckpoint readManifest readRun (fun report => liftExcept (report.mapError IO.userError)) :=
  readIntegrityCheckpointSized_eq_of_reports dir readManifest readSize readPrefix readRun manifestRead decoded reported

/-- Read-only size and prefix reports establish the exact ordered payloads
and state reached by the prefix of the sized run loop. -/
theorem readIntegrityRunBytesSized_prefix_of_reports {state : Type} (dir : DiskDirectory)
    (manifest : IntegrityCheckpoint) (readSize : FilePath → EStateM IO.Error state Nat)
    (readPrefix : FilePath → Nat → EStateM IO.Error state ByteArray) (initial : state)
    (stop : Nat) (fits : stop < UInt64.size) (payload : Nat → ByteArray)
    (reported : ∀ index < stop, ∃ stamp,
      manifest.runs[index]? = some stamp ∧ stamp.byteCount.toNat < USize.size ∧
      (payload index).size = stamp.byteCount.toNat ∧
      readSize (dir.file (.run manifest.header.generation index)) initial = .ok stamp.byteCount.toNat initial ∧
      readPrefix (dir.file (.run manifest.header.generation index)) stamp.byteCount.toNat initial =
        .ok (payload index) initial) :
    readIntegrityRunBytesSized dir { manifest with header := { manifest.header with runCount := stop.toUInt64 } }
      readSize readPrefix initial = .ok ((List.range stop).map payload) initial := by
  let readRun := readStampedRun dir manifest.runs.toArray readSize readPrefix manifest.header.generation
  have readOne (index : Nat) (within : index < stop) : readRun index initial = .ok (payload index) initial := by
    obtain ⟨stamp, found, fits, size, sized, read⟩ := reported index within
    have exactRead := readExactRecoveryFileWith_accepts (dir.file (.run manifest.header.generation index))
      stamp.byteCount.toNat runExtentError readSize readPrefix fits sized read size
    simpa [readRun, readStampedRun, found, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure] using exactRead
  have readAll (indices : List Nat) (within : ∀ index ∈ indices, index < stop) :
      (indices.mapM readRun) initial = .ok (indices.map payload) initial := by
    induction indices with
    | nil => rfl
    | cons index rest ih =>
      have tail := ih (fun index member => within index (List.mem_cons_of_mem _ member))
      simp [List.mapM_cons, readOne index (within index List.mem_cons_self), tail,
        Bind.bind, EStateM.bind, Pure.pure, EStateM.pure]
  simp only [readIntegrityRunBytesSized, readCheckpointRunBytes_eq_mapM, UInt64.toNat_ofNat_of_lt' fits]
  exact readAll (List.range stop) (fun _ member => List.mem_range.mp member)

/-- A run with a rejected extent stops the ordered reader after the size
callback. The shortened loop supplies the actual reached state for the
preceding indices and uses the same stamps as the complete loop. -/
theorem readIntegrityRunBytesSized_rejectsExtent {state : Type} (dir : DiskDirectory)
    (manifest : IntegrityCheckpoint) (readSize : FilePath → EStateM IO.Error state Nat)
    (readPrefix : FilePath → Nat → EStateM IO.Error state ByteArray)
    {index actual : Nat} {stamp : RunIntegrity} {initial prior observed : state} {previous : List ByteArray}
    (within : index < manifest.header.runCount.toNat) (stampAt : manifest.runs[index]? = some stamp)
    (earlier : readIntegrityRunBytesSized dir
        { manifest with header := { manifest.header with runCount := index.toUInt64 } }
        readSize readPrefix initial = .ok previous prior)
    (sized : readSize (dir.file (.run manifest.header.generation index)) prior = .ok actual observed)
    (wrong : ¬ (actual = stamp.byteCount.toNat ∧ stamp.byteCount.toNat < USize.size)) :
    readIntegrityRunBytesSized dir manifest readSize readPrefix initial =
      .error (IO.userError checkpointIntegrityMismatch) observed := by
  have countFits := Nat.lt_trans within manifest.header.runCount.toNat_lt_size
  have countExact : index.toUInt64.toNat = index := UInt64.toNat_ofNat_of_lt' countFits
  have countSplit : index + 1 + (manifest.header.runCount.toNat - (index + 1)) =
      manifest.header.runCount.toNat := Nat.add_sub_of_le within
  have indices : List.range manifest.header.runCount.toNat = List.range index ++ index ::
      (List.range (manifest.header.runCount.toNat - (index + 1))).map ((index + 1) + ·) := by
    calc
      List.range manifest.header.runCount.toNat =
          List.range (index + 1 + (manifest.header.runCount.toNat - (index + 1))) :=
        congrArg List.range countSplit.symm
      _ = _ := by rw [List.range_add, List.range_succ]; simp
  have reject := readExactRecoveryFileWith_rejectsSize (dir.file (.run manifest.header.generation index))
    stamp.byteCount.toNat runExtentError readSize readPrefix sized wrong
  simp only [readIntegrityRunBytesSized, readCheckpointRunBytes_eq_mapM, countExact] at earlier
  change (readIntegrityRunBytesSized dir manifest readSize readPrefix) initial = .error runExtentError observed
  simp [readIntegrityRunBytesSized, readCheckpointRunBytes_eq_mapM, indices, List.mapM_append, List.mapM_cons,
    Bind.bind, EStateM.bind, earlier, readStampedRun, stampAt, reject]

/-- Size rejection returns from checkpoint acquisition with the reached
state before opening that run's payload or restoring the table. -/
theorem readIntegrityCheckpointSized_rejectsExtent {state : Type} (dir : DiskDirectory)
    (readManifest : EStateM IO.Error state (Option ByteArray))
    (readSize : FilePath → EStateM IO.Error state Nat)
    (readPrefix : FilePath → Nat → EStateM IO.Error state ByteArray)
    {bytes : ByteArray} {manifest : IntegrityCheckpoint}
    {index actual : Nat} {stamp : RunIntegrity} {initial listed prior observed : state} {previous : List ByteArray}
    (manifestRead : readManifest initial = .ok (some bytes) listed)
    (decoded : IntegrityCheckpoint.decode bytes = .ok manifest)
    (within : index < manifest.header.runCount.toNat) (stampAt : manifest.runs[index]? = some stamp)
    (earlier : readIntegrityRunBytesSized dir
        { manifest with header := { manifest.header with runCount := index.toUInt64 } }
        readSize readPrefix listed = .ok previous prior)
    (sized : readSize (dir.file (.run manifest.header.generation index)) prior = .ok actual observed)
    (wrong : ¬ (actual = stamp.byteCount.toNat ∧ stamp.byteCount.toNat < USize.size)) :
    readIntegrityCheckpointSized dir readManifest readSize readPrefix initial =
      .error (IO.userError checkpointIntegrityMismatch) observed := by
  have rejected := readIntegrityRunBytesSized_rejectsExtent dir manifest readSize readPrefix within stampAt
    earlier sized wrong
  simp [readIntegrityCheckpointSized, Bind.bind, EStateM.bind, liftExcept, Except.mapError,
    Pure.pure, EStateM.pure, manifestRead, decoded, rejected]

private def requestedBytes {α : Type} : EStateM.Result IO.Error Nat α → Nat
  | .ok _ bytes | .error _ bytes => bytes

private def recordRequest {α : Type} (size : Nat) (report : Except IO.Error α) :
    EStateM IO.Error Nat α := fun previous =>
  match report with
  | .ok value => .ok value (previous + size)
  | .error cause => .error cause (previous + size)

private def runRequestSize (manifest : IntegrityCheckpoint) (index : Nat) : Nat :=
  ((manifest.runs[index]?).map (fun stamp => stamp.byteCount.toNat)).getD 0

open RecoveryRequestCount in
/-- A file's exact extent guard spends no payload requests. A reached
payload call may spend at most its requested length, including on error. -/
theorem readExactRecoveryFileWith_payloadCallsBound (path : FilePath) (expected : Nat) (mismatch : IO.Error)
    (readSize : FilePath → Except IO.Error Nat) (readPrefix : FilePath → Nat → EStateM IO.Error Nat ByteArray)
    (bounded : ∀ before, reached (readPrefix path expected before) ≤ before + expected) (before : Nat) :
    reached (readExactRecoveryFileWith path expected mismatch (fun target => liftExcept (readSize target))
      readPrefix before) ≤ before + expected := by
  unfold readExactRecoveryFileWith
  cases measured : readSize path with
  | error cause =>
    simp [measured, liftExcept, Bind.bind, EStateM.bind, throw, throwThe, MonadExceptOf.throw, EStateM.throw, reached]
  | ok actual =>
    by_cases fits : actual = expected ∧ expected < USize.size
    · cases payload : readPrefix path expected before with
      | error cause after =>
        simpa [measured, fits, payload, liftExcept, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure] using bounded before
      | ok bytes after =>
        by_cases exactSize : bytes.size = expected <;>
          simpa [measured, fits, payload, exactSize, liftExcept, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure,
            throw, throwThe, MonadExceptOf.throw, EStateM.throw, reached] using bounded before
    · simp [measured, fits, liftExcept, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure,
        throw, throwThe, MonadExceptOf.throw, EStateM.throw, reached]

private theorem runRequestSizes_exact (manifest : IntegrityCheckpoint)
    (count : manifest.runs.length = manifest.header.runCount.toNat) :
    (List.range manifest.header.runCount.toNat).map (runRequestSize manifest) =
      manifest.runs.map (fun stamp => stamp.byteCount.toNat) := by
  rw [← count]
  apply List.ext_getElem
  · simp
  · intro index _ bound
    have within : index < manifest.runs.length := by simpa using bound
    simp [runRequestSize, List.getElem?_eq_getElem within]

open RecoveryRequestCount in
/-- Sum the reached prefix callback costs in the actual run-index loop.
Rejections at a missing stamp, size lookup, or extent guard charge no
payload callback at that index. -/
theorem readIntegrityRunBytesSized_payloadCallsBound (dir : DiskDirectory) {manifest : IntegrityCheckpoint}
    {manifestBytes : ByteArray} (decoded : IntegrityCheckpoint.decode manifestBytes = .ok manifest)
    (readSize : FilePath → Except IO.Error Nat) (readPrefix : FilePath → Nat → EStateM IO.Error Nat ByteArray)
    (bounded : ∀ path count before, reached (readPrefix path count before) ≤ before + count) (before : Nat) :
    reached (readIntegrityRunBytesSized dir manifest (fun path => liftExcept (readSize path)) readPrefix before) ≤
      before + (manifest.runs.map (fun stamp => stamp.byteCount.toNat)).sum := by
  have each (index calls : Nat) :
      reached (readStampedRun dir manifest.runs.toArray (fun path => liftExcept (readSize path)) readPrefix
        manifest.header.generation index calls) ≤ calls + runRequestSize manifest index := by
    simp only [readStampedRun, runRequestSize, List.getElem?_toArray]
    cases declared : manifest.runs[index]? with
    | none => exact Nat.le_refl _
    | some stamp => exact readExactRecoveryFileWith_payloadCallsBound _ _ _ readSize readPrefix (bounded _ _) calls
  unfold readIntegrityRunBytesSized
  rw [readCheckpointRunBytes_eq_mapM]
  have bound := mapM_weightedBound _ (List.range manifest.header.runCount.toNat) (runRequestSize manifest) before each
  rwa [runRequestSizes_exact manifest (IntegrityCheckpoint.decode_spec decoded).2.2] at bound

/-- Count requested run payload bytes in the executable ordered loop,
including a prefix call that reports an error after being issued. -/
def countCheckpointRunBytes (dir : DiskDirectory) (manifest : IntegrityCheckpoint)
    (readSize : FilePath → Except IO.Error Nat) (readPrefix : FilePath → Nat → Except IO.Error ByteArray) : Nat :=
  requestedBytes ((readIntegrityRunBytesSized dir manifest (fun path => recordRequest 0 (readSize path))
    (fun path bytes => recordRequest bytes (readPrefix path bytes))) 0)

/-- Every run request reached after an accepted manifest counts toward its
stamp budget. A size rejection spends no payload bytes at that index,
and a reported read error can spend at most its already issued request. -/
theorem countCheckpointRunBytes_bound (dir : DiskDirectory) {manifest : IntegrityCheckpoint}
    {manifestBytes : ByteArray} (decoded : IntegrityCheckpoint.decode manifestBytes = .ok manifest)
    (readSize : FilePath → Except IO.Error Nat) (readPrefix : FilePath → Nat → Except IO.Error ByteArray) :
    countCheckpointRunBytes dir manifest readSize readPrefix ≤
      (manifest.runs.map (fun stamp => stamp.byteCount.toNat)).sum := by
  have measured (path : FilePath) : recordRequest 0 (readSize path) = liftExcept (readSize path) := by
    funext state
    cases readSize path <;> rfl
  have charged path count before :
      RecoveryRequestCount.reached (recordRequest count (readPrefix path count) before) ≤ before + count := by
    cases readPrefix path count <;> exact Nat.le_refl _
  unfold countCheckpointRunBytes
  simp only [measured]
  have same (report : EStateM.Result IO.Error Nat (List ByteArray)) :
      RecoveryRequestCount.reached report = requestedBytes report := by cases report <;> rfl
  simpa only [Nat.zero_add, same] using readIntegrityRunBytesSized_payloadCallsBound dir decoded readSize
    (fun path count => recordRequest count (readPrefix path count)) charged 0

open RecoveryRequestCount in
private theorem issuedStampedRun_bound (dir : DiskDirectory) (manifest : IntegrityCheckpoint)
    (readSize : FilePath → Except IO.Error Nat) (readPrefix : FilePath → Nat → Except IO.Error ByteArray)
    (index before : Nat) :
    RecoveryRequestCount.reached (readStampedRun dir manifest.runs.toArray
      (fun path => RecoveryRequestCount.issued (readSize path))
      (fun path count => RecoveryRequestCount.issued (readPrefix path count)) manifest.header.generation index before)
      ≤ before + 2 := by
  unfold readStampedRun
  cases declared : manifest.runs.toArray[index]? with
  | none => simp [throw, throwThe, MonadExceptOf.throw, EStateM.throw, reached]
  | some stamp =>
    dsimp only
    unfold readExactRecoveryFileWith
    apply bind_bound (first := 1) (second := 1)
    · simp [reached_issued]
    · intro actual after _
      by_cases extent : actual = stamp.byteCount.toNat ∧ stamp.byteCount.toNat < USize.size
      · simp only [ite_eq_left extent]
        apply bind_bound (first := 1) (second := 0)
        · simp [reached_issued]
        · intro payload final _
          by_cases size : payload.size = stamp.byteCount.toNat <;>
            simp [size, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure, throw, throwThe,
              MonadExceptOf.throw, EStateM.throw, reached]
      · simp [extent, Bind.bind, EStateM.bind, throw, throwThe, MonadExceptOf.throw, EStateM.throw, reached]

/-- An absent or rejected manifest selects no checkpoint runs. -/
noncomputable def decodedCheckpointRunCount : Except IO.Error (Option ByteArray) → Nat
  | .ok (some bytes) => ((IntegrityCheckpoint.decode bytes).toOption.map (·.header.runCount.toNat)).getD 0
  | _ => 0

open RecoveryRequestCount in
/-- At most one manifest read and two requests for each run in the decoded
manifest. An absent, rejected, or unreadable manifest opens no run. -/
theorem readIntegrityCheckpointSized_requestBound (dir : DiskDirectory)
    (readManifest : Except IO.Error (Option ByteArray)) (readSize : FilePath → Except IO.Error Nat)
    (readPrefix : FilePath → Nat → Except IO.Error ByteArray) (before : Nat) :
    RecoveryRequestCount.reached (readIntegrityCheckpointSized dir (RecoveryRequestCount.issued readManifest)
      (fun path => RecoveryRequestCount.issued (readSize path))
      (fun path count => RecoveryRequestCount.issued (readPrefix path count)) before) ≤
      before + (1 + 2 * decodedCheckpointRunCount readManifest) := by
  unfold readIntegrityCheckpointSized decodedCheckpointRunCount
  cases report : readManifest with
  | error cause => simp [issued, Bind.bind, EStateM.bind, reached]
  | ok value =>
    cases value with
    | none => simp [issued, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure, reached]
    | some bytes =>
      cases decoded : IntegrityCheckpoint.decode bytes with
      | error cause =>
        simp [issued, liftExcept, Except.mapError, decoded, Bind.bind, EStateM.bind, reached,
          throw, throwThe, MonadExceptOf.throw, EStateM.throw, Except.toOption]
      | ok manifest =>
        simp only [issued, Bind.bind, EStateM.bind, decoded, Except.mapError, liftExcept, Pure.pure,
          EStateM.pure, Except.toOption, Option.map_some, Option.getD_some]
        have runs : reached (readIntegrityRunBytesSized dir manifest (fun path => issued (readSize path))
            (fun path count => issued (readPrefix path count)) (before + 1)) ≤
            before + 1 + 2 * manifest.header.runCount.toNat := by
          unfold readIntegrityRunBytesSized
          rw [readCheckpointRunBytes_eq_mapM]
          simpa only [List.length_range] using mapM_bound _ (List.range manifest.header.runCount.toNat) (before + 1) 2
            (issuedStampedRun_bound dir manifest readSize readPrefix)
        cases outcome : readIntegrityRunBytesSized dir manifest (fun path => issued (readSize path))
            (fun path count => issued (readPrefix path count)) (before + 1) with
        | error cause count =>
          rw [outcome] at runs
          simp only [reached] at runs ⊢
          omega
        | ok files count =>
          rw [outcome] at runs
          cases loaded : loadIntegrityRunSet manifest files <;>
            simp only [loaded, EStateM.pure, throw, throwThe, MonadExceptOf.throw, EStateM.throw, reached] at runs ⊢ <;> omega

end Alvoki.Storage
