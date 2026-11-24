import Alvoki.Storage.Disk.DiskPaths
import Alvoki.Storage.Disk.IntegrityCheckpointRead
import Alvoki.Storage.Disk.RecoverySizedReads

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

private def countedRun (dir : DiskDirectory) (manifest : IntegrityCheckpoint)
    (readSize : FilePath → Except IO.Error Nat) (readPrefix : FilePath → Nat → Except IO.Error ByteArray)
    (index : Nat) : EStateM IO.Error Nat ByteArray :=
  readStampedRun dir manifest.runs.toArray (fun path => recordRequest 0 (readSize path))
    (fun path bytes => recordRequest bytes (readPrefix path bytes)) manifest.header.generation index

private theorem countedRun_le (dir : DiskDirectory) (manifest : IntegrityCheckpoint)
    (readSize : FilePath → Except IO.Error Nat) (readPrefix : FilePath → Nat → Except IO.Error ByteArray)
    (index initial : Nat) :
    requestedBytes (countedRun dir manifest readSize readPrefix index initial) ≤
      initial + runRequestSize manifest index := by
  unfold countedRun readStampedRun runRequestSize
  simp only [List.getElem?_toArray]
  cases declared : manifest.runs[index]? with
  | none => exact Nat.le_refl _
  | some stamp =>
    change requestedBytes (readExactRecoveryFileWith (m := EStateM IO.Error Nat) _ _ _ _ _ initial) ≤ initial + stamp.byteCount.toNat
    unfold readExactRecoveryFileWith
    cases measured : readSize (dir.file (.run manifest.header.generation index)) with
    | error cause => simp [recordRequest, measured, Bind.bind, EStateM.bind, requestedBytes]
    | ok actual =>
      by_cases fits : actual = stamp.byteCount.toNat ∧ stamp.byteCount.toNat < USize.size
      · cases read : readPrefix (dir.file (.run manifest.header.generation index)) stamp.byteCount.toNat with
        | error cause => simp [recordRequest, measured, fits, read, Bind.bind, EStateM.bind, requestedBytes]
        | ok payload =>
          by_cases exact : payload.size = stamp.byteCount.toNat <;>
            simp [recordRequest, measured, fits, read, exact, Bind.bind, EStateM.bind, requestedBytes,
              Pure.pure, EStateM.pure, throw, throwThe, MonadExceptOf.throw, EStateM.throw]
      · simp [recordRequest, measured, fits, Bind.bind, EStateM.bind, requestedBytes,
          throw, throwThe, MonadExceptOf.throw, EStateM.throw]

private theorem checkpointRequests_le (dir : DiskDirectory) (manifest : IntegrityCheckpoint)
    (readSize : FilePath → Except IO.Error Nat) (readPrefix : FilePath → Nat → Except IO.Error ByteArray)
    (indices : List Nat) (initial : Nat) :
    requestedBytes ((indices.mapM (countedRun dir manifest readSize readPrefix)) initial) ≤
      initial + (indices.map (runRequestSize manifest)).sum := by
  induction indices generalizing initial with
  | nil => exact Nat.le_refl _
  | cons index rest ih =>
    have first := countedRun_le dir manifest readSize readPrefix index initial
    simp only [List.mapM_cons, Bind.bind, EStateM.bind, List.map_cons, List.sum_cons]
    cases head : countedRun dir manifest readSize readPrefix index initial with
    | error cause final =>
      rw [head] at first
      simp only [requestedBytes] at first ⊢
      omega
    | ok payload reached =>
      have later := ih reached
      rw [head] at first
      cases tail : (rest.mapM (countedRun dir manifest readSize readPrefix)) reached with
      | error cause final =>
        rw [tail] at later
        simp only [requestedBytes] at first later
        simp only [tail, requestedBytes]
        omega
      | ok payloads final =>
        rw [tail] at later
        simp only [requestedBytes] at first later
        simp only [tail, requestedBytes, Pure.pure, EStateM.pure]
        omega

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
  unfold countCheckpointRunBytes readIntegrityRunBytesSized
  rw [readCheckpointRunBytes_eq_mapM]
  have bound := checkpointRequests_le dir manifest readSize readPrefix (List.range manifest.header.runCount.toNat) 0
  rw [runRequestSizes_exact manifest (IntegrityCheckpoint.decode_spec decoded).2.2, Nat.zero_add] at bound
  exact bound

end Alvoki.Storage
