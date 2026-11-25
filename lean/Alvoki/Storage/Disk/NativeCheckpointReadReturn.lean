import Alvoki.Storage.Disk.IntegrityCheckpointSizedRead

namespace Alvoki.Storage

open System Manifest

variable {heap : Type}

/-- Distinguish a returned error from a guard failure in the shared exact
payload reader. The prefix callback, if reached, uses the checked size and
the heap supplied by the fixed size callback. -/
inductive ExactRecoveryFileReturn (path : FilePath) (expected : Nat) (mismatch : IO.Error)
    (readSize : FilePath → EStateM IO.Error heap Nat)
    (readPrefix : FilePath → Nat → EStateM IO.Error heap ByteArray) (entry : heap) :
    EStateM.Result IO.Error heap ByteArray → Prop where
  | sizeError {cause : IO.Error} {reached : heap} (reported : readSize path entry = .error cause reached) :
      ExactRecoveryFileReturn path expected mismatch readSize readPrefix entry (.error cause reached)
  | wrongSize {actual : Nat} {reached : heap}
      (reported : readSize path entry = .ok actual reached) (wrong : ¬ (actual = expected ∧ expected < USize.size)) :
      ExactRecoveryFileReturn path expected mismatch readSize readPrefix entry (.error mismatch reached)
  | prefixError {afterSize reached : heap} {cause : IO.Error}
      (sized : readSize path entry = .ok expected afterSize) (representable : expected < USize.size)
      (failed : readPrefix path expected afterSize = .error cause reached) :
      ExactRecoveryFileReturn path expected mismatch readSize readPrefix entry (.error cause reached)
  | wrongPrefix {afterSize reached : heap} {bytes : ByteArray}
      (sized : readSize path entry = .ok expected afterSize) (representable : expected < USize.size)
      (returned : readPrefix path expected afterSize = .ok bytes reached) (wrong : bytes.size ≠ expected) :
      ExactRecoveryFileReturn path expected mismatch readSize readPrefix entry (.error mismatch reached)
  | accepted {afterSize reached : heap} {bytes : ByteArray}
      (sized : readSize path entry = .ok expected afterSize) (representable : expected < USize.size)
      (returned : readPrefix path expected afterSize = .ok bytes reached) (exactSize : bytes.size = expected) :
      ExactRecoveryFileReturn path expected mismatch readSize readPrefix entry (.ok bytes reached)

/-- Classify the exact-size check and prefix read for a fixed production
callback pair. No reported success or preselected failure is required. -/
theorem ExactRecoveryFileReturn.classifies (path : FilePath) (expected : Nat) (mismatch : IO.Error)
    (readSize : FilePath → EStateM IO.Error heap Nat)
    (readPrefix : FilePath → Nat → EStateM IO.Error heap ByteArray) (entry : heap) :
    ExactRecoveryFileReturn path expected mismatch readSize readPrefix entry
      (readExactRecoveryFileWith path expected mismatch readSize readPrefix entry) := by
  simp only [readExactRecoveryFileWith, Bind.bind, EStateM.bind]
  cases sized : readSize path entry with
  | error cause reached => exact .sizeError sized
  | ok actual afterSize =>
    by_cases admitted : actual = expected ∧ expected < USize.size
    · simp only [ite_eq_left admitted, Pure.pure, EStateM.bind]
      cases read : readPrefix path expected afterSize with
      | error cause reached => exact .prefixError (admitted.1 ▸ sized) admitted.2 read
      | ok bytes reached =>
        by_cases same : bytes.size = expected
        · simp only [ite_eq_left same]
          exact .accepted (admitted.1 ▸ sized) admitted.2 read same
        · simp only [ite_eq_right same, EStateM.bind]
          exact .wrongPrefix (admitted.1 ▸ sized) admitted.2 read same
    · simp only [ite_eq_right admitted, EStateM.bind]
      exact .wrongSize sized admitted

private theorem mapM_firstError {α β : Type} (perform : α → EStateM IO.Error heap β)
    (items : List α) {entry reached : heap} {cause : IO.Error}
    (failed : (items.mapM perform) entry = .error cause reached) :
    ∃ earlier item rest found atIssue, items = earlier ++ item :: rest ∧
      (earlier.mapM perform) entry = .ok found atIssue ∧ perform item atIssue = .error cause reached := by
  induction items generalizing entry with
  | nil => simp [Pure.pure, EStateM.pure] at failed
  | cons item rest ih =>
    cases head : perform item entry with
    | error cause' reached' =>
      simp only [List.mapM_cons, Bind.bind, EStateM.bind, head, EStateM.Result.error.injEq] at failed
      obtain ⟨rfl, rfl⟩ := failed
      exact ⟨[], item, rest, [], entry, rfl, rfl, head⟩
    | ok value after =>
      have later : (rest.mapM perform) after = .error cause reached := by
        cases ran : (rest.mapM perform) after with
        | error cause' reached' =>
          simpa only [List.mapM_cons, Bind.bind, EStateM.bind, head, ran] using failed
        | ok found final =>
          simp [List.mapM_cons, Bind.bind, EStateM.bind, head, ran, Pure.pure, EStateM.pure] at failed
      obtain ⟨earlier, issuing, remaining, found, atIssue, order, prefixRead, rejected⟩ := ih later
      exact ⟨item :: earlier, issuing, remaining, value :: found, atIssue, congrArg (List.cons item) order,
        by simp [List.mapM_cons, Bind.bind, EStateM.bind, head, prefixRead, Pure.pure, EStateM.pure], rejected⟩

private theorem range_failedIndex {count index : Nat} {earlier rest : List Nat}
    (order : List.range count = earlier ++ index :: rest) : index < count ∧ earlier = List.range index := by
  have lengths := congrArg List.length order
  simp only [List.length_range, List.length_append, List.length_cons] at lengths
  have within : earlier.length < count := by omega
  have atIndex := congrArg (fun indices : List Nat => indices[earlier.length]?) order
  rw [List.getElem?_range within, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self] at atIndex
  have position : earlier.length = index := Option.some.inj atIndex
  refine ⟨position ▸ within, ?_⟩
  have taken := congrArg (List.take earlier.length) order
  rw [List.take_range, Nat.min_eq_left (Nat.le_of_lt within), List.take_left, position] at taken
  exact taken.symm

/-- The actual decoded generation's ordered run reader stopped at this
stamped file. Its own shorter loop supplies the state reached before the
failed size check or prefix read. -/
structure SelectedCheckpointRunFailure (directory : DiskDirectory) (manifest : IntegrityCheckpoint)
    (readSize : FilePath → EStateM IO.Error heap Nat)
    (readPrefix : FilePath → Nat → EStateM IO.Error heap ByteArray)
    (entry : heap) (cause : IO.Error) (reached : heap) : Prop where
  atRun : ∃ index < manifest.header.runCount.toNat, ∃ (stamp : RunIntegrity) (previous : List ByteArray) (atIssue : heap),
    manifest.runs[index]? = some stamp ∧
    readIntegrityRunBytesSized directory { manifest with header := { manifest.header with runCount := index.toUInt64 } }
      readSize readPrefix entry = .ok previous atIssue ∧
    ExactRecoveryFileReturn (directory.file (.run manifest.header.generation index)) stamp.byteCount.toNat
      (IO.userError checkpointIntegrityMismatch) readSize readPrefix atIssue (.error cause reached)

/-- Invert an ordinary error from the actual decoded checkpoint run loop
to its first failing file, without observing a separate run sequence. -/
theorem readIntegrityRunBytesSized_firstFailure (directory : DiskDirectory)
    {manifest : IntegrityCheckpoint} {raw : ByteArray} (decoded : IntegrityCheckpoint.decode raw = .ok manifest)
    (readSize : FilePath → EStateM IO.Error heap Nat)
    (readPrefix : FilePath → Nat → EStateM IO.Error heap ByteArray)
    {entry reached : heap} {cause : IO.Error}
    (failed : readIntegrityRunBytesSized directory manifest readSize readPrefix entry = .error cause reached) :
    SelectedCheckpointRunFailure directory manifest readSize readPrefix entry cause reached := by
  simp only [readIntegrityRunBytesSized, readCheckpointRunBytes_eq_mapM] at failed
  obtain ⟨earlier, index, remaining, previous, atIssue, order, prefixRead, rejected⟩ :=
    mapM_firstError _ _ failed
  obtain ⟨within, rfl⟩ := range_failedIndex order
  have fits : index < manifest.runs.length :=
    (IntegrityCheckpoint.decode_spec decoded).2.2.symm ▸ within
  let stamp := manifest.runs[index]'fits
  have found : manifest.runs[index]? = some stamp := List.getElem?_eq_getElem fits
  have shortened : index.toUInt64.toNat = index :=
    UInt64.toNat_ofNat_of_lt' (Nat.lt_trans within manifest.header.runCount.toNat_lt_size)
  refine ⟨index, within, stamp, previous, atIssue, found, ?_, ?_⟩
  · simpa only [readIntegrityRunBytesSized, readCheckpointRunBytes_eq_mapM, shortened] using prefixRead
  · have failedFile : readExactRecoveryFileWith (directory.file (.run manifest.header.generation index))
        stamp.byteCount.toNat (IO.userError checkpointIntegrityMismatch) readSize readPrefix atIssue = .error cause reached := by
      change ((do
          let some stamp := manifest.runs.toArray[index]? | throw (IO.userError checkpointIntegrityMismatch)
          readExactRecoveryFileWith (directory.file (.run manifest.header.generation index))
            stamp.byteCount.toNat (IO.userError checkpointIntegrityMismatch) readSize readPrefix) :
          EStateM IO.Error heap ByteArray) atIssue = .error cause reached at rejected
      simpa only [List.getElem?_toArray, found] using rejected
    simpa only [failedFile] using
      (ExactRecoveryFileReturn.classifies (directory.file (.run manifest.header.generation index))
        stamp.byteCount.toNat (IO.userError checkpointIntegrityMismatch) readSize readPrefix atIssue)

/-- Ordinary outcomes of the strict checkpoint reader. The manifest and
ordered run payloads are the values supplied by the same fixed callbacks. -/
inductive SizedCheckpointReadReturn (directory : DiskDirectory)
    (readManifest : EStateM IO.Error heap (Option ByteArray))
    (readSize : FilePath → EStateM IO.Error heap Nat)
    (readPrefix : FilePath → Nat → EStateM IO.Error heap ByteArray) (entry : heap) :
    EStateM.Result IO.Error heap (Option (PackedTable × UInt64)) → Prop where
  | manifestError {cause : IO.Error} {reached : heap}
      (failed : readManifest entry = .error cause reached) :
      SizedCheckpointReadReturn directory readManifest readSize readPrefix entry (.error cause reached)
  | absent {reached : heap} (read : readManifest entry = .ok none reached) :
      SizedCheckpointReadReturn directory readManifest readSize readPrefix entry (.ok none reached)
  | rejectedManifest {raw : ByteArray} {cause : String} {reached : heap}
      (read : readManifest entry = .ok (some raw) reached)
      (rejected : IntegrityCheckpoint.decode raw = .error cause) :
      SizedCheckpointReadReturn directory readManifest readSize readPrefix entry (.error (IO.userError cause) reached)
  | runError {raw : ByteArray} {manifest : IntegrityCheckpoint} {cause : IO.Error} {afterManifest reached : heap}
      (read : readManifest entry = .ok (some raw) afterManifest)
      (decoded : IntegrityCheckpoint.decode raw = .ok manifest)
      (failed : readIntegrityRunBytesSized directory manifest readSize readPrefix afterManifest = .error cause reached)
      (first : SelectedCheckpointRunFailure directory manifest readSize readPrefix afterManifest cause reached) :
      SizedCheckpointReadReturn directory readManifest readSize readPrefix entry (.error cause reached)
  | invalidRunSet {raw : ByteArray} {manifest : IntegrityCheckpoint} {files : List ByteArray}
      {cause : String} {afterManifest reached : heap}
      (read : readManifest entry = .ok (some raw) afterManifest)
      (decoded : IntegrityCheckpoint.decode raw = .ok manifest)
      (runs : readIntegrityRunBytesSized directory manifest readSize readPrefix afterManifest = .ok files reached)
      (rejected : loadIntegrityRunSet manifest files = .error cause) :
      SizedCheckpointReadReturn directory readManifest readSize readPrefix entry (.error (IO.userError cause) reached)
  | restored {raw : ByteArray} {manifest : IntegrityCheckpoint} {files : List ByteArray} {table : PackedTable}
      {afterManifest reached : heap}
      (read : readManifest entry = .ok (some raw) afterManifest)
      (decoded : IntegrityCheckpoint.decode raw = .ok manifest)
      (runs : readIntegrityRunBytesSized directory manifest readSize readPrefix afterManifest = .ok files reached)
      (loaded : loadIntegrityRunSet manifest files = .ok table) :
      SizedCheckpointReadReturn directory readManifest readSize readPrefix entry
        (.ok (some (table, manifest.header.generation)) reached)

/-- Derive the reached checkpoint branch, including its first failing run
if any. The pure restore sees the exact bytes returned in manifest order. -/
theorem SizedCheckpointReadReturn.classifies (directory : DiskDirectory)
    (readManifest : EStateM IO.Error heap (Option ByteArray))
    (readSize : FilePath → EStateM IO.Error heap Nat)
    (readPrefix : FilePath → Nat → EStateM IO.Error heap ByteArray) (entry : heap) :
    SizedCheckpointReadReturn directory readManifest readSize readPrefix entry
      (readIntegrityCheckpointSized directory readManifest readSize readPrefix entry) := by
  simp only [readIntegrityCheckpointSized, Bind.bind, EStateM.bind]
  cases observed : readManifest entry with
  | error cause reached => exact .manifestError observed
  | ok found afterManifest =>
    cases found with
    | none => exact .absent observed
    | some raw =>
      dsimp only
      cases decoded : IntegrityCheckpoint.decode raw with
      | error cause =>
        simpa [decoded, liftExcept, Except.mapError, Bind.bind, EStateM.bind, throw, throwThe,
          MonadExceptOf.throw, EStateM.throw] using
          (SizedCheckpointReadReturn.rejectedManifest (directory := directory) (readSize := readSize)
            (readPrefix := readPrefix) observed decoded)
      | ok manifest =>
        simp only [liftExcept, Except.mapError, Pure.pure, EStateM.pure, EStateM.bind]
        cases runs : readIntegrityRunBytesSized directory manifest readSize readPrefix afterManifest with
        | error cause reached =>
          exact .runError observed decoded runs (readIntegrityRunBytesSized_firstFailure directory decoded _ _ runs)
        | ok files reached =>
          cases restored : loadIntegrityRunSet manifest files with
          | error cause =>
            simpa [restored, liftExcept, Except.mapError, Bind.bind, EStateM.bind, throw, throwThe,
              MonadExceptOf.throw, EStateM.throw] using
              (SizedCheckpointReadReturn.invalidRunSet observed decoded runs restored)
          | ok table =>
            simpa only [restored, EStateM.pure] using
              (SizedCheckpointReadReturn.restored observed decoded runs restored)

end Alvoki.Storage
