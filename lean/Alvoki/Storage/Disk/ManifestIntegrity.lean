import Alvoki.Storage.Disk.Manifest
import ByteWords

namespace Alvoki.Manifest
open Alvoki.ByteWords

/-- FNV-1a over the complete bytes of a checkpoint run. Distinct byte
sequences can share the same checksum. -/
def checksumRun (bytes : ByteArray) : UInt64 :=
  bytes.foldl (fun hash byte => (hash ^^^ byte.toUInt64) * 1099511628211) 14695981039346656037

structure RunIntegrity where
  byteCount : UInt64
  checksum : UInt64
  deriving Repr, DecidableEq

def RunIntegrity.ofBytes (bytes : ByteArray) : RunIntegrity :=
  ⟨bytes.size.toUInt64, checksumRun bytes⟩

def RunIntegrity.matches (expected : RunIntegrity) (bytes : ByteArray) : Bool :=
  bytes.size == expected.byteCount.toNat && checksumRun bytes == expected.checksum

theorem RunIntegrity.matches_iff (expected : RunIntegrity) (bytes : ByteArray) :
    expected.matches bytes = true ↔
      bytes.size = expected.byteCount.toNat ∧ checksumRun bytes = expected.checksum := by
  simp [RunIntegrity.matches]

structure IntegrityCheckpoint where
  header : Checkpoint
  runs : List RunIntegrity
  deriving Repr, DecidableEq

def IntegrityCheckpoint.fromRuns (header : Checkpoint) (files : List ByteArray) : IntegrityCheckpoint :=
  ⟨header, files.map RunIntegrity.ofBytes⟩

private def matchingRuns : List RunIntegrity → List ByteArray → Bool
  | [], [] => true
  | expected :: remaining, bytes :: files => expected.matches bytes && matchingRuns remaining files
  | _, _ => false

/-- Check the advertised run count and each observed file at its index. -/
def IntegrityCheckpoint.validateRuns (manifest : IntegrityCheckpoint) (files : List ByteArray) : Bool :=
  manifest.runs.length == manifest.header.runCount.toNat && matchingRuns manifest.runs files

private theorem matchingRuns_iff (expected : List RunIntegrity) (files : List ByteArray) :
    matchingRuns expected files = true ↔ expected.length = files.length ∧
      ∀ (index : Nat) (stamp : RunIntegrity) (bytes : ByteArray),
        expected[index]? = some stamp → files[index]? = some bytes →
        bytes.size = stamp.byteCount.toNat ∧ checksumRun bytes = stamp.checksum := by
  induction expected generalizing files with
  | nil => cases files <;> simp [matchingRuns]
  | cons first rest ih =>
    cases files with
    | nil => simp [matchingRuns]
    | cons bytes files =>
      rw [matchingRuns, Bool.and_eq_true_iff, RunIntegrity.matches_iff, ih]
      constructor
      · rintro ⟨head, lengths, tail⟩
        refine ⟨congrArg Nat.succ lengths, ?_⟩
        intro index stamp loaded expectedAt observedAt
        cases index with
        | zero => simpa using (Option.some.inj expectedAt ▸ Option.some.inj observedAt ▸ head)
        | succ index => exact tail index stamp loaded expectedAt observedAt
      · rintro ⟨lengths, matched⟩
        refine ⟨matched 0 first bytes rfl rfl, Nat.succ.inj lengths, ?_⟩
        exact fun index stamp loaded expectedAt observedAt =>
          matched (index + 1) stamp loaded expectedAt observedAt

theorem IntegrityCheckpoint.validateRuns_iff (manifest : IntegrityCheckpoint) (files : List ByteArray) :
    manifest.validateRuns files = true ↔
      manifest.runs.length = manifest.header.runCount.toNat ∧ manifest.runs.length = files.length ∧
      ∀ (index : Nat) (stamp : RunIntegrity) (bytes : ByteArray),
        manifest.runs[index]? = some stamp → files[index]? = some bytes →
        bytes.size = stamp.byteCount.toNat ∧ checksumRun bytes = stamp.checksum := by
  simp [IntegrityCheckpoint.validateRuns, matchingRuns_iff]

theorem IntegrityCheckpoint.rejects_run_count {manifest : IntegrityCheckpoint} {files : List ByteArray}
    (wrongCount : files.length ≠ manifest.header.runCount.toNat) : manifest.validateRuns files = false := by
  apply Bool.eq_false_iff.mpr
  intro accepted
  obtain ⟨recorded, observed, _⟩ := (manifest.validateRuns_iff files).mp accepted
  exact wrongCount (observed.symm.trans recorded)

theorem IntegrityCheckpoint.validateRuns_fromRuns (header : Checkpoint) (files : List ByteArray)
    (count : files.length = header.runCount.toNat)
    (fits : ∀ bytes ∈ files, bytes.size < UInt64.size) :
    (IntegrityCheckpoint.fromRuns header files).validateRuns files = true := by
  rw [IntegrityCheckpoint.validateRuns_iff]
  refine ⟨by simpa [IntegrityCheckpoint.fromRuns] using count, by simp [IntegrityCheckpoint.fromRuns], ?_⟩
  intro index stamp bytes expectedAt observedAt
  rw [IntegrityCheckpoint.fromRuns, List.getElem?_map, observedAt] at expectedAt
  cases Option.some.inj expectedAt
  exact ⟨(UInt64.toNat_ofNat_of_lt' (fits bytes (List.mem_of_getElem? observedAt))).symm, rfl⟩

/-- A changed file at a recorded index is rejected when its byte length or
FNV-1a checksum differs from the recorded value. -/
theorem IntegrityCheckpoint.rejects_run {manifest : IntegrityCheckpoint} {files : List ByteArray}
    {index : Nat} {stamp : RunIntegrity} {bytes : ByteArray}
    (recorded : manifest.runs[index]? = some stamp) (observed : files[index]? = some bytes)
    (differs : bytes.size ≠ stamp.byteCount.toNat ∨ checksumRun bytes ≠ stamp.checksum) :
    manifest.validateRuns files = false := by
  apply Bool.eq_false_iff.mpr
  intro accepted
  have matched := ((manifest.validateRuns_iff files).mp accepted).2.2 index stamp bytes recorded observed
  exact differs.elim (fun length => length matched.1) (fun checksum => checksum matched.2)

theorem IntegrityCheckpoint.rejects_changed_run {header : Checkpoint} {original observed : List ByteArray}
    {index : Nat} {written loaded : ByteArray}
    (originalAt : original[index]? = some written) (observedAt : observed[index]? = some loaded)
    (fits : written.size < UInt64.size)
    (differs : loaded.size ≠ written.size ∨ checksumRun loaded ≠ checksumRun written) :
    (IntegrityCheckpoint.fromRuns header original).validateRuns observed = false := by
  have recorded : (IntegrityCheckpoint.fromRuns header original).runs[index]? =
      some (RunIntegrity.ofBytes written) := by
    simp [IntegrityCheckpoint.fromRuns, List.getElem?_map, originalAt]
  apply IntegrityCheckpoint.rejects_run recorded observedAt
  simpa [RunIntegrity.ofBytes, UInt64.toNat_ofNat_of_lt' fits] using differs

def integrityMagic : UInt64 := 0x32464e4d4f564c41

private def integrityHeader (header : Checkpoint) : List UInt64 :=
  [integrityMagic, header.generation, header.committed, header.floor, header.runCount]

private def runFields : List RunIntegrity → List UInt64
  | [] => []
  | stamp :: rest => stamp.byteCount :: stamp.checksum :: runFields rest

@[simp] private theorem runFields_length (runs : List RunIntegrity) :
    (runFields runs).length = 2 * runs.length := by
  induction runs with
  | nil => rfl
  | cons head rest ih => simp [runFields, ih]; omega

private def readRunFields : List UInt64 → Option (List RunIntegrity)
  | [] => some []
  | count :: checksum :: rest => (readRunFields rest).map (⟨count, checksum⟩ :: ·)
  | [_] => none

@[simp] private theorem readRunFields_runFields (runs : List RunIntegrity) :
    readRunFields (runFields runs) = some runs := by
  induction runs with
  | nil => rfl
  | cons head rest ih => cases head; simp [runFields, readRunFields, ih]

private theorem runFields_readRunFields {words : List UInt64} {runs : List RunIntegrity}
    (read : readRunFields words = some runs) : runFields runs = words := by
  induction words using readRunFields.induct generalizing runs with
  | case1 => cases read; rfl
  | case2 count checksum rest ih =>
    obtain ⟨decoded, accepted, rfl⟩ := Option.map_eq_some_iff.mp read
    simp [runFields, ih accepted]
  | case3 => contradiction

private def integrityWords (manifest : IntegrityCheckpoint) : List UInt64 :=
  let header := integrityHeader manifest.header
  let runs := runFields manifest.runs
  header ++ (checksumWords (header ++ runs) :: runs)

private theorem appendWords (words : List UInt64) (initial : ByteArray) :
    words.foldl pushWordFast initial = initial ++ encodeWords words := by
  induction words generalizing initial with
  | nil => simp [encodeWords]
  | cons head tail ih =>
    rw [List.foldl_cons, ih, pushWordFast_append, ByteArray.append_assoc]
    rfl

/-- V2 stores the six-word manifest prefix followed by two words per run.
The checksum in word five covers the preceding header and the ordered run
integrity table. Each word is an unsigned little-endian 64-bit integer. -/
def IntegrityCheckpoint.encode (manifest : IntegrityCheckpoint) : ByteArray :=
  let words := integrityWords manifest
  words.foldl pushWordFast (ByteArray.emptyWithCapacity (8 * words.length))

private theorem encode_reference (manifest : IntegrityCheckpoint) :
    manifest.encode = encodeWords (integrityWords manifest) := by
  unfold IntegrityCheckpoint.encode
  rw [appendWords]
  change ByteArray.empty ++ encodeWords (integrityWords manifest) = _
  simp

@[simp] theorem IntegrityCheckpoint.encode_size (manifest : IntegrityCheckpoint) :
    manifest.encode.size = 48 + 16 * manifest.runs.length := by
  simp [encode_reference, integrityWords, integrityHeader]
  omega

private theorem encodedRunCount (manifest : IntegrityCheckpoint) :
    word manifest.encode 32 = manifest.header.runCount := by
  rw [encode_reference]
  change word (encodeWords (integrityWords manifest)) (8 * 4) = _
  rw [word_encodeWords]
  · rfl
  · simp [integrityWords, integrityHeader]

private def wordsFromBytes (bytes : ByteArray) : List UInt64 :=
  (List.range (bytes.size / 8)).map fun index => word bytes (8 * index)

@[simp] private theorem wordsFromBytes_encodeWords (words : List UInt64) :
    wordsFromBytes (encodeWords words) = words := by
  apply List.ext_getElem
  · simp [wordsFromBytes]
  · intro index _ within
    simpa [wordsFromBytes] using word_encodeWords words index within

private theorem encodeWords_wordsFromBytes (bytes : ByteArray) (aligned : bytes.size % 8 = 0) :
    encodeWords (wordsFromBytes bytes) = bytes := by
  apply eq_of_aligned_words
  · simp [wordsFromBytes]
    omega
  · intro index within
    have existsWord : index < (wordsFromBytes bytes).length := by
      simp [wordsFromBytes]
      omega
    rw [word_encodeWords _ _ existsWord]
    simp [wordsFromBytes]

private def decodeIntegrityWords : List UInt64 → Except String IntegrityCheckpoint
  | tag :: generation :: committed :: floor :: count :: checksum :: runWords => do
    if tag != integrityMagic then throw "invalid integrity manifest version"
    if committed < floor then throw "manifest floor exceeds the watermark"
    if runWords.length != 2 * count.toNat then throw "integrity manifest run count mismatch"
    if checksum != checksumWords ([tag, generation, committed, floor, count] ++ runWords) then
      throw "integrity manifest checksum mismatch"
    let some runs := readRunFields runWords | throw "incomplete manifest run integrity record"
    return ⟨⟨generation, committed, floor, count⟩, runs⟩
  | _ => .error "invalid integrity manifest length"

def IntegrityCheckpoint.decode (bytes : ByteArray) : Except String IntegrityCheckpoint :=
  if bytes.size < 48 then .error "invalid integrity manifest length"
  else if bytes.size ≠ 48 + 16 * (word bytes 32).toNat then .error "integrity manifest run count mismatch"
  else decodeIntegrityWords (wordsFromBytes bytes)

theorem IntegrityCheckpoint.decode_encode (manifest : IntegrityCheckpoint)
    (valid : manifest.header.floor ≤ manifest.header.committed)
    (count : manifest.runs.length = manifest.header.runCount.toNat) :
    IntegrityCheckpoint.decode manifest.encode = .ok manifest := by
  have enough : ¬ manifest.encode.size < 48 := by rw [manifest.encode_size]; omega
  have sized : manifest.encode.size = 48 + 16 * (word manifest.encode 32).toNat := by
    rw [manifest.encode_size, encodedRunCount, count]
  rw [IntegrityCheckpoint.decode, ite_eq_right enough, ite_eq_right (fun different => different sized),
    encode_reference, wordsFromBytes_encodeWords]
  simp [integrityWords, integrityHeader, decodeIntegrityWords, UInt64.not_lt.mpr valid, count] <;> rfl

private theorem decodeIntegrityWords_spec {words : List UInt64} {manifest : IntegrityCheckpoint}
    (accepted : decodeIntegrityWords words = .ok manifest) :
    integrityWords manifest = words ∧ manifest.header.floor ≤ manifest.header.committed ∧
      manifest.runs.length = manifest.header.runCount.toNat := by
  rcases words with _ | ⟨tag, _ | ⟨generation, _ | ⟨committed, _ | ⟨floor, _ |
    ⟨count, _ | ⟨checksum, runWords⟩⟩⟩⟩⟩⟩ <;> try contradiction
  simp only [decodeIntegrityWords, Bind.bind, Except.bind] at accepted
  split at accepted
  · contradiction
  rename_i tagValid
  split at accepted
  · contradiction
  rename_i floorValid
  split at accepted
  · contradiction
  rename_i countValid
  split at accepted
  · contradiction
  rename_i checksumValid
  split at accepted
  · rename_i runs decoded
    cases accepted
    have fields := runFields_readRunFields decoded
    have version : tag = integrityMagic := by simpa using tagValid
    have checksumEq : checksum = checksumWords ([tag, generation, committed, floor, count] ++ runWords) := by
      simpa using checksumValid
    have expectedLength : runWords.length = 2 * count.toNat := by simpa using countValid
    refine ⟨by simp [integrityWords, integrityHeader, fields, version, checksumEq],
      UInt64.not_lt.mp floorValid, ?_⟩
    have length := congrArg List.length fields
    simp only [runFields_length] at length
    change runs.length = count.toNat
    omega
  · contradiction

/-- Accepted integrity manifests have an exact byte re-encoding. -/
theorem IntegrityCheckpoint.decode_spec {bytes : ByteArray} {manifest : IntegrityCheckpoint}
    (accepted : IntegrityCheckpoint.decode bytes = .ok manifest) :
    manifest.encode = bytes ∧ manifest.header.floor ≤ manifest.header.committed ∧
      manifest.runs.length = manifest.header.runCount.toNat := by
  unfold IntegrityCheckpoint.decode at accepted
  split at accepted
  · contradiction
  split at accepted
  · contradiction
  rename_i expectedSize
  have sized : bytes.size = 48 + 16 * (word bytes 32).toNat := by simpa using expectedSize
  have aligned : bytes.size % 8 = 0 := by omega
  obtain ⟨encoded, floor, count⟩ := decodeIntegrityWords_spec accepted
  exact ⟨by rw [encode_reference, encoded, encodeWords_wordsFromBytes bytes aligned], floor, count⟩

theorem IntegrityCheckpoint.encodedTag (manifest : IntegrityCheckpoint) : word manifest.encode 0 = integrityMagic := by
  rw [encode_reference]
  change word (encodeWords (integrityWords manifest)) (8 * 0) = _
  rw [word_encodeWords]
  · rfl
  · simp [integrityWords, integrityHeader]

end Alvoki.Manifest
