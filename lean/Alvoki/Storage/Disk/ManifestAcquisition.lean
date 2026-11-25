import Alvoki.Storage.Disk.ManifestIntegrity
import Alvoki.Storage.Disk.ReadRecoveryPrefix

namespace Alvoki.Manifest

open ByteWords

/-- The count word in the fixed six-word header determines the stamp bytes. -/
def IntegrityCheckpoint.declaredStampBytes (header : ByteArray) : Nat :=
  16 * (word header 32).toNat

/-- Keep at most one byte beyond the declared manifest size. -/
def IntegrityCheckpoint.acquisitionSize (bytes : ByteArray) : Nat :=
  min bytes.size (48 + declaredStampBytes bytes + 1)

theorem IntegrityCheckpoint.decode_acquisitionPrefix (bytes : ByteArray) :
    decode (bytes.extract 0 (acquisitionSize bytes)) = decode bytes := by
  unfold acquisitionSize declaredStampBytes
  by_cases fits : bytes.size ≤ 48 + 16 * (word bytes 32).toNat + 1
  · simp [Nat.min_eq_left fits]
  · let cap := 48 + 16 * (word bytes 32).toNat + 1
    have within : cap ≤ bytes.size := Nat.le_of_lt (Nat.lt_of_not_ge fits)
    rw [show min bytes.size cap = cap from Nat.min_eq_right within]
    have count : word (bytes.extract 0 cap) 32 = word bytes 32 := by
      simpa only [Nat.zero_add] using word_extract bytes 0 cap 32 (by dsimp [cap]; omega) within
    have size : (bytes.extract 0 cap).size = cap := by
      simp [ByteArray.size_extract, Nat.min_eq_left within]
    have enough : ¬ bytes.size < 48 := by dsimp [cap] at within; omega
    have cappedEnough : ¬ cap < 48 := by dsimp [cap]; omega
    have tooLong : bytes.size ≠ 48 + 16 * (word bytes 32).toNat := by omega
    have cappedTooLong : cap ≠ 48 + 16 * (word bytes 32).toNat := by dsimp [cap]; omega
    simp only [decode, enough, cappedEnough, size, count, ite_eq_left tooLong, ite_eq_left cappedTooLong, ↓reduceIte]

/-- An accepted manifest still supplies all its exact original bytes. -/
theorem IntegrityCheckpoint.acquisitionPrefix_eq_of_decode {bytes : ByteArray} {manifest : IntegrityCheckpoint}
    (accepted : decode bytes = .ok manifest) :
    bytes.extract 0 (acquisitionSize bytes) = bytes := by
  have bounded := (decode_acquisitionPrefix bytes).trans accepted
  exact (decode_spec bounded).1.symm.trans (decode_spec accepted).1

end Alvoki.Manifest

namespace Alvoki.Storage

open Manifest

/-- Model acquisition on one opened file with a checked extent. Read
through the fixed header, followed by the declared stamps and at most one
oversize witness. The machine guard covers the accumulated prefix. -/
@[inline] def readIntegrityManifestPrefixWith [Monad m] [MonadExceptOf IO.Error m]
    (read : USize → m ByteArray) (extent : Nat) : m ByteArray := do
  let mismatch := IO.userError "integrity manifest extent changed while reading"
  let header ← readExactPrefixWith mismatch read (min 48 extent) .empty
  if header.size < 48 then return header
  let rest := min (extent - 48) (IntegrityCheckpoint.declaredStampBytes header + 1)
  unless 48 + rest < USize.size do
    throw (IO.userError "integrity manifest prefix exceeds machine size")
  readExactPrefixWith mismatch read rest header

/-- Given the extent and successful chunk observations for the same stable
opened description, acquisition supplies exactly the decoder's prefix.
Only that prefix has to fit the platform, with no separate run-count cap. -/
theorem readIntegrityManifestPrefixWith_completes
    {source : ByteArray} {read : USize → EStateM IO.Error Nat ByteArray} {extent : Nat}
    (checked : extent = source.size)
    (observes : PrefixChunkObserves source read) (available : PrefixChunksAvailable source read)
    (fits : IntegrityCheckpoint.acquisitionSize source < USize.size) :
    readIntegrityManifestPrefixWith read extent 0 =
      .ok (source.extract 0 (IntegrityCheckpoint.acquisitionSize source)) (IntegrityCheckpoint.acquisitionSize source) := by
  subst extent
  let mismatch := IO.userError "integrity manifest extent changed while reading"
  have headerFits : min 48 source.size < USize.size :=
    Nat.lt_of_le_of_lt (Nat.min_le_left ..) (Nat.lt_of_lt_of_le (by decide) USize.le_size)
  have headerRead := readExactPrefixWith_completesAtStart mismatch observes available _
    headerFits (Nat.min_le_right 48 source.size)
  dsimp [mismatch] at headerRead
  unfold readIntegrityManifestPrefixWith
  simp only [Bind.bind, EStateM.bind, headerRead]
  by_cases short : source.size < 48
  · have acquisition : IntegrityCheckpoint.acquisitionSize source = source.size := by
      unfold IntegrityCheckpoint.acquisitionSize
      exact Nat.min_eq_left (by omega)
    simp [Nat.min_eq_right (Nat.le_of_lt short), short, acquisition, Pure.pure, EStateM.pure]
  · have enough := Nat.le_of_not_gt short
    have fullHeader := Nat.min_eq_left enough
    rw [fullHeader]
    let header := source.extract 0 48
    have headerSize : (source.extract 0 48).size = 48 := by
      simp [ByteArray.size_extract, Nat.min_eq_left enough]
    have declared : IntegrityCheckpoint.declaredStampBytes header =
        IntegrityCheckpoint.declaredStampBytes source := by
      unfold IntegrityCheckpoint.declaredStampBytes header
      rw [ByteWords.word_extract _ 0 48 32 (by decide) enough]
    let rest := min (source.size - 48) (IntegrityCheckpoint.declaredStampBytes header + 1)
    have stop : 48 + rest = IntegrityCheckpoint.acquisitionSize source := by
      dsimp only [rest, IntegrityCheckpoint.acquisitionSize]
      rw [declared]
      omega
    have within : rest < USize.size := by omega
    have covered : 48 + rest ≤ source.size :=
      stop ▸ Nat.min_le_left ..
    have tailRead := readExactPrefixWith_completes mismatch observes available rest within
      (offset := 48) (bytes := header) covered
    have concatenated : header ++ source.extract 48 (48 + rest) = source.extract 0 (48 + rest) := by
      exact (ByteArray.extract_eq_extract_append_extract 48 (by omega) (by omega)).symm
    have capFits : 48 + rest < USize.size := stop ▸ fits
    rw [concatenated, stop] at tailRead
    dsimp only [header, rest] at capFits
    simp only [headerSize, Nat.lt_irrefl, ↓reduceIte, ite_eq_left capFits]
    exact tailRead

/-- Every strict accepted manifest whose bytes fit in memory is returned
intact. The cursor reaches exactly the end of that file. -/
theorem readIntegrityManifestPrefixWith_accepted
    {source : ByteArray} {read : USize → EStateM IO.Error Nat ByteArray}
    {manifest : IntegrityCheckpoint} (accepted : IntegrityCheckpoint.decode source = .ok manifest)
    (observes : PrefixChunkObserves source read) (available : PrefixChunksAvailable source read)
    (fits : source.size < USize.size) :
    readIntegrityManifestPrefixWith read source.size 0 = .ok source source.size := by
  have exactBytes := IntegrityCheckpoint.acquisitionPrefix_eq_of_decode accepted
  have noMore : IntegrityCheckpoint.acquisitionSize source ≤ source.size := Nat.min_le_left ..
  have atEnd : IntegrityCheckpoint.acquisitionSize source = source.size := by
    simpa [ByteArray.size_extract, Nat.min_eq_left noMore] using congrArg ByteArray.size exactBytes
  rw [readIntegrityManifestPrefixWith_completes rfl observes available (Nat.lt_of_le_of_lt noMore fits),
    exactBytes, atEnd]

end Alvoki.Storage
