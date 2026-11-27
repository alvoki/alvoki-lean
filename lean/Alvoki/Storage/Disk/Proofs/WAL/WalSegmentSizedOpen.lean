import Alvoki.Storage.Disk.RecoverySizedReads
import Alvoki.Storage.Disk.WalSegmentBoundedOpen

namespace Alvoki.Storage.WalSegmentRepair

open System
open WAL (frameSize)

private def selectedSpanError : IO.Error := IO.userError "invalid selected WAL segment spans"

private def readSizedSeal [Monad m] [MonadExceptOf IO.Error m] (dir : DiskDirectory)
    (readSize : FilePath → m Nat) (readPrefix : FilePath → Nat → m ByteArray)
    (extent : WalReadExtent) : m (Nat × ByteArray) := do
  let bytes ← readExactRecoveryFileWith (dir.file (.walSegment extent.first)) extent.bytes
    selectedSpanError readSize readPrefix
  pure (extent.first, bytes)

def readSizedWalSeals [Monad m] [MonadExceptOf IO.Error m] (dir : DiskDirectory)
    (readSize : FilePath → m Nat) (readPrefix : FilePath → Nat → m ByteArray)
    (extents : List WalReadExtent) : m (List (Nat × ByteArray)) :=
  extents.mapM (readSizedSeal dir readSize readPrefix)

/-- Use the same canonical selected inventory, with each sealed file
admitted at its exact adjacent-offset span before any bytes are requested.
The keeper retains the existing marker-prefix and physical-size rule. -/
def readSelectedWithSizedSeals [Monad m] [MonadExceptOf IO.Error m]
    (dir : DiskDirectory) (watermark : Nat) (length : UInt64)
    (list : FilePath → m (Array IO.FS.DirEntry)) (lstat : FilePath → m (Except IO.Error IO.FS.Metadata))
    (readSize : FilePath → m Nat) (readSealedPrefix : FilePath → Nat → m ByteArray)
    (readKeeperPrefix : FilePath → Nat → m KeeperPrefix) :
    m (WalSegmentMarkerReads × Nat) :=
  withAbsoluteWalCutoff watermark length fun through => do
    let entries ← list dir.path
    let offsets ← scanWalSegmentOffsets (probeWalSegmentWith dir lstat) (entries.toList.map (·.fileName))
    let some (required, newer) := selectWalSegmentReadsThrough offsets watermark through
      | throw (IO.userError "no WAL segment covers the checkpoint watermark")
    let _ :: _ := required
      | throw (IO.userError "no WAL segment covers the commit marker")
    let some plan := walRecoveryReadPlan through required
      | throw selectedSpanError
    let sealed ← readSizedWalSeals dir readSize readSealedPrefix plan.sealed
    let kept ← readKeeperPrefix (dir.file (.walSegment plan.keeper.first)) plan.keeper.bytes
    unless kept.bytes.size = plan.keeper.bytes ∧ plan.keeper.bytes ≤ kept.fileSize do
      throw (IO.userError "invalid WAL keeper prefix or physical size")
    return (⟨sealed ++ [(plan.keeper.first, kept.bytes)], newer⟩, kept.fileSize)

/-- The seal loop stops after the reached extent observation. It neither
reads this malformed payload nor reaches any later seal. -/
theorem readSizedWalSeals_rejectsExtent {state : Type} (dir : DiskDirectory)
    (readSize : FilePath → EStateM IO.Error state Nat)
    (readPrefix : FilePath → Nat → EStateM IO.Error state ByteArray)
    (earlier later : List WalReadExtent) (extent : WalReadExtent)
    {initial reached observed : state} {previous : List (Nat × ByteArray)} {actual : Nat}
    (prior : readSizedWalSeals dir readSize readPrefix earlier initial = .ok previous reached)
    (sized : readSize (dir.file (.walSegment extent.first)) reached = .ok actual observed)
    (wrong : ¬ (actual = extent.bytes ∧ extent.bytes < USize.size)) :
    readSizedWalSeals dir readSize readPrefix (earlier ++ extent :: later) initial =
      .error (IO.userError "invalid selected WAL segment spans") observed := by
  have reject := readExactRecoveryFileWith_rejectsSize (dir.file (.walSegment extent.first)) extent.bytes
    selectedSpanError readSize readPrefix sized wrong
  change readSizedWalSeals dir readSize readPrefix (earlier ++ extent :: later) initial =
    .error selectedSpanError observed
  unfold readSizedWalSeals at prior ⊢
  simp [List.mapM_append, List.mapM_cons, Bind.bind, EStateM.bind, prior, readSizedSeal, reject]

/-- Once the canonical extent plan is reached, a seal error is returned
with that exact file state, before any keeper callback. -/
theorem readSelectedWithSizedSeals_sealedFailure {state : Type} (dir : DiskDirectory) (watermark : Nat) (length : UInt64)
    (list : FilePath → EStateM IO.Error state (Array IO.FS.DirEntry))
    (lstat : FilePath → EStateM IO.Error state (Except IO.Error IO.FS.Metadata))
    (readSize : FilePath → EStateM IO.Error state Nat)
    (readSealedPrefix : FilePath → Nat → EStateM IO.Error state ByteArray)
    (readKeeperPrefix : FilePath → Nat → EStateM IO.Error state KeeperPrefix)
    (checked : length.toNat % frameSize = 0 ∧ watermark ≤ length.toNat / frameSize)
    {initial listedState selectedState final : state}
    {entries : Array IO.FS.DirEntry} (listed : list dir.path initial = .ok entries listedState)
    {offsets rest newer : List Nat} {first : Nat}
    (scanned : scanWalSegmentOffsets (probeWalSegmentWith dir lstat) (entries.toList.map (·.fileName)) listedState =
      .ok offsets selectedState)
    (addresses : selectWalSegmentReadsThrough offsets watermark (length.toNat / frameSize) =
      some (first :: rest, newer))
    {plan : WalRecoveryReadPlan}
    (planned : walRecoveryReadPlan (length.toNat / frameSize) (first :: rest) = some plan)
    {cause : IO.Error}
    (failed : readSizedWalSeals dir readSize readSealedPrefix plan.sealed selectedState = .error cause final) :
    readSelectedWithSizedSeals dir watermark length list lstat readSize readSealedPrefix readKeeperPrefix initial =
      .error cause final := by
  simp [readSelectedWithSizedSeals, withAbsoluteWalCutoff_estate, checked, listed, scanned, addresses, planned, failed,
    Bind.bind, EStateM.bind]

private theorem payloadCount (dir : DiskDirectory) (readBin : FilePath → Except IO.Error ByteArray)
    {offsets : List Nat} {files : List ByteArray}
    (read : readWalSegmentPayloadsWith dir readBin offsets = .ok files) : files.length = offsets.length := by
  unfold readWalSegmentPayloadsWith at read
  induction offsets generalizing files with
  | nil => cases read; rfl
  | cons first rest ih =>
    simp only [List.mapM_cons, Bind.bind, Except.bind] at read
    cases payload : readBin (dir.file (.walSegment first)) with
    | error cause => simp [payload] at read
    | ok bytes =>
      cases remaining : rest.mapM (fun offset => readBin (dir.file (.walSegment offset))) with
      | error cause => simp [payload, remaining] at read
      | ok later =>
        simp [payload, remaining, Pure.pure, Except.pure] at read
        simpa [← read] using ih remaining

private theorem readSizedWalSeals_reported (dir : DiskDirectory) (readSize : FilePath → Except IO.Error Nat)
    (readPrefix : FilePath → Nat → Except IO.Error ByteArray) (files : List (Nat × ByteArray))
    (reported : ∀ file ∈ files,
      file.2.size < USize.size ∧ readSize (dir.file (.walSegment file.1)) = .ok file.2.size ∧
      readPrefix (dir.file (.walSegment file.1)) file.2.size = .ok file.2) :
    readSizedWalSeals dir readSize readPrefix (files.map (fun file => ⟨file.1, file.2.size⟩)) = .ok files := by
  induction files with
  | nil => rfl
  | cons file rest ih =>
    obtain ⟨fits, size, payload⟩ := reported file (by simp)
    have remaining := ih (fun file found => reported file (List.mem_cons_of_mem _ found))
    simp [readSizedWalSeals] at remaining
    simp [readSizedWalSeals, List.mapM_cons, readSizedSeal, readExactRecoveryFileWith, fits, size, payload,
      remaining, Bind.bind, Except.bind, Pure.pure, Except.pure]

/-- On validated old input, exact size and bounded payload observations at
each selected seal produce exactly the old preparation input. The health
premises concern just the selected seals, including their USize fit. -/
theorem readSelectedWithSizedSeals_compatible (dir : DiskDirectory) (watermark : Nat) (length : UInt64)
    (list : FilePath → Except IO.Error (Array IO.FS.DirEntry))
    (lstat : FilePath → Except IO.Error (Except IO.Error IO.FS.Metadata))
    (readBin : FilePath → Except IO.Error ByteArray) (readSize : FilePath → Except IO.Error Nat)
    (readSealedPrefix : FilePath → Nat → Except IO.Error ByteArray)
    (readKeeperPrefix : FilePath → Nat → Except IO.Error KeeperPrefix)
    (checked : length.toNat % frameSize = 0 ∧ watermark ≤ length.toNat / frameSize)
    {entries : Array IO.FS.DirEntry} (listed : list dir.path = .ok entries)
    {offsets sealed newer : List Nat} {keeper : Nat}
    (scanned : scanWalSegmentOffsets (probeWalSegmentWith dir lstat) (entries.toList.map (·.fileName)) = .ok offsets)
    (addresses : selectWalSegmentReadsThrough offsets watermark (length.toNat / frameSize) =
      some (sealed ++ [keeper], newer))
    {files : List ByteArray} (payloads : readWalSegmentPayloadsWith dir readBin sealed = .ok files)
    {kept : KeeperPrefix}
    (read : readKeeperPrefix (dir.file (.walSegment keeper)) ((length.toNat / frameSize - keeper) * frameSize) = .ok kept)
    (keeperSize : kept.bytes.size = (length.toNat / frameSize - keeper) * frameSize)
    (covers : (length.toNat / frameSize - keeper) * frameSize ≤ kept.fileSize)
    (spans : checkSelectedWalSegmentSpans (length.toNat / frameSize) (sealed.zip files ++ [(keeper, kept.bytes)]) = true)
    (sizedSeals : ∀ file ∈ sealed.zip files,
      file.2.size < USize.size ∧ readSize (dir.file (.walSegment file.1)) = .ok file.2.size ∧
      readSealedPrefix (dir.file (.walSegment file.1)) file.2.size = .ok file.2) :
    readSelectedWithSizedSeals dir watermark length list lstat readSize readSealedPrefix readKeeperPrefix =
      readSelectedWithPrefix dir watermark length list lstat readBin readKeeperPrefix := by
  obtain ⟨endAt, tail, last, planned, _⟩ := walRecoveryReadPlan_ofCheckedSpans spans
  simp only [List.getLast?_append, List.getLast?_singleton, Option.some_or, Option.some.injEq, Prod.mk.injEq]
    at last
  rcases last with ⟨rfl, rfl⟩
  have starts : (sealed.zip files).map Prod.fst = sealed :=
    List.map_fst_zip (Nat.le_of_eq (payloadCount dir readBin payloads).symm)
  have orderedPlan : walRecoveryReadPlan (length.toNat / frameSize) (sealed ++ [keeper]) =
      some ⟨(sealed.zip files).map (fun file => ⟨file.1, file.2.size⟩),
        ⟨keeper, (length.toNat / frameSize - keeper) * frameSize⟩⟩ := by
    simpa only [List.dropLast_append_cons, List.dropLast_singleton, List.append_nil, List.map_append,
      List.map_singleton, Prod.fst, starts] using planned
  have sealedRead := readSizedWalSeals_reported dir readSize readSealedPrefix (sealed.zip files) sizedSeals
  rw [readSelectedWithPrefix_reported dir watermark length list lstat readBin readKeeperPrefix
    checked listed scanned addresses payloads read keeperSize covers]
  simp [readSelectedWithSizedSeals, withAbsoluteWalCutoff, checked, listed, scanned, addresses, orderedPlan,
    sealedRead, read, keeperSize, covers, Bind.bind, Except.bind, Pure.pure, Except.pure]
  cases sealed <;> rfl

end Alvoki.Storage.WalSegmentRepair
