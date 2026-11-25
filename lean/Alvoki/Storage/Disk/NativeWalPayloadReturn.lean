import Alvoki.Storage.Disk.NativeCheckpointReadReturn
import Alvoki.Storage.Disk.WalSegmentCachedExtentOpen

namespace Alvoki.Storage.WalSegmentRepair

open System
open WAL (frameSize)

variable {heap : Type}

/-- This is the ordered result of the selected payload reader. Each accepted
seal supplies the next reached heap. The last file uses the keeper prefix
request and its own cached physical extent. -/
inductive CachedWalPayloadReturn {heap : Type} (directory : DiskDirectory) (through : Nat)
    (readSeal : FilePath → Nat → EStateM IO.Error heap ByteArray)
    (readKeeper : FilePath → Nat → Nat → EStateM IO.Error heap ByteArray) :
    List (Nat × IO.FS.Metadata) → heap → EStateM.Result IO.Error heap (List (Nat × ByteArray) × Nat) → Prop where
  | noKeeper (entry : heap) :
      CachedWalPayloadReturn directory through readSeal readKeeper [] entry
        (.error (IO.userError "no WAL segment covers the commit marker") entry)
  | keeperError {first : Nat} {metadata : IO.FS.Metadata} {entry reached : heap} {cause : IO.Error}
      (failed : readKeeper (directory.file (.walSegment first)) ((through - first) * frameSize)
        metadata.byteSize.toNat entry = .error cause reached) :
      CachedWalPayloadReturn directory through readSeal readKeeper [(first, metadata)] entry (.error cause reached)
  | invalidKeeper {first : Nat} {metadata : IO.FS.Metadata} {entry reached : heap} {bytes : ByteArray}
      (read : readKeeper (directory.file (.walSegment first)) ((through - first) * frameSize)
        metadata.byteSize.toNat entry = .ok bytes reached)
      (wrong : ¬ (bytes.size = (through - first) * frameSize ∧ (through - first) * frameSize ≤ metadata.byteSize.toNat)) :
      CachedWalPayloadReturn directory through readSeal readKeeper [(first, metadata)] entry
        (.error (IO.userError "invalid WAL keeper prefix or physical size") reached)
  | kept {first : Nat} {metadata : IO.FS.Metadata} {entry reached : heap} {bytes : ByteArray}
      (read : readKeeper (directory.file (.walSegment first)) ((through - first) * frameSize)
        metadata.byteSize.toNat entry = .ok bytes reached)
      (checked : bytes.size = (through - first) * frameSize ∧ (through - first) * frameSize ≤ metadata.byteSize.toNat) :
      CachedWalPayloadReturn directory through readSeal readKeeper [(first, metadata)] entry
        (.ok ([(first, bytes)], metadata.byteSize.toNat) reached)
  | invalidOrder {first next : Nat} {metadata nextMetadata : IO.FS.Metadata} {rest : List (Nat × IO.FS.Metadata)}
      {entry : heap} (wrong : ¬ first < next) :
      CachedWalPayloadReturn directory through readSeal readKeeper ((first, metadata) :: (next, nextMetadata) :: rest)
        entry (.error selectedWalSpanError entry)
  | sealError {first next : Nat} {metadata nextMetadata : IO.FS.Metadata} {rest : List (Nat × IO.FS.Metadata)}
      {entry reached : heap} {cause : IO.Error} (forward : first < next)
      (failed : ExactRecoveryFileReturn (directory.file (.walSegment first)) ((next - first) * frameSize)
        selectedWalSpanError (fun _ => pure metadata.byteSize.toNat) readSeal entry (.error cause reached)) :
      CachedWalPayloadReturn directory through readSeal readKeeper ((first, metadata) :: (next, nextMetadata) :: rest)
        entry (.error cause reached)
  | sealedThenError {first next : Nat} {metadata nextMetadata : IO.FS.Metadata} {rest : List (Nat × IO.FS.Metadata)}
      {entry afterSeal reached : heap} {bytes : ByteArray} {cause : IO.Error} (forward : first < next)
      (read : ExactRecoveryFileReturn (directory.file (.walSegment first)) ((next - first) * frameSize)
        selectedWalSpanError (fun _ => pure metadata.byteSize.toNat) readSeal entry (.ok bytes afterSeal))
      (remaining : CachedWalPayloadReturn directory through readSeal readKeeper
        ((next, nextMetadata) :: rest) afterSeal (.error cause reached)) :
      CachedWalPayloadReturn directory through readSeal readKeeper ((first, metadata) :: (next, nextMetadata) :: rest)
        entry (.error cause reached)
  | sealed {first next : Nat} {metadata nextMetadata : IO.FS.Metadata} {rest : List (Nat × IO.FS.Metadata)}
      {entry afterSeal reached : heap} {bytes : ByteArray} {files : List (Nat × ByteArray)} {size : Nat}
      (forward : first < next)
      (read : ExactRecoveryFileReturn (directory.file (.walSegment first)) ((next - first) * frameSize)
        selectedWalSpanError (fun _ => pure metadata.byteSize.toNat) readSeal entry (.ok bytes afterSeal))
      (remaining : CachedWalPayloadReturn directory through readSeal readKeeper
        ((next, nextMetadata) :: rest) afterSeal (.ok (files, size) reached)) :
      CachedWalPayloadReturn directory through readSeal readKeeper ((first, metadata) :: (next, nextMetadata) :: rest)
        entry (.ok ((first, bytes) :: files, size) reached)

/-- Classify the actual selected payload read using only the fixed seal
and keeper callbacks. The witnessed accepted prefix stops at the first
failed check or callback, or yields the exact ordered bytes and extent. -/
theorem CachedWalPayloadReturn.classifies (directory : DiskDirectory) (through : Nat)
    (readSeal : FilePath → Nat → EStateM IO.Error heap ByteArray)
    (readKeeper : FilePath → Nat → Nat → EStateM IO.Error heap ByteArray)
    (required : List (Nat × IO.FS.Metadata)) (entry : heap) :
    CachedWalPayloadReturn directory through readSeal readKeeper required entry
      (readCachedWalPayloads directory through readSeal readKeeper required entry) := by
  induction required generalizing entry with
  | nil => exact .noKeeper entry
  | cons head tail ih =>
    obtain ⟨first, metadata⟩ := head
    cases tail with
    | nil =>
      let count := (through - first) * frameSize
      let size := metadata.byteSize.toNat
      change CachedWalPayloadReturn directory through readSeal readKeeper [(first, metadata)] entry
        (((do
          let bytes ← readKeeper (directory.file (.walSegment first)) count size
          unless bytes.size = count ∧ count ≤ size do throw (IO.userError "invalid WAL keeper prefix or physical size")
          pure ([(first, bytes)], size)) : EStateM IO.Error heap (List (Nat × ByteArray) × Nat)) entry)
      simp only [Bind.bind, EStateM.bind]
      cases read : readKeeper (directory.file (.walSegment first)) count size entry with
      | error cause reached => exact .keeperError read
      | ok bytes reached =>
        by_cases checked : bytes.size = count ∧ count ≤ size
        · simpa only [ite_eq_left checked, Pure.pure, EStateM.pure] using
            (CachedWalPayloadReturn.kept (through := through) (readSeal := readSeal) read checked)
        · simpa [checked, Bind.bind, EStateM.bind, throw, throwThe, MonadExceptOf.throw, EStateM.throw] using
            (CachedWalPayloadReturn.invalidKeeper (through := through) (readSeal := readSeal) read checked)
    | cons next rest =>
      obtain ⟨next, nextMetadata⟩ := next
      rw [readCachedWalPayloads_cons_cons]
      by_cases forward : first < next
      · simp only [ite_eq_left forward, Bind.bind, EStateM.bind, Pure.pure]
        have observed := ExactRecoveryFileReturn.classifies (directory.file (.walSegment first))
          ((next - first) * frameSize) selectedWalSpanError (fun _ => pure metadata.byteSize.toNat) readSeal entry
        cases read : readExactRecoveryFileWith (directory.file (.walSegment first)) ((next - first) * frameSize)
            selectedWalSpanError (fun _ => EStateM.pure metadata.byteSize.toNat) readSeal entry with
        | error cause reached =>
          exact .sealError forward (by simpa only [Pure.pure, read] using observed)
        | ok bytes afterSeal =>
          have acceptedSeal : ExactRecoveryFileReturn (directory.file (.walSegment first)) ((next - first) * frameSize)
              selectedWalSpanError (fun _ => pure metadata.byteSize.toNat) readSeal entry (.ok bytes afterSeal) := by
            simpa only [Pure.pure, read] using observed
          have continued := ih afterSeal
          dsimp only
          cases tailRead : readCachedWalPayloads directory through readSeal readKeeper ((next, nextMetadata) :: rest) afterSeal with
          | error cause reached =>
            exact .sealedThenError forward acceptedSeal (by simpa only [tailRead] using continued)
          | ok payload reached =>
            obtain ⟨files, size⟩ := payload
            exact .sealed forward acceptedSeal (by simpa only [tailRead] using continued)
      · simpa [forward, Bind.bind, EStateM.bind, throw, throwThe, MonadExceptOf.throw, EStateM.throw] using
          (CachedWalPayloadReturn.invalidOrder (directory := directory) (through := through) (readSeal := readSeal)
            (readKeeper := readKeeper) (metadata := metadata) (nextMetadata := nextMetadata) (rest := rest)
            (entry := entry) forward)

end Alvoki.Storage.WalSegmentRepair
