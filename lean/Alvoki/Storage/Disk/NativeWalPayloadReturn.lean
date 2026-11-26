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

/-- Recover the existing seal schedule from a successful payload return.
The keeper read starts at the last seal's reached heap. The payloads in
the result can be certified using any predicate on those exact seals. -/
theorem CachedWalPayloadReturn.successfulKeeper
    {directory : DiskDirectory} {through : Nat}
    {readSeal : FilePath → Nat → EStateM IO.Error heap ByteArray}
    {readKeeper : FilePath → Nat → Nat → EStateM IO.Error heap ByteArray}
    {required : List (Nat × IO.FS.Metadata)} {entry : heap}
    {result : EStateM.Result IO.Error heap (List (Nat × ByteArray) × Nat)}
    (observed : CachedWalPayloadReturn directory through readSeal readKeeper required entry result)
    {files : List (Nat × ByteArray)} {size : Nat} {reached : heap}
    (returned : result = .ok (files, size) reached) :
    ∃ (keeper : Nat) (metadata : IO.FS.Metadata) (issued : heap) (bytes : ByteArray)
      (earlier : List (Nat × ByteArray))
      (seals : CachedWalKeeperReached directory readSeal keeper metadata required entry issued),
      required.getLast? = some (keeper, metadata) ∧
      files = earlier ++ [(keeper, bytes)] ∧ earlier.map Prod.fst = required.dropLast.map Prod.fst ∧
      size = metadata.byteSize.toNat ∧
      readKeeper (directory.file (.walSegment keeper)) ((through - keeper) * frameSize)
        metadata.byteSize.toNat issued = .ok bytes reached ∧
      (bytes.size = (through - keeper) * frameSize ∧ (through - keeper) * frameSize ≤ metadata.byteSize.toNat) ∧
      (∀ {selected : Nat → ByteArray → Prop},
        (∀ payload ∈ earlier, selected payload.1 payload.2) → seals.HasPayloads selected) := by
  induction observed generalizing files size reached with
  | noKeeper _ | keeperError _ | invalidKeeper _ _ | invalidOrder _ | sealError _ _ | sealedThenError _ _ _ =>
    cases returned
  | @kept first metadata entry after bytes read checked =>
    obtain ⟨payload, rfl⟩ := EStateM.Result.ok.inj returned
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj payload
    exact ⟨first, metadata, entry, bytes, [], .noSeals, rfl, rfl, rfl, rfl, read, checked, fun _ => .noSeals⟩
  | @sealed first next metadata nextMetadata rest entry afterSeal after bytes tailFiles fileSize forward read tail ih =>
    obtain ⟨payload, rfl⟩ := EStateM.Result.ok.inj returned
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj payload
    obtain ⟨keeper, keeperMetadata, issued, keeperBytes, earlier, seals, last, payloads, offsets, extent, readKeeper,
      checked, certifies⟩ := ih rfl
    cases read with
    | accepted sized fits readSeal exactSize =>
      obtain ⟨span, atEntry⟩ := EStateM.Result.ok.inj sized
      subst atEntry
      let schedule := CachedWalKeeperReached.sealed forward span fits readSeal exactSize seals
      refine ⟨keeper, keeperMetadata, issued, keeperBytes, (first, bytes) :: earlier, schedule, ?_,
        congrArg (List.cons (first, bytes)) payloads, ?_, extent, readKeeper, checked, ?_⟩
      · simpa only [List.getLast?_cons_cons] using last
      · simpa only [List.dropLast_cons_cons, List.map_cons] using congrArg (List.cons first) offsets
      · intro selected exactPayloads
        exact .sealed (forward := forward) (span := span) (fits := fits) (reported := readSeal) (size := exactSize)
          (exactPayloads _ List.mem_cons_self)
          (certifies (fun payload member => exactPayloads payload (List.mem_cons_of_mem _ member)))

end Alvoki.Storage.WalSegmentRepair
