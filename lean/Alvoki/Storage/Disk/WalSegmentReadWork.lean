import Alvoki.Storage.Disk.WalSegmentBoundedOpen

namespace Alvoki.Storage.WalSegmentRepair

open System
open WAL (frameSize)

/-- One request issued by WAL acquisition under the directory lock. -/
inductive WalReadCall where
  | list (path : FilePath)
  | metadata (path : FilePath)
  | sealed (path : FilePath)
  | keeper (path : FilePath) (bytes : Nat)

-- Keep callbacks in reverse order so recording a request takes one cons.
private def logged {α : Type} (calls : List WalReadCall) (report : Except IO.Error α) :
    EStateM IO.Error (List WalReadCall) α :=
  fun previous => match report with
    | .ok value => .ok value (calls.reverse ++ previous)
    | .error cause => .error cause (calls.reverse ++ previous)

private def metadataCalls (dir : DiskDirectory) (names : List String) : List WalReadCall :=
  (names.filterMap parseWalSegmentName).map (fun first => .metadata (dir.file (.walSegment first)))

private theorem probeListedWalSegment_logged (dir : DiskDirectory)
    (lstat : FilePath → Except IO.Error (Except IO.Error IO.FS.Metadata))
    (name : String) (previous : List WalReadCall) :
    probeListedWalSegment (probeWalSegmentWith dir (fun path => logged [.metadata path] (lstat path))) name previous =
      logged (metadataCalls dir [name]) (probeListedWalSegment (probeWalSegmentWith dir lstat) name) previous := by
  unfold probeListedWalSegment
  cases parsed : parseWalSegmentName name with
  | none => simp [metadataCalls, parsed, logged, Pure.pure, EStateM.pure, Except.pure]
  | some first =>
    unfold probeWalSegmentWith
    cases observed : lstat (dir.file (.walSegment first)) with
    | error cause =>
      simp [metadataCalls, parsed, logged, observed, Bind.bind, EStateM.bind, Except.bind]
    | ok value =>
      cases named : classifyWalSegmentLookup (dir.file (.walSegment first)) first value <;>
        simp [metadataCalls, parsed, logged, observed, named, Bind.bind, EStateM.bind, Except.bind,
          Pure.pure, EStateM.pure, Except.pure] <;> rfl

private theorem filterMapWalSegmentOffsets_logged (dir : DiskDirectory)
    (lstat : FilePath → Except IO.Error (Except IO.Error IO.FS.Metadata))
    (names : List String) {offsets : List Nat}
    (reported : names.filterMapM (probeListedWalSegment (probeWalSegmentWith dir lstat)) = .ok offsets)
    (previous : List WalReadCall) :
    (names.filterMapM (probeListedWalSegment
      (probeWalSegmentWith dir (fun path => logged [.metadata path] (lstat path))))) previous =
      .ok offsets ((metadataCalls dir names).reverse ++ previous) ∧ offsets.length ≤ names.length := by
  induction names generalizing previous offsets with
  | nil =>
    cases reported
    exact ⟨rfl, Nat.le_refl _⟩
  | cons name names ih =>
    simp only [List.filterMapM_cons, Bind.bind, Except.bind] at reported
    simp only [List.filterMapM_cons, Bind.bind, EStateM.bind, probeListedWalSegment_logged]
    have calls : metadataCalls dir (name :: names) = metadataCalls dir [name] ++ metadataCalls dir names := by
      simp only [show name :: names = [name] ++ names from rfl, metadataCalls,
        List.filterMap_append, List.map_append]
    cases head : probeListedWalSegment (probeWalSegmentWith dir lstat) name with
    | error cause => simp [head] at reported
    | ok found =>
      cases found with
      | none =>
        simp only [head] at reported
        refine ⟨?_, Nat.le_trans (ih reported previous).2 (Nat.le_succ _)⟩
        simp only [logged, (ih reported _).1, calls, List.reverse_append, List.append_assoc]
      | some first =>
        simp only [head] at reported
        cases tail : names.filterMapM (probeListedWalSegment (probeWalSegmentWith dir lstat)) with
        | error cause => simp [tail] at reported
        | ok rest =>
          have exactResult : first :: rest = offsets := by
            simpa [tail, Bind.bind, Except.bind, Pure.pure, Except.pure] using reported
          subst offsets
          refine ⟨?_, Nat.succ_le_succ (ih tail previous).2⟩
          simp [logged, (ih tail _).1, calls, List.reverse_append, List.append_assoc,
            EStateM.bind, Pure.pure, EStateM.pure]

private theorem scanWalSegmentOffsets_logged (dir : DiskDirectory)
    (lstat : FilePath → Except IO.Error (Except IO.Error IO.FS.Metadata))
    (names : List String) {offsets : List Nat}
    (reported : scanWalSegmentOffsets (probeWalSegmentWith dir lstat) names = .ok offsets)
    (previous : List WalReadCall) :
    scanWalSegmentOffsets (probeWalSegmentWith dir (fun path => logged [.metadata path] (lstat path))) names previous =
      .ok offsets ((metadataCalls dir names).reverse ++ previous) ∧ offsets.length ≤ names.length := by
  unfold scanWalSegmentOffsets at reported ⊢
  cases filtered : names.filterMapM (probeListedWalSegment (probeWalSegmentWith dir lstat)) with
  | error cause => simp [Functor.map, Except.map, filtered] at reported
  | ok found =>
    have sorted : found.mergeSort = offsets := by simpa [filtered, Functor.map, Except.map] using reported
    obtain ⟨reads, count⟩ := filterMapWalSegmentOffsets_logged dir lstat names filtered previous
    exact ⟨by simp [Functor.map, EStateM.map, reads, sorted], by rw [← sorted, List.length_mergeSort]; exact count⟩

private def sealedCalls (dir : DiskDirectory) (offsets : List Nat) : List WalReadCall :=
  offsets.map (fun first => .sealed (dir.file (.walSegment first)))

private theorem readWalSegmentPayloadsWith_logged (dir : DiskDirectory)
    (readBin : FilePath → Except IO.Error ByteArray)
    (offsets : List Nat) {payloads : List ByteArray}
    (reported : readWalSegmentPayloadsWith dir readBin offsets = .ok payloads)
    (previous : List WalReadCall) :
    readWalSegmentPayloadsWith dir (fun path => logged [.sealed path] (readBin path)) offsets previous =
      .ok payloads ((sealedCalls dir offsets).reverse ++ previous) := by
  unfold readWalSegmentPayloadsWith at *
  induction offsets generalizing payloads previous with
  | nil =>
    cases reported
    rfl
  | cons first rest ih =>
    simp only [List.mapM_cons, Bind.bind, Except.bind] at reported
    cases head : readBin (dir.file (.walSegment first)) with
    | error cause => simp [head] at reported
    | ok bytes =>
      simp only [head] at reported
      cases tail : rest.mapM (fun offset => readBin (dir.file (.walSegment offset))) with
      | error cause => simp [tail] at reported
      | ok more =>
        have exactResult : bytes :: more = payloads := by
          simpa [tail, Bind.bind, Except.bind, Pure.pure, Except.pure] using reported
        subst payloads
        simp [List.mapM_cons, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure, logged, head, ih tail,
          sealedCalls, List.append_assoc]

/-- Run the shared WAL acquisition schedule with each callback recorded. -/
def recordWalReadCalls (dir : DiskDirectory) (watermark : Nat) (length : UInt64)
    (list : FilePath → Except IO.Error (Array IO.FS.DirEntry))
    (lstat : FilePath → Except IO.Error (Except IO.Error IO.FS.Metadata))
    (readBin : FilePath → Except IO.Error ByteArray) (readPrefix : FilePath → Nat → Except IO.Error KeeperPrefix) :
    EStateM.Result IO.Error (List WalReadCall) (WalSegmentMarkerReads × Nat) :=
  readSelectedWithPrefix dir watermark length
    (fun path => logged [.list path] (list path))
    (fun path => logged [.metadata path] (lstat path))
    (fun path => logged [.sealed path] (readBin path))
    (fun path bytes => logged [.keeper path bytes] (readPrefix path bytes)) []

/-- For accepted acquisition reports, the actual shared worker lists the
directory once, probes just the canonical names, and reads the selected
sealed files in order. It requests exactly the marker-selected prefix at
the keeper, independently of the physical unselected tail length. -/
theorem recordWalReadCalls_exact (dir : DiskDirectory) (watermark : Nat) (length : UInt64)
    (list : FilePath → Except IO.Error (Array IO.FS.DirEntry))
    (lstat : FilePath → Except IO.Error (Except IO.Error IO.FS.Metadata))
    (readBin : FilePath → Except IO.Error ByteArray)
    (readPrefix : FilePath → Nat → Except IO.Error KeeperPrefix)
    (checked : length.toNat % frameSize = 0 ∧ watermark ≤ length.toNat / frameSize)
    {entries : Array IO.FS.DirEntry} (listed : list dir.path = .ok entries)
    {offsets sealed newer : List Nat} {keeper : Nat}
    (scanned : scanWalSegmentOffsets (probeWalSegmentWith dir lstat) (entries.toList.map (·.fileName)) = .ok offsets)
    (addresses : selectWalSegmentReadsThrough offsets watermark (length.toNat / frameSize) =
      some (sealed ++ [keeper], newer))
    {files : List ByteArray} (payloads : readWalSegmentPayloadsWith dir readBin sealed = .ok files)
    {kept : KeeperPrefix}
    (read : readPrefix (dir.file (.walSegment keeper)) ((length.toNat / frameSize - keeper) * frameSize) = .ok kept)
    (size : kept.bytes.size = (length.toNat / frameSize - keeper) * frameSize)
    (covers : (length.toNat / frameSize - keeper) * frameSize ≤ kept.fileSize) :
    let keeperSize := (length.toNat / frameSize - keeper) * frameSize
    let calls := [WalReadCall.list dir.path] ++ metadataCalls dir (entries.toList.map IO.FS.DirEntry.fileName) ++
      sealedCalls dir sealed ++ [WalReadCall.keeper (dir.file (.walSegment keeper)) keeperSize]
    recordWalReadCalls dir watermark length list lstat readBin readPrefix =
      .ok (⟨sealed.zip files ++ [(keeper, kept.bytes)], newer⟩, kept.fileSize) calls.reverse ∧
      calls.length ≤ 2 * entries.size + 1 ∧ keeperSize ≤ length.toNat := by
  intro keeperSize calls
  have scan := scanWalSegmentOffsets_logged dir lstat _ scanned [WalReadCall.list dir.path]
  refine ⟨?_, ?_, ?_⟩
  · simp [recordWalReadCalls, readSelectedWithPrefix, withAbsoluteWalCutoff_estate, checked, listed, addresses, read,
      size, covers, scan.1, readWalSegmentPayloadsWith_logged dir readBin _ payloads,
      logged, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure, List.reverse_append, List.append_assoc, calls, keeperSize]
  · have stats : (metadataCalls dir (entries.toList.map IO.FS.DirEntry.fileName)).length ≤ entries.size := by
      simpa [metadataCalls] using List.length_filterMap_le (f := parseWalSegmentName)
        (l := entries.toList.map IO.FS.DirEntry.fileName)
    have selected : sealed.length + 1 ≤ offsets.length := by
      unfold selectWalSegmentReadsThrough selectWalSegmentReads at addresses
      cases first : (offsets.filter (fun offset => decide (offset ≤ watermark))).max? with
      | none => simp [first, Option.bind, Bind.bind] at addresses
      | some start =>
        simp only [first, Bind.bind, Option.bind, Pure.pure, Option.some.injEq,
          Prod.mk.injEq] at addresses
        have bound :=
          (List.takeWhile_sublist (l := offsets.filter (fun offset => decide (start ≤ offset)))
            (p := fun offset => decide (offset ≤ length.toNat / frameSize))).length_le
        rw [addresses.1, List.length_append, List.length_singleton] at bound
        exact Nat.le_trans bound (List.filter_sublist.length_le)
    have offsetsFit : offsets.length ≤ entries.size := by simpa using scan.2
    simp only [calls, List.length_append, List.length_singleton, sealedCalls, List.length_map]
    omega
  · exact Nat.le_trans (Nat.mul_le_mul_right _ (Nat.sub_le _ _)) (Nat.div_mul_le_self _ _)

end Alvoki.Storage.WalSegmentRepair
