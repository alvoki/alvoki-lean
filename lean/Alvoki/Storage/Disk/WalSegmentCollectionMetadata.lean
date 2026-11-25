import Alvoki.Storage.Disk.SegmentedRetainedWriter
import Alvoki.Storage.Disk.WalSegmentUnlinkSchedule
import Alvoki.Storage.Disk.WalSegmentCollectionPlan

namespace Alvoki.Storage

open System
open WAL (frameSize)

/-- An accepted no-follow report gives a positive exact span wholly before
the keeper and covered by the strict checkpoint and marker. -/
theorem walCollectionEnd_covered {pair : DirectoryPublication.Bindings} {range : MarkedWalRange}
    (decoded : pair.walRange = some range) {first keeper last : Nat} {metadata : IO.FS.Metadata}
    (accepted : walCollectionEnd first keeper range metadata = some last) :
    metadata.type = .file ∧ metadata.numLinks = 1 ∧ last = first + metadata.byteSize.toNat / frameSize ∧
      metadata.byteSize.toNat = (last - first) * frameSize ∧
      first < last ∧ last ≤ keeper ∧ first ≠ keeper ∧ last ≤ range.watermark ∧ last ≤ range.through := by
  unfold walCollectionEnd at accepted
  dsimp only at accepted
  split at accepted
  · rename_i checked
    obtain ⟨regular, links, positive, aligned, before, covered⟩ := checked
    have kind : metadata.type = .file := by
      cases kind : metadata.type <;> first | rfl | (rw [kind] at regular; cases regular)
    cases accepted
    have exactBytes : metadata.byteSize.toNat = metadata.byteSize.toNat / frameSize * frameSize := by
      simpa only [aligned, Nat.zero_add, Nat.mul_comm] using (Nat.mod_add_div metadata.byteSize.toNat frameSize).symm
    have nonempty : first < first + metadata.byteSize.toNat / frameSize := by
      have frames : 0 < metadata.byteSize.toNat / frameSize := by
        apply Nat.pos_of_ne_zero
        intro zero
        rw [zero, Nat.zero_mul] at exactBytes
        omega
      omega
    exact ⟨kind, links, rfl, by simpa using exactBytes, nonempty, before,
      Nat.ne_of_lt (Nat.lt_of_lt_of_le nonempty before), covered,
      Nat.le_trans covered (DirectoryPublication.Bindings.walRange_accounting decoded).2.1⟩
  · contradiction

/-- Filter the sorted canonical inventory using the settled pair and the
same no-follow reports. The keeper is skipped before any size lookup. -/
def OpenPathReadReports.walCollectionOffsets (reports : OpenPathReadReports) (directory : DiskDirectory)
    (offsets : List Nat) (keeper : Nat) (pair : DirectoryPublication.Bindings) : List Nat :=
  match pair.walRange with
  | none => []
  | some range => offsets.filter fun first =>
    if first = keeper then false
    else
      match reports.lstat (directory.file (.walSegment first)) with
      | .ok metadata => (walCollectionEnd first keeper range metadata).isSome
      | .error _ => false

private theorem readWalSegmentExtent_reported (reports : OpenPathReadReports) (directory : DiskDirectory)
    (name : String) :
    (readWalSegmentExtentWith (m := Except IO.Error) directory (fun path => .ok (reports.lstat path)) name).map
      (Option.map Prod.fst) = probeListedWalSegment (reports.probeWalSegment directory) name := by
  cases parsed : parseWalSegmentName name with
  | none => simp [readWalSegmentExtentWith, probeListedWalSegment, parsed, Pure.pure, Except.pure, Except.map]
  | some first =>
    simp only [readWalSegmentExtentWith, probeListedWalSegment, parsed, Bind.bind, Except.bind,
      OpenPathReadReports.probeWalSegment]
    cases reported : reports.lstat (directory.file (.walSegment first)) with
    | ok metadata =>
      by_cases regular : metadata.type == .file <;> simp [classifyWalSegmentLookup, regular] <;> rfl
    | error cause =>
      cases cause <;> try rfl
      rename_i file osCode details
      by_cases missing : osCode == 2 <;> simp [classifyWalSegmentLookup, missing] <;> rfl

private theorem filterMapM_mapReport {α β γ ε : Type} (values : List α)
    (f : α → Except ε (Option β)) (g : β → γ) :
    values.filterMapM (fun value => (f value).map (Option.map g)) =
      (values.filterMapM f).map (List.map g) := by
  induction values with
  | nil => rfl
  | cons value rest ih =>
    simp only [List.filterMapM_cons, Bind.bind, Except.bind]
    cases first : f value with
    | error => rfl
    | ok option =>
      cases option with
      | none => exact ih
      | some found =>
        change ((rest.filterMapM (fun value => (f value).map (Option.map g))).bind _) = _
        rw [ih]
        cases rest.filterMapM f <;> rfl

/-- The cached scan projects to the original numerically ordered inventory. -/
theorem OpenPathReadReports.walSegmentExtents_offsets (reports : OpenPathReadReports) (directory : DiskDirectory)
    (names : List String) :
    (readWalSegmentExtentsWith (m := Except IO.Error) directory (fun path => .ok (reports.lstat path)) names).map (List.map Prod.fst) =
      reports.walSegmentOffsets directory names := by
  let probe := readWalSegmentExtentWith (m := Except IO.Error) directory (fun path => .ok (reports.lstat path))
  have collected := filterMapM_mapReport names probe Prod.fst
  simp only [probe, readWalSegmentExtent_reported] at collected
  unfold readWalSegmentExtentsWith OpenPathReadReports.walSegmentOffsets scanWalSegmentOffsets
  rw [collected]
  cases inventory : names.filterMapM probe with
  | error => rfl
  | ok extents =>
    change _ = Except.ok ((extents.map Prod.fst).mergeSort)
    exact congrArg Except.ok (List.map_mergeSort (fun _ _ _ _ => rfl))

private theorem readWalSegmentExtent_metadata {directory : DiskDirectory}
    {probe : FilePath → Except IO.Error (Except IO.Error IO.FS.Metadata)}
    {name : String} {entry : Nat × IO.FS.Metadata}
    (seen : readWalSegmentExtentWith directory probe name = .ok (some entry)) :
    probe (directory.file (.walSegment entry.1)) = .ok (.ok entry.2) := by
  cases parsed : parseWalSegmentName name with
  | none => simp [readWalSegmentExtentWith, parsed, Pure.pure, Except.pure] at seen
  | some first =>
    simp only [readWalSegmentExtentWith, parsed, Bind.bind, Except.bind] at seen
    cases probed : probe (directory.file (.walSegment first)) with
    | error cause => rw [probed] at seen; contradiction
    | ok report =>
      rw [probed] at seen
      cases report with
      | ok metadata =>
        by_cases regular : metadata.type == .file
        · simp [classifyWalSegmentLookup, regular, Pure.pure, Except.pure, Except.toOption] at seen
          subst entry
          exact probed
        · simp [classifyWalSegmentLookup, regular, throw] at seen
      | error cause =>
        cases cause <;> try contradiction
        rename_i file osCode details
        by_cases missing : osCode = 2 <;> simp [classifyWalSegmentLookup, missing, Pure.pure, Except.pure, throw] at seen

private theorem filterMapM_member {α β ε : Type} {f : α → Except ε (Option β)} {l : List α} {out : List β}
    (ran : l.filterMapM f = .ok out) {entry : β} (member : entry ∈ out) :
    ∃ name ∈ l, f name = .ok (some entry) := by
  induction l generalizing out with
  | nil => cases ran; contradiction
  | cons name rest ih =>
    simp only [List.filterMapM_cons, Bind.bind, Except.bind] at ran
    cases seen : f name with
    | error => rw [seen] at ran; contradiction
    | ok result =>
      rw [seen] at ran
      cases result with
      | none =>
        obtain ⟨source, listed, reported⟩ := ih ran member
        exact ⟨source, List.mem_cons_of_mem _ listed, reported⟩
      | some head =>
        cases tail : rest.filterMapM f with
        | error => rw [tail] at ran; contradiction
        | ok suffix =>
          simp only [tail, Pure.pure, Except.pure, Except.ok.injEq] at ran
          subst out
          rcases List.mem_cons.mp member with rfl | later
          · exact ⟨name, List.mem_cons_self, seen⟩
          · obtain ⟨source, listed, reported⟩ := ih tail later
            exact ⟨source, List.mem_cons_of_mem _ listed, reported⟩

/-- Each selected extent comes from its own successful canonical probe. -/
theorem readWalSegmentExtentsWith_metadata {directory : DiskDirectory}
    {probe : FilePath → Except IO.Error (Except IO.Error IO.FS.Metadata)}
    {names : List String} {extents : List (Nat × IO.FS.Metadata)}
    (read : readWalSegmentExtentsWith directory probe names = .ok extents)
    {entry : Nat × IO.FS.Metadata} (member : entry ∈ extents) :
    probe (directory.file (.walSegment entry.1)) = .ok (.ok entry.2) := by
  unfold readWalSegmentExtentsWith at read
  simp only [Bind.bind, Except.bind] at read
  cases scans : names.filterMapM (readWalSegmentExtentWith directory probe) with
  | error => rw [scans] at read; contradiction
  | ok entries =>
    simp only [scans, Pure.pure, Except.pure, Except.ok.injEq] at read
    subst extents
    obtain ⟨_, _, reported⟩ := filterMapM_member scans (List.mem_mergeSort.mp member)
    exact readWalSegmentExtent_metadata reported

theorem OpenPathReadReports.walSegmentExtents_metadata {reports : OpenPathReadReports} {directory : DiskDirectory}
    {names : List String} {extents : List (Nat × IO.FS.Metadata)}
    (read : readWalSegmentExtentsWith (m := Except IO.Error) directory (fun path => .ok (reports.lstat path)) names = .ok extents)
    {entry : Nat × IO.FS.Metadata} (member : entry ∈ extents) :
    reports.lstat (directory.file (.walSegment entry.1)) = .ok entry.2 :=
  Except.ok.inj (readWalSegmentExtentsWith_metadata read member)

theorem OpenPathReadReports.walCollectionOffsets_eq_extents (reports : OpenPathReadReports) (directory : DiskDirectory)
    (keeper : Nat) {pair : DirectoryPublication.Bindings} {range : MarkedWalRange}
    (decoded : pair.walRange = some range) (extents : List (Nat × IO.FS.Metadata))
    (observed : ∀ entry ∈ extents, reports.lstat (directory.file (.walSegment entry.1)) = .ok entry.2) :
    reports.walCollectionOffsets directory (extents.map Prod.fst) keeper pair =
      walCollectionOffsetsFromExtents extents keeper range := by
  unfold OpenPathReadReports.walCollectionOffsets walCollectionOffsetsFromExtents
  rw [decoded]
  induction extents with
  | nil => rfl
  | cons entry rest ih =>
    obtain ⟨first, metadata⟩ := entry
    have report := observed (first, metadata) List.mem_cons_self
    have tail := ih (fun entry member => observed entry (List.mem_cons_of_mem _ member))
    simp only [List.map_cons, List.filter_cons, List.filterMap_cons, report, tail]
    by_cases active : first = keeper
    · simp [active]
    · cases captured : walCollectionEnd first keeper range metadata <;> simp [active]

/-- Under the reported read-only callbacks, successful checked preflight
feeds the original model selector from the same ordered observations. -/
theorem planWalCollectionWith_reported (reports : OpenPathReadReports) (directory : DiskDirectory)
    (generation : UInt64) (walBytes keeper : Nat)
    (list : FilePath → Except IO.Error (Array IO.FS.DirEntry))
    {pair : DirectoryPublication.Bindings} {range : MarkedWalRange} {current : Option UInt64}
    (manifest : reports.readOptional (directory.file .manifest) = .ok pair.manifest)
    (marker : reports.readOptional (directory.file .walBoundary) = .ok pair.walBoundary)
    (installed : validateIntegrityRunCollectionGeneration generation pair.manifest = .ok current)
    (decoded : pair.walRange = some range) (count : walBytes = range.through * frameSize)
    {entries : Array IO.FS.DirEntry} (listed : list directory.path = .ok entries)
    {extents : List (Nat × IO.FS.Metadata)}
    (scan : readWalSegmentExtentsWith (m := Except IO.Error) directory (fun path => .ok (reports.lstat path))
      (entries.toList.map (·.fileName)) = .ok extents)
    (healthy : checkWalCollectionInventory extents keeper range = true) :
    planWalCollectionWith directory generation walBytes keeper reports.readOptional list
        (fun path => .ok (reports.lstat path)) =
      (reports.walSegmentOffsets directory (entries.toList.map (·.fileName))).map
        (fun offsets => reports.walCollectionOffsets directory offsets keeper pair) := by
  have offsets := reports.walSegmentExtents_offsets directory (entries.toList.map (·.fileName))
  rw [scan] at offsets
  rw [← offsets]
  have samePair : DirectoryPublication.Bindings.mk pair.manifest pair.walBoundary = pair := by cases pair; rfl
  unfold planWalCollectionWith
  simp only [Bind.bind, Except.bind, manifest, marker, installed, Except.mapError, liftExcept, Pure.pure, Except.pure]
  rw [samePair, decoded]
  simp only [count, ↓reduceIte, listed, scan, healthy, Except.map]
  exact congrArg Except.ok (reports.walCollectionOffsets_eq_extents directory keeper decoded extents
    (fun _ member => OpenPathReadReports.walSegmentExtents_metadata scan member)).symm

/-- Every selected offset came from a nonkeeper extent and its checked end. -/
theorem walCollectionOffsetsFromExtents_observed {extents : List (Nat × IO.FS.Metadata)}
    {keeper first : Nat} {range : MarkedWalRange}
    (planned : first ∈ walCollectionOffsetsFromExtents extents keeper range) :
    first ≠ keeper ∧ ∃ metadata last, (first, metadata) ∈ extents ∧
      walCollectionEnd first keeper range metadata = some last := by
  unfold walCollectionOffsetsFromExtents at planned
  obtain ⟨⟨offset, metadata⟩, member, found⟩ := List.mem_filterMap.mp planned
  by_cases active : offset = keeper
  · simp [active] at found
  · cases checked : walCollectionEnd offset keeper range metadata with
    | none => simp [active, checked] at found
    | some last =>
      simp [active, checked] at found
      subst first
      exact ⟨active, metadata, last, member, checked⟩

/-- The exact stored payload of a chain member has the length given by its
absolute endpoints. This fact survives unlinking other members. -/
theorem WalSegment.Chain.member_byteSize {history : List WAL.Write} {first : Nat} {segments : List WalSegment}
    (chain : Chain history first segments) {segment : WalSegment} (member : segment ∈ segments) :
    segment.bytes.size = (segment.last - segment.first) * frameSize := by
  have startsWithin {start : Nat} {rest : List WalSegment} (tail : Chain history start rest) :
      start ≤ history.length := by
    induction tail with
    | endOfHistory => exact Nat.le_refl _
    | cons ordered _ _ _ ih => exact Nat.le_trans ordered ih
  induction chain with
  | endOfHistory => simp at member
  | @cons head rest _ _ payload tail ih =>
    rcases List.mem_cons.mp member with same | later
    · subst segment
      have count : head.last - head.first ≤ (history.drop head.first).length := by
        rw [List.length_drop]
        exact Nat.sub_le_sub_right (startsWithin tail) head.first
      rw [payload, WAL.encode_size, List.length_take, Nat.min_eq_left count, Nat.mul_comm]
    · exact ih later

private theorem walCollectionEnd_isSome {segment : WalSegment} {keeper : Nat} {range : MarkedWalRange}
    {metadata : IO.FS.Metadata} (ordered : segment.first ≤ segment.last)
    (kind : metadata.type = .file) (links : metadata.numLinks = 1)
    (extent : metadata.byteSize.toNat = (segment.last - segment.first) * frameSize) :
    (walCollectionEnd segment.first keeper range metadata).isSome =
      decide (segment.first < segment.last ∧ segment.last ≤ keeper ∧ segment.last ≤ range.watermark) := by
  have frames := Nat.mul_div_cancel (segment.last - segment.first) (show 0 < frameSize by decide)
  have endpoint : segment.first + metadata.byteSize.toNat / frameSize = segment.last := by
    rw [extent, frames, Nat.add_sub_of_le ordered]
  have positive : 0 < metadata.byteSize.toNat ↔ segment.first < segment.last := by
    rw [extent, Nat.mul_pos_iff_of_pos_right (show 0 < frameSize by decide), Nat.sub_pos_iff_lt]
  have regular : (metadata.type == .file) = true := by rw [kind]; rfl
  have aligned : metadata.byteSize.toNat % frameSize = 0 := by rw [extent, Nat.mul_mod_left]
  simp only [walCollectionEnd, regular, true_and, links, aligned, endpoint, positive]
  split <;> simp_all

/-- A partial inventory suffices to approve every returned path. Completeness
is required for equality with the full plan. Here the observed nonkeeper
paths must denote sealed files and report their physical extent. -/
theorem walCollectionOffsetsFromExtents_approved {wal : WalSegmentImage} {history : List WAL.Write}
    (layout : wal.ReadLayout history) (settled : wal.directory.crashImages = [wal.directory.active])
    {range : MarkedWalRange} (decoded : wal.directory.active.walRange = some range)
    {extents : List (Nat × IO.FS.Metadata)}
    (sealedAt : ∀ entry ∈ extents, entry.1 ≠ wal.active.first →
      ∃ segment ∈ wal.sealed, segment.first = entry.1)
    (physical : ∀ entry ∈ extents, ∀ segment ∈ wal.sealed, segment.first = entry.1 →
      entry.2.byteSize.toNat = segment.bytes.size)
    (spans : ∀ segment ∈ wal.sealed, segment.bytes.size = (segment.last - segment.first) * frameSize)
    {first : Nat} (planned : first ∈ walCollectionOffsetsFromExtents extents wal.active.first range) :
    (∃ segment ∈ wal.sealed, segment.first = first) ∧
      ∀ segment ∈ wal.sealed, segment.first = first → wal.Eligible segment := by
  obtain ⟨notKeeper, metadata, last, member, accepted⟩ := walCollectionOffsetsFromExtents_observed planned
  refine ⟨sealedAt (first, metadata) member notKeeper, ?_⟩
  intro segment sealed same
  have details := walCollectionEnd_covered decoded accepted
  have ordered := layout.forward segment (List.mem_append_left _ sealed)
  have extent := (physical (first, metadata) member segment sealed same).trans (spans segment sealed)
  have bounds := walCollectionEnd_isSome ordered details.1 details.2.1 extent (keeper := wal.active.first)
    (range := range)
  rw [same, accepted] at bounds
  have eligible := of_decide_eq_true bounds.symm
  refine ⟨⟨same.symm ▸ eligible.1, eligible.2.1⟩, ?_⟩
  intro pair selected
  have samePair : pair = wal.directory.active := by
    simpa [WalSegmentImage.Selects, settled] using selected
  subst pair
  exact ⟨range, decoded, eligible.2.2⟩

namespace WalSegmentRepair

/-- A complete held inventory, with true physical sizes for the exact
immutable payloads, yields the model's entire unlink plan. An earlier
collection may have removed arbitrary covered sealed names. -/
theorem HealthyBoundedWalReports.collectionOffsets_exact {directory owners descriptor wal pair watermark durable tail}
    (raw : HealthyBoundedWalReports directory owners descriptor wal pair watermark durable tail)
    {history : List WAL.Write} (layout : wal.ReadLayout history)
    (visible : wal.directory.active = pair) (settled : wal.directory.crashImages = [pair])
    {range : MarkedWalRange} (decoded : pair.walRange = some range)
    (physical : ∀ segment ∈ wal.sealed, ∀ metadata,
      raw.reports.lstat (directory.file (.walSegment segment.first)) = .ok metadata →
        metadata.byteSize.toNat = segment.bytes.size)
    (spans : ∀ segment ∈ wal.sealed, segment.bytes.size = (segment.last - segment.first) * frameSize) :
    (raw.reports.walSegmentOffsets directory (raw.entries.toList.map (·.fileName))).map
        (fun offsets => raw.reports.walCollectionOffsets directory offsets wal.active.first pair) =
      .ok wal.collectionOffsets := by
  rw [raw.scan layout]
  simp only [Except.map, Except.ok.injEq]
  have test (segment : WalSegment) (member : segment ∈ wal.sealed) :
      (if segment.first = wal.active.first then false
       else match raw.reports.lstat (directory.file (.walSegment segment.first)) with
         | .ok metadata => (walCollectionEnd segment.first wal.active.first range metadata).isSome
         | .error _ => false) = wal.canRemove segment := by
    have ordered := List.pairwise_append.mp layout.ordered
    have before := ordered.2.2 segment member _ List.mem_cons_self
    have present := List.mem_map_of_mem (f := WalSegment.first) (List.mem_append_left [wal.active] member)
    obtain ⟨metadata, observed, kind, links⟩ := raw.regular segment.first present
    have forward := layout.forward segment (List.mem_append_left _ member)
    have extent := (physical segment member metadata observed).trans (spans segment member)
    have permitted := walCollectionEnd_isSome forward kind links extent (keeper := wal.active.first) (range := range)
    simp [Nat.ne_of_lt before.1, observed, permitted, WalSegmentImage.canRemove, visible, settled, decoded,
      Bool.and_assoc]
  unfold OpenPathReadReports.walCollectionOffsets WalSegmentImage.collectionOffsets
  rw [decoded]
  simp only [WalSegmentImage.segments, List.map_append, List.map_cons, List.map_nil,
    List.filter_append, List.filter_cons, Bool.false_eq_true, ↓reduceIte, List.filter_nil,
    List.append_nil]
  rw [List.filter_map]
  congr 1
  exact List.filter_congr test

end WalSegmentRepair

namespace DiskSession

/-- A settled writer authenticates the strict pair, and its original chain
fixes the lengths of the sealed payloads that survive earlier unlinks. The
fresh held observations supply the physical size of each surviving file. -/
theorem SegmentedWriterState.Ready.collectionOffsets_exact {directory descriptor state after tail}
    (ready : SegmentedWriterState.Ready directory descriptor state)
    (retry : WalSegmentCollectionRetry state.wal after)
    (raw : WalSegmentRepair.HealthyBoundedWalReports directory state.owners descriptor after state.target.pair
      state.target.range.watermark state.published.durable tail)
    (physical : ∀ segment ∈ after.sealed, ∀ metadata,
      raw.reports.lstat (directory.file (.walSegment segment.first)) = .ok metadata →
        metadata.byteSize.toNat = segment.bytes.size) :
    (raw.reports.walSegmentOffsets directory (raw.entries.toList.map (·.fileName))).map
        (fun offsets => raw.reports.walCollectionOffsets directory offsets state.installed.activeFirst state.target.pair) =
      .ok after.collectionOffsets := by
  have visible := (ready.collectionReadPlan retry (pair := after.directory.active) (List.mem_cons_self ..)).1
  have ⟨samePair, settled⟩ := retry.keepsSettledPair ready.walDirectorySettled
  rw [← samePair, visible] at settled
  have keeper : after.active.first = state.installed.activeFirst := by
    rw [retry.keepsActive, ready.resumed.keeper, ready.active]
  rw [← keeper]
  exact raw.collectionOffsets_exact (retry.readLayout ready.layout) visible settled state.target.decoded physical
    (fun _ member => ready.chain.member_byteSize (List.mem_append_left _ (retry.sealedSublist.subset member)))

end DiskSession
end Alvoki.Storage
