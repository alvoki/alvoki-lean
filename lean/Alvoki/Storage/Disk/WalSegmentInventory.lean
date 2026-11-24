import Alvoki.Storage.Disk.LockedOpenFileReads
import Alvoki.Storage.Disk.WalSegmentRotationIO
import Alvoki.Storage.Disk.WalSegmentFileName

namespace Alvoki.Storage

open System

namespace OpenPathReadReports

/-- Probe a canonical segment's reconstructed path with no-follow metadata.
Only Linux `ENOENT` supplies absence. A nonregular file or another lookup
error stops the inventory before it can select an older active address. -/
def probeWalSegment (reports : OpenPathReadReports) (directory : DiskDirectory) (first : Nat) :
    Except IO.Error (Option Nat) :=
  let path := directory.file (.walSegment first)
  match reports.lstat path with
  | .ok metadata =>
    if metadata.type == .file then .ok (some first)
    else .error (IO.userError s!"expected a regular WAL segment: '{path}'")
  | .error error@(.noFileOrDirectory _ osCode _) =>
    if osCode == 2 then .ok none else .error error
  | .error error => .error error

private theorem probeWalSegment_present {reports : OpenPathReadReports} {directory : DiskDirectory}
    {first found : Nat} : reports.probeWalSegment directory first = .ok (some found) ↔
      first = found ∧ ∃ metadata, reports.lstat (directory.file (.walSegment first)) = .ok metadata ∧
        metadata.type = .file := by
  constructor
  · intro observed
    unfold probeWalSegment at observed
    dsimp only at observed
    cases lookup : reports.lstat (directory.file (.walSegment first)) with
    | error cause =>
      cases cause <;> simp [lookup] at observed
      split at observed <;> simp at observed
    | ok metadata =>
      rw [lookup] at observed
      by_cases regular : metadata.type == .file
      · have same : first = found := by simpa [regular] using observed
        refine ⟨same, metadata, rfl, ?_⟩
        cases kind : metadata.type <;> first | rfl | (rw [kind] at regular; cases regular)
      · simp [regular] at observed
  · rintro ⟨rfl, metadata, lookup, regular⟩
    simp [probeWalSegment, lookup, regular]
    rfl

private def listedSegment (reports : OpenPathReadReports) (directory : DiskDirectory) (name : String) :
    Except IO.Error (Option Nat) :=
  match parseWalSegmentName name with
  | none => .ok none
  | some offset => reports.probeWalSegment directory offset

private theorem listedSegment_present {reports : OpenPathReadReports} {directory : DiskDirectory}
    {name : String} {first : Nat} : listedSegment reports directory name = .ok (some first) ↔
      name = renderWalSegmentName first ∧
        ∃ metadata, reports.lstat (directory.file (.walSegment first)) = .ok metadata ∧ metadata.type = .file := by
  constructor
  · intro observed
    cases parsed : parseWalSegmentName name with
    | none => simp [listedSegment, parsed] at observed
    | some offset =>
      have chosen : reports.probeWalSegment directory offset = .ok (some first) := by
        simpa [listedSegment, parsed] using observed
      obtain ⟨rfl, regular⟩ := probeWalSegment_present.mp chosen
      exact ⟨parseWalSegmentName_eq_some_iff.mp parsed, regular⟩
  · rintro ⟨rfl, regular⟩
    simpa [listedSegment, parseWalSegmentName_render] using
      (probeWalSegment_present.mpr ⟨rfl, regular⟩)

private theorem filterMapM_ok {Error α β : Type} {f : α → Except Error (Option β)}
    {entries : List α} {results : List β} (ran : entries.filterMapM f = .ok results) :
    results = entries.filterMap (fun entry => (f entry).toOption.join) := by
  induction entries generalizing results with
  | nil => cases ran; simp
  | cons entry rest ih =>
    simp only [List.filterMapM_cons, Bind.bind, Except.bind] at ran
    cases checked : f entry with
    | error cause => rw [checked] at ran; contradiction
    | ok result =>
      rw [checked] at ran
      cases result with
      | none => simpa [checked, Except.toOption, Option.join] using ih ran
      | some value =>
        cases scanned : rest.filterMapM f with
        | error cause => simp [scanned] at ran
        | ok tail =>
          have exactResults : results = value :: tail := by
            simpa [scanned, Bind.bind, Except.bind, Pure.pure, Except.pure] using ran.symm
          subst results
          simp [checked, Except.toOption, Option.join, ih scanned]

private theorem report_isPresent {Error α : Type} {report : Except Error (Option α)} {value : α} :
    report.toOption.join = some value ↔ report = .ok (some value) := by
  cases report <;> simp [Except.toOption, Option.join]

/-- The locked listing can include obsolete missing entries and unrelated
names. Successful lookups sort the actual regular canonical addresses by
their absolute frame starts, without reading any segment payload. -/
def walSegmentOffsets (reports : OpenPathReadReports) (directory : DiskDirectory) (names : List String) :
    Except IO.Error (List Nat) :=
  (names.filterMapM (listedSegment reports directory)).map (·.mergeSort)

private theorem offsets_scan {reports : OpenPathReadReports} {directory : DiskDirectory} {names : List String}
    {offsets : List Nat} (scanned : reports.walSegmentOffsets directory names = .ok offsets) :
    ∃ found, names.filterMapM (listedSegment reports directory) = .ok found ∧ offsets = found.mergeSort := by
  unfold walSegmentOffsets at scanned
  cases collected : names.filterMapM (listedSegment reports directory) with
  | error cause => rw [collected] at scanned; contradiction
  | ok found => exact ⟨found, rfl, by simpa [collected, Except.map] using scanned.symm⟩

theorem mem_walSegmentOffsets {reports : OpenPathReadReports} {directory : DiskDirectory} {names : List String}
    {offsets : List Nat} (scanned : reports.walSegmentOffsets directory names = .ok offsets) {first : Nat} :
    first ∈ offsets ↔ renderWalSegmentName first ∈ names ∧
      ∃ metadata, reports.lstat (directory.file (.walSegment first)) = .ok metadata ∧ metadata.type = .file := by
  obtain ⟨found, collected, rfl⟩ := offsets_scan scanned
  rw [List.mem_mergeSort, filterMapM_ok collected, List.mem_filterMap]
  constructor
  · rintro ⟨name, listed, read⟩
    obtain ⟨rfl, regular⟩ := listedSegment_present.mp (report_isPresent.mp read)
    exact ⟨listed, regular⟩
  · rintro ⟨listed, regular⟩
    exact ⟨_, listed, report_isPresent.mpr (listedSegment_present.mpr ⟨rfl, regular⟩)⟩

theorem walSegmentOffsets_ordered {reports : OpenPathReadReports} {directory : DiskDirectory} {names : List String}
    {offsets : List Nat} (scanned : reports.walSegmentOffsets directory names = .ok offsets) :
    offsets.Pairwise (· ≤ ·) := by
  obtain ⟨found, _, rfl⟩ := offsets_scan scanned
  apply (List.pairwise_mergeSort (le := fun a b => decide (a ≤ b)) (fun a b c ab bc =>
    decide_eq_true (Nat.le_trans (of_decide_eq_true ab) (of_decide_eq_true bc))) (fun a b =>
    Bool.or_eq_true_iff.mpr ((Nat.le_total a b).imp decide_eq_true decide_eq_true)) found).imp
  exact of_decide_eq_true

/-- Distinct listed basenames produce strictly ordered addresses, because
the canonical spelling identifies exactly one basename for each start. -/
theorem walSegmentOffsets_strict {reports : OpenPathReadReports} {directory : DiskDirectory} {names : List String}
    {offsets : List Nat} (scanned : reports.walSegmentOffsets directory names = .ok offsets)
    (uniqueNames : names.Nodup) : offsets.Pairwise (· < ·) := by
  have ordered := walSegmentOffsets_ordered scanned
  obtain ⟨found, collected, rfl⟩ := offsets_scan scanned
  have unique : found.Nodup := by
    rw [filterMapM_ok collected]
    apply List.Pairwise.filterMap _ _ uniqueNames
    intro left right different first fromLeft next fromRight same
    subst next
    have leftName := (listedSegment_present.mp (report_isPresent.mp fromLeft)).1
    have rightName := (listedSegment_present.mp (report_isPresent.mp fromRight)).1
    exact different (leftName.trans rightName.symm)
  exact (ordered.and ((List.mergeSort_perm found _).symm.nodup unique)).imp
    (fun bounds => Nat.lt_of_le_of_ne bounds.1 bounds.2)

/-- Read only the prospective successor payload. An existing successor can
be reused once its no-follow optional read verifies an exact zero-byte file. -/
def observeWalSuccessor (reports : OpenPathReadReports) (directory : DiskDirectory) (first : Nat) :
    Except IO.Error Bool :=
  WalSegmentRotation.observeSuccessorWith (reports.readOptional (directory.file (.walSegment first)))

theorem observeWalSuccessor_probe {reports : OpenPathReadReports} {directory : DiskDirectory} {first : Nat}
    {present : Bool} (observed : reports.observeWalSuccessor directory first = .ok present) :
    reports.probeWalSegment directory first = .ok (if present then some first else none) := by
  unfold observeWalSuccessor WalSegmentRotation.observeSuccessorWith readOptional readOptionalDatabaseFile at observed
  unfold probeWalSegment
  simp only [Pure.pure, Except.pure, Bind.bind, Except.bind] at observed
  cases lookup : reports.lstat (directory.file (.walSegment first)) with
  | error cause =>
    cases cause <;> simp [lookup] at observed ⊢
    rename_i _ code _
    by_cases missing : code = 2 <;> simp_all
  | ok metadata =>
    by_cases regular : metadata.type == .file
    · cases read : reports.readBin (directory.file (.walSegment first)) with
      | error cause => simp [lookup, regular, read] at observed
      | ok bytes =>
        by_cases empty : bytes.size = 0 <;> simp_all
    · simp [lookup, regular] at observed

theorem observeWalSuccessor_eq {reports : OpenPathReadReports} {directory : DiskDirectory}
    {first : Nat} {visible : Option ByteArray} {present : Bool}
    (observes : reports.OptionalAgrees (directory.file (.walSegment first)) visible)
    (observed : reports.observeWalSuccessor directory first = .ok present) :
    visible = if present then some ByteArray.empty else none := by
  let file := directory.file (.walSegment first)
  let raw : OptionalPathRead visible := ⟨reports.lstat file, reports.readBin file, observes.missing, observes.contents⟩
  change (do
    let result ← raw.result file
    match result with
    | none => pure false
    | some bytes => if bytes.size = 0 then pure true else throw (IO.userError "WAL segment successor is not empty")) =
      .ok present at observed
  cases reported : raw.result file with
  | error cause => simp [reported, Bind.bind, Except.bind] at observed
  | ok result =>
    have exactFile := raw.resultVisible file reported
    cases result with
    | none =>
      have absent : present = false := by simpa [reported, Bind.bind, Except.bind, Pure.pure, Except.pure] using observed.symm
      simpa [absent] using exactFile
    | some bytes =>
      by_cases empty : bytes.size = 0
      · have presentNow : present = true := by
          simpa [reported, Bind.bind, Except.bind, empty, Pure.pure, Except.pure] using observed.symm
        simpa [presentNow, ByteArray.size_eq_zero_iff.mp empty] using exactFile
      · simp [reported, Bind.bind, Except.bind, empty] at observed

end OpenPathReadReports

/-- Successful listing and no-follow reports are interpreted under the
canonical database lock. The caller supplies stable namespace and directory
enumeration observations for this same lock owner. -/
structure LockedWalSegmentInventory (directory : DiskDirectory) where
  owners : DiskSession.LockOwners
  descriptor : Nat
  held : owners.Owns directory descriptor
  names : List String
  reports : OpenPathReadReports

def LockedWalSegmentInventory.offsets {directory : DiskDirectory} (inventory : LockedWalSegmentInventory directory) :
    Except IO.Error (List Nat) :=
  inventory.reports.walSegmentOffsets directory inventory.names

/-- A selected active address is the greatest present canonical regular
file in the locked inventory. Its basename reconstructs that exact path. -/
theorem LockedWalSegmentInventory.activeAddress {directory : DiskDirectory}
    (inventory : LockedWalSegmentInventory directory) {offsets : List Nat} {active : Nat}
    (scanned : inventory.offsets = .ok offsets) (greatest : offsets.max? = some active) :
    renderWalSegmentName active ∈ inventory.names ∧
      ∃ metadata, inventory.reports.lstat (directory.file (.walSegment active)) = .ok metadata ∧ metadata.type = .file ∧
        ∀ first ∈ offsets, first ≤ active := by
  obtain ⟨member, bounded⟩ := List.max?_eq_some_iff.mp greatest
  obtain ⟨listed, metadata, regular, kind⟩ := OpenPathReadReports.mem_walSegmentOffsets scanned |>.mp member
  exact ⟨listed, metadata, regular, kind, bounded⟩

/-- A greater prospective address is distinct from every current segment.
Its own exact no-follow lookup also supplies the absence required by the
exclusive create operation. -/
theorem LockedWalSegmentInventory.reserveSuccessor {directory : DiskDirectory}
    (inventory : LockedWalSegmentInventory directory) {offsets : List Nat} {active next : Nat}
    (scanned : inventory.offsets = .ok offsets) (greatest : offsets.max? = some active) (forward : active < next)
    {visible : Option ByteArray}
    (observes : inventory.reports.OptionalAgrees (directory.file (.walSegment next)) visible)
    (missing : inventory.reports.observeWalSuccessor directory next = .ok false) :
    visible = none ∧ ∀ first, renderWalSegmentName first ∈ inventory.names →
      (∃ metadata, inventory.reports.lstat (directory.file (.walSegment first)) = .ok metadata ∧
        metadata.type = .file) → directory.file (.walSegment next) ≠ directory.file (.walSegment first) := by
  have absent := OpenPathReadReports.observeWalSuccessor_eq observes missing
  refine ⟨absent, ?_⟩
  intro first listed regular alias
  have member := (OpenPathReadReports.mem_walSegmentOffsets scanned).mpr ⟨listed, regular⟩
  have before := (List.max?_eq_some_iff.mp greatest).2 first member
  exact Nat.ne_of_lt (Nat.lt_of_le_of_lt before forward) (directory.walSegment_path_injective alias).symm

/-- With the earlier active still listed, the observed presence of its
successor determines which address is greatest. Other present segments
must be covered by the same known address interval. -/
theorem greatestWalSegmentAfterRotation {offsets : List Nat} {previous next : Nat} {present : Bool}
    (old : previous ∈ offsets) (forward : previous < next)
    (bounded : ∀ first ∈ offsets, first ≤ previous ∨ first = next)
    (observed : next ∈ offsets ↔ present = true) : offsets.max? = some (if present then next else previous) := by
  cases present with
  | false =>
    refine List.max?_eq_some_iff.mpr ⟨old, ?_⟩
    intro first member
    rcases bounded first member with within | rfl
    · exact within
    · cases observed.mp member
  | true =>
    refine List.max?_eq_some_iff.mpr ⟨observed.mpr rfl, ?_⟩
    intro first member
    rcases bounded first member with within | rfl
    · exact Nat.le_trans within (Nat.le_of_lt forward)
    · exact Nat.le_refl _

/-- A verified empty successor is the greatest present address if it
survived. Otherwise the old active remains greatest. Successful listing
must include the successor's canonical basename when it is present. -/
theorem LockedWalSegmentInventory.reopenActive {directory : DiskDirectory}
    (inventory : LockedWalSegmentInventory directory) {offsets : List Nat} {previous next : Nat} {present : Bool}
    (scanned : inventory.offsets = .ok offsets) (old : previous ∈ offsets) (forward : previous < next)
    (bounded : ∀ first ∈ offsets, first ≤ previous ∨ first = next)
    (observed : inventory.reports.observeWalSuccessor directory next = .ok present)
    (listed : present = true → renderWalSegmentName next ∈ inventory.names) :
    offsets.max? = some (if present then next else previous) := by
  apply greatestWalSegmentAfterRotation old forward bounded
  have probe := OpenPathReadReports.observeWalSuccessor_probe observed
  rw [OpenPathReadReports.mem_walSegmentOffsets scanned]
  cases present with
  | false =>
    constructor
    · rintro ⟨_, regular⟩
      have present := OpenPathReadReports.probeWalSegment_present.mpr ⟨rfl, regular⟩
      rw [probe] at present
      simp at present
    · intro impossible; contradiction
  | true =>
    constructor
    · intro _; rfl
    · intro actual
      exact ⟨listed actual, (OpenPathReadReports.probeWalSegment_present.mp probe).2⟩

end Alvoki.Storage
