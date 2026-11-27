import Alvoki.Storage.Disk.Proofs.Session.CheckedDirectoryRead
import Alvoki.Storage.Disk.Proofs.WAL.WalInventorySortWork

namespace Alvoki.Storage

open System

private def visitName {α : Type} (readName : String → Except IO.Error (Option α)) (name : String) :
    EStateM IO.Error (List String) (Option α) := fun before =>
  match readName name with
  | .ok found => .ok found (name :: before)
  | .error cause => .error cause (name :: before)

private theorem filterMapVisited {α : Type} (readName : String → Except IO.Error (Option α))
    (names before : List String) :
    let expected := names.filterMapM readName
    match names.filterMapM (visitName readName) before with
    | .ok found after => expected = .ok found ∧ after = names.reverse ++ before
    | .error cause after => expected = .error cause ∧ ∃ prefixNames failed rest,
        names = prefixNames ++ failed :: rest ∧ after = failed :: prefixNames.reverse ++ before ∧
        readName failed = .error cause ∧
        ∀ name ∈ prefixNames, ∃ found, readName name = .ok found := by
  dsimp only
  induction names generalizing before with
  | nil => simp [Pure.pure, EStateM.pure, Except.pure]
  | cons name rest ih =>
    simp only [List.filterMapM_cons]
    cases head : readName name with
    | error cause =>
      simp only [visitName, head, Bind.bind, EStateM.bind, Except.bind]
      exact ⟨trivial, [], name, rest, rfl, rfl, head, by simp⟩
    | ok extent =>
      have tail := ih (name :: before)
      cases observed : rest.filterMapM (visitName readName) (name :: before) with
      | error cause after =>
        rw [observed] at tail
        obtain ⟨reported, prior, failed, later, names, reached, rejected, accepted⟩ := tail
        cases extent <;>
          simp only [visitName, head, Bind.bind, EStateM.bind, Except.bind, observed, reported]
        all_goals
          refine ⟨trivial, name :: prior, failed, later, by simp [names], by simpa using reached, rejected, ?_⟩
          intro earlier seen
          rcases List.mem_cons.mp seen with rfl | inPrefix
          · exact ⟨_, head⟩
          · exact accepted earlier inPrefix
      | ok found after =>
        rw [observed] at tail
        obtain ⟨reported, reached⟩ := tail
        cases extent <;> simp [visitName, head, Bind.bind, EStateM.bind, Except.bind,
          Pure.pure, EStateM.pure, Except.pure, observed, reported, reached]

/-- Work charged by the cached extent scan, before selection or payload reads. -/
structure WalInventoryWork where
  result : Except IO.Error (List (Nat × IO.FS.Metadata))
  visited : List String
  comparisons : Nat

/-- Record every name handed to the canonical extent probe, including a
rejected name, and count the comparisons on the successful sort branch. -/
noncomputable def readWalSegmentExtentsWithWork (directory : DiskDirectory)
    (lstat : FilePath → Except IO.Error (Except IO.Error IO.FS.Metadata)) (names : List String) : WalInventoryWork :=
  let readName := readWalSegmentExtentWith directory lstat
  match names.filterMapM (visitName readName) [] with
  | .ok extents visited =>
    let (sorted, comparisons) := mergeSortWithComparisonWork (fun left right => left.1 ≤ right.1) extents
    ⟨.ok sorted, visited.reverse, comparisons⟩
  | .error cause visited => ⟨.error cause, visited.reverse, 0⟩

/-- The actual extent scan and its counted interpretation return the same
list or error. Only the successful branch sorts, with at most one
comparison per returned extent per merge level. -/
theorem readWalSegmentExtentsWithWork_spec (directory : DiskDirectory)
    (lstat : FilePath → Except IO.Error (Except IO.Error IO.FS.Metadata)) (names : List String) :
    let work := readWalSegmentExtentsWithWork directory lstat names
    work.result = readWalSegmentExtentsWith directory lstat names ∧
    match work.result with
    | .ok extents => work.visited = names ∧
        ∀ levels, extents.length ≤ 2 ^ levels → work.comparisons ≤ extents.length * levels
    | .error cause => work.comparisons = 0 ∧ ∃ prefixNames failed rest,
        names = prefixNames ++ failed :: rest ∧ work.visited = prefixNames ++ [failed] ∧
        readWalSegmentExtentWith directory lstat failed = .error cause ∧
        ∀ name ∈ prefixNames, ∃ found, readWalSegmentExtentWith directory lstat name = .ok found := by
  let readName := readWalSegmentExtentWith directory lstat
  have visits := filterMapVisited readName names []
  cases observed : names.filterMapM (visitName readName) [] with
  | ok extents after =>
    rw [observed] at visits
    obtain ⟨found, reached⟩ := visits
    dsimp only [readName] at observed found
    obtain ⟨same, _, bounded⟩ :=
      mergeSortWithComparisonWork_spec (fun left right => left.1 ≤ right.1) extents
    simp only [readWalSegmentExtentsWithWork, readWalSegmentExtentsWith, observed, found, reached,
      Bind.bind, Except.bind, Pure.pure, Except.pure, List.append_nil, List.reverse_reverse, same,
      List.length_mergeSort]
    exact ⟨trivial, trivial, bounded⟩
  | error cause after =>
    rw [observed] at visits
    obtain ⟨reported, prior, failed, rest, namesExact, reached, rejected, accepted⟩ := visits
    dsimp only [readName] at observed reported
    simp only [readWalSegmentExtentsWithWork, readWalSegmentExtentsWith,
      observed, reported, reached, Bind.bind, Except.bind, List.append_nil, List.reverse_cons, List.reverse_reverse]
    exact ⟨trivial, trivial, prior, failed, rest, namesExact, rfl, rejected, accepted⟩

/-- Bound logical parser input by the whole listing. An error charges the
prefix ending at the name that returned it. The UTF-8 sum measures inputs
to the parser, while its internal string and numeric costs are separate. -/
theorem readWalSegmentExtentsWithWork_bound (directory : DiskDirectory)
    (lstat : FilePath → Except IO.Error (Except IO.Error IO.FS.Metadata)) (names : List String) :
    let visited := (readWalSegmentExtentsWithWork directory lstat names).visited
    visited.length ≤ names.length ∧
      (visited.map String.utf8ByteSize).sum ≤ (names.map String.utf8ByteSize).sum := by
  dsimp only
  have reached := (readWalSegmentExtentsWithWork_spec directory lstat names).2
  cases result : (readWalSegmentExtentsWithWork directory lstat names).result with
  | ok extents =>
    rw [result] at reached
    simp [reached.1]
  | error cause =>
    rw [result] at reached
    obtain ⟨_, prior, failed, rest, whole, visited, _⟩ := reached
    rw [visited, whole]
    simp only [List.length_append, List.length_cons, List.length_nil, Nat.zero_add,
      List.map_append, List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, Nat.add_zero]
    omega

private theorem nameBytes_filter_le (names : List String) (keep : String → Bool) :
    ((names.filter keep).map String.utf8ByteSize).sum ≤ (names.map String.utf8ByteSize).sum := by
  induction names with
  | nil => simp
  | cons name rest ih =>
    cases kept : keep name <;> simp [kept] <;> omega

/-- After a clean directory scan, bound WAL name recognition directly by
the raw reported names, including the discarded dot entries. -/
theorem OpenedDirectoryScan.walNameWork_bound (scan : OpenedDirectoryScan) (directory : DiskDirectory)
    (lstat : FilePath → Except IO.Error (Except IO.Error IO.FS.Metadata)) :
    let listed := (scan.entries directory.path).toList.map (·.fileName)
    let visited := (readWalSegmentExtentsWithWork directory lstat listed).visited
    visited.length ≤ scan.names.length ∧
      (visited.map String.utf8ByteSize).sum ≤ (scan.names.map String.utf8ByteSize).sum := by
  have names : (scan.entries directory.path).toList.map (·.fileName) = scan.visibleNames := by
    simp [scan.entries_toList, List.map_map, Function.comp_def]
  dsimp only
  rw [names]
  obtain ⟨count, bytes⟩ := readWalSegmentExtentsWithWork_bound directory lstat scan.visibleNames
  exact ⟨Nat.le_trans count (List.length_filter_le ..), Nat.le_trans bytes (nameBytes_filter_le ..)⟩

end Alvoki.Storage
