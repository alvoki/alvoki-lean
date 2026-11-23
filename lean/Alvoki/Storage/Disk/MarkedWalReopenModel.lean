import Alvoki.Storage.Disk.WalBoundary
import Alvoki.Storage.Publication.DirectoryPublicationModel

namespace Alvoki.WAL.Boundary
open Storage

/-- Directory metadata remains paired. Until a shared directory sync, WAL
contents can conservatively be chosen independently of a metadata pair. -/
structure ReopenImage where
  directory : DirectoryPublication.Image
  wal : Publication.Image

/-- Each metadata pair has an expected prefix. Every possible WAL binding must
contain the prefix required by every still selectable metadata pair. -/
private def accepts (directory : DirectoryPublication.Image)
    (expected : DirectoryPublication.Bindings → ByteArray) (walBinding : Option ByteArray) : Prop :=
  ∀ pair ∈ directory.active :: directory.crashImages,
    ∃ marker contents length, pair.walBoundary = some marker ∧ walBinding = some contents ∧
      decode marker = .ok length ∧ select length contents = .ok (expected pair)

def ReopenImage.Valid (image : ReopenImage) (expected : DirectoryPublication.Bindings → ByteArray) : Prop :=
  image.wal.Valid (accepts image.directory expected)

/-- The repair path takes its replacement from the visible marker and WAL.
Every marker that could still survive a crash must fit in that replacement. -/
structure ReopenImage.RepairsTo (image : ReopenImage) (length : UInt64) (trimmed : ByteArray) : Prop where
  visibleMarker : ∃ marker, image.directory.active.walBoundary = some marker ∧ decode marker = .ok length
  selected : ∃ contents, image.wal.active = some contents ∧ select length contents = .ok trimmed ∧
    trimmed.size < contents.size
  coversCandidates : ∀ pair ∈ image.directory.active :: image.directory.crashImages,
    ∀ marker count, pair.walBoundary = some marker → decode marker = .ok count → count.toNat ≤ length.toNat

/-- The WAL repair uses the ordinary replacement schedule. A cut before its
last operation leaves both metadata bindings unsettled. A cut including the
successful directory sync settles them together with the repaired WAL name. -/
def ReopenImage.repairCut (image : ReopenImage) (trimmed : ByteArray) (cut : Nat) : Option ReopenImage :=
  (image.wal.execute trimmed (Publication.steps.take cut)).map fun wal =>
    ⟨if Publication.steps.length ≤ cut then image.directory.syncDirectory else image.directory, wal⟩

/-- On the aligned reopen path, syncing the directory settles all three names
after the visible WAL has been synced. -/
def ReopenImage.syncDirectory (image : ReopenImage) : ReopenImage :=
  ⟨image.directory.syncDirectory, { image.wal with crashImages := [image.wal.active] }⟩

def ReopenImage.crash (pair : DirectoryPublication.Bindings) (wal : Option ByteArray) : ReopenImage :=
  ⟨.settled pair, .settled wal⟩

private theorem accepts_syncDirectory {directory : DirectoryPublication.Image}
    {expected : DirectoryPublication.Bindings → ByteArray} {wal : Option ByteArray}
    (valid : accepts directory expected wal) : accepts directory.syncDirectory expected wal := by
  intro pair chosen
  have current : pair = directory.active := by
    simpa [DirectoryPublication.Image.syncDirectory] using chosen
  exact valid pair (List.mem_cons.mpr (.inl current))

private theorem accepts_repair {image : ReopenImage} {expected : DirectoryPublication.Bindings → ByteArray}
    {length : UInt64} {trimmed : ByteArray}
    (valid : image.Valid expected) (repair : image.RepairsTo length trimmed) :
    accepts image.directory expected (some trimmed) := by
  obtain ⟨contents, present, selected, _⟩ := repair.selected
  intro pair chosen
  obtain ⟨marker, old, count, bound, same, decoded, selectedPrefix⟩ := valid.activeValid pair chosen
  rw [present] at same
  cases same
  have fits := repair.coversCandidates pair chosen marker count bound decoded
  exact ⟨marker, trimmed, count, bound, rfl, decoded,
    (select_shorter_after_trim selected fits).trans selectedPrefix⟩

theorem ReopenImage.repairCut_valid {image after : ReopenImage}
    {expected : DirectoryPublication.Bindings → ByteArray} {length : UInt64} {trimmed : ByteArray}
    (valid : image.Valid expected) (repair : image.RepairsTo length trimmed)
    (cut : Nat) (ran : image.repairCut trimmed cut = some after) : after.Valid expected := by
  unfold repairCut at ran
  obtain ⟨wal, replaced, rfl⟩ := Option.map_eq_some_iff.mp ran
  have path : Publication.Retry (fun _ bytes => bytes = trimmed) image.wal wal :=
    .attempt (.refl _) rfl cut replaced
  have acceptsReplacement := accepts_repair valid repair
  have walValid := Publication.retry_preserves
    (fun _ _ _ equal => equal.symm ▸ acceptsReplacement) valid path
  by_cases complete : Publication.steps.length ≤ cut
  · simpa only [Valid, ite_eq_left complete] using
      (show wal.Valid (accepts image.directory.syncDirectory expected) from
        ⟨walValid.hasCrashImage, accepts_syncDirectory walValid.activeValid,
          fun candidate survives => accepts_syncDirectory (walValid.crashValid candidate survives)⟩)
  · simpa only [Valid, ite_eq_right complete] using walValid

theorem ReopenImage.repair_complete (image : ReopenImage) (trimmed : ByteArray) :
    image.repairCut trimmed Publication.steps.length =
      some ⟨image.directory.syncDirectory, .settled (some trimmed)⟩ := by
  simp [repairCut, Publication.successful_replace]

theorem ReopenImage.syncDirectory_valid {image : ReopenImage}
    {expected : DirectoryPublication.Bindings → ByteArray} (valid : image.Valid expected) :
    image.syncDirectory.Valid expected := by
  refine ⟨by simp [syncDirectory], accepts_syncDirectory valid.activeValid, ?_⟩
  intro wal survives
  have selected : wal = image.wal.active := List.mem_singleton.mp survives
  exact selected.symm ▸ accepts_syncDirectory valid.activeValid

theorem ReopenImage.crash_valid {image : ReopenImage} {expected : DirectoryPublication.Bindings → ByteArray}
    (valid : image.Valid expected) {pair : DirectoryPublication.Bindings} {wal : Option ByteArray}
    (metadataSurvives : pair ∈ image.directory.crashImages) (walSurvives : wal ∈ image.wal.crashImages) :
    (crash pair wal).Valid expected := by
  apply Publication.Image.settled_valid
  intro installed chosen
  have selected : installed = pair := by
    simpa [crash, DirectoryPublication.Image.settled] using chosen
  exact valid.crashValid wal walSurvives installed (List.mem_cons.mpr (.inr (selected.symm ▸ metadataSurvives)))

/-- A failed repair can retry from any schedule cut, including one whose
directory sync took effect. A crash chooses a metadata pair and a WAL binding. -/
inductive ReopenRetry (initial : ReopenImage) : ReopenImage → Prop where
  | start : ReopenRetry initial initial
  | repair (path : ReopenRetry initial before) (choice : before.RepairsTo length trimmed)
      (ran : before.repairCut trimmed cut = some after) : ReopenRetry initial after
  | syncDirectory (path : ReopenRetry initial before) : ReopenRetry initial before.syncDirectory
  | crash (path : ReopenRetry initial before) (pairSurvives : pair ∈ before.directory.crashImages)
      (walSurvives : wal ∈ before.wal.crashImages) : ReopenRetry initial (.crash pair wal)

theorem reopenRetry_valid {initial after : ReopenImage} {expected : DirectoryPublication.Bindings → ByteArray}
    (valid : initial.Valid expected) (path : ReopenRetry initial after) : after.Valid expected := by
  induction path with
  | start => exact valid
  | repair _ choice ran earlier => exact ReopenImage.repairCut_valid earlier choice _ ran
  | syncDirectory _ earlier => exact ReopenImage.syncDirectory_valid earlier
  | crash _ pairSurvives walSurvives earlier =>
    exact ReopenImage.crash_valid earlier pairSurvives walSurvives

/-- Given the checkpoint that belongs to the chosen metadata pair, its replay
input is unchanged by retries, even if the physical WAL name selects the old file. -/
theorem ReopenImage.recover_chosen {image : ReopenImage}
    {expected : DirectoryPublication.Bindings → ByteArray} (valid : image.Valid expected)
    (checkpoint : PackedTable) {pair : DirectoryPublication.Bindings} {wal : Option ByteArray}
    (metadataChosen : pair ∈ image.directory.active :: image.directory.crashImages)
    (walChosen : wal ∈ image.wal.active :: image.wal.crashImages) :
    ∃ marker contents, pair.walBoundary = some marker ∧ wal = some contents ∧
      (do
        let length ← decode marker
        let selected ← select length contents
        recoverSelected checkpoint selected) = recoverSelected checkpoint (expected pair) := by
  have accepted : accepts image.directory expected wal := by
    rcases List.mem_cons.mp walChosen with rfl | survives
    · exact valid.activeValid
    · exact valid.crashValid _ survives
  obtain ⟨marker, contents, length, boundary, present, decoded, selected⟩ := accepted pair metadataChosen
  refine ⟨marker, contents, boundary, present, ?_⟩
  rw [decoded]
  change (do let bytes ← select length contents; recoverSelected checkpoint bytes) = _
  rw [selected]
  rfl

end Alvoki.WAL.Boundary
