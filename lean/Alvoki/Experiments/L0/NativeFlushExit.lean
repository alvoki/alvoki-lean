import Alvoki.Experiments.L0.MutationExitCut
import Alvoki.Experiments.L0.NativeFlush
import Alvoki.Experiments.L0.NativeFlushBoot

namespace ExperimentalL0.NativeFlushExit
open NativeScope (W)
open NativeRead (Footprint tableNamespace)
open NativeReadScope (Files)
open NativeFlushRestart (stored proposal Survivor)
open MutationExitCut (Frame)
open WalRecoverySlice.Segmented (Recoverable)
open System

abbrev Result := EST.Out IO.Error IO.RealWorld Session

/-- These are the visible media at return from the store, before the update
publishes its session or tries to close. In the admitted case a later power
loss can still choose different bytes from the current active manifest. -/
inductive Media (physical : W → Footprint inode) (root : FilePath) (before : Selected) (s : Session)
    (w : W) : Catalog → Prop where
  | original (catalog : (tableNamespace physical root).Represents w before.tables)
      (stable : (physical w).manifest.Stable (L0Manifest.encode before.version)) :
      Media physical root before s w before.tables
  | published (id : UInt64) (fresh : before.tables id = none) (fits : before.view.tail < UInt64.size)
      (catalog : (tableNamespace physical root).Represents w (stored before s id).tables)
      (stable : (physical w).manifest.Stable (L0Manifest.encode (proposal before s id))) :
      Media physical root before s w (stored before s id).tables
  | admitted (id : UInt64) (fresh : before.tables id = none) (fits : before.view.tail < UInt64.size)
      (catalog : (tableNamespace physical root).Represents w (stored before s id).tables)
      (allowed : (physical w).manifest.Admits (L0Manifest.encode before.version)
        (some (L0Manifest.encode (proposal before s id)))) :
      Media physical root before s w (stored before s id).tables

theorem Media.advance (source : Media physical root before s w tables)
    (edge : Frame physical root tables w cut) : Media physical root before s cut tables := by
  cases source with
  | original catalog stable =>
    exact .original (catalog.frame edge.catalog)
      ⟨edge.manifest.trans stable.1, edge.survivors.trans stable.2⟩
  | published id fresh fits catalog stable =>
    exact .published id fresh fits (catalog.frame edge.catalog)
      ⟨edge.manifest.trans stable.1, edge.survivors.trans stable.2⟩
  | admitted id fresh fits catalog allowed =>
    exact .admitted id fresh fits (catalog.frame edge.catalog)
      (by simpa only [DurableBlob.Image.Admits, edge.manifest, edge.survivors] using allowed)

/-- Boot resolves each catalog binding from the appropriate live or durable inode.
A post-rename error retains its whole survivor set until this selection. -/
theorem Media.reboot {physical : W → Footprint inode} {media : NativeTableCreate.Media (tableNamespace physical root)}
    (source : Media physical root before s cut tables)
    (stable : media.stable.Represents cut tables) (wal : Recoverable before.view none (physical cut).disk)
    (boot : NativeFlushRestart.Boot physical root media tables cut mode after) :
    ∃ img, Survivor physical root before s after img ∧ Files physical root img after := by
  have disk := boot.wal.recoverable wal
  cases source with
  | original catalog saved =>
    have active := boot.active saved
    exact ⟨_, .old active, ⟨boot.catalog catalog stable, active, disk⟩⟩
  | published id fresh fits catalog saved =>
    have live := boot.catalog catalog stable
    have row := live id s.mem.toList (by simp [stored])
    have active := boot.active saved
    exact ⟨_, .newTable id fresh fits row active, ⟨live, active, disk⟩⟩
  | admitted id fresh fits catalog allowed =>
    have live := boot.catalog catalog stable
    rcases boot.selected allowed with old | new
    · refine ⟨_, .old old, ⟨?_, old, disk⟩⟩
      intro k rows bound
      have ne : k ≠ id := by rintro rfl; simp [fresh] at bound
      exact live k rows (by simpa [stored, ne] using bound)
    · have row := live id s.mem.toList (by simp [stored])
      exact ⟨_, .newTable id fresh fits row new, ⟨live, new, disk⟩⟩

structure Edge (physical : W → Footprint inode) (root : FilePath)
    (media : NativeTableCreate.Media (tableNamespace physical root)) (tables : Catalog) (w t : W) : Prop
    extends Frame physical root tables w t where
  stable : media.stable.Keeps w t tables

theorem Edge.same (physical : W → Footprint inode) (root : FilePath)
    (media : NativeTableCreate.Media (tableNamespace physical root)) (tables : Catalog) (w : W) :
    Edge physical root media tables w w :=
  ⟨Frame.refl .., fun _ _ _ _ _ n c => ⟨n,c⟩⟩

theorem Edge.trans (ab : Edge physical root media tables a b)
    (bc : Edge physical root media tables b c) : Edge physical root media tables a c :=
  ⟨ab.toFrame.trans bc.toFrame, ab.stable.trans bc.stable⟩

def resultAt (root : FilePath) (image : Selected) (s : Session) (w : W) : Result :=
  if s.mem.isEmpty then .ok s w
  else if image.view.tail < UInt64.size then NativeFlush.store root image s w
  else .error (IO.userError "absolute WAL position exhausted") w

end ExperimentalL0.NativeFlushExit
