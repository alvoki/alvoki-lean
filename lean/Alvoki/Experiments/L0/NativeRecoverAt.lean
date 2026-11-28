import Alvoki.Experiments.L0.NativeManifest
import Alvoki.Experiments.L0.NativeRecovery
import Alvoki.Experiments.L0.NativeTableCheck
import Alvoki.Experiments.L0.NativeScope
import Alvoki.Experiments.WAL.Segmented.Proofs.Writeback

namespace ExperimentalL0.NativeRecoverAt

open System Lifecycle Alvoki.NativePost
open NativeRead (Footprint Owned tableNamespace)
abbrev Wal := WalRecoverySlice.Segmented.Native.Handle
abbrev Ref := IO.Ref (Phase Wal)
abbrev S := WalRecoverySlice.Segmented.Session

variable {inode : Type} {physical : W → Footprint inode} {root : FilePath}
  {lock : IO.FS.Handle} {ref : Ref} {image : Selected} {history : Rows}

structure Opening (physical : W → Footprint inode) (root : FilePath)
    (lock : IO.FS.Handle) (ref : Ref) (image : Selected) (w : W) : Prop where
  owned : Owned (physical w) root lock ref
  phase : (physical w).phase = .opening
  catalog : (tableNamespace physical root).Represents w image.tables
  disk : WalRecoverySlice.Segmented.Recoverable image.view none (physical w).disk

/-- The manifest read changes neither the owned root/cell nor a selected
table binding. Background writes are represented by concrete WAL writebacks. -/
structure ManifestFrame (physical : W → Footprint inode) (root : FilePath)
    (tables : Catalog) (s t : W) : Prop where
  lock : (physical t).rootLock = (physical s).rootLock
  ref : (physical t).phaseRef = (physical s).phaseRef
  phase : (physical t).phase = (physical s).phase
  disk : NativeRead.Writebacks (physical s).disk (physical t).disk
  tablesKept : (tableNamespace physical root).Keeps s t tables

theorem ManifestFrame.refl : ManifestFrame physical root tables w w :=
  ⟨rfl, rfl, rfl, .nil, fun _ _ _ _ _ a b => ⟨a, b⟩⟩

theorem Opening.frame (start : Opening physical root lock ref image s)
    (step : ManifestFrame physical root image.tables s t) :
    Opening physical root lock ref image t := by
  refine ⟨⟨step.lock.trans start.owned.1, step.ref.trans start.owned.2⟩,
    step.phase.trans start.phase, start.catalog.frame step.tablesKept, ?_⟩
  have keep {a b} (w : NativeRead.Writebacks a b)
      (h : WalRecoverySlice.Segmented.Recoverable image.view none a) :
      WalRecoverySlice.Segmented.Recoverable image.view none b := by
    induction w with
    | nil => exact h
    | next _ id file ih => exact ih.writeback id file
  exact keep step.disk start.disk

structure Held (physical : W → Footprint inode) (root : FilePath)
    (lock : IO.FS.Handle) (ref : Ref) (image : Selected) (phase : Phase Wal) (w : W) : Prop where
  owned : Owned (physical w) root lock ref
  phaseEq : (physical w).phase = phase
  catalog : (tableNamespace physical root).Represents w image.tables
  manifest : (physical w).manifest.Stable (L0Manifest.encode image.version)

def Child (physical : W → Footprint inode) (image : Selected) (wal : Wal) (w : W) : Prop :=
  ∃ child, (physical w).readyWal wal = some child ∧
    WalRecoverySlice.Segmented.Installed child (physical w).disk ∧ child.view = image.view

abbrev ManifestReady (physical : W → Footprint inode) (root : FilePath)
    (lock : IO.FS.Handle) (ref : Ref) (image : Selected) (w : W) : Prop :=
  Held physical root lock ref image .opening w ∧
    WalRecoverySlice.Segmented.Recoverable image.view none (physical w).disk

abbrev Attached (physical : W → Footprint inode) (root : FilePath) (lock : IO.FS.Handle)
    (ref : Ref) (image : Selected) (wal : Wal) (w : W) : Prop :=
  Held physical root lock ref image (.recovering wal) w ∧ Child physical image wal w

def Failed (physical : W → Footprint inode) (root : FilePath) (lock : IO.FS.Handle)
    (ref : Ref) (image : Selected) (w : W) : Prop :=
  Opening physical root lock ref image w ∨ ∃ wal, Attached physical root lock ref image wal w

theorem Held.frame (held : Held physical root lock ref image phase s)
    (step : NativeRead.Frame physical root wal image.tables s t) :
    Held physical root lock ref image phase t :=
  ⟨⟨step.lock.trans held.owned.1, step.ref.trans held.owned.2⟩,
    step.phase.trans held.phaseEq, held.catalog.frame step.tablesKept,
    ⟨step.manifest.trans held.manifest.1, step.survivors.trans held.manifest.2⟩⟩

theorem Child.frame (held : Child physical image wal s)
    (step : NativeRead.Frame physical root wal image.tables s t) : Child physical image wal t := by
  obtain ⟨c, cached, installed, view⟩ := held
  exact ⟨c, step.child.trans cached, step.disk.installed installed, view⟩

theorem manifest (d : Durable image history) (opening : Opening physical root lock ref image start)
    (bytes : (physical start).manifest.active = L0Manifest.encode image.version)
    (prim : NativeManifest.Primitives (root / "manifest")
      (ManifestFrame physical root image.tables start) (fun w => (physical w).manifest)) :
    Returns (Native.callbackComponents root ref).manifest.reopen start
      (fun v t => v = image.version ∧ ManifestReady physical root lock ref image t)
      (Failed physical root lock ref image) := by
  have result := NativeManifest.reopen prim ManifestFrame.refl bytes d.unique
  change Returns (NativeManifest.backend (root / "manifest")).reopen _ _ _
  unfold Returns
  cases ran : (NativeManifest.backend (root / "manifest")).reopen.run start with
  | error _ t => rw [ran] at result; exact .inl (opening.frame result.1)
  | ok v t =>
    rw [ran] at result
    cases v with
    | error _ => exact .inl (opening.frame result.1)
    | ok v =>
      obtain ⟨rfl, step, _, stable⟩ := result
      have after := opening.frame step
      exact ⟨rfl, ⟨after.owned, after.phase, after.catalog, stable⟩, after.disk⟩

theorem tables (d : Durable image history) (attached : Attached physical root lock ref image wal start)
    (prim : NativeRead.Primitives (tableNamespace physical root) life
      (NativeRead.Frame physical root wal image.tables start)) :
    Returns (checkTables (Native.callbackComponents root ref).tables image.version.tables) start
      (fun _ t => Attached physical root lock ref image wal t)
      (fun t => Attached physical root lock ref image wal t) := by
  have result := NativeRead.checkTables_frame prim (Native.callbackComponents root ref).tables
    rfl d (fun _ step => attached.1.catalog.frame step.tablesKept) start NativeRead.Frame.refl
  have keep {t} (step : NativeRead.Frame physical root wal image.tables start t) :
      Attached physical root lock ref image wal t := ⟨attached.1.frame step, attached.2.frame step⟩
  unfold Returns
  cases ran : (checkTables (Native.callbackComponents root ref).tables image.version.tables).run start with
  | error => rw [ran] at result; exact keep result
  | ok v t =>
    rw [ran] at result
    cases v with
    | error => exact keep result
    | ok => exact keep result.1

/-- Physical effects of a swap of the owned phase reference. Only the
phase slot is replaced. The before/after relation permits WAL writeback. -/
structure Swapped (physical : W → Footprint inode) (root : FilePath) (wal : Wal)
    (tables : Catalog) (next : Phase Wal) (s t : W) : Prop where
  lock : (physical t).rootLock = (physical s).rootLock
  ref : (physical t).phaseRef = (physical s).phaseRef
  phase : (physical t).phase = next
  child : (physical t).readyWal wal = (physical s).readyWal wal
  disk : NativeRead.Writebacks (physical s).disk (physical t).disk
  active : (physical t).manifest.active = (physical s).manifest.active
  survivors : (physical t).manifest.survivors = (physical s).manifest.survivors
  tablesKept : (tableNamespace physical root).Keeps s t tables

theorem Swapped.held (step : Swapped physical root wal image.tables next s t)
    (before : Held physical root lock ref image old s) : Held physical root lock ref image next t :=
  ⟨⟨step.lock.trans before.owned.1, step.ref.trans before.owned.2⟩,
    step.phase, before.catalog.frame step.tablesKept,
    ⟨step.active.trans before.manifest.1, step.survivors.trans before.manifest.2⟩⟩

theorem Swapped.keepsChild (step : Swapped physical root wal image.tables next s t)
    (before : Child physical image wal s) : Child physical image wal t := by
  obtain ⟨c, cached, valid, view⟩ := before
  exact ⟨c, step.child.trans cached, step.disk.installed valid, view⟩

theorem published (step : Swapped physical root wal image.tables (.online wal session) s t)
    (before : Attached physical root lock ref image wal s) (installed : Installed session image history) :
    NativeRead.Online physical root lock ref wal session image history t := by
  have held := step.held before.1
  exact ⟨held.owned, held.phaseEq, step.keepsChild before.2, held.manifest, held.catalog, installed⟩

/-- Local runtime/storage correspondence. The optional session at an
owned WAL handle denotes its two actual heap bindings. -/
def Cached (heap : WalRecoverySlice.Segmented.Native.PhaseMemory)
    (physical : W → Footprint inode) (root : FilePath) (lock : IO.FS.Handle) (ref : Ref) : Prop :=
  ∀ w, Owned (physical w) root lock ref → ∀ h c, (physical w).readyWal h = some c ↔ heap.Ready h c w

/-- The stage-specific frame on the actual mutex and inner phase reference
operations used by scan. -/
structure ScanPrimitives (physical : W → Footprint inode) (root : FilePath) (wal : Wal)
    (tables : Catalog) (epoch : W) : Prop where
  lock : ∀ (m : Std.BaseMutex) t, NativeRead.Frame physical root wal tables epoch t →
    NativeRead.Frame physical root wal tables epoch (m.lock t).state
  read : ∀ (r : IO.Ref (WalRecoverySlice.Segmented.Native.Phase WalRecoverySlice.Segmented.Native.Store)) t,
    NativeRead.Frame physical root wal tables epoch t →
    NativeRead.Frame physical root wal tables epoch ((r.get : BaseIO _) t).state
  unlock : ∀ (m : Std.BaseMutex) t, NativeRead.Frame physical root wal tables epoch t →
    NativeRead.Frame physical root wal tables epoch (m.unlock t).state

theorem scanned (heap : WalRecoverySlice.Segmented.Native.PhaseMemory)
    (cached : Cached heap physical root lock ref) (before : Attached physical root lock ref image wal start)
    (prim : ScanPrimitives physical root wal image.tables start) :
    IOReturns (WalRecoverySlice.Segmented.Native.scan wal) start
      (fun v t => v = image.view ∧ Attached physical root lock ref image wal t) failed := by
  obtain ⟨c, slot, _, view⟩ := before.2
  have ready := (cached _ before.1.owned wal c).mp slot
  have ran := (WalRecoverySlice.Segmented.Native.scan_ready_world heap ready).1
  have frame := WalRecoverySlice.Segmented.Native.scanWorld_frame wal prim.lock prim.read prim.unlock
    NativeRead.Frame.refl
  unfold IOReturns
  rw [ran]
  exact ⟨view, before.1.frame frame, before.2.frame frame⟩

theorem checked {a : F α} (safe : Returns a w ok failed) :
    NativeScope.Post (Native.checked a) w ok (fun _ t => failed t) := by
  unfold NativeScope.Post Native.checked Returns at *
  cases ran : a.run w with
  | error e t => simpa [Bind.bind, instMonadEIO._aux_13, EST.bind, ran] using safe
  | ok v t =>
    cases v <;> simpa [Bind.bind, instMonadEIO._aux_13, EST.bind, ran, Pure.pure,
      instMonadEIO._aux_5, EST.pure, throw, throwThe, MonadExceptOf.throw, instMonadExceptOfEIO._aux_1, EST.throw] using safe

end ExperimentalL0.NativeRecoverAt
