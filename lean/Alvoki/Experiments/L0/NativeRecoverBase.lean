import Alvoki.Experiments.L0.NativeManifest
import Alvoki.Experiments.L0.NativeRecovery
import Alvoki.Experiments.L0.NativeTableCheck
import Alvoki.Experiments.L0.NativePublish
import Alvoki.Experiments.WAL.Segmented.Proofs.Writeback
import Alvoki.Experiments.WAL.Segmented.Proofs.RuntimeStoreOpen

namespace ExperimentalL0.NativeRecoverAt

open System Lifecycle Alvoki.NativePost
open NativeRead (Footprint Owned tableNamespace)
abbrev Wal := WalRecoverySlice.Segmented.Native.Handle
abbrev Ref := IO.Ref (Phase Wal)
abbrev S := WalRecoverySlice.Segmented.Session

variable {inode : Type} {physical : W → Footprint inode} {root : FilePath}
  {lock : IO.FS.Handle} {ref : Ref} {image : Selected} {history : Rows}

structure Opening (physical : W → Footprint inode) (root : FilePath)
    (lock : IO.FS.Handle) (ref : Ref) (image : Selected) (w : W) (req : Option WalRecoverySlice.Segmented.Contract.Request := none) : Prop where
  owned : Owned (physical w) root lock ref
  phase : (physical w).phase = .opening
  catalog : (tableNamespace physical root).Represents w image.tables
  disk : WalRecoverySlice.Segmented.Recoverable image.view req (physical w).disk

/-- The manifest read changes neither the owned root/cell nor a selected
table binding. Background writes are represented by concrete WAL writebacks. -/
structure ManifestFrame (physical : W → Footprint inode) (root : FilePath)
    (tables : Catalog) (s t : W) : Prop where
  lock : (physical t).rootLock = (physical s).rootLock
  ref : (physical t).phaseRef = (physical s).phaseRef
  phase : (physical t).phase = (physical s).phase
  disk : WalRecoverySlice.Segmented.Writebacks (physical s).disk (physical t).disk
  tablesKept : (tableNamespace physical root).Keeps s t tables

theorem ManifestFrame.refl : ManifestFrame physical root tables w w :=
  ⟨rfl, rfl, rfl, .nil, fun _ _ _ _ _ a b => ⟨a, b⟩⟩

theorem Opening.frame (start : Opening physical root lock ref image s req)
    (step : ManifestFrame physical root image.tables s t) :
    Opening physical root lock ref image t req := by
  refine ⟨⟨step.lock.trans start.owned.1, step.ref.trans start.owned.2⟩,
    step.phase.trans start.phase, start.catalog.frame step.tablesKept, ?_⟩
  exact WalRecoverySlice.Segmented.Writebacks.recoverable step.disk start.disk

structure Held (physical : W → Footprint inode) (root : FilePath)
    (lock : IO.FS.Handle) (ref : Ref) (image : Selected) (phase : Phase Wal) (w : W) : Prop where
  owned : Owned (physical w) root lock ref
  phaseEq : (physical w).phase = phase
  catalog : (tableNamespace physical root).Represents w image.tables
  manifest : (physical w).manifest.Stable (L0Manifest.encode image.version)

abbrev Child {inode : Type} := NativeRead.RegisteredChild (inode := inode)

abbrev ManifestReady (physical : W → Footprint inode) (root : FilePath)
    (lock : IO.FS.Handle) (ref : Ref) (image : Selected) (w : W) (req : Option WalRecoverySlice.Segmented.Contract.Request := none) : Prop :=
  Held physical root lock ref image .opening w ∧
    WalRecoverySlice.Segmented.Recoverable image.view req (physical w).disk

abbrev Attached (physical : W → Footprint inode) (root : FilePath) (lock : IO.FS.Handle)
    (ref : Ref) (image : Selected) (wal : Wal) (w : W) : Prop :=
  Held physical root lock ref image (.recovering wal) w ∧ Child physical root image wal w

def Failed (physical : W → Footprint inode) (root : FilePath) (lock : IO.FS.Handle)
    (ref : Ref) (image : Selected) (w : W) : Prop :=
  (Opening physical root lock ref image w ∧ (physical w).manifest.active = L0Manifest.encode image.version) ∨
    ∃ wal, Attached physical root lock ref image wal w

theorem Held.frame (held : Held physical root lock ref image phase s)
    (step : NativeRead.Frame physical root wal image.tables s t) :
    Held physical root lock ref image phase t :=
  ⟨⟨step.lock.trans held.owned.1, step.ref.trans held.owned.2⟩,
    step.phase.trans held.phaseEq, held.catalog.frame step.tablesKept,
    ⟨step.manifest.trans held.manifest.1, step.survivors.trans held.manifest.2⟩⟩

theorem Child.frame (held : Child physical root image wal s)
    (step : NativeRead.Frame physical root wal image.tables s t) : Child physical root image wal t := by
  obtain ⟨c, cached, origin, installed, view⟩ := held
  exact ⟨c, step.child.trans cached, origin, installed.frame step cached, view⟩

theorem manifestOpening (d : Durable image history) (opening : Opening physical root lock ref image start req)
    (bytes : (physical start).manifest.active = L0Manifest.encode image.version)
    (prim : NativeManifest.Primitives (root / "manifest")
      (ManifestFrame physical root image.tables start) (fun w => (physical w).manifest)) :
    Returns (Native.callbackComponents root ref).manifest.reopen start
      (fun v t => v = image.version ∧ ManifestReady physical root lock ref image t req)
      (fun t => Opening physical root lock ref image t req ∧ (physical t).manifest.active = L0Manifest.encode image.version) := by
  have result := NativeManifest.reopen prim ManifestFrame.refl bytes d.unique
  change Returns (NativeManifest.backend (root / "manifest")).reopen _ _ _
  have retry {t} (same : (physical t).manifest = (physical start).manifest ∨
      (physical t).manifest = (physical start).manifest.barrier) :
      (physical t).manifest.active = L0Manifest.encode image.version := by
    rcases same with h | h <;> simpa only [h, DurableBlob.Image.barrier] using bytes
  unfold Returns
  cases ran : (NativeManifest.backend (root / "manifest")).reopen.run start with
  | error _ t => rw [ran] at result; exact ⟨opening.frame result.1, retry result.2⟩
  | ok v t =>
    rw [ran] at result
    cases v with
    | error _ => exact ⟨opening.frame result.1, retry result.2⟩
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
abbrev Swapped (physical : W → Footprint inode) (root : FilePath) (wal : Wal)
    (tables : Catalog) (next : Phase Wal) (s t : W) :=
  NativeRead.FrameTo physical root wal tables s t next

theorem Swapped.held (step : Swapped physical root wal image.tables next s t)
    (before : Held physical root lock ref image old s) : Held physical root lock ref image next t :=
  ⟨⟨step.lock.trans before.owned.1, step.ref.trans before.owned.2⟩,
    step.phase, before.catalog.frame step.tablesKept,
    ⟨step.manifest.trans before.manifest.1, step.survivors.trans before.manifest.2⟩⟩

theorem Swapped.keepsChild (step : Swapped physical root wal image.tables next s t)
    (before : Child physical root image wal s) : Child physical root image wal t := by
  obtain ⟨c, cached, origin, valid, view⟩ := before
  exact ⟨c, step.child.trans cached, origin, valid.frame step cached, view⟩

theorem Attached.sessionAt (attached : Attached physical root lock ref image wal w)
    (installed : Installed session image history) :
    NativeRead.SessionAt physical root lock ref wal session image history w (.recovering wal) :=
  ⟨attached.1.owned, attached.1.phaseEq, attached.2, attached.1.manifest, attached.1.catalog, installed⟩

/-- Local runtime/storage correspondence. The optional session at an
owned WAL handle denotes its two actual heap bindings. -/
def Cached (heap : WalRecoverySlice.Segmented.Native.PhaseMemory)
    (physical : W → Footprint inode) (root : FilePath) (lock : IO.FS.Handle) (ref : Ref) : Prop :=
  ∀ w, Owned (physical w) root lock ref → ∀ h c, (physical w).readyWal h = some c ↔ heap.Registered h c w

/-- The stage-specific frame on the actual mutex and inner phase reference
operations used by scan. -/
abbrev ScanPrimitives (physical : W → Footprint inode) (root : FilePath) (wal : Wal)
    (tables : Catalog) (epoch : W) :=
  WalRecoverySlice.Segmented.Native.ScanFrames wal epoch (NativeRead.Frame physical root wal tables epoch)

theorem scanned (heap : WalRecoverySlice.Segmented.Native.PhaseMemory)
    (cached : Cached heap physical root lock ref) (before : Attached physical root lock ref image wal start)
    (prim : ScanPrimitives physical root wal image.tables start) :
    IOReturns (WalRecoverySlice.Segmented.Native.scan wal) start
      (fun v t => v = image.view ∧ Attached physical root lock ref image wal t) failed := by
  obtain ⟨c, slot, _, _, view⟩ := before.2
  have ready := (cached _ before.1.owned wal c).mp slot
  have ran := (WalRecoverySlice.Segmented.Native.scan_ready_world heap ready.ready).1
  have frame := WalRecoverySlice.Segmented.Native.scanWorld_frame prim NativeRead.Frame.refl
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

/-- Read and swap semantics are restricted to the particular phase reference
under the root's verified ownership, including either primitive's reached footprint. -/
structure PhasePrimitives (physical : W → Footprint inode) (root : FilePath)
    (lock : IO.FS.Handle) (ref : Ref) (image : Selected) : Prop where
  read : ∀ w, Owned (physical w) root lock ref → ∃ t,
    (ref.get : IO (Phase Wal)) w = .ok (physical w).phase t ∧
    ManifestFrame physical root image.tables w t ∧ (physical t).manifest = (physical w).manifest ∧
    ∀ wal, (physical w).phase.wal = some wal → (physical t).readyWal wal = (physical w).readyWal wal ∧
      ∀ reg bs, (physical w).readyWal wal = some reg → (physical w).walChild reg bs → (physical t).walChild reg bs
  swap : ∀ w, Owned (physical w) root lock ref → ∀ wal next, ∃ t,
    (ref.swap next : IO (Phase Wal)) w = .ok (physical w).phase t ∧
    Swapped physical root wal image.tables next w t

/-- A reference read starts with the owned cell. Once it holds a WAL it
also preserves that handle's cached session. The opening case requires no
such handle to exist. -/
theorem PhasePrimitives.refRead (phase : PhasePrimitives physical root lock ref image) (wal : Wal) :
    NativeRead.RefRead physical root lock ref wal image.tables := by
  intro w owned attached
  obtain ⟨t, ran, frame, manifest, child⟩ := phase.read w owned
  exact ⟨t, ran, frame.lock, frame.ref, frame.phase, (child wal attached).1, (child wal attached).2, frame.disk,
    congrArg DurableBlob.Image.active manifest, congrArg DurableBlob.Image.survivors manifest, frame.tablesKept⟩

/-- Recovery attachment and public session publication share the very same
owned-reference swap contract. -/
theorem PhasePrimitives.refSwap (phase : PhasePrimitives physical root lock ref image) (wal : Wal) :
    NativeRead.RefSwap physical root lock ref wal image.tables := by
  intro w owns next
  obtain ⟨t, ran, effects⟩ := phase.swap w owns wal next
  rw [NativeScope.swap_io] at ran
  obtain ⟨value, world⟩ := EST.Out.ok.inj ran
  exact ⟨value, world ▸ effects⟩

theorem readOpening (prim : PhasePrimitives physical root lock ref image)
    (ready : ManifestReady physical root lock ref image w req) :
    Returns (Native.componentCell ref).read w
      (fun phase t => phase = .opening ∧ ManifestReady physical root lock ref image t req) failed := by
  obtain ⟨t, ran, frame, same, _⟩ := prim.read w ready.1.owned
  apply Returns.liftIO
  unfold IOReturns
  rw [ran]
  have before : Opening physical root lock ref image w req :=
    ⟨ready.1.owned, ready.1.phaseEq, ready.1.catalog, ready.2⟩
  have after := before.frame frame
  exact ⟨ready.1.phaseEq, ⟨after.owned, after.phase, after.catalog, same ▸ ready.1.manifest⟩, after.disk⟩

theorem attach (prim : PhasePrimitives physical root lock ref image)
    (held : Held physical root lock ref image .opening w) (child : Child physical root image wal w) :
    Returns ((Native.componentCell ref).swap (.recovering wal)) w
      (fun _ t => Attached physical root lock ref image wal t) failed := by
  obtain ⟨t, ran, step⟩ := prim.swap w held.owned wal (.recovering wal)
  apply Returns.liftIO
  unfold IOReturns
  rw [ran]
  exact ⟨Swapped.held step held, Swapped.keepsChild step child⟩

/-- Both outer IO errors and typed errors stop before the continuation. -/
def ReportedError (a : F α) (w t : W) : Prop :=
  (∃ e, a.run w = .error e t) ∨ ∃ e, a.run w = .ok (.error e) t

theorem record {a : F α} (h : Returns a w ok fail) :
    Returns a w (fun x t => ok x t ∧ a.run w = .ok (.ok x) t)
      (fun t => fail t ∧ ReportedError a w t) := by
  unfold Returns at *
  cases ran : a.run w with
  | error e t => rw [ran] at h; exact ⟨h, .inl ⟨e, ran⟩⟩
  | ok r t =>
    rw [ran] at h
    cases r with
    | error e => exact ⟨h, .inr ⟨e, ran⟩⟩
    | ok x => exact ⟨h, rfl⟩

theorem ReportedError.not_ok {a : F α} (stop : ReportedError a w t)
    (ok : a.run w = .ok (.ok x) u) : False := by
  rcases stop with ⟨_, eq⟩ | ⟨_, eq⟩ <;> rw [eq] at ok <;> cases ok

/-- The public recovery has consumed the selected manifest and WAL view.
The durable bounds and replay proof make this the actual start of checkTables. -/
def CheckEntry (root : FilePath) (ref : Ref) (image : Selected) (start entered : W) : Prop :=
  let ops := Native.callbackComponents root ref
  ∃ t, ops.manifest.reopen.run start = .ok (.ok image.version) t ∧
    ops.reopenWal.run t = .ok (.ok image.view) entered

def NoChecks (root : FilePath) (ref : Ref) (image : Selected) (start : W) :=
  ¬ ∃ entered, CheckEntry root ref image start entered

/-- Successful and failed checks both retain the actual check-list entry,
its return world, and release of every descriptor acquired along its prefix. -/
def CheckReceipt (root : FilePath) (ref : Ref) (image : Selected) (life : NativeRead.Lifetime)
    (start finish : W) (passed : Bool) : Prop :=
  let action := checkTables (Native.callbackComponents root ref).tables image.version.tables
  ∃ entered, CheckEntry root ref image start entered ∧
    (if passed then action.run entered = .ok (.ok ()) finish else ReportedError action entered finish) ∧
    ∀ id w, NativeRead.CheckReached (root / "tables") image.version.tables entered id w →
      (NativeRead.Call.mk (root / "tables") id .check w).Balanced life

end ExperimentalL0.NativeRecoverAt
