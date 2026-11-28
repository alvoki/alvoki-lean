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
  disk : WalRecoverySlice.Segmented.Writebacks (physical s).disk (physical t).disk
  tablesKept : (tableNamespace physical root).Keeps s t tables

theorem ManifestFrame.refl : ManifestFrame physical root tables w w :=
  ⟨rfl, rfl, rfl, .nil, fun _ _ _ _ _ a b => ⟨a, b⟩⟩

theorem Opening.frame (start : Opening physical root lock ref image s)
    (step : ManifestFrame physical root image.tables s t) :
    Opening physical root lock ref image t := by
  refine ⟨⟨step.lock.trans start.owned.1, step.ref.trans start.owned.2⟩,
    step.phase.trans start.phase, start.catalog.frame step.tablesKept, ?_⟩
  exact WalRecoverySlice.Segmented.Writebacks.recoverable step.disk start.disk

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
  (Opening physical root lock ref image w ∧ (physical w).manifest.active = L0Manifest.encode image.version) ∨
    ∃ wal, Attached physical root lock ref image wal w

theorem Held.frame (held : Held physical root lock ref image phase s)
    (step : NativeRead.Frame physical root wal image.tables s t) :
    Held physical root lock ref image phase t :=
  ⟨⟨step.lock.trans held.owned.1, step.ref.trans held.owned.2⟩,
    step.phase.trans held.phaseEq, held.catalog.frame step.tablesKept,
    ⟨step.manifest.trans held.manifest.1, step.survivors.trans held.manifest.2⟩⟩

theorem Child.frame (held : Child physical image wal s)
    (step : NativeRead.Frame physical root wal image.tables s t) : Child physical image wal t := by
  obtain ⟨c, cached, installed, view⟩ := held
  exact ⟨c, step.child.trans cached, WalRecoverySlice.Segmented.Writebacks.installed step.disk installed, view⟩

theorem manifest (d : Durable image history) (opening : Opening physical root lock ref image start)
    (bytes : (physical start).manifest.active = L0Manifest.encode image.version)
    (prim : NativeManifest.Primitives (root / "manifest")
      (ManifestFrame physical root image.tables start) (fun w => (physical w).manifest)) :
    Returns (Native.callbackComponents root ref).manifest.reopen start
      (fun v t => v = image.version ∧ ManifestReady physical root lock ref image t)
      (Failed physical root lock ref image) := by
  have result := NativeManifest.reopen prim ManifestFrame.refl bytes d.unique
  change Returns (NativeManifest.backend (root / "manifest")).reopen _ _ _
  have retry {t} (same : (physical t).manifest = (physical start).manifest ∨
      (physical t).manifest = (physical start).manifest.barrier) :
      (physical t).manifest.active = L0Manifest.encode image.version := by
    rcases same with h | h <;> simpa only [h, DurableBlob.Image.barrier] using bytes
  unfold Returns
  cases ran : (NativeManifest.backend (root / "manifest")).reopen.run start with
  | error _ t => rw [ran] at result; exact .inl ⟨opening.frame result.1, retry result.2⟩
  | ok v t =>
    rw [ran] at result
    cases v with
    | error _ => exact .inl ⟨opening.frame result.1, retry result.2⟩
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
    (before : Child physical image wal s) : Child physical image wal t := by
  obtain ⟨c, cached, valid, view⟩ := before
  exact ⟨c, step.child.trans cached, WalRecoverySlice.Segmented.Writebacks.installed step.disk valid, view⟩

theorem Attached.sessionAt (attached : Attached physical root lock ref image wal w)
    (installed : Installed session image history) :
    NativeRead.SessionAt physical root lock ref wal session image history w (.recovering wal) :=
  ⟨attached.1.owned, attached.1.phaseEq, attached.2, attached.1.manifest, attached.1.catalog, installed⟩

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

/-- Read and swap semantics are restricted to the particular phase reference
under the root's verified ownership, including either primitive's reached footprint. -/
structure PhasePrimitives (physical : W → Footprint inode) (root : FilePath)
    (lock : IO.FS.Handle) (ref : Ref) (image : Selected) : Prop where
  read : ∀ w, Owned (physical w) root lock ref → ∃ t,
    (ref.get : IO (Phase Wal)) w = .ok (physical w).phase t ∧
    ManifestFrame physical root image.tables w t ∧ (physical t).manifest = (physical w).manifest ∧
    ∀ wal, (physical w).phase.wal = some wal → (physical t).readyWal wal = (physical w).readyWal wal
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
  exact ⟨t, ran, frame.lock, frame.ref, frame.phase, child wal attached, frame.disk,
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

private theorem readOpening (prim : PhasePrimitives physical root lock ref image)
    (ready : ManifestReady physical root lock ref image w) :
    Returns (Native.componentCell ref).read w
      (fun phase t => phase = .opening ∧ ManifestReady physical root lock ref image t) failed := by
  obtain ⟨t, ran, frame, same, _⟩ := prim.read w ready.1.owned
  apply Returns.liftIO
  unfold IOReturns
  rw [ran]
  have before : Opening physical root lock ref image w :=
    ⟨ready.1.owned, ready.1.phaseEq, ready.1.catalog, ready.2⟩
  have after := before.frame frame
  exact ⟨ready.1.phaseEq, ⟨after.owned, after.phase, after.catalog, same ▸ ready.1.manifest⟩, after.disk⟩

private theorem attach (prim : PhasePrimitives physical root lock ref image)
    (held : Held physical root lock ref image .opening w) (child : Child physical image wal w) :
    Returns ((Native.componentCell ref).swap (.recovering wal)) w
      (fun _ t => Attached physical root lock ref image wal t) failed := by
  obtain ⟨t, ran, step⟩ := prim.swap w held.owned wal (.recovering wal)
  apply Returns.liftIO
  unfold IOReturns
  rw [ran]
  exact ⟨Swapped.held step held, Swapped.keepsChild step child⟩

/-- Applied to the segmented disk producer at its concrete recovery entry.
The failure branch retains the same root/phase and a recoverable disk. -/
def OpenDiskPost (heap : WalRecoverySlice.Segmented.Native.PhaseMemory)
    (physical : W → Footprint inode) (root : FilePath) (lock : IO.FS.Handle)
    (ref : Ref) (image : Selected) (w : W) : Prop :=
  IOReturns (WalRecoverySlice.Segmented.Native.openExisting (root / "wal")) w
    (fun h t => ∃ c, heap.Ready h c t ∧ WalRecoverySlice.Segmented.Installed c (physical t).disk ∧
      c.view = image.view ∧ Held physical root lock ref image .opening t)
    (fun t => WalRecoverySlice.Segmented.Recoverable image.view none (physical t).disk ∧
      Held physical root lock ref image .opening t)

/-- Assemble the concrete native callbacks. The private WAL handle returned
by open is installed before scan and carried through every table check.
A failure before that swap keeps opening custody; a later failure records
the very handle that cleanup must take. -/
theorem recoverAt_of_open (d : Durable image history)
    (opening : Opening physical root lock ref image start)
    (bytes : (physical start).manifest.active = L0Manifest.encode image.version)
    (manifestPrim : NativeManifest.Primitives (root / "manifest")
      (ManifestFrame physical root image.tables start) (fun w => (physical w).manifest))
    (heap : WalRecoverySlice.Segmented.Native.PhaseMemory) (cache : Cached heap physical root lock ref)
    (openDisk : ∀ w, ManifestReady physical root lock ref image w →
      OpenDiskPost heap physical root lock ref image w)
    (phase : PhasePrimitives physical root lock ref image)
    (scanPrim : ∀ wal w, Attached physical root lock ref image wal w →
      ScanPrimitives physical root wal image.tables w)
    (tablePrim : ∀ wal w, Attached physical root lock ref image wal w →
      NativeRead.Primitives (tableNamespace physical root) life (NativeRead.Frame physical root wal image.tables w)) :
    NativeScope.Post (Native.recoverAt root ref) start
      (fun session t => Installed session image history ∧ ∃ wal, Attached physical root lock ref image wal t)
      (fun _ t => Failed physical root lock ref image t) := by
  apply checked
  apply NativeRecovery.recover (Native.callbackComponents root ref) image d (manifest d opening bytes manifestPrim)
  · intro w ready
    apply NativeRecovery.reopenWal (Native.componentCell ref) _ (Native.storageCallbacks root).openWal
      (Native.storageCallbacks root).scan (readOpening phase ready)
      (acquired := fun h t => Held physical root lock ref image .opening t ∧ Child physical image h t)
      (attached := Attached physical root lock ref image)
    · intro t can
      apply (Returns.liftIO (openDisk t can)).mapPost
      · rintro wal u ⟨c, readyWal, disk, view, held⟩
        exact ⟨held, c, (cache u held.owned wal c).mpr readyWal, disk, view⟩
      · rintro u ⟨disk, held⟩
        exact .inl ⟨⟨held.owned, held.phaseEq, held.catalog, disk⟩, held.manifest.1⟩
    · intro wal t acquired
      exact attach phase acquired.1 acquired.2
    · intro wal t attached
      apply (Returns.liftIO (scanned heap cache attached (scanPrim wal t attached))).mapPost
      · rintro v u ⟨view, after⟩
        exact ⟨view, wal, after⟩
      · exact fun _ impossible => False.elim impossible
  · rintro w ⟨wal, attached⟩
    apply (tables d attached (tablePrim wal w attached)).mapPost
    · exact fun _ _ after => ⟨wal, after⟩
    · exact fun _ after => .inr ⟨wal, after⟩

/-- A native recovery started on the selected files produces the replayed
session and the still-attached physical child that the outer phase publish
uses. The WAL producer supplies its actual CONTROL read, root barrier,
child access and retired-file collection under the acquired store. -/
theorem recoverAt (d : Durable image history)
    (opening : Opening physical root lock ref image start)
    (bytes : (physical start).manifest.active = L0Manifest.encode image.version)
    (manifestPrim : NativeManifest.Primitives (root / "manifest")
      (ManifestFrame physical root image.tables start) (fun w => (physical w).manifest))
    (heap : WalRecoverySlice.Segmented.Native.PhaseMemory) (cache : Cached heap physical root lock ref)
    (walIO : WalRecoverySlice.Segmented.Native.OpenIO heap (root / "wal") (fun w => (physical w).disk)
      image.view (Held physical root lock ref image .opening))
    (phase : PhasePrimitives physical root lock ref image)
    (scanPrim : ∀ wal w, Attached physical root lock ref image wal w →
      ScanPrimitives physical root wal image.tables w)
    (tablePrim : ∀ wal w, Attached physical root lock ref image wal w →
      NativeRead.Primitives (tableNamespace physical root) life (NativeRead.Frame physical root wal image.tables w)) :
    NativeScope.Post (Native.recoverAt root ref) start
      (fun session t => Installed session image history ∧ ∃ wal, Attached physical root lock ref image wal t)
      (fun _ t => Failed physical root lock ref image t) :=
  recoverAt_of_open d opening bytes manifestPrim heap cache
    (fun _ ⟨held, disk⟩ => WalRecoverySlice.Segmented.Native.openExisting_diskPost walIO ⟨disk, held⟩)
    phase scanPrim tablePrim

/-- The first failed manifest stat is propagated with its exact error and
world. Neither WAL acquisition nor any table check runs on this branch. -/
theorem recoverAt_manifestStatError (root : FilePath) (ref : Ref)
    (failed : (root / "manifest" / "BLOB").metadata w = .error e t) :
    Native.recoverAt root ref w = .error e t := by
  have file : IO.FS.readBinFile (root / "manifest" / "BLOB") w = .error e t := by
    simp only [IO.FS.readBinFile, Bind.bind, instMonadEIO._aux_13, EST.bind, failed]
  have blob : (DurableBlob.native (root / "manifest")).reopen w = .error e t := by
    rw [DurableBlob.native_reopen_schedule]
    simp only [Bind.bind, instMonadEIO._aux_13, EST.bind, file]
  have manifest : (Native.callbackComponents root ref).manifest.reopen.run w = .error e t := by
    change (NativeManifest.backend _).reopen.run w = _
    rw [NativeManifest.decodeReached, blob]
  unfold Native.recoverAt Native.checked ExperimentalL0.recover
  rw [ExceptT.run_bind]
  simp only [Bind.bind, instMonadEIO._aux_13, EST.bind, manifest]

/-- A manifest error after the concrete root lock was granted skips the
callback. The owned fresh reference contains no child and cleanup unlocks
the root; the manifest exception stays primary even if unlock reports one. -/
theorem withOpen_manifestStatError (path root : FilePath) (use : Native.Handle → IO α)
    (resolved : Native.validatedRoot path start = .ok root t)
    (opened : IO.FS.Handle.mk (root / "l0.lock") .append t = .ok lock u)
    (held : lock.tryLock true u = .ok true v)
    (failed : (root / "manifest" / "BLOB").metadata
      (IO.mkRef (.opening : Phase Wal) v).state = .error e reached)
    (old : let ref := (IO.mkRef (.opening : Phase Wal) v).val
      ((ref.swap .offline : BaseIO (Phase Wal)) reached).val = .opening) :
    let ref := (IO.mkRef (.opening : Phase Wal) v).val
    let after := ((ref.swap .offline : BaseIO (Phase Wal)) reached).state
    Native.withOpen path use start = .error e (lock.unlock.toBaseIO after).state := by
  have result := NativeScope.withOpen_recoveryError path root use resolved opened held
    (recoverAt_manifestStatError root _ failed)
  dsimp only at old result ⊢
  rw [old] at result
  exact result

end ExperimentalL0.NativeRecoverAt
