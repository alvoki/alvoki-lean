import Alvoki.Experiments.L0.NativeRecoverBase
import Alvoki.Experiments.WAL.Segmented.Proofs.ChildAuthority

namespace ExperimentalL0.NativeRecoverAt

open System Lifecycle Alvoki.NativePost
open NativeRead (Footprint tableNamespace)
open WalRecoverySlice.Segmented (PermittedView)

variable {inode : Type} {physical : W → Footprint inode} {root : FilePath}
  {lock : IO.FS.Handle} {ref : Ref} {image : Selected}
  {req : Option WalRecoverySlice.Segmented.Contract.Request}
  {hist : WalRecoverySlice.Segmented.Contract.View → Rows}

abbrev selectedAt (image : Selected) (v : WalRecoverySlice.Segmented.Contract.View) : Selected :=
  {image with view := v}

def Early (physical : W → Footprint inode) (root : FilePath) (lock : IO.FS.Handle) (ref : Ref)
    (image : Selected) (req : Option WalRecoverySlice.Segmented.Contract.Request) (t : W) : Prop :=
  Opening physical root lock ref image t req ∧ (physical t).manifest.active = L0Manifest.encode image.version

open WalRecoverySlice.Segmented.Native (OpenIO LocalOpenIO)

/-- Interpretation of the child heap projection at the particular originally
registered WAL handle. An empty slot supplies no ownership. -/
def ChildCache (physical : W → Footprint inode) (root : FilePath) (lock : IO.FS.Handle) (ref : Ref)
    (ops : OpenIO heap (root / "wal") (fun w => (physical w).disk) known Q req) : Prop :=
  ∀ w, NativeRead.Owned (physical w) root lock ref → ∀ h reg,
    (physical w).readyWal h = some reg → NativeRead.Original root h reg → ∀ bs,
    (physical w).walChild reg bs ↔ ∃ path : reg.store.root = ops.acquire.canonical,
      (ops.worker reg.store path).children.owns reg.session.control.policy reg.session.control.active reg.child bs w

open WalRecoverySlice.SingleFile (appendBindings)
open WalRecoverySlice.Persistence (historyCursor)
open WalRecoverySlice.Segmented (segmentHistory sessionOf ReadyLayout)
open WalRecoverySlice.Segmented.Native (segmentPath)
open WalRecoverySlice.Segmented.Native.AppendIO (ChildAuthority)

/-- Recover the exact append authority from the registered slot at a later
owned world. Its writer, marker descriptors, policy and cursor all come from
the selected worker's child. -/
theorem ChildCache.authority
    {ops : LocalOpenIO heap (root / "wal") (fun w => (physical w).disk) known Q req}
    (cache : ChildCache physical root lock ref ops.toOpenIO)
    (owned : NativeRead.Owned (physical w) root lock ref) (slot : (physical w).readyWal h = some reg)
    (origin : NativeRead.Original root h reg) (installed : NativeRead.InstalledChild physical reg w) :
    ∃ path : reg.store.root = ops.acquire.canonical, ∃ hist,
      reg.session = sessionOf reg.session.control hist ∧ ReadyLayout reg.session.control hist (physical w).disk ∧
      ∃ a : ChildAuthority (ops.worker reg.store path).children.memory
          (segmentPath reg.store.root reg.session.control.active) reg.session.control.active reg.session.control.policy reg.child,
        let bs := segmentHistory reg.session.control.capacity reg.session.control.active hist
        a.Live w (.active .lock (appendBindings reg.session.control.policy) (historyCursor bs) bs) := by
  obtain ⟨hist, eq, child, layout, _, _⟩ := installed
  obtain ⟨path, held⟩ := (cache w owned h reg slot origin _).mp child
  exact ⟨path, hist, eq, layout, ChildAuthority.opened held layout.active⟩

/-- The registered active child fixes the observed view at its actual return.
Before this point every reported error leaves the original pending disk. -/
theorem reopenWal_selected (ready : ManifestReady physical root lock ref image start req)
    (heap : WalRecoverySlice.Segmented.Native.PhaseMemory) (cache : Cached heap physical root lock ref)
    (walIO : WalRecoverySlice.Segmented.Native.OpenIO heap (root / "wal") (fun w => (physical w).disk)
      image.view (Held physical root lock ref image .opening) req)
    (childCache : ChildCache physical root lock ref walIO)
    (phase : PhasePrimitives physical root lock ref image)
    (scanPrim : ∀ view wal w, PermittedView image.view req view →
      Attached physical root lock ref (selectedAt image view) wal w →
      ScanPrimitives physical root wal image.tables w) :
    Returns (Native.callbackComponents root ref).reopenWal start
      (fun v t => PermittedView image.view req v ∧ ∃ wal, Attached physical root lock ref (selectedAt image v) wal t)
      (Early physical root lock ref image req) := by
  apply NativeRecovery.reopenWal (Native.componentCell ref) _ (Native.storageCallbacks root).openWal
    (Native.storageCallbacks root).scan (readOpening phase ready)
    (acquired := fun wal t => ∃ v, PermittedView image.view req v ∧
      Held physical root lock ref (selectedAt image v) .opening t ∧ Child physical root (selectedAt image v) wal t)
    (attached := fun wal t => ∃ v, PermittedView image.view req v ∧ Attached physical root lock ref (selectedAt image v) wal t)
  · rintro u ⟨held, disk⟩
    apply (Returns.liftIO (WalRecoverySlice.Segmented.Native.openExisting_registered_selected walIO ⟨disk, held⟩)).mapPost
    · rintro wal t ⟨reg, source, cached, locks, ⟨path, custody⟩, choice, frame⟩
      have slot := (cache t frame.owned wal reg).mpr cached
      have original : NativeRead.Original root wal reg := ⟨⟨u, t, source⟩, locks⟩
      obtain ⟨hist, eq, owned, layout, live, durable⟩ := custody
      exact ⟨reg.session.view, choice, ⟨frame.owned, frame.phaseEq, frame.catalog, frame.manifest⟩, reg, slot, original,
        ⟨hist, eq, (childCache t frame.owned wal reg slot original _).mpr ⟨path, owned⟩, layout, live, durable⟩, rfl⟩
    · rintro t ⟨retry, held⟩
      exact ⟨⟨held.owned, held.phaseEq, held.catalog, retry⟩, held.manifest.1⟩
  · rintro wal w ⟨v, choice, held, child⟩
    apply (attach (image := selectedAt image v) (failed := fun _ => False) ⟨phase.read, phase.swap⟩ held child).mapPost
    · exact fun _ _ x => ⟨v, choice, x⟩
    · exact fun _ => False.elim
  · rintro wal w ⟨v, choice, held⟩
    apply (Returns.liftIO (scanned (failed := fun _ => False) heap cache held (scanPrim v wal w choice held))).mapPost
    · rintro out t ⟨rfl, held⟩
      exact ⟨choice, wal, held⟩
    · exact fun _ => False.elim

/-- Recovery selects a WAL outcome before checking any SSTable. A check
failure retains that specific child for cleanup; a manifest or WAL-acquisition
failure retains the pending history for retry. -/
theorem recoverAt_selected_checks
    (durable : ∀ v, PermittedView image.view req v → Durable (selectedAt image v) (hist v))
    (opening : Opening physical root lock ref image start req)
    (bytes : (physical start).manifest.active = L0Manifest.encode image.version)
    (manifestPrim : NativeManifest.Primitives (root / "manifest")
      (ManifestFrame physical root image.tables start) (fun w => (physical w).manifest))
    (heap : WalRecoverySlice.Segmented.Native.PhaseMemory) (cache : Cached heap physical root lock ref)
    (walIO : WalRecoverySlice.Segmented.Native.OpenIO heap (root / "wal") (fun w => (physical w).disk)
      image.view (Held physical root lock ref image .opening) req)
    (childCache : ChildCache physical root lock ref walIO)
    (phase : PhasePrimitives physical root lock ref image)
    (scanPrim : ∀ view wal w, PermittedView image.view req view →
      Attached physical root lock ref (selectedAt image view) wal w →
      ScanPrimitives physical root wal image.tables w)
    (tablePrim : ∀ view wal w, PermittedView image.view req view →
      Attached physical root lock ref (selectedAt image view) wal w →
      NativeRead.Primitives (tableNamespace physical root) life (NativeRead.Frame physical root wal image.tables w)) :
    NativeScope.Post (Native.recoverAt root ref) start
      (fun session t => ∃ v, PermittedView image.view req v ∧ Installed session (selectedAt image v) (hist v) ∧
        (∃ wal, Attached physical root lock ref (selectedAt image v) wal t) ∧
        CheckReceipt root ref (selectedAt image v) life start t true)
      (fun _ t => (Early physical root lock ref image req t ∧ ∀ v, NoChecks root ref (selectedAt image v) start) ∨
        ∃ v, PermittedView image.view req v ∧ (∃ wal, Attached physical root lock ref (selectedAt image v) wal t) ∧
          CheckReceipt root ref (selectedAt image v) life start t false) := by
  let ops := Native.callbackComponents root ref
  apply checked
  unfold ExperimentalL0.recover
  apply (record (manifestOpening (image := image) (durable image.view (.inl rfl)) opening bytes manifestPrim)).mapPost (fun _ _ x => x) ?_ |>.bind
  · rintro version w ⟨⟨rfl, ready⟩, manifestRan⟩
    apply (record (reopenWal_selected ready heap cache walIO childCache phase scanPrim)).mapPost (fun _ _ x => x) ?_ |>.bind
    · rintro view t ⟨⟨choice, wal, attached⟩, walRan⟩
      have d := durable view choice
      have entry : CheckEntry root ref (selectedAt image view) start t := ⟨w, manifestRan, walRan⟩
      have prim := tablePrim view wal t choice attached
      have released (id u) (visit : NativeRead.CheckReached (root / "tables") image.version.tables t id u) :=
        NativeRead.checkTables_balanced prim d (fun _ step => attached.1.catalog.frame step.tablesKept)
          NativeRead.Frame.refl visit
      have bounds := d.bounds
      have replay := d.replay_pending
      dsimp only [selectedAt] at bounds replay
      simp only [bounds, and_self, ite_true, replay]
      apply (record (tables d attached prim)).mapPost (fun _ _ x => x) ?_ |>.bind
      · rintro _ u ⟨after, passed⟩
        exact ⟨view, choice, ⟨d, rfl, rfl⟩, ⟨wal, after⟩, t, entry, passed, released⟩
      · rintro u ⟨after, stopped⟩
        exact .inr ⟨view, choice, ⟨wal, after⟩, t, entry, stopped, released⟩
    · rintro u ⟨early, stopped⟩
      refine .inl ⟨early, ?_⟩
      rintro v ⟨_, origin, earlier, ok⟩
      have same : origin = w := (EST.Out.ok.inj (earlier.symm.trans manifestRan)).2
      subst origin
      exact stopped.not_ok ok
  · rintro u ⟨early, stopped⟩
    exact .inl ⟨early, fun _ ⟨_, _, ran, _⟩ => stopped.not_ok ran⟩

theorem recoverAt_selected
    (durable : ∀ v, PermittedView image.view req v → Durable (selectedAt image v) (hist v))
    (opening : Opening physical root lock ref image start req)
    (bytes : (physical start).manifest.active = L0Manifest.encode image.version)
    (manifestPrim : NativeManifest.Primitives (root / "manifest")
      (ManifestFrame physical root image.tables start) (fun w => (physical w).manifest))
    (heap : WalRecoverySlice.Segmented.Native.PhaseMemory) (cache : Cached heap physical root lock ref)
    (walIO : WalRecoverySlice.Segmented.Native.OpenIO heap (root / "wal") (fun w => (physical w).disk)
      image.view (Held physical root lock ref image .opening) req)
    (childCache : ChildCache physical root lock ref walIO)
    (phase : PhasePrimitives physical root lock ref image)
    (scanPrim : ∀ view wal w, PermittedView image.view req view →
      Attached physical root lock ref (selectedAt image view) wal w →
      ScanPrimitives physical root wal image.tables w)
    (tablePrim : ∀ view wal w, PermittedView image.view req view →
      Attached physical root lock ref (selectedAt image view) wal w →
      NativeRead.Primitives (tableNamespace physical root) life (NativeRead.Frame physical root wal image.tables w)) :
    NativeScope.Post (Native.recoverAt root ref) start
      (fun session t => ∃ v, PermittedView image.view req v ∧ Installed session (selectedAt image v) (hist v) ∧
        ∃ wal, Attached physical root lock ref (selectedAt image v) wal t)
      (fun _ t => Early physical root lock ref image req t ∨ ∃ v, PermittedView image.view req v ∧
        ∃ wal, Attached physical root lock ref (selectedAt image v) wal t) :=
  (recoverAt_selected_checks durable opening bytes manifestPrim heap cache walIO childCache phase scanPrim tablePrim).weaken
    (fun _ _ ⟨v, permit, installed, held, _⟩ => ⟨v, permit, installed, held⟩)
    (fun _ _ stop => stop.elim (fun early => .inl early.1) (fun ⟨v, permit, held, _⟩ => .inr ⟨v, permit, held⟩))

end ExperimentalL0.NativeRecoverAt
