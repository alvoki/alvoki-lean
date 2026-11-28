import Alvoki.Experiments.L0.NativeRecoverBase

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

/-- The registered active child fixes the observed view at its actual return.
Before this point every reported error leaves the original pending disk. -/
theorem reopenWal_selected (ready : ManifestReady physical root lock ref image start req)
    (heap : WalRecoverySlice.Segmented.Native.PhaseMemory) (cache : Cached heap physical root lock ref)
    (walIO : WalRecoverySlice.Segmented.Native.OpenIO heap (root / "wal") (fun w => (physical w).disk)
      image.view (Held physical root lock ref image .opening) req)
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
    · rintro wal t ⟨reg, source, cached, locks, ⟨_, custody⟩, choice, frame⟩
      exact ⟨reg.session.view, choice, ⟨frame.owned, frame.phaseEq, frame.catalog, frame.manifest⟩, reg, (cache t frame.owned wal reg).mpr cached,
        ⟨⟨u, t, source⟩, locks⟩, custody.installed, rfl⟩
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
    apply (record (reopenWal_selected ready heap cache walIO phase scanPrim)).mapPost (fun _ _ x => x) ?_ |>.bind
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
  (recoverAt_selected_checks durable opening bytes manifestPrim heap cache walIO phase scanPrim tablePrim).weaken
    (fun _ _ ⟨v, permit, installed, held, _⟩ => ⟨v, permit, installed, held⟩)
    (fun _ _ stop => stop.elim (fun early => .inl early.1) (fun ⟨v, permit, held, _⟩ => .inr ⟨v, permit, held⟩))

end ExperimentalL0.NativeRecoverAt
