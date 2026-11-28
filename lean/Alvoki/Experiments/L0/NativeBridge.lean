import Alvoki.Experiments.L0.NativeFacts
import Alvoki.Experiments.L0.WalRecovery
import Alvoki.Experiments.L0.Refinement
import Alvoki.Experiments.L0.ManifestComposition
import Alvoki.Experiments.L0.TableAllocationProofs
import Alvoki.Experiments.L0.NativeTableReads

namespace ExperimentalL0.NativeBridge
open WalRecoverySlice.Segmented
open ImmutableSSTable Unified

/-- Records the actual before and returned WAL sessions for a successful
native append at the boundary of the segmented effects model. -/
inductive WalReceipt (before after : Contract.View) (batch : Contract.Batch) : Prop where
  | issued
      (prior : Run events (.online priorSession state))
      (completed : (requestCall effects priorSession (.append batch)).run state =
        .ok (.ok nextSession) reached)
      (old : priorSession.view = before) (new : nextSession.view = after) :
      WalReceipt before after batch

theorem WalReceipt.effect (receipt : WalReceipt before after batch) :
    after = before.append batch := by
  cases receipt with
  | issued prior completed old new =>
    rw [← old, ← new]
    exact wal_append prior completed

/-- Primitive effects on table names and the synced build artifact. The
directory barrier turns that artifact into a durable catalog binding. -/
structure TableCreationEvidence (create : Rows → StorageM σ UInt64)
    (selected : σ → Selected) (ns : TableNamespace σ) where
  names : σ → UInt64 → Bool
  writer : Type
  synced : σ → UInt64 → Option (ns.inode × ByteArray)
  output : OutputOps (NativeWriteM writer ns.inode) writer
  supplier : NativeWriteM writer ns.inode (Option Entry)
  primitiveEffects : ∀ id, NativeWriteEffects output (tablePath ns.directory id) supplier
  occupied : UInt64 → StorageM σ Bool
  build : UInt64 → Rows → StorageM σ Unit
  syncDirectory : StorageM σ Unit
  schedule : create = createTableAt occupied build syncDirectory
  absent : ∀ s id, names s id = false → (selected s).tables id = none
  probe : ∀ s id, match occupied id s with
    | .ok result after => result = names s id ∧ (names after, selected after) = (names s, selected s)
    | .error _ after => (names after, selected after) = (names s, selected s)
  buildFrame : ∀ s id rows, match build id rows s with
    | .ok _ after | .error _ after => selected after = selected s
  writerCall : ∀ s id rows after, build id rows s = .ok () after →
    ∃ initial reached count,
      initial.rows = rows.map (Entry.encode keyCodec mutationCodec) ∧
      (buildFileWith output Alvoki.CRC32C.extend (tablePath ns.directory id) (tableLayout id)
        supplier (fun message => message)).run initial = .ok count reached ∧
      ∀ handle identity bytes, reached.BoundTo (tablePath ns.directory id) handle identity →
        reached.durable = some (identity, bytes) → synced after id = some (identity, bytes)
  syncAddsOnly : ∀ s id rows written after, build id rows s = .ok () written →
    syncDirectory written = .ok () after → ∀ key, key ≠ id →
      (selected after).tables key = (selected written).tables key
  syncEffect : ∀ s, match syncDirectory s with
    | .ok _ after => (selected s).TableFrame (selected after) ∧
        ∀ id rows identity bytes, synced s id = some (identity, bytes) →
          Image Alvoki.CRC32C.extend (tableLayout id)
            (rows.map (Entry.encode keyCodec mutationCodec)) bytes →
          (selected after).tables id = some rows ∧
            ns.names after (tablePath ns.directory id) = some identity ∧
            ns.contents after identity = some bytes
    | .error _ after => selected after = selected s

private theorem TableCreationEvidence.syncedImage {create : Rows → StorageM σ UInt64}
    (e : TableCreationEvidence create selected ns)
    (ran : e.build tableId rows s = .ok () after) :
    ∃ identity bytes, e.synced after tableId = some (identity, bytes) ∧
      Image Alvoki.CRC32C.extend (tableLayout tableId)
        (rows.map (Entry.encode keyCodec mutationCodec)) bytes := by
  obtain ⟨initial, reached, count, input, run, installed⟩ := e.writerCall _ _ _ _ ran
  obtain ⟨_, _, image, handle, identity, bound, _, durable, _⟩ :=
    buildFileWith_refines (e.primitiveEffects tableId) run
  exact ⟨identity, reached.appended, installed handle identity reached.appended bound durable,
    input ▸ image⟩

theorem TableCreationEvidence.published {create : Rows → StorageM σ UInt64} (e : TableCreationEvidence create selected ns)
    (ran : create rows s = .ok tableId after) :
    ns.Bound after tableId rows := by
  rw [e.schedule] at ran
  obtain ⟨_, written, _, built, barrier⟩ := createTableAt_success ran
  obtain ⟨identity, bytes, synced, image⟩ := e.syncedImage built
  have published := e.syncEffect written
  rw [barrier] at published
  exact ⟨identity, bytes, (published.2 _ _ _ _ synced image).2.1,
    (published.2 _ _ _ _ synced image).2.2, image⟩

/-- Only the reserved table becomes visible in the logical catalog.
The probe frames the catalog and the build leaves visibility to the barrier. -/
theorem TableCreationEvidence.catalogInserted {create : Rows → StorageM σ UInt64}
    (e : TableCreationEvidence create selected ns)
    (ran : create rows s = .ok tableId after) :
    (selected after).tables = fun key =>
      if key = tableId then some rows else (selected s).tables key := by
  rw [e.schedule] at ran
  obtain ⟨reserved, written, allocation, built, barrier⟩ := createTableAt_success ran
  have probe := freeTableId_spec e.occupied (fun state => (e.names state, selected state)) (·.1)
    e.probe 0 s
  rw [allocation] at probe
  have unchanged : selected reserved = selected s := congrArg Prod.snd probe.2
  obtain ⟨identity, bytes, synced, image⟩ := e.syncedImage built
  have published := e.syncEffect written
  rw [barrier] at published
  funext key
  by_cases same : key = tableId
  · subst key
    simpa only [ite_true] using (published.2 _ _ _ _ synced image).1
  · simp only [same, ite_false]
    have builtFrame := e.buildFrame reserved tableId rows
    rw [built] at builtFrame
    rw [e.syncAddsOnly _ _ _ _ _ built barrier key same, builtFrame, unchanged]

/-- A failed create may leave an orphan. It does not install a new logical binding. -/
theorem TableCreationEvidence.failureCatalog {create : Rows → StorageM σ UInt64}
    (e : TableCreationEvidence create selected ns)
    (ran : create rows s = .error error after) :
    selected after = selected s := by
  rw [e.schedule] at ran
  have probe := freeTableId_spec e.occupied (fun state => (e.names state, selected state)) (·.1)
    e.probe 0 s
  cases allocated : freeTableId e.occupied 0 s with
  | error message reached =>
    rw [allocated] at probe
    simp [createTableAt, Bind.bind, EStateM.bind, allocated] at ran
    exact ran.2 ▸ congrArg Prod.snd probe
  | ok tableId reserved =>
    rw [allocated] at probe
    have reservation : selected reserved = selected s := congrArg Prod.snd probe.2
    have builtFrame := e.buildFrame reserved tableId rows
    cases built : e.build tableId rows reserved with
    | error message reached =>
      rw [built] at builtFrame
      simp [createTableAt, Bind.bind, EStateM.bind, allocated, built] at ran
      exact ran.2 ▸ builtFrame.trans reservation
    | ok value written =>
      rw [built] at builtFrame
      have synced := e.syncEffect written
      cases barrier : e.syncDirectory written with
      | error message reached =>
        rw [barrier] at synced
        simp [createTableAt, Bind.bind, EStateM.bind, allocated, built, barrier] at ran
        exact ran.2 ▸ synced.trans (builtFrame.trans reservation)
      | ok returned reached =>
        simp [createTableAt, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure,
          allocated, built, barrier] at ran

/-- The writer and barrier establish the newly allocated binding. The
allocation frame accounts for the previously published names and excludes
unpublished orphans from the logical catalog. -/
theorem TableCreationEvidence.catalogAfter {create : Rows → StorageM σ UInt64}
    (e : TableCreationEvidence create selected ns)
    (prior : ns.Represents s (selected s).tables)
    (ran : create rows s = .ok tableId after)
    (keeps : ns.Keeps s after (selected s).tables) :
    ns.Represents after (selected after).tables := by
  rw [e.catalogInserted ran]
  exact prior.insert keeps (e.published ran)

theorem TableCreationEvidence.effect {create : Rows → StorageM σ UInt64} (e : TableCreationEvidence create selected ns) (rows : Rows) (s : σ) :
    match create rows s with
    | .ok id after => (selected after).view = (selected s).view ∧
        (selected after).version = (selected s).version ∧
        (selected s).tables.Created (selected after).tables id rows
    | .error _ after => (selected s).TableFrame (selected after) := by
  rw [e.schedule]
  let prepared (state : σ) (id : UInt64) (rows : Rows) :=
    ∃ identity bytes, e.synced state id = some (identity, bytes) ∧
      Image Alvoki.CRC32C.extend (tableLayout id)
        (rows.map (Entry.encode keyCodec mutationCodec)) bytes
  apply createTableAt_bindings selected e.names prepared e.occupied e.build e.syncDirectory
    e.absent e.probe _ _ rows s
  · intro before id input
    have frame := e.buildFrame before id input
    cases ran : e.build id input before with
    | error error reached =>
      rw [ran] at frame
      simp [Selected.TableFrame, Catalog.Preserves, frame]
    | ok value after =>
      cases value
      rw [ran] at frame
      exact ⟨by simp [Selected.TableFrame, Catalog.Preserves, frame], e.syncedImage ran⟩
  · intro before
    have effect := e.syncEffect before
    cases ran : e.syncDirectory before with
    | error error reached =>
      rw [ran] at effect
      simp [Selected.TableFrame, Catalog.Preserves, effect]
    | ok value after =>
      rw [ran] at effect
      refine ⟨effect.1, ?_⟩
      intro id rows witnessed
      obtain ⟨identity, bytes, synced, image⟩ := witnessed
      exact (effect.2 id rows identity bytes synced image).1

/-- Local evidence for reached callbacks. Manifest effects are derived from the shared schedule and primitive
reports. WAL effects are obtained from component traces. Table creation carries the
namespace durability and isolation conditions; a read carries the exact
built image served by its descriptor. State indices identify the reached
phase. Relating the reported callbacks to native IO remains a premise. -/
structure CallbackEvidence (ops : Components (StorageM σ)) (selected : σ → Selected)
    (namespaceState : TableNamespace σ) : Prop where
  walRecovery : Nonempty (WalRecovery.Interpretation ops selected)
  manifest : Nonempty (ManifestComposition.Interpretation ops.manifest selected)
  append : ∀ s batch, match ops.append batch s with
    | .ok _ after => WalReceipt (selected s).view (selected after).view batch ∧
        (selected after).version = (selected s).version ∧ (selected after).tables = (selected s).tables
    | .error _ after => selected after = selected s ∨
        (RecoveryChoices.Retry (.offline (selected s).view (some (.append batch)))
          (.ready (selected s).version) (.online (selected after).view) (.ready (selected after).version) ∧
          (selected after).tables = (selected s).tables)
  create : Nonempty (TableCreationEvidence ops.tables.create selected namespaceState)
  reads : Nonempty (NativeTableReads.Interpretation ops.tables selected namespaceState)

private theorem selected_eq {a b : Selected}
    (view : a.view = b.view) (version : a.version = b.version) (tables : a.tables = b.tables) :
    a = b := by cases a; cases b; simp_all

theorem CallbackEvidence.effects (evidence : CallbackEvidence ops selected namespaceState) :
    ComponentEffects ops selected where
  scan s := by
    obtain ⟨wal⟩ := evidence.walRecovery
    exact wal.scanEffect s
  reopenWal s := by
    obtain ⟨wal⟩ := evidence.walRecovery
    exact wal.reopenEffect s
  reopenManifest s := by
    obtain ⟨manifest⟩ := evidence.manifest
    exact manifest.reopenEffect s
  append s batch := by
    have receipt := evidence.append s batch
    cases ran : ops.append batch s with
    | ok value after =>
      rw [ran] at receipt
      exact selected_eq receipt.1.effect receipt.2.1 receipt.2.2
    | error error after =>
      rw [ran] at receipt
      rcases receipt with same | ⟨retry, tables⟩
      · exact Or.inl same
      · obtain ⟨old | new, version⟩ := retry.afterAppend
        · exact Or.inl (selected_eq old version tables)
        · exact Or.inr (selected_eq new version tables)
  create s rows _ := by
    obtain ⟨creation⟩ := evidence.create
    have made := creation.effect rows s
    cases ran : ops.tables.create rows s <;> simpa [ran, Selected.TableFrame] using made
  publish s proposal valid := by
    obtain ⟨manifest⟩ := evidence.manifest
    exact manifest.publishEffect s proposal valid
  check s id := by
    obtain ⟨reads⟩ := evidence.reads
    exact reads.checkEffect s id

/-- WAL mutation uses the supplied namespace frames on the reached scan
and append calls, including when either call reports an error. -/
theorem CallbackEvidence.writeCatalog {ops : Components (StorageM σ)}
    (evidence : CallbackEvidence ops selected ns)
    (prior : ns.Represents s (selected s).tables)
    (scan : ∀ s, match ops.scan s with
      | .ok _ after | .error _ after => ns.Keeps s after (selected s).tables)
    (append : ∀ s batch, match ops.append batch s with
      | .ok _ after | .error _ after => ns.Keeps s after (selected s).tables)
    (session : Session) (change : Change) :
    match write ops session change s with
    | .ok _ after | .error _ after => ns.Represents after (selected after).tables := by
  have scanLogical := evidence.effects.scan s
  have scanPhysical := scan s
  cases scanned : ops.scan s with
  | error error after =>
    rw [scanned] at scanLogical scanPhysical
    simpa [write, Bind.bind, EStateM.bind, scanned, scanLogical] using prior.frame scanPhysical
  | ok view middle =>
    rw [scanned] at scanLogical scanPhysical
    have ready : ns.Represents middle (selected middle).tables :=
      scanLogical.2.symm ▸ prior.frame scanPhysical
    by_cases fits : view.tail + 1 < UInt64.size
    · have logical := evidence.effects.append middle (encode change)
      have physical := append middle (encode change)
      cases sent : ops.append (encode change) middle with
      | ok value after =>
        rw [sent] at logical physical
        simpa [write, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure, scanned, fits,
          sent, logical, Selected.append] using ready.frame physical
      | error error after =>
        rw [sent] at logical physical
        rcases logical with old | new
        · simpa [write, Bind.bind, EStateM.bind, scanned, fits, sent, old] using ready.frame physical
        · simpa [write, Bind.bind, EStateM.bind, scanned, fits, sent, new, Selected.append]
            using ready.frame physical
    · simp only [write, Bind.bind, EStateM.bind, scanned, fits, ite_false]
      exact ready

/-- The normal flush schedule carries the exact durable catalog through
scan, creation and manifest publication. Failed creation leaves only
physical orphans. A publication error keeps the already installed table. -/
theorem CallbackEvidence.flushCatalog {ops : Components (StorageM σ)}
    (evidence : CallbackEvidence ops selected ns)
    (prior : ns.Represents s (selected s).tables)
    (scan : ∀ s, match ops.scan s with
      | .ok _ after | .error _ after => ns.Keeps s after (selected s).tables)
    (create : ∀ s rows, match ops.tables.create rows s with
      | .ok _ after | .error _ after => ns.Keeps s after (selected s).tables)
    (publish : ∀ s version, match ops.manifest.publish version s with
      | .ok _ after | .error _ after =>
        (selected after).tables = (selected s).tables ∧ ns.Keeps s after (selected s).tables)
    (session : Session) :
    match flush ops session s with
    | .ok _ after | .error _ after => ns.Represents after (selected after).tables := by
  by_cases empty : session.mem.isEmpty = true
  · simpa [flush, empty, Pure.pure, EStateM.pure] using prior
  have scanLogical := evidence.effects.scan s
  have scanPhysical := scan s
  cases scanned : ops.scan s with
  | error error after =>
    rw [scanned] at scanLogical scanPhysical
    simpa [flush, empty, Bind.bind, EStateM.bind, scanned, scanLogical] using prior.frame scanPhysical
  | ok view middle =>
    rw [scanned] at scanLogical scanPhysical
    have ready : ns.Represents middle (selected middle).tables :=
      scanLogical.2.symm ▸ prior.frame scanPhysical
    by_cases fits : view.tail < UInt64.size
    · obtain ⟨producer⟩ := evidence.create
      have physical := create middle session.mem.toList
      cases built : ops.tables.create session.mem.toList middle with
      | error error after =>
        rw [built] at physical
        have unchanged := producer.failureCatalog built
        simpa [flush, empty, Bind.bind, EStateM.bind, scanned, fits, built, unchanged]
          using ready.frame physical
      | ok tableId stored =>
        rw [built] at physical
        have installed := producer.catalogAfter ready built physical
        let version : L0Manifest.Version := ⟨tableId :: session.version.tables, view.tail.toUInt64⟩
        have kept := publish stored version
        cases sent : ops.manifest.publish version stored with
        | ok value after =>
          rw [sent] at kept
          dsimp [version] at sent
          simpa [flush, empty, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure, scanned, fits,
            built, sent, kept.1] using installed.frame kept.2
        | error error after =>
          rw [sent] at kept
          dsimp [version] at sent
          simpa [flush, empty, Bind.bind, EStateM.bind, scanned, fits, built,
            sent, kept.1] using installed.frame kept.2
    · simp [flush, empty, Bind.bind, EStateM.bind, scanned, fits]
      exact ready

end ExperimentalL0.NativeBridge
