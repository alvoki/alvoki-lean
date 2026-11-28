import Alvoki.Experiments.L0.NativeFacts
import Alvoki.Experiments.L0.Refinement
import Alvoki.Experiments.L0.ManifestComposition
import Alvoki.Experiments.L0.TableAllocationProofs
import Alvoki.Experiments.L0.DurableCatalog

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
    | .ok _ after | .error _ after => (selected s).TableFrame (selected after)
  writerCall : ∀ s id rows after, build id rows s = .ok () after →
    ∃ initial reached count,
      initial.rows = rows.map (Entry.encode keyCodec mutationCodec) ∧
      (buildFileWith output Alvoki.CRC32C.extend (tablePath ns.directory id) (tableLayout id)
        supplier (fun message => message)).run initial = .ok count reached ∧
      ∀ handle identity bytes, reached.BoundTo (tablePath ns.directory id) handle identity →
        reached.durable = some (identity, bytes) → synced after id = some (identity, bytes)
  syncEffect : ∀ s, match syncDirectory s with
    | .ok _ after => (selected s).TableFrame (selected after) ∧
        ∀ id rows identity bytes, synced s id = some (identity, bytes) →
          Image Alvoki.CRC32C.extend (tableLayout id)
            (rows.map (Entry.encode keyCodec mutationCodec)) bytes →
          (selected after).tables id = some rows ∧
            ns.names after (tablePath ns.directory id) = some identity ∧
            ns.contents after identity = some bytes
    | .error _ after => (selected s).TableFrame (selected after)

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

/-- The writer and barrier establish the newly allocated binding. The
allocation frame accounts for the previously published names and excludes
unpublished orphans from the logical catalog. -/
theorem TableCreationEvidence.catalogAfter {create : Rows → StorageM σ UInt64}
    (e : TableCreationEvidence create selected ns)
    (prior : ns.Represents s (selected s).tables)
    (ran : create rows s = .ok tableId after)
    (keeps : ns.Keeps s after (selected s).tables)
    (catalog : (selected after).tables =
      fun key => if key = tableId then some rows else (selected s).tables key) :
    ns.Represents after (selected after).tables := by
  rw [catalog]
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
    | error error reached => simpa [ran] using frame
    | ok value after =>
      cases value
      rw [ran] at frame
      exact ⟨frame, e.syncedImage ran⟩
  · intro before
    have effect := e.syncEffect before
    cases ran : e.syncDirectory before with
    | error error reached => simpa [ran] using effect
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
  scan : ∀ s, match ops.scan s with
    | .ok view after => WalScanReceipt (selected s).view view ∧ selected after = selected s
    | .error _ after => selected after = selected s
  reopenWal : ∀ s, match ops.reopenWal s with
    | .ok view after => WalOpenReceipt (selected s).view view ∧ selected after = selected s
    | .error _ after => selected after = selected s
  manifest : Nonempty (ManifestComposition.Interpretation ops.manifest selected)
  append : ∀ s batch, match ops.append batch s with
    | .ok _ after => WalReceipt (selected s).view (selected after).view batch ∧
        (selected after).version = (selected s).version ∧ (selected after).tables = (selected s).tables
    | .error _ after => selected after = selected s ∨
        (RecoveryChoices.Retry (.offline (selected s).view (some (.append batch)))
          (.ready (selected s).version) (.online (selected after).view) (.ready (selected after).version) ∧
          (selected after).tables = (selected s).tables)
  create : Nonempty (TableCreationEvidence ops.tables.create selected namespaceState)
  check : ∀ s id, match ops.tables.check id s with
    | .ok _ after | .error _ after => selected after = selected s
  lookup : ∀ s id key rows, (selected s).tables id = some rows →
    match ops.tables.lookup id key s with
    | .ok result after => selected after = selected s ∧
        namespaceState.Keeps s after (selected s).tables ∧
        ∃ (handle : IO.FS.Handle) (inodeAt : IO.FS.Handle → Option namespaceState.inode),
          inodeAt handle = namespaceState.names s (tablePath namespaceState.directory id) ∧
          (∀ identity bytes, inodeAt handle = some identity →
            namespaceState.contents s identity = some bytes →
            nativeReadPrimitives.ReadsExactly handle bytes) ∧
          withTableSource (handleSource handle) id (·.lookup key) = pure result
    | .error _ after => selected after = selected s

private theorem selected_eq {a b : Selected}
    (view : a.view = b.view) (version : a.version = b.version) (tables : a.tables = b.tables) :
    a = b := by cases a; cases b; simp_all

theorem CallbackEvidence.lookupFromCatalog {ops : Components (StorageM σ)}
    (evidence : CallbackEvidence ops selected ns)
    (catalog : ns.Represents s (selected s).tables)
    (tableId key : UInt64) (bound : (selected s).tables tableId = some rows) :
    match ops.tables.lookup tableId key s with
    | .ok result after => result = lookupRows rows key ∧ selected after = selected s ∧
        ns.Represents after (selected after).tables
    | .error _ after => selected after = selected s := by
    have read := evidence.lookup s tableId key rows bound
    cases ran : ops.tables.lookup tableId key s with
    | ok value after =>
      rw [ran] at read
      obtain ⟨frame, keeps, handle, inodeAt, picked, primitives, returned⟩ := read
      have expected := TableNamespace.lookup (catalog tableId rows bound) handle
        inodeAt picked primitives key
      obtain ⟨world⟩ := (inferInstance : Nonempty (Void IO.RealWorld))
      have equal := returned.symm.trans expected
      exact ⟨EST.Out.ok.inj (congrFun equal world) |>.1, frame, frame.symm ▸ catalog.frame keeps⟩
    | error error after => simpa [ran] using read

theorem CallbackEvidence.effects (evidence : CallbackEvidence ops selected namespaceState) :
    ComponentEffects ops selected where
  scan s := by
    have read := evidence.scan s
    cases ran : ops.scan s with
    | ok value after =>
      rw [ran] at read
      exact ⟨read.1.effect, read.2⟩
    | error error after => simpa [ran] using read
  reopenWal s := by
    have read := evidence.reopenWal s
    cases ran : ops.reopenWal s with
    | ok value after =>
      rw [ran] at read
      exact ⟨read.1.effect, read.2⟩
    | error error after => simpa [ran] using read
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
  check := evidence.check

theorem CallbackEvidence.get {ops : Components (StorageM σ)}
    (evidence : CallbackEvidence ops selected ns)
    (catalog : ns.Represents s (selected s).tables)
    (prior : Installed session (selected s) history) (key : UInt64) :
    match get ops session key s with
    | .ok value after => value = denote history key ∧ selected after = selected s
    | .error _ after => selected after = selected s :=
  get_refines_from (fun s => ns.Represents s (selected s).tables)
    (fun _ id key _ ready binding => evidence.lookupFromCatalog ready id key binding)
    s catalog session prior key

end ExperimentalL0.NativeBridge
