import Alvoki.Experiments.L0.NativeFacts
import Alvoki.Experiments.L0.ManifestComposition
import Alvoki.Experiments.L0.TableAllocationProofs
import Alvoki.Experiments.L0.TableProofs

namespace ExperimentalL0.NativeBridge
open WalRecoverySlice.Segmented

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

/-- The actual read descriptor serves the durable image from the same table
binding. The image comes from the shared builder on the logical rows. -/
structure TableSource (file : Option ByteArray) (rows : Rows) (handle : IO.FS.Handle) : Prop where
  image : ∃ count bytes, file = some bytes ∧ ImmutableSSTable.modelBuild
    (rows.map (ImmutableSSTable.Entry.encode keyCodec mutationCodec)) = .ok (count, bytes) ∧
    (ImmutableSSTable.handleSource handle).Serves bytes

/-- A healthy acquired source is sufficient to derive the typed open. -/
def TableOpen (file : Option ByteArray) (rows : Rows) : Prop :=
  ∃ handle, TableSource file rows handle

/-- Produce the check result and its witness using the same ID and handle.
Stat and descriptor acquisition are premises about the reached path. -/
theorem tableOpenAt {dir : System.FilePath} {id : UInt64}
    {stat : System.FilePath → ExceptT String IO IO.FS.Metadata}
    {withRead : System.FilePath → (IO.FS.Handle → ExceptT String IO Unit) → ExceptT String IO Unit}
    (report : stat (tablePath dir id) = pure metadata) (valid : isTableFile metadata = true)
    (scope : withRead (tablePath dir id) (fun handle => nativeTableAction handle (fun _ => pure ())) =
      nativeTableAction acquired (fun _ => pure ()))
    (files : System.FilePath → Option ByteArray)
    (binding : files (tablePath dir id) = some bytes)
    (built : ImmutableSSTable.modelBuild
      (rows.map (ImmutableSSTable.Entry.encode keyCodec mutationCodec)) = .ok (count, bytes))
    (serves : (ImmutableSSTable.handleSource acquired).Serves bytes) :
    withTableAt stat withRead dir id (fun handle => nativeTableAction handle (fun _ => pure ())) =
      pure () ∧ TableOpen (files (tablePath dir id)) rows :=
  ⟨native_table_descriptor_checked report valid scope built serves,
    acquired, ⟨count, bytes, binding, built, serves⟩⟩

theorem TableOpen.represents (receipt : TableOpen file rows) :
    ∃ (handle : IO.FS.Handle) (table : ImmutableSSTable.TypedTable (EIO String) UInt64 Mutation),
      table.Represents (· < ·) rows ∧
      withTableSource (ImmutableSSTable.handleSource handle) (fun opened => pure opened) = pure table := by
  obtain ⟨handle, source⟩ := receipt
  obtain ⟨_, _, _, built, serves⟩ := source.image
  obtain ⟨table, represents, opened⟩ := native_table_source_built handle built serves
  exact ⟨handle, table, represents, opened _⟩

/-- A healthy lookup records the result of the very same open/read
schedule used by the native adapter. -/
inductive TableRead (file : Option ByteArray) (rows : Rows) (key : UInt64) (result : Option Mutation) : Prop where
  | read (source : TableSource file rows handle)
      (returned : withTableSource (ImmutableSSTable.handleSource handle) (·.lookup key) = pure result) :
      TableRead file rows key result

theorem TableRead.effect (receipt : TableRead file rows key result) : result = lookupRows rows key := by
  cases receipt with
  | @read handle source returned =>
    obtain ⟨_, _, _, built, serves⟩ := source.image
    have equal := returned.symm.trans (native_table_lookup handle built serves key)
    obtain ⟨world⟩ := (inferInstance : Nonempty (Void IO.RealWorld))
    exact EST.Out.ok.inj (congrFun equal world) |>.1

/-- Primitive effects on table names and the synced build artifact. The
directory barrier turns that artifact into a durable catalog binding. -/
structure TableCreationEvidence (create : Rows → StorageM σ UInt64)
    (selected : σ → Selected) where
  names : σ → UInt64 → Bool
  prepared : σ → UInt64 → Rows → Prop
  occupied : UInt64 → StorageM σ Bool
  build : UInt64 → Rows → StorageM σ Unit
  syncDirectory : StorageM σ Unit
  schedule : create = createTableAt occupied build syncDirectory
  absent : ∀ s id, names s id = false → (selected s).tables id = none
  probe : ∀ s id, match occupied id s with
    | .ok result after => result = names s id ∧ (names after, selected after) = (names s, selected s)
    | .error _ after => (names after, selected after) = (names s, selected s)
  buildEffect : ∀ s id rows, match build id rows s with
    | .ok _ after => (selected s).TableFrame (selected after) ∧ prepared after id rows
    | .error _ after => (selected s).TableFrame (selected after)
  syncEffect : ∀ s, match syncDirectory s with
    | .ok _ after => (selected s).TableFrame (selected after) ∧
        ∀ id rows, prepared s id rows → (selected after).tables id = some rows
    | .error _ after => (selected s).TableFrame (selected after)

theorem TableCreationEvidence.effect {create : Rows → StorageM σ UInt64} (e : TableCreationEvidence create selected) (rows : Rows) (s : σ) :
    match create rows s with
    | .ok id after => (selected after).view = (selected s).view ∧
        (selected after).version = (selected s).version ∧
        (selected s).tables.Created (selected after).tables id rows
    | .error _ after => (selected s).TableFrame (selected after) := by
  rw [e.schedule]
  exact createTableAt_bindings selected e.names e.prepared e.occupied e.build e.syncDirectory
    e.absent e.probe e.buildEffect e.syncEffect rows s

/-- Local evidence for reached callbacks. WAL and manifest mutation effects
are obtained by eliminating component traces. Table creation carries the
namespace durability and isolation conditions; a read carries the exact
built image served by its descriptor. State indices identify the reached
phase. Relating the reported callbacks to native IO remains a premise. -/
structure CallbackEvidence (ops : Components (StorageM σ)) (selected : σ → Selected)
    (fileBytes : σ → UInt64 → Option ByteArray) : Prop where
  scan : ∀ s, match ops.scan s with
    | .ok view after => WalScanReceipt (selected s).view view ∧ selected after = selected s
    | .error _ after => selected after = selected s
  reopenWal : ∀ s, match ops.reopenWal s with
    | .ok view after => WalOpenReceipt (selected s).view view ∧ selected after = selected s
    | .error _ after => selected after = selected s
  reopenManifest : ∀ s, match ops.manifest.reopen s with
    | .ok version after => version = (selected s).version ∧ selected after = selected s
    | .error _ after => selected after = selected s
  append : ∀ s batch, match ops.append batch s with
    | .ok _ after => WalReceipt (selected s).view (selected after).view batch ∧
        (selected after).version = (selected s).version ∧ (selected after).tables = (selected s).tables
    | .error _ after => selected after = selected s ∨
        (RecoveryChoices.Retry (.offline (selected s).view (some (.append batch)))
          (.ready (selected s).version) (.online (selected after).view) (.ready (selected after).version) ∧
          (selected after).tables = (selected s).tables)
  create : Nonempty (TableCreationEvidence ops.tables.create selected)
  publish : ∀ s proposal, proposal.Valid → match ops.manifest.publish proposal s with
    | .ok _ after => (selected after).version = proposal ∧
        (selected after).view = (selected s).view ∧ (selected after).tables = (selected s).tables
    | .error _ after => selected after = selected s ∨
        (RecoveryChoices.Retry (.online (selected s).view)
          (.offline (selected s).version (some proposal)) (.online (selected after).view)
          (.ready (selected after).version) ∧ (selected after).tables = (selected s).tables)
  check : ∀ s id, match ops.tables.check id s with
    | .ok _ after => (∃ rows, (selected s).tables id = some rows ∧ TableOpen (fileBytes s id) rows) ∧
        selected after = selected s
    | .error _ after => selected after = selected s
  lookup : ∀ s id key rows, (selected s).tables id = some rows →
    match ops.tables.lookup id key s with
    | .ok result after => TableRead (fileBytes s id) rows key result ∧ selected after = selected s
    | .error _ after => selected after = selected s

private theorem selected_eq {a b : Selected}
    (view : a.view = b.view) (version : a.version = b.version) (tables : a.tables = b.tables) :
    a = b := by cases a; cases b; simp_all

theorem CallbackEvidence.laws (evidence : CallbackEvidence ops selected fileBytes) :
    ComponentLaws ops selected where
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
  reopenManifest := evidence.reopenManifest
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
    have receipt := evidence.publish s proposal valid
    cases ran : ops.manifest.publish proposal s with
    | ok value after =>
      rw [ran] at receipt
      exact selected_eq receipt.2.1 receipt.1 receipt.2.2
    | error error after =>
      rw [ran] at receipt
      rcases receipt with same | ⟨retry, tables⟩
      · exact Or.inl same
      · obtain ⟨view, old | new⟩ := retry.afterPublish
        · exact Or.inl (selected_eq view old tables)
        · exact Or.inr (selected_eq view new tables)
  check s id := by
    have read := evidence.check s id
    cases ran : ops.tables.check id s with
    | ok value after =>
      rw [ran] at read
      exact read.2
    | error error after => simpa [ran] using read
  lookup s id key rows bound := by
    have read := evidence.lookup s id key rows bound
    cases ran : ops.tables.lookup id key s with
    | ok value after =>
      rw [ran] at read
      exact ⟨read.1.effect, read.2⟩
    | error error after => simpa [ran] using read

end ExperimentalL0.NativeBridge
