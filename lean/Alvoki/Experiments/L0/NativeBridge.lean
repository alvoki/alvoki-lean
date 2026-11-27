import Alvoki.Experiments.L0.NativeFacts
import Alvoki.Experiments.L0.ManifestComposition
import Alvoki.Experiments.L0.TableAllocationProofs
import Alvoki.Experiments.L0.TableProofs

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

/-- The actual read descriptor serves the durable image from the same table
binding. The image comes from the shared builder on the logical rows. -/
structure TableSource (id : UInt64) (file : Option ByteArray) (rows : Rows) (handle : IO.FS.Handle) : Prop where
  image : ∃ bytes, file = some bytes ∧
    ImmutableSSTable.Unified.Image Alvoki.CRC32C.extend (tableLayout id)
      (rows.map (ImmutableSSTable.Entry.encode keyCodec mutationCodec)) bytes ∧
    ImmutableSSTable.nativeReadPrimitives.ReadsExactly handle bytes

/-- Produce the check result and its witness using the same ID and handle.
Stat and descriptor acquisition are premises about the reached path. -/
theorem tableOpenAt {dir : System.FilePath} {id : UInt64}
    {stat : System.FilePath → ExceptT String IO IO.FS.Metadata}
    {withRead : System.FilePath → (IO.FS.Handle → ExceptT String IO Unit) → ExceptT String IO Unit}
    (report : stat (tablePath dir id) = pure metadata) (valid : isTableFile metadata = true)
    (scope : withRead (tablePath dir id) (fun handle => nativeTableAction handle id (fun _ => pure ())) =
      nativeTableAction acquired id (fun _ => pure ()))
    (names : System.FilePath → Option inode) (contents : inode → Option ByteArray)
    (inodeAt : IO.FS.Handle → Option inode)
    (binding : names (tablePath dir id) = some identity)
    (persisted : contents identity = some bytes)
    (selected : inodeAt acquired = names (tablePath dir id))
    (built : ImmutableSSTable.Unified.Image Alvoki.CRC32C.extend (tableLayout id)
      (rows.map (ImmutableSSTable.Entry.encode keyCodec mutationCodec)) bytes)
    (readEffects : ∀ file image, inodeAt acquired = some file → contents file = some image →
      ImmutableSSTable.nativeReadPrimitives.ReadsExactly acquired image) :
    withTableAt stat withRead dir id (fun handle => nativeTableAction handle id (fun _ => pure ())) =
      pure () ∧ TableSource id ((names (tablePath dir id)).bind contents) rows acquired := by
  have serves := readEffects identity bytes (selected.trans binding) persisted
  exact ⟨native_table_descriptor_checked report valid scope built serves,
    ⟨bytes, by simp [binding, persisted], built, serves⟩⟩

/-- A healthy lookup records the result of the very same open/read
schedule used by the native adapter. -/
inductive TableRead (id : UInt64) (file : Option ByteArray) (rows : Rows) (key : UInt64) (result : Option Mutation) : Prop where
  | read (source : TableSource id file rows handle)
      (returned : withTableSource (ImmutableSSTable.handleSource handle) id (·.lookup key) = pure result) :
      TableRead id file rows key result

theorem TableRead.effect {id : UInt64} (receipt : TableRead id file rows key result) : result = lookupRows rows key := by
  cases receipt with
  | @read handle source returned =>
    obtain ⟨_, _, built, serves⟩ := source.image
    have equal := returned.symm.trans (native_table_lookup handle built serves key)
    obtain ⟨world⟩ := (inferInstance : Nonempty (Void IO.RealWorld))
    exact EST.Out.ok.inj (congrFun equal world) |>.1

/-- Primitive effects on table names and the synced build artifact. The
directory barrier turns that artifact into a durable catalog binding. -/
structure TableCreationEvidence (create : Rows → StorageM σ UInt64)
    (selected : σ → Selected) where
  names : σ → UInt64 → Bool
  directory : System.FilePath
  inode : Type
  writer : Type
  synced : σ → UInt64 → Option (inode × ByteArray)
  output : OutputOps (NativeWriteM writer inode) writer
  supplier : NativeWriteM writer inode (Option Entry)
  primitiveEffects : ∀ id, NativeWriteEffects output (tablePath directory id) supplier
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
      (buildFileWith output Alvoki.CRC32C.extend (tablePath directory id) (tableLayout id)
        supplier (fun message => message)).run initial = .ok count reached ∧
      ∀ handle identity bytes, reached.BoundTo (tablePath directory id) handle identity →
        reached.durable = some (identity, bytes) → synced after id = some (identity, bytes)
  syncEffect : ∀ s, match syncDirectory s with
    | .ok _ after => (selected s).TableFrame (selected after) ∧
        ∀ id rows identity bytes, synced s id = some (identity, bytes) →
          Image Alvoki.CRC32C.extend (tableLayout id)
            (rows.map (Entry.encode keyCodec mutationCodec)) bytes →
          (selected after).tables id = some rows
    | .error _ after => (selected s).TableFrame (selected after)

theorem TableCreationEvidence.effect {create : Rows → StorageM σ UInt64} (e : TableCreationEvidence create selected) (rows : Rows) (s : σ) :
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
      obtain ⟨initial, reached, count, exactInput, built, installed⟩ :=
        e.writerCall before id input after ran
      obtain ⟨_, _, image, handle, identity, bound, _, durable, _⟩ :=
        buildFileWith_refines (e.primitiveEffects id) built
      exact ⟨frame, identity, reached.appended, installed handle identity reached.appended bound durable,
        exactInput ▸ image⟩
  · intro before
    have effect := e.syncEffect before
    cases ran : e.syncDirectory before with
    | error error reached => simpa [ran] using effect
    | ok value after =>
      rw [ran] at effect
      refine ⟨effect.1, ?_⟩
      intro id rows witnessed
      obtain ⟨identity, bytes, synced, image⟩ := witnessed
      exact effect.2 id rows identity bytes synced image

/-- Local evidence for reached callbacks. Manifest effects are derived from the shared schedule and primitive
reports. WAL effects are obtained from component traces. Table creation carries the
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
  manifest : Nonempty (ManifestComposition.Interpretation ops.manifest selected)
  append : ∀ s batch, match ops.append batch s with
    | .ok _ after => WalReceipt (selected s).view (selected after).view batch ∧
        (selected after).version = (selected s).version ∧ (selected after).tables = (selected s).tables
    | .error _ after => selected after = selected s ∨
        (RecoveryChoices.Retry (.offline (selected s).view (some (.append batch)))
          (.ready (selected s).version) (.online (selected after).view) (.ready (selected after).version) ∧
          (selected after).tables = (selected s).tables)
  create : Nonempty (TableCreationEvidence ops.tables.create selected)
  check : ∀ s id, match ops.tables.check id s with
    | .ok _ after | .error _ after => selected after = selected s
  lookup : ∀ s id key rows, (selected s).tables id = some rows →
    match ops.tables.lookup id key s with
    | .ok result after => TableRead id (fileBytes s id) rows key result ∧ selected after = selected s
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
  lookup s id key rows bound := by
    have read := evidence.lookup s id key rows bound
    cases ran : ops.tables.lookup id key s with
    | ok value after =>
      rw [ran] at read
      exact ⟨read.1.effect, read.2⟩
    | error error after => simpa [ran] using read

end ExperimentalL0.NativeBridge
