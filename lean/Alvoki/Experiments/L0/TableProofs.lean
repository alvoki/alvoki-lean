import Alvoki.Experiments.L0.TableSchedule
import Alvoki.Experiments.L0.CodecProofs
import Alvoki.Experiments.L0.ComponentContract
import Alvoki.Experiments.SSTable.Proofs.UnifiedNativeEndToEnd

namespace ExperimentalL0
open ImmutableSSTable

/-- The table returned when opening the exact built source has the typed
representation. Both native table callbacks use this very open schedule. -/
theorem withTableSource_built [Monad m] [LawfulMonad m] [MonadExceptOf String m]
    {source : Source m} {id : UInt64}
    (built : Unified.Image Alvoki.CRC32C.extend (tableLayout id)
      (rows.map (Entry.encode keyCodec mutationCodec)) bytes)
    (serves : source.Serves bytes) :
    ∃ table : TypedTable m UInt64 Mutation, table.Represents (· < ·) rows ∧
      ∀ {α} (use : TypedTable m UInt64 Mutation → m α), withTableSource source id use = use table := by
  obtain ⟨table, opened, represents⟩ := built.open_represents serves
  refine ⟨⟨table, keyCodec, mutationCodec⟩, typed_table_from_bytes represents, ?_⟩
  intro α use
  unfold withTableSource
  change Unified.openTableChecked source Alvoki.CRC32C.extend id = pure table at opened
  rw [opened, pure_bind]

/-- Run the owned writer and acquire the published inode. The SSTable
producer supplies checked open and the byte-level representation. -/
theorem table_open_published_inode [DecidableEq inode]
    {ops : OutputOps (Unified.NativeWriteM writer inode) writer}
    {nextRow : Unified.NativeWriteM writer inode (Option Entry)}
    {acquire : System.FilePath → IO.FS.Mode → StorageM σ reader}
    {before written : Unified.NativeWriteState writer inode}
    {dir : System.FilePath} {id : UInt64} {rows : Rows}
    {start acquired : σ} {held : reader} {inodeAt : reader → Option inode}
    (effects : Unified.NativeWriteEffects ops (tablePath dir id) nextRow)
    (input : before.rows = rows.map (Entry.encode keyCodec mutationCodec))
    (built : (Unified.buildFileWith ops Alvoki.CRC32C.extend (tablePath dir id) (tableLayout id)
      nextRow (fun message => message)).run before = .ok count written)
    (opened : acquire (tablePath dir id) .read start = .ok held acquired)
    (selected : ∀ output identity, written.BoundTo (tablePath dir id) output identity →
      inodeAt held = some identity) :
    ∃ table : TypedTable (StorageM σ) UInt64 Mutation,
      Unified.openCheckedWith ((written.readSnapshot inodeAt).primitives acquire)
        Alvoki.CRC32C.extend (tablePath dir id) id start = .ok table.table acquired ∧
      table.Represents (· < ·) rows := by
  obtain ⟨_, table, checked, represents⟩ :=
    Unified.buildFileWith_open_represents effects built opened selected
  rw [input] at represents
  exact ⟨⟨table, keyCodec, mutationCodec⟩, checked, typed_table_from_bytes represents⟩

private theorem lawfulEIO : LawfulMonad (EIO String) := .mk'
  (id_map := fun x => funext fun state => by
    change EST.bind x (fun value => EST.pure (id value)) state = x state
    cases h : x state <;> simp [EST.bind, EST.pure, h])
  (pure_bind := fun _ _ => rfl)
  (bind_assoc := fun x f g => funext fun state => by
    change EST.bind (EST.bind x f) g state = EST.bind x (fun value => EST.bind (f value) g) state
    cases h : x state <;> simp [EST.bind, h])
  (map_const := fun _ _ => rfl)

/-- The descriptor acquired by the native callback is the same descriptor
used for the table's footer, index and row reads. The filesystem premise is
that this specific descriptor serves the durable built bytes. -/
theorem native_table_source_built (handle : IO.FS.Handle) {id : UInt64}
    (built : Unified.Image Alvoki.CRC32C.extend (tableLayout id)
      (rows.map (Entry.encode keyCodec mutationCodec)) bytes)
    (serves : nativeReadPrimitives.ReadsExactly handle bytes) :
    ∃ table : TypedTable (EIO String) UInt64 Mutation, table.Represents (· < ·) rows ∧
      ∀ {α} (use : TypedTable (EIO String) UInt64 Mutation → EIO String α),
        withTableSource (handleSource handle) id use = use table := by
  letI := lawfulEIO
  exact withTableSource_built built (serves.source_serves built.extent)

theorem native_table_check (handle : IO.FS.Handle) {id : UInt64} {rows : Rows}
    (built : Unified.Image Alvoki.CRC32C.extend (tableLayout id)
      (rows.map (Entry.encode keyCodec mutationCodec)) bytes)
    (serves : nativeReadPrimitives.ReadsExactly handle bytes) :
    withTableSource (handleSource handle) id (fun _ => pure ()) = pure () := by
  obtain ⟨_, _, opened⟩ := native_table_source_built handle built serves
  exact opened _

theorem native_table_lookup (handle : IO.FS.Handle) {id : UInt64}
    (built : Unified.Image Alvoki.CRC32C.extend (tableLayout id)
      (rows.map (Entry.encode keyCodec mutationCodec)) bytes)
    (serves : nativeReadPrimitives.ReadsExactly handle bytes) (key : UInt64) :
    withTableSource (handleSource handle) id (·.lookup key) = pure (lookupRows rows key) := by
  obtain ⟨_, represents, opened⟩ := native_table_source_built handle built serves
  rw [opened, typed_lookup_spec represents]

end ExperimentalL0

namespace ExperimentalL0

section Scope

variable {stat : EStateM String σ IO.FS.Metadata}
  {withRead : (handle → EStateM String σ α) → EStateM String σ α}
  {use : handle → EStateM String σ α}

theorem table_descriptor_stat_error (report : stat initial = .error error after) :
    withTableDescriptor stat withRead use initial = .error error after := by
  simp [withTableDescriptor, Bind.bind, EStateM.bind, report]

theorem table_descriptor_rejected (report : stat initial = .ok metadata after)
    (invalid : isTableFile metadata = false) :
    withTableDescriptor stat withRead use initial =
      .error "expected a singly linked regular SSTable" after := by
  simp [withTableDescriptor, Bind.bind, EStateM.bind, report, invalid]
  rfl

/-- The successful stat permits entry to the scoped open. Propagate the
scope's error, whether acquisition or the descriptor action reported it. -/
theorem table_descriptor_open_error (report : stat initial = .ok metadata checked)
    (valid : isTableFile metadata = true)
    (openError : withRead use checked = .error error after) :
    withTableDescriptor stat withRead use initial = .error error after := by
  simp [withTableDescriptor, Bind.bind, EStateM.bind, report, valid, openError]

/-- A successful scoped acquisition runs the actual continuation on the
acquired descriptor. Its result can be success or a table operation error.
The scope premise records that closing drops only the private descriptor,
so it frames the continuation's reported state. -/
theorem table_descriptor_acquired (report : stat initial = .ok metadata checked)
    (valid : isTableFile metadata = true)
    (scope : withRead use checked = use acquired entered) :
    withTableDescriptor stat withRead use initial = use acquired entered := by
  simp [withTableDescriptor, Bind.bind, EStateM.bind, report, valid, scope]

end Scope

/-- After acquiring the actual descriptor, the table check succeeds once
its source supplies the exact healthy builder image. -/
theorem native_table_action_check (handle : IO.FS.Handle) {id : UInt64} {rows : Rows}
    (built : ImmutableSSTable.Unified.Image Alvoki.CRC32C.extend (tableLayout id)
      (rows.map (ImmutableSSTable.Entry.encode keyCodec mutationCodec)) bytes)
    (serves : ImmutableSSTable.nativeReadPrimitives.ReadsExactly handle bytes) :
    nativeTableAction handle id (fun _ => pure ()) = pure () := by
  unfold nativeTableAction
  rw [native_table_check handle built serves]
  rfl


theorem native_table_descriptor_checked {id : UInt64} {rows : Rows}
    {stat : ExceptT String IO IO.FS.Metadata}
    {withRead : (IO.FS.Handle → ExceptT String IO Unit) → ExceptT String IO Unit}
    (report : stat = pure metadata) (valid : isTableFile metadata = true)
    (scope : withRead (fun handle => nativeTableAction handle id (fun _ => pure ())) =
      nativeTableAction acquired id (fun _ => pure ()))
    (built : ImmutableSSTable.Unified.Image Alvoki.CRC32C.extend (tableLayout id)
      (rows.map (ImmutableSSTable.Entry.encode keyCodec mutationCodec)) bytes)
    (serves : ImmutableSSTable.nativeReadPrimitives.ReadsExactly acquired bytes) :
    withTableDescriptor stat withRead (fun handle => nativeTableAction handle id (fun _ => pure ())) =
      pure () := by
  unfold withTableDescriptor
  rw [report]
  change (if isTableFile metadata then
    withRead (fun handle => nativeTableAction handle id (fun _ => pure ()))
    else throw "expected a singly linked regular SSTable") = pure ()
  simp only [valid, ite_eq_left, scope, native_table_action_check acquired built serves]

end ExperimentalL0
