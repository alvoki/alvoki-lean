import Alvoki.Experiments.L0.TableSchedule
import Alvoki.Experiments.L0.CodecProofs
import Alvoki.Experiments.SSTable.Proofs.Reader
import Alvoki.Experiments.SSTable.Native

namespace ExperimentalL0
open ImmutableSSTable

/-- The table returned when opening the exact built source has the typed
representation. Both native table callbacks use this very open schedule. -/
theorem withTableSource_built [Monad m] [LawfulMonad m] [MonadExceptOf String m]
    {source : Source m}
    (built : modelBuild (rows.map (Entry.encode keyCodec mutationCodec)) = .ok (count, bytes))
    (serves : source.Serves bytes) :
    ∃ table : TypedTable m UInt64 Mutation, table.Represents (· < ·) rows ∧
      ∀ {α} (use : TypedTable m UInt64 Mutation → m α), withTableSource source use = use table := by
  obtain ⟨table, opened, represents⟩ := open_built_table built serves
  refine ⟨⟨table, keyCodec, mutationCodec⟩, typed_table_from_bytes represents, ?_⟩
  intro α use
  unfold withTableSource
  rw [opened, pure_bind]

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
theorem native_table_source_built (handle : IO.FS.Handle)
    (built : modelBuild (rows.map (Entry.encode keyCodec mutationCodec)) = .ok (count, bytes))
    (serves : (handleSource handle).Serves bytes) :
    ∃ table : TypedTable (EIO String) UInt64 Mutation, table.Represents (· < ·) rows ∧
      ∀ {α} (use : TypedTable (EIO String) UInt64 Mutation → EIO String α),
        withTableSource (handleSource handle) use = use table := by
  letI := lawfulEIO
  exact withTableSource_built built serves

theorem table_source_lookup [Monad m] [LawfulMonad m] [MonadExceptOf String m]
    {source : Source m}
    (built : modelBuild (rows.map (Entry.encode keyCodec mutationCodec)) = .ok (count, bytes))
    (serves : source.Serves bytes) (key : UInt64) :
    withTableSource source (·.lookup key) = pure (lookupRows rows key) := by
  obtain ⟨table, represents, openTable⟩ := withTableSource_built built serves
  rw [openTable, typed_lookup_spec represents]

theorem table_source_check [Monad m] [LawfulMonad m] [MonadExceptOf String m]
    {source : Source m} {rows : Rows}
    (built : modelBuild (rows.map (Entry.encode keyCodec mutationCodec)) = .ok (count, bytes))
    (serves : source.Serves bytes) :
    withTableSource source (fun _ => pure ()) = pure () := by
  obtain ⟨_, _, openTable⟩ := withTableSource_built built serves
  exact openTable _

theorem native_table_check (handle : IO.FS.Handle) {rows : Rows}
    (built : modelBuild (rows.map (Entry.encode keyCodec mutationCodec)) = .ok (count, bytes))
    (serves : (handleSource handle).Serves bytes) :
    withTableSource (handleSource handle) (fun _ => pure ()) = pure () := by
  obtain ⟨_, _, opened⟩ := native_table_source_built handle built serves
  exact opened _

theorem native_table_lookup (handle : IO.FS.Handle)
    (built : modelBuild (rows.map (Entry.encode keyCodec mutationCodec)) = .ok (count, bytes))
    (serves : (handleSource handle).Serves bytes) (key : UInt64) :
    withTableSource (handleSource handle) (·.lookup key) = pure (lookupRows rows key) := by
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
theorem native_table_action_check (handle : IO.FS.Handle) {rows : Rows}
    (built : ImmutableSSTable.modelBuild
      (rows.map (ImmutableSSTable.Entry.encode keyCodec mutationCodec)) = .ok (count, bytes))
    (serves : (ImmutableSSTable.handleSource handle).Serves bytes) :
    nativeTableAction handle (fun _ => pure ()) = pure () := by
  unfold nativeTableAction
  rw [native_table_check handle built serves]
  rfl


theorem native_table_descriptor_checked {rows : Rows}
    {stat : ExceptT String IO IO.FS.Metadata}
    {withRead : (IO.FS.Handle → ExceptT String IO Unit) → ExceptT String IO Unit}
    (report : stat = pure metadata) (valid : isTableFile metadata = true)
    (scope : withRead (fun handle => nativeTableAction handle (fun _ => pure ())) =
      nativeTableAction acquired (fun _ => pure ()))
    (built : ImmutableSSTable.modelBuild
      (rows.map (ImmutableSSTable.Entry.encode keyCodec mutationCodec)) = .ok (count, bytes))
    (serves : (ImmutableSSTable.handleSource acquired).Serves bytes) :
    withTableDescriptor stat withRead (fun handle => nativeTableAction handle (fun _ => pure ())) =
      pure () := by
  unfold withTableDescriptor
  rw [report]
  change (if isTableFile metadata then
    withRead (fun handle => nativeTableAction handle (fun _ => pure ()))
    else throw "expected a singly linked regular SSTable") = pure ()
  simp only [valid, ite_eq_left, scope, native_table_action_check acquired built serves]

end ExperimentalL0
