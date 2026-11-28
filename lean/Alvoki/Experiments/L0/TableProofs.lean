import Alvoki.Experiments.L0.TableSchedule
import Alvoki.Experiments.L0.CodecProofs
import Alvoki.Experiments.L0.ComponentContract
import Alvoki.Experiments.SSTable.Proofs.UnifiedNativeEndToEnd
import Alvoki.Experiments.SSTable.Proofs.UnifiedReadSafety

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

theorem lawfulEIO : LawfulMonad (EIO String) := .mk'
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

/-- The actual typed lookup needs correct bytes only on successful
primitive calls. A different request is allowed to report an error. -/
theorem table_lookup_success {source : Source (EIO String)} {id : UInt64}
    (built : Unified.Image Alvoki.CRC32C.extend (tableLayout id)
      (rows.map (Entry.encode keyCodec mutationCodec)) bytes)
    (safe : Unified.ReadSafety source bytes) (key : UInt64)
    (ran : withTableSource source id (·.lookup key) start = .ok value after) :
    value = lookupRows rows key := by
  letI := lawfulEIO
  have nativeRun : (do
      let handle ← Unified.openChecked source Alvoki.CRC32C.extend id
      (TypedTable.mk handle.table keyCodec mutationCodec).lookup key) start = .ok value after := by
    simpa [withTableSource, Unified.openTableChecked, bind_assoc] using ran
  have referenceRun := Unified.checkedTypedLookup_success safe keyCodec mutationCodec key nativeRun
  have served : (Unified.ReadSafety.reference bytes).Serves bytes := ⟨rfl, fun _ _ _ _ => rfl⟩
  obtain ⟨table, represented, opened⟩ := withTableSource_built built served
  have exactRead : withTableSource (Unified.ReadSafety.reference bytes) id (·.lookup key) =
      pure (lookupRows rows key) := by rw [opened, typed_lookup_spec represented]
  have refRun : withTableSource (Unified.ReadSafety.reference bytes) id (·.lookup key) () =
      .ok value () := by
    simpa [withTableSource, Unified.openTableChecked, bind_assoc] using referenceRun
  rw [exactRead] at refRun
  exact (EStateM.Result.ok.inj refRun).1.symm

open Unified in
theorem table_lookup_scoped {id : UInt64} {source : Source (EIO String)} (safe : ScopedRead P source bytes)
    (built : Image Alvoki.CRC32C.extend (tableLayout id)
      (rows.map (Entry.encode keyCodec mutationCodec)) bytes) (key : UInt64) :
    ReadPost P (· = lookupRows rows key) (withTableSource source id (·.lookup key)) := by
  letI := lawfulEIO
  have served : (ReadSafety.reference bytes).Serves bytes := ⟨rfl, fun _ _ _ _ => rfl⟩
  obtain ⟨table, represented, opened⟩ := withTableSource_built built served
  have ref : withTableSource (ReadSafety.reference bytes) id (·.lookup key) =
      pure (lookupRows rows key) := by rw [opened, typed_lookup_spec represented]
  intro w valid
  have observed := checkedTypedLookup_scoped (crc := Alvoki.CRC32C.extend) (tableId := id)
    safe keyCodec mutationCodec key w valid
  simp only [withTableSource, openTableChecked, bind_assoc, pure_bind] at ref ⊢
  rw [ref] at observed
  split <;> rename_i ran <;> rw [ran] at observed
  · exact observed
  · exact ⟨observed.1, (EStateM.Result.ok.inj observed.2).1.symm⟩

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

/-- The scope executes the continuation on the handle returned by open.
The runtime drops the last reference when the continuation returns. The
equation covers both continuation outcomes and keeps the reached world. -/
theorem nativeTableAt_afterStat {dir : System.FilePath} {id : UInt64}
    {use : ImmutableSSTable.TypedTable (EIO String) UInt64 Mutation → EIO String α}
    {start checked : Void IO.RealWorld}
    (stat : (nativeTableStat (tablePath dir id)).run start = .ok (.ok metadata) checked)
    (regular : isTableFile metadata = true) :
    (nativeTableAt dir id use).run start =
      match IO.FS.Handle.mk (tablePath dir id) .read checked with
      | .ok handle entered => (nativeTableAction handle id use).run entered
      | .error error reached => .error error reached := by
  let resume (md : IO.FS.Metadata) : ExceptT String IO α :=
    if isTableFile md then nativeTableReadScope (tablePath dir id)
      (fun held => nativeTableAction held id use)
    else throw "expected a singly linked regular SSTable"
  change ((nativeTableStat (tablePath dir id) >>= resume).run) start = _
  rw [ExceptT.run_bind]
  simp only [Bind.bind, instMonadEIO._aux_13, EST.bind, stat]
  simp [resume, regular, nativeTableReadScope, IO.FS.withFile, ExceptT.mk, ExceptT.run,
    Bind.bind, instMonadEIO._aux_13, EST.bind]
  cases opened : IO.FS.Handle.mk (tablePath dir id) .read checked <;> simp

/-- On either return branch, attribute the reached world to the last
operation that actually ran. A rejected stat never acquires a descriptor. -/
theorem nativeTableAt_reached {dir : System.FilePath} {id : UInt64}
    {use : ImmutableSSTable.TypedTable (EIO String) UInt64 Mutation → EIO String α}
    {start : Void IO.RealWorld} :
    (nativeTableAt dir id use).run start =
      match (nativeTableStat (tablePath dir id)).run start with
      | .error error checked => .error error checked
      | .ok (.error error) checked => .ok (.error error) checked
      | .ok (.ok md) checked =>
        if isTableFile md then
          match IO.FS.Handle.mk (tablePath dir id) .read checked with
          | .ok handle entered => (nativeTableAction handle id use).run entered
          | .error error reached => .error error reached
        else .ok (.error "expected a singly linked regular SSTable") checked := by
  let resume (md : IO.FS.Metadata) : ExceptT String IO α :=
    if isTableFile md then nativeTableReadScope (tablePath dir id)
      (fun held => nativeTableAction held id use)
    else throw "expected a singly linked regular SSTable"
  cases stat : (nativeTableStat (tablePath dir id)).run start with
  | error error checked =>
    change ((nativeTableStat (tablePath dir id) >>= resume).run) start = _
    rw [ExceptT.run_bind]
    simp [Bind.bind, instMonadEIO._aux_13, EST.bind, stat]
  | ok result checked =>
    cases result with
    | error error =>
      change ((nativeTableStat (tablePath dir id) >>= resume).run) start = _
      rw [ExceptT.run_bind]
      simp only [Bind.bind, instMonadEIO._aux_13, EST.bind, stat]
      rfl
    | ok md =>
      by_cases regular : isTableFile md = true
      · simpa [regular] using (nativeTableAt_afterStat (use := use) stat regular)
      · change ((nativeTableStat (tablePath dir id) >>= resume).run) start = _
        rw [ExceptT.run_bind]
        simp only [Bind.bind, instMonadEIO._aux_13, EST.bind, stat, ite_eq_right regular]
        have rejected : resume md = throw "expected a singly linked regular SSTable" := by
          simp [resume, regular]
        rw [rejected]
        rfl

/-- A successful scoped action must have passed stat and acquired the
descriptor at the derived name. These are the effects of that execution. -/
theorem nativeTableAt_success {dir : System.FilePath} {id : UInt64}
    {use : ImmutableSSTable.TypedTable (EIO String) UInt64 Mutation → EIO String α}
    (ran : (nativeTableAt dir id use).run start = .ok (.ok value) reached) :
    ∃ md checked handle entered,
      (nativeTableStat (tablePath dir id)).run start = .ok (.ok md) checked ∧
      isTableFile md = true ∧
      IO.FS.Handle.mk (tablePath dir id) .read checked = .ok handle entered := by
  rw [nativeTableAt_reached] at ran
  split at ran
  · cases ran
  · cases (EST.Out.ok.inj ran).1
  · rename_i md checked stat
    split at ran
    · rename_i regular
      split at ran
      · rename_i handle entered opened
        exact ⟨md, checked, handle, entered, stat, regular, opened⟩
      · cases ran
    · cases (EST.Out.ok.inj ran).1

theorem nativeTableAt_acquired {dir : System.FilePath} {id : UInt64}
    {use : ImmutableSSTable.TypedTable (EIO String) UInt64 Mutation → EIO String α}
    {start checked entered : Void IO.RealWorld}
    (stat : (nativeTableStat (tablePath dir id)).run start = .ok (.ok metadata) checked)
    (regular : isTableFile metadata = true)
    (acquired : IO.FS.Handle.mk (tablePath dir id) .read checked = .ok handle entered) :
    (nativeTableAt dir id use).run start = (nativeTableAction handle id use).run entered := by
  rw [nativeTableAt_afterStat stat regular, acquired]

end ExperimentalL0
