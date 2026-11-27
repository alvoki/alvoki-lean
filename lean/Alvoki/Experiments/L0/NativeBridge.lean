import Alvoki.Experiments.L0.NativeFacts

namespace ExperimentalL0.NativeBridge
open WalRecoverySlice.Segmented

/-- The certificate names the exact builder result for the durable file
that the adapter opened. Filesystem primitives establish the stable source
premise, not the lookup result. -/
theorem built_lookup [Monad m] [LawfulMonad m] [MonadExceptOf String m]
    {source : ImmutableSSTable.Source m}
    (built : ImmutableSSTable.modelBuild
      (rows.map (ImmutableSSTable.Entry.encode keyCodec mutationCodec)) = .ok (count, bytes))
    (serves : source.Serves bytes) (key : UInt64) :
    (do
      let table ← ImmutableSSTable.openTable source
      (ImmutableSSTable.TypedTable.mk table keyCodec mutationCodec).lookup key) =
      pure (lookupRows rows key) := by
  obtain ⟨table, opened, rep⟩ := ImmutableSSTable.open_built_table built serves
  rw [opened, pure_bind, typed_lookup_spec (typed_table_from_bytes rep)]

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

/-- A successful publication's byte trace and the decoder observation of
the version in the durable image. -/
inductive ManifestReceipt (proposed actual : L0Manifest.Version) : Prop where
  | issued
      (run : DurableBlob.Run (L0Manifest.encode .empty)
        (events ++ [.published (L0Manifest.encode proposed)]) true image)
      (submitted : ∀ event ∈ events ++ [.published (L0Manifest.encode proposed)],
        event.Submitted (fun bytes => ∃ v, v.Valid ∧ L0Manifest.encode v = bytes))
      (decoded : L0Manifest.decode image.active = some actual) :
      ManifestReceipt proposed actual

theorem ManifestReceipt.effect (receipt : ManifestReceipt proposed actual)
    (valid : proposed.Valid) : actual = proposed := by
  cases receipt with
  | issued run submitted decoded =>
    exact Option.some.inj (decoded.symm.trans (manifest_publish run submitted valid))

/-- A healthy table lookup records its actual result against a source
serving one completed builder image. This ties the input rows to the
observed result without a separate logical lookup assumption. -/
inductive TableRead (file : Option ByteArray) (rows : Rows) (key : UInt64) (result : Option Mutation) : Prop where
  | read {source : ImmutableSSTable.Source (Except String)}
      (built : ImmutableSSTable.modelBuild
        (rows.map (ImmutableSSTable.Entry.encode keyCodec mutationCodec)) = .ok (count, bytes))
      (binding : file = some bytes) (serves : source.Serves bytes)
      (returned : (do
        let table ← ImmutableSSTable.openTable source
        (ImmutableSSTable.TypedTable.mk table keyCodec mutationCodec).lookup key) = .ok result) :
      TableRead file rows key result

theorem TableRead.effect (receipt : TableRead file rows key result) : result = lookupRows rows key := by
  cases receipt with
  | read built _ serves returned =>
    rw [built_lookup built serves key] at returned
    exact (Except.ok.inj returned).symm

/-- Read-only component callbacks may change private handles or phase, but
keep the selected durable image. On success they return its observation. -/
def Observation (selected : σ → Selected) (before : σ) (value : α)
    (result : EStateM.Result String σ α) : Prop :=
  match result with
  | .ok actual after => actual = value ∧ selected after = selected before
  | .error _ after => selected after = selected before

/-- Success of exclusive creation, file fsync and directory fsync establishes
this binding of the builder image. Other names keep their prior contents. -/
structure CreatedFile (before after : Catalog) (id : UInt64) (rows : Rows)
    (file : Option ByteArray) : Prop where
  unused : before id = none
  bound : after id = some rows
  outside : ∀ other, other ≠ id → after other = before other
  image : ∃ count bytes, file = some bytes ∧ ImmutableSSTable.modelBuild
    (rows.map (ImmutableSSTable.Entry.encode keyCodec mutationCodec)) = .ok (count, bytes)

theorem CreatedFile.effect {id : UInt64} (made : CreatedFile before after id rows file) :
    before.Created after id rows := by
  refine ⟨made.unused, made.bound, ?_⟩
  intro other existing previous
  by_cases same : other = id
  · subst other
    rw [made.unused] at previous
    contradiction
  · rw [made.outside other same, previous]

/-- Local evidence for reached callbacks. WAL and manifest mutation effects
are obtained by eliminating component traces. Table creation carries the
namespace durability and isolation conditions; a read carries the exact
built image served by its descriptor. State indices identify the reached
phase. Relating the reported callbacks to native IO remains a premise. -/
structure CallbackEvidence (ops : Components (StorageM σ)) (selected : σ → Selected)
    (fileBytes : σ → UInt64 → Option ByteArray) : Prop where
  scan : ∀ s, Observation selected s (selected s).view (ops.scan s)
  reopenWal : ∀ s, Observation selected s (selected s).view (ops.reopenWal s)
  reopenManifest : ∀ s, Observation selected s (selected s).version (ops.manifest.reopen s)
  append : ∀ s batch, match ops.append batch s with
    | .ok _ after => WalReceipt (selected s).view (selected after).view batch ∧
        (selected after).version = (selected s).version ∧ (selected after).tables = (selected s).tables
    | .error _ after => selected after = selected s ∨
        (RecoveryChoices.Retry (.offline (selected s).view (some (.append batch)))
          (.ready (selected s).version) (.online (selected after).view) (.ready (selected after).version) ∧
          (selected after).tables = (selected s).tables)
  create : ∀ s rows, Rows.Ordered rows →
    match ops.tables.create rows s with
    | .ok id after => (selected after).view = (selected s).view ∧
        (selected after).version = (selected s).version ∧
        CreatedFile (selected s).tables (selected after).tables id rows (fileBytes after id)
    | .error _ after => (selected after).view = (selected s).view ∧
        (selected after).version = (selected s).version ∧
        (selected s).tables.Preserves (selected after).tables
  publish : ∀ s proposal, proposal.Valid → match ops.manifest.publish proposal s with
    | .ok _ after => ManifestReceipt proposal (selected after).version ∧
        (selected after).view = (selected s).view ∧ (selected after).tables = (selected s).tables
    | .error _ after => selected after = selected s ∨
        (RecoveryChoices.Retry (.online (selected s).view)
          (.offline (selected s).version (some proposal)) (.online (selected after).view)
          (.ready (selected after).version) ∧ (selected after).tables = (selected s).tables)
  check : ∀ s id, Observation selected s () (ops.tables.check id s)
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
    cases ran : ops.scan s <;> simpa [Observation, ran] using read
  reopenWal s := by
    have read := evidence.reopenWal s
    cases ran : ops.reopenWal s <;> simpa [Observation, ran] using read
  reopenManifest s := by
    have read := evidence.reopenManifest s
    cases ran : ops.manifest.reopen s <;> simpa [Observation, ran] using read
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
  create s rows ordered := by
    have made := evidence.create s rows ordered
    cases ran : ops.tables.create rows s with
    | error error after => simpa [ran] using made
    | ok id after =>
      rw [ran] at made
      exact ⟨made.1, made.2.1, made.2.2.effect⟩
  publish s proposal valid := by
    have receipt := evidence.publish s proposal valid
    cases ran : ops.manifest.publish proposal s with
    | ok value after =>
      rw [ran] at receipt
      exact selected_eq receipt.2.1 (receipt.1.effect valid) receipt.2.2
    | error error after =>
      rw [ran] at receipt
      rcases receipt with same | ⟨retry, tables⟩
      · exact Or.inl same
      · obtain ⟨view, old | new⟩ := retry.afterPublish
        · exact Or.inl (selected_eq view old tables)
        · exact Or.inr (selected_eq view new tables)
  check s id := by
    have read := evidence.check s id
    cases ran : ops.tables.check id s <;> simp only [Observation, ran] at read ⊢
    · exact read.2
    · exact read
  lookup s id key rows bound := by
    have read := evidence.lookup s id key rows bound
    cases ran : ops.tables.lookup id key s with
    | ok value after =>
      rw [ran] at read
      exact ⟨read.1.effect, read.2⟩
    | error error after => simpa [ran] using read

private def reached : EStateM.Result String σ α → σ
  | .ok _ after | .error _ after => after

/-- Reports of the actual shared operation schedule. The callback interpreter
can carry private adapter phase and effect observations. The initial image is
provided by a previously initialized database. -/
inductive ObservedRun (ops : Components (StorageM σ)) (selected : σ → Selected) :
    List Event → Option Session → σ → Prop where
  | initial : Nonempty (Durable (selected s) []) → ObservedRun ops selected [] none s
  | written : ObservedRun ops selected events (some session) s →
      write ops session change s = .ok next after →
      ObservedRun ops selected (events ++ [.written change]) (some next) after
  | writeUncertain : ObservedRun ops selected events (some session) s →
      write ops session change s = result →
      ObservedRun ops selected (events ++ [.writeUncertain change]) none (reached result)
  | got : ObservedRun ops selected events (some session) s →
      get ops session key s = .ok value after →
      ObservedRun ops selected (events ++ [.got key value]) (some session) after
  | readFailed : ObservedRun ops selected events (some session) s →
      get ops session key s = .error error after →
      ObservedRun ops selected events (some session) after
  | flushed : ObservedRun ops selected events (some session) s →
      flush ops session s = .ok next after →
      ObservedRun ops selected (events ++ [.flushed]) (some next) after
  | flushUncertain : ObservedRun ops selected events (some session) s →
      flush ops session s = result →
      ObservedRun ops selected (events ++ [.flushUncertain]) none (reached result)
  | reopened : ObservedRun ops selected events none s →
      recover ops s = .ok session after →
      ObservedRun ops selected (events ++ [.reopened]) (some session) after
  | openFailed : ObservedRun ops selected events none s →
      recover ops s = .error error after →
      ObservedRun ops selected (events ++ [.openFailed]) none after
  | stopped : ObservedRun ops selected events session s → selected after = selected s →
      ObservedRun ops selected (events ++ [.stop]) none after

theorem ObservedRun.projects (run : ObservedRun ops selected events session s)
    (evidence : CallbackEvidence ops selected fileBytes) : Execution.Run events session (selected s) := by
  have laws := evidence.laws
  induction run with
  | initial durable => exact .initial durable
  | @written _ session s change next after _ result ih =>
    refine .written ih (fun _ installed => ?_)
    have effect := write_refines laws s session installed change
    rw [result] at effect
    exact effect
  | @writeUncertain _ session s change observed _ result ih =>
    refine .writeUncertain ih (fun _ installed => ?_)
    have effect := write_refines laws s session installed change
    rw [result] at effect
    cases observed with
    | ok next after =>
      obtain ⟨d, _, _⟩ := effect
      exact Or.inr ⟨d⟩
    | error error after => exact effect
  | @got _ session s key value after _ result ih =>
    have frame : selected after = selected s := by
      obtain ⟨_ | _, _, represented⟩ := ih.refines
      · obtain ⟨_, _, same, _, installed⟩ := represented
        cases same
        have effect := get_refines laws s session installed key
        rw [result] at effect
        exact effect.2
      · have impossible := represented.1
        contradiction
    rw [frame]
    refine .got ih (fun _ installed => ?_)
    have effect := get_refines laws s session installed key
    rw [result] at effect
    exact effect.1
  | @readFailed _ session s key error after _ result ih =>
    obtain ⟨_ | _, _, represented⟩ := ih.refines
    · obtain ⟨_, _, same, _, installed⟩ := represented
      cases same
      have effect := get_refines laws s session installed key
      rw [result] at effect
      exact effect ▸ ih
    · have impossible := represented.1
      contradiction
  | flushed _ result ih =>
    refine .flushed ih (fun _ installed => ?_)
    have effect := flush_refines laws _ _ installed
    rw [result] at effect
    exact effect
  | @flushUncertain _ session s observed _ result ih =>
    refine .flushUncertain ih (fun _ installed => ?_)
    have effect := flush_refines laws _ _ installed
    rw [result] at effect
    cases observed with
    | ok next after =>
      obtain ⟨d, _, _⟩ := effect
      exact ⟨d⟩
    | error error after => exact effect
  | reopened _ result ih =>
    refine .reopened ih (fun _ durable => ?_)
    have effect := recover_refines laws _ durable
    rw [result] at effect
    exact effect.2
  | openFailed _ result ih =>
    refine .openFailed ih (fun _ durable => ?_)
    have effect := recover_refines laws _ durable
    rw [result] at effect
    exact ⟨effect ▸ durable⟩
  | stopped _ frame ih => exact frame ▸ .stop ih

theorem ObservedRun.refines (run : ObservedRun ops selected events session s)
    (evidence : CallbackEvidence ops selected fileBytes) :
    ∃ state, Client.Allows events state ∧ Execution.Represents session (selected s) state :=
  (run.projects evidence).refines

end ExperimentalL0.NativeBridge
