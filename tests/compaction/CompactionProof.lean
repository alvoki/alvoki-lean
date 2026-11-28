import Alvoki.Experiments.L0.RecoveryChoices
import Alvoki.Experiments.DurableBlob.Proofs
import Alvoki.Experiments.Manifest.Proofs

namespace ExperimentalL0.CompactionExperiment

open WalRecoverySlice.Segmented

/-- A finite reference for the intended streaming producer. Replay requires
oldest-first input, while a manifest lists runs newest first. -/
def mergeReference (newer older : Rows) : Rows :=
  (replay (older.reverse ++ newer.reverse)).toList

theorem mergeReference_ordered (newer older : Rows) :
    (mergeReference newer older).Ordered :=
  rows_ordered _

theorem mergeReference_lookup (newer older : Rows) (key : UInt64) :
    lookupRows (mergeReference newer older) key =
      (lookupRows newer key).or (lookupRows older key) := by
  rw [mergeReference, rows_lookup, replay_lookup, latest_append]
  simp [latest, lookupRows]

/-- The stronger mutation-level guarantee also works with older runs that
could otherwise resurrect a deleted key. -/
theorem overlay_replace (newest newer older suffix : List Rows) (output : Rows)
    (exactLookup : ∀ key, lookupRows output key = overlay (newer ++ older) key)
    (key : UInt64) :
    overlay (newest ++ newer ++ older ++ suffix) key =
      overlay (newest ++ output :: suffix) key := by
  have append (xs ys : List Rows) :
      overlay (xs ++ ys) key = (overlay xs key).or (overlay ys key) := by
    induction xs with
    | nil => rfl
    | cons rows rest ih =>
      simp only [List.cons_append, overlay, ih]
      cases lookupRows rows key <;> rfl
  rw [List.append_assoc newest newer older, List.append_assoc newest (newer ++ older) suffix,
    append newest, append newest, append, overlay, exactLookup]

/-- Prepare the physical catalog first. The old and proposed manifest then
both witness the same history over the same WAL view. -/
def publicationChoices {before : Selected} {history newer older output : Rows}
    {newerId olderId outputId : UInt64} {suffix : List UInt64} {catalog : Catalog}
    (prior : Durable before history)
    (plan : before.version.tables = newerId :: olderId :: suffix)
    (created : before.tables.Created catalog outputId output)
    (ordered : output.Ordered)
    (exactLookup : ∀ key, lookupRows output key =
      (lookupRows newer key).or (lookupRows older key))
    (newerBound : before.tables newerId = some newer)
    (olderBound : before.tables olderId = some older) :
    Durable { before with tables := catalog } history ×
    { next : Durable ⟨before.view, ⟨outputId :: suffix, before.version.flushedThrough⟩, catalog⟩
        history // next.pending = prior.pending } := by
  have frame (ids : List UInt64) (runs : List Rows)
      (bound : ids.mapM before.tables = some runs) :
      ids.mapM catalog = some runs ∧ ∀ id ∈ ids, (before.tables id).isSome = true := by
    induction ids generalizing runs with
    | nil => exact ⟨bound, by simp⟩
    | cons id rest ih =>
      cases head : before.tables id with
      | none => simp [List.mapM_cons, head] at bound
      | some rows =>
        cases tail : rest.mapM before.tables with
        | none => simp [List.mapM_cons, head, tail] at bound
        | some restRows =>
          simp [List.mapM_cons, head, tail] at bound
          subst runs
          obtain ⟨restBound, present⟩ := ih restRows tail
          refine ⟨by simp [List.mapM_cons, created.2.2 id rows head, restBound], ?_⟩
          intro key member
          rcases List.mem_cons.mp member with rfl | member
          · simp [head]
          · exact present key member
  have bindings := prior.bindings
  rw [plan] at bindings
  cases bound : suffix.mapM before.tables with
  | none => simp [List.mapM_cons, newerBound, olderBound, bound] at bindings
  | some runs =>
    have runEq : newer :: older :: runs = prior.runs := by
      simpa [List.mapM_cons, newerBound, olderBound, bound] using bindings
    obtain ⟨kept, present⟩ := frame suffix runs bound
    have nodup : suffix.Nodup := by
      have valid := prior.unique
      unfold L0Manifest.Version.Valid at valid
      rw [plan] at valid
      exact (List.nodup_cons.mp (List.nodup_cons.mp valid).2).2
    have fresh : outputId ∉ suffix := by
      intro member
      simpa [created.1] using present outputId member
    refine ⟨{ prior with bindings := (frame _ _ prior.bindings).1 },
      ⟨⟨prior.flushed, prior.pending, prior.split, prior.base, prior.boundary, prior.wal,
        List.nodup_cons.mpr ⟨fresh, nodup⟩, output :: runs, ?_, ?_, ?_⟩, rfl⟩⟩
    · simp [List.mapM_cons, created.2.1, kept]
    · intro key
      rw [← prior.covered key, ← runEq]
      have exactOverlay (k : UInt64) : lookupRows output k = overlay [newer, older] k := by
        simpa [overlay] using exactLookup k
      exact (overlay_replace [] [newer] [older] runs output exactOverlay key).symm
    · intro rows member
      rcases List.mem_cons.mp member with rfl | rest
      · exact ordered
      · apply prior.ordered
        rw [← runEq]
        simp [rest]

/-- After acknowledged publication, the existing ready-session relation
holds with the same memtable and logical history. -/
theorem install_compacted {before : Selected} {history newer older : Rows}
    {newerId olderId outputId : UInt64} {suffix : List UInt64} {catalog : Catalog}
    {session : Session}
    (installed : Installed session before history)
    (plan : before.version.tables = newerId :: olderId :: suffix)
    (newerBound : before.tables newerId = some newer)
    (olderBound : before.tables olderId = some older)
    (created : before.tables.Created catalog outputId (mergeReference newer older)) :
    let version : L0Manifest.Version := ⟨outputId :: suffix, before.version.flushedThrough⟩
    Installed { session with version } ⟨before.view, version, catalog⟩ history := by
  obtain ⟨prior, _, mem⟩ := installed
  let durable := (publicationChoices prior plan created (mergeReference_ordered ..)
    (mergeReference_lookup newer older) newerBound olderBound).2
  exact ⟨durable.val, rfl, by simpa [durable.property] using mem⟩

/-- Use the reference output to instantiate both manifest choices and feed
them to the existing L0 recovery retry argument. -/
theorem merge_recovery {before : Selected} {history newer older : Rows}
    {newerId olderId outputId : UInt64} {suffix : List UInt64} {catalog : Catalog}
    {observed : Contract.View} {version : L0Manifest.Version}
    (prior : Durable before history)
    (plan : before.version.tables = newerId :: olderId :: suffix)
    (newerBound : before.tables newerId = some newer)
    (olderBound : before.tables olderId = some older)
    (created : before.tables.Created catalog outputId (mergeReference newer older))
    (retry : RecoveryChoices.Retry (.online before.view)
      (.offline before.version (some ⟨outputId :: suffix, before.version.flushedThrough⟩))
      (.online observed) (.ready version)) :
    Nonempty (Durable ⟨observed, version, catalog⟩ history) ∧
      (observed.batches.drop (version.flushedThrough.toNat - observed.base)).mapM decode =
        some prior.pending := by
  obtain ⟨old, new⟩ := publicationChoices prior plan created (mergeReference_ordered ..)
    (mergeReference_lookup newer older) newerBound olderBound
  obtain ⟨rfl, rfl | rfl⟩ := retry.afterPublish
  · exact ⟨⟨old⟩, prior.replay_pending⟩
  · exact ⟨⟨new.val⟩, prior.replay_pending⟩

/-- The publication interpreter supplies the manifest choice and its settlement
even when an earlier reopen failed. Catalog and WAL persistence are premises
of this composition. -/
theorem manifest_effect_recovery {before : Selected} {history newer older : Rows}
    {newerId olderId outputId : UInt64} {suffix : List UInt64} {catalog : Catalog}
    (prior : Durable before history)
    (plan : before.version.tables = newerId :: olderId :: suffix)
    (newerBound : before.tables newerId = some newer)
    (olderBound : before.tables olderId = some older)
    (created : before.tables.Created catalog outputId (mergeReference newer older))
    (dir : System.FilePath) (publish failed opened : DurableBlob.LinuxEffects.Reports)
    (initial crashed afterFailure settled : DurableBlob.Image) (bytes : ByteArray)
    (stable : initial.Stable (L0Manifest.encode before.version))
    (restart :
      let proposal : L0Manifest.Version := ⟨outputId :: suffix, before.version.flushedThrough⟩
      let reached := match (DurableBlob.LinuxEffects.backend dir publish).publish
          (L0Manifest.encode proposal) initial with
        | .ok _ image | .error _ image => image
      crashed = reached ∨ ∃ survivor ∈ reached.survivors, crashed = .settled survivor)
    (failure : (DurableBlob.LinuxEffects.backend dir failed).reopen crashed =
      .error () afterFailure)
    (success : (DurableBlob.LinuxEffects.backend dir opened).reopen afterFailure =
      .ok bytes settled) :
    ∃ version, L0Manifest.decode bytes = some version ∧
      settled.Stable (L0Manifest.encode version) ∧
      Nonempty (Durable ⟨before.view, version, catalog⟩ history) ∧
      (before.view.batches.drop (version.flushedThrough.toNat - before.view.base)).mapM decode =
        some prior.pending := by
  let proposal : L0Manifest.Version := ⟨outputId :: suffix, before.version.flushedThrough⟩
  let oldBytes := L0Manifest.encode before.version
  let proposedBytes := L0Manifest.encode proposal
  have reached := (DurableBlob.LinuxEffects.publishUncertainAdmits dir publish stable proposedBytes).2
  have admitted : crashed.Admits oldBytes (some proposedBytes) := by
    rcases restart with rfl | ⟨survivor, member, rfl⟩
    · exact reached
    · have permitted := reached.2 survivor member
      simpa [DurableBlob.Image.Admits, DurableBlob.Image.settled] using permitted
  obtain ⟨_, admissible⟩ :=
    DurableBlob.LinuxEffects.reopenFailedAdmits dir failed admitted failure
  obtain ⟨openedStep, pinned⟩ := DurableBlob.LinuxEffects.reopenSettles dir opened admissible success
  have permitted : DurableBlob.Permitted oldBytes (some proposedBytes) bytes := by
    cases openedStep with
    | opened choice => exact choice
  have proposed := (publicationChoices prior plan created (mergeReference_ordered ..)
    (mergeReference_lookup newer older) newerBound olderBound).2
  have choice : ∃ version, version.Valid ∧ bytes = L0Manifest.encode version ∧
      DurableBlob.Permitted before.version (some proposal) version := by
    rcases permitted with same | next
    · exact ⟨before.version, prior.unique, same, Or.inl rfl⟩
    · exact ⟨proposal, proposed.val.unique, (Option.some.inj next).symm, Or.inr rfl⟩
  obtain ⟨version, valid, rfl, allowed⟩ := choice
  have retry : RecoveryChoices.Retry (.online before.view)
      (.offline before.version (some proposal)) (.online before.view) (.ready version) :=
    .manifest (.manifest .initial .openFailed trivial) (.opened allowed) trivial
  obtain ⟨durable, replay⟩ := merge_recovery prior plan newerBound olderBound created retry
  exact ⟨version, L0Manifest.decode_encode valid, pinned, durable, replay⟩

/-- A process stop at this cut leaves the proposal live. The two
power-loss selections are both represented by the actual schedule. -/
example (dir : System.FilePath) (old proposal : L0Manifest.Version) :
    let reports : DurableBlob.LinuxEffects.Reports :=
      { readActive := true, openDirectory := true, syncDirectory := .beforeEffect,
        openWriter := true, write := true, flush := true, syncWriter := .ok, rename := .ok }
    let initial := DurableBlob.Image.settled (L0Manifest.encode old)
    let staged := match (DurableBlob.LinuxEffects.backend dir reports).publish
        (L0Manifest.encode proposal) initial with
      | .ok _ image | .error _ image => image
    staged.active = L0Manifest.encode proposal ∧
      L0Manifest.encode old ∈ staged.survivors ∧
      L0Manifest.encode proposal ∈ staged.survivors := by
  intro reports initial staged
  have effect : staged.active = L0Manifest.encode proposal ∧
      staged.survivors = [L0Manifest.encode proposal, L0Manifest.encode old] := by
    dsimp [staged, initial, reports]
    simp [DurableBlob.LinuxEffects.backend, DurableBlob.Primitives.backend,
      DurableBlob.Primitives.files, DurableBlob.Files.backend, DurableBlob.publishWith,
      DurableBlob.LinuxEffects.primitives, DurableBlob.Image.settled,
      Bind.bind, Pure.pure, EStateM.bind, EStateM.pure] <;> exact ⟨rfl, rfl⟩
  simp [effect.1, effect.2]

/-- Dropping a selected tombstone revives a value in an untouched table. -/
example :
    (overlay [[(1, .delete)], [(1, .put 7)]] 1).bind Mutation.value = none ∧
    (overlay [[], [(1, .put 7)]] 1).bind Mutation.value = some 7 := by decide

/-- Moving a compacted span past an unselected newer run changes its winner. -/
example :
    overlay [[(1, .put 9)], mergeReference [(1, .put 7)] []] 1 = some (.put 9) ∧
    overlay [mergeReference [(1, .put 7)] [], [(1, .put 9)]] 1 = some (.put 7) := by decide

end ExperimentalL0.CompactionExperiment
