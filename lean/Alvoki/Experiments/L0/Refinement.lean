import Alvoki.Experiments.L0.Proofs
import Alvoki.Experiments.L0.ComponentContract

namespace ExperimentalL0
open WalRecoverySlice.Segmented

def overlay (runs : List Rows) (key : UInt64) : Option Mutation :=
  match runs with
  | [] => none
  | rows :: older => (lookupRows rows key).or (overlay older key)

def denote (changes : Rows) : Database := fun key => (latest changes key).bind Mutation.value

theorem denote_write (history : Rows) (change : Change) :
    denote (history ++ [change]) = change.apply (denote history) := by
  funext key
  unfold denote Change.apply
  rw [latest_append]
  by_cases same : change.1 = key
  · simp [latest, same]
  · have different := Ne.symm same
    simp [latest, same, different]

/-- The flushed history is proof-only. Released positions are not needed by replay. -/
structure Durable (image : Selected) (history : Rows) where
  flushed : Rows
  pending : Rows
  split : history = flushed ++ pending
  base : image.view.base ≤ flushed.length
  boundary : image.version.flushedThrough.toNat = flushed.length
  wal : image.view.batches = ((flushed.drop image.view.base) ++ pending).map encode
  unique : image.version.Valid
  runs : List Rows
  bindings : image.version.tables.mapM image.tables = some runs
  covered : ∀ key, overlay runs key = latest flushed key
  ordered : ∀ rows ∈ runs, Rows.Ordered rows

def Installed (session : Session) (image : Selected) (history : Rows) : Prop :=
  ∃ durable : Durable image history, session.version = image.version ∧ session.mem = replay durable.pending

private theorem Durable.tail_eq (durable : Durable image history) :
    image.view.tail = history.length := by
  have lengths := congrArg List.length durable.split
  simp only [List.length_append] at lengths
  rw [Contract.View.tail, durable.wal]
  simp only [List.length_map, List.length_append, List.length_drop]
  have := durable.base
  omega

theorem Durable.bounds (durable : Durable image history) :
    image.view.base ≤ image.version.flushedThrough.toNat ∧
      image.version.flushedThrough.toNat ≤ image.view.tail := by
  have lengths := congrArg List.length durable.split
  simp only [List.length_append] at lengths
  rw [durable.boundary, durable.tail_eq]
  exact ⟨durable.base, by omega⟩

private theorem decode_batches (rows : Rows) : (rows.map encode).mapM decode = some rows := by
  induction rows with
  | nil => rfl
  | cons row rows ih => simp [List.mapM_cons, decode_encode, ih]

theorem Durable.replay_pending (d : Durable image history) :
    (image.view.batches.drop (image.version.flushedThrough.toNat - image.view.base)).mapM decode =
      some d.pending := by
  rw [d.boundary, d.wal, ← List.map_drop]
  rw [List.drop_append_of_le_length (by simp)]
  rw [List.drop_drop, Nat.add_sub_of_le d.base]
  simp only [List.drop_length, List.nil_append, decode_batches]


variable {ops : Components (StorageM σ)} {selected : σ → Selected}

private theorem check_frame (laws : ComponentLaws ops selected) (ids : List UInt64) (s : σ) :
    match checkTables ops.tables ids s with
    | .ok _ after | .error _ after => selected after = selected s := by
  induction ids generalizing s with
  | nil => rfl
  | cons id ids ih =>
    have frame := laws.check s id
    cases step : ops.tables.check id s with
    | error error after => simpa [checkTables, Bind.bind, EStateM.bind, step] using frame
    | ok value after =>
      rw [step] at frame
      have next := ih after
      cases rest : checkTables ops.tables ids after <;>
        simp_all [checkTables, Bind.bind, EStateM.bind]

theorem recover_refines (laws : ComponentLaws ops selected) (s : σ)
    (d : Durable (selected s) history) :
    match recover ops s with
    | .ok session after => selected after = selected s ∧ Installed session (selected after) history
    | .error _ after => selected after = selected s := by
  have manifest := laws.reopenManifest s
  cases opened : ops.manifest.reopen s with
  | error error after =>
    simpa [recover, Bind.bind, EStateM.bind, opened] using manifest
  | ok version middle =>
    rw [opened] at manifest
    obtain ⟨rfl, manifestFrame⟩ := manifest
    have wal := laws.reopenWal middle
    cases reopened : ops.reopenWal middle with
    | error error after =>
      rw [reopened] at wal
      simpa [recover, Bind.bind, EStateM.bind, opened, reopened] using wal.trans manifestFrame
    | ok view checked =>
      rw [reopened] at wal
      obtain ⟨rfl, walFrame⟩ := wal
      have frame : selected checked = selected s := walFrame.trans manifestFrame
      have check := check_frame laws (selected s).version.tables checked
      cases tables : checkTables ops.tables (selected s).version.tables checked with
      | error error after =>
        rw [tables] at check
        simpa [recover, Bind.bind, EStateM.bind, opened, reopened, manifestFrame,
          d.bounds, d.replay_pending, tables] using check.trans frame
      | ok value after =>
        rw [tables] at check
        have final := check.trans frame
        simp [recover, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure, opened, reopened,
          manifestFrame, d.bounds, d.replay_pending, tables]
        refine ⟨final, ?_⟩
        rw [final]
        exact ⟨d, rfl, rfl⟩

private def Durable.append (d : Durable image history) (change : Change) :
    Durable (image.append (encode change)) (history ++ [change]) := by
  refine ⟨d.flushed, d.pending ++ [change], ?_, d.base, d.boundary, ?_, d.unique,
    d.runs, d.bindings, d.covered, d.ordered⟩
  · exact (congrArg (· ++ [change]) d.split).trans (List.append_assoc ..)
  · simp [Selected.append, Contract.View.append, d.wal, List.map_append, List.append_assoc]

theorem write_refines (laws : ComponentLaws ops selected) (s : σ) (session : Session)
    (prior : Installed session (selected s) history) (change : Change) :
    match write ops session change s with
    | .ok next after => Installed next (selected after) (history ++ [change])
    | .error _ after => Nonempty (Durable (selected after) history) ∨
        Nonempty (Durable (selected after) (history ++ [change])) := by
  obtain ⟨d, version, mem⟩ := prior
  let extended := d.append change
  have scan := laws.scan s
  cases scanned : ops.scan s with
  | error error after =>
    rw [scanned] at scan
    simpa [write, Bind.bind, EStateM.bind, scanned, scan] using
      (Or.inl ⟨d⟩ : Nonempty (Durable (selected s) history) ∨
        Nonempty (Durable (selected s) (history ++ [change])))
  | ok view middle =>
    rw [scanned] at scan
    obtain ⟨rfl, frame⟩ := scan
    by_cases fit : (selected s).view.tail + 1 < UInt64.size
    · have appended := laws.append middle (encode change)
      cases issued : ops.append (encode change) middle with
      | error error after =>
        rw [issued] at appended
        simp [write, Bind.bind, EStateM.bind, scanned, fit, issued]
        rw [frame] at appended
        rcases appended with old | new
        · exact Or.inl ⟨old ▸ d⟩
        · exact Or.inr ⟨new ▸ extended⟩
      | ok value after =>
        rw [issued, frame] at appended
        simp [write, Bind.bind, EStateM.bind, scanned, fit, issued, Pure.pure, EStateM.pure]
        rw [appended]
        exact ⟨extended, version, by
          change insert session.mem change = replay (d.pending ++ [change])
          simp [mem, replay, List.foldl_append]⟩
    · simp [write, Bind.bind, EStateM.bind, scanned, fit]
      exact Or.inl ⟨frame ▸ d⟩

private theorem bindings_frame {before after : Catalog} {ids : List UInt64} (kept : before.Preserves after)
    (bound : ids.mapM before = some runs) :
    ids.mapM after = some runs ∧ ∀ id ∈ ids, ∃ rows, before id = some rows := by
  induction ids generalizing runs with
  | nil => exact ⟨bound, by simp⟩
  | cons id ids ih =>
    cases head : before id with
    | none => simp [List.mapM_cons, head] at bound
    | some rows =>
      cases tail : ids.mapM before with
      | none => simp [List.mapM_cons, head, tail] at bound
      | some older =>
        simp [List.mapM_cons, head, tail] at bound
        subst runs
        have rest := ih tail
        refine ⟨by simp [List.mapM_cons, kept id rows head, rest.1], ?_⟩
        intro key member
        rcases List.mem_cons.mp member with rfl | member
        · exact ⟨_, head⟩
        · exact rest.2 key member

private def Durable.frame (d : Durable before history)
    (view : after.view = before.view) (version : after.version = before.version)
    (kept : before.tables.Preserves after.tables) : Durable after history where
  flushed := d.flushed
  pending := d.pending
  split := d.split
  base := view ▸ d.base
  boundary := version ▸ d.boundary
  wal := view ▸ d.wal
  unique := version ▸ d.unique
  runs := d.runs
  bindings := version ▸ (bindings_frame kept d.bindings).1
  covered := d.covered
  ordered := d.ordered

private def proposal (s : Selected) (id : UInt64) : L0Manifest.Version :=
  ⟨id :: s.version.tables, s.view.tail.toUInt64⟩

private theorem proposal_valid {id : UInt64} (d : Durable before history)
    (fresh : before.tables id = none) : (proposal before id).Valid := by
  refine List.nodup_cons.mpr ⟨?_, d.unique⟩
  intro member
  obtain ⟨_, binds⟩ := (bindings_frame (fun _ _ h => h) d.bindings).2 id member
  rw [fresh] at binds
  contradiction

private def Durable.flush (d : Durable prior history)
    (stored : Durable next history) (id : UInt64) (rows : Rows)
    (fresh : prior.tables id = none) (bound : next.tables id = some rows)
    (version : next.version = prior.version)
    (contents : ∀ key, lookupRows rows key = latest stored.pending key)
    (ordered : Rows.Ordered rows) (fits : prior.view.tail < UInt64.size) :
    Durable (next.publish (proposal prior id)) history := by
  refine ⟨history, [], by simp, ?_, ?_, ?_, proposal_valid d fresh, rows :: stored.runs, ?_, ?_, ?_⟩
  · exact Nat.le_trans stored.base (by have h := congrArg List.length stored.split; simp at h; omega)
  · exact (UInt64.toNat_ofNat_of_lt' fits).trans d.tail_eq
  · change next.view.batches = (history.drop next.view.base ++ []).map encode
    rw [stored.wal, List.append_nil]
    have dropped := congrArg (List.drop next.view.base) stored.split
    rw [dropped, List.drop_append_of_le_length stored.base]
  · change (id :: prior.version.tables).mapM next.tables = _
    simp [List.mapM_cons, bound, ← version, stored.bindings]
  · intro key
    simp only [overlay, contents, stored.covered]
    exact (latest_append stored.flushed stored.pending key).symm.trans
      (congrArg (fun changes => latest changes key) stored.split).symm
  · intro table member
    rcases List.mem_cons.mp member with rfl | older
    · exact ordered
    · exact stored.ordered table older

theorem flush_refines (laws : ComponentLaws ops selected) (s : σ) (session : Session)
    (prior : Installed session (selected s) history) :
    match flush ops session s with
    | .ok next after => Installed next (selected after) history
    | .error _ after => Nonempty (Durable (selected after) history) := by
  obtain ⟨d, version, mem⟩ := prior
  by_cases empty : session.mem.isEmpty = true
  · simpa [flush, empty, Pure.pure, EStateM.pure] using
      (show Installed session (selected s) history from ⟨d, version, mem⟩)
  have scan := laws.scan s
  cases scanned : ops.scan s with
  | error error after =>
    rw [scanned] at scan
    simpa [flush, empty, Bind.bind, EStateM.bind, scanned, scan] using
      (show Nonempty (Durable (selected s) history) from ⟨d⟩)
  | ok view middle =>
    rw [scanned] at scan
    obtain ⟨rfl, frame⟩ := scan
    by_cases fit : (selected s).view.tail < UInt64.size
    · let rows := session.mem.toList
      have ordered := rows_ordered session.mem
      have created := laws.create middle rows ordered
      cases made : ops.tables.create rows middle with
      | error error after =>
        rw [made, frame] at created
        simp [flush, empty, Bind.bind, EStateM.bind, scanned, fit, rows, made]
        exact ⟨d.frame created.1 created.2.1 created.2.2⟩
      | ok id allocated =>
        rw [made, frame] at created
        obtain ⟨sameWal, sameVersion, fresh, bound, preserves⟩ := created
        let stored := d.frame sameWal sameVersion preserves
        have contents (key : UInt64) : lookupRows rows key = latest stored.pending key := by
          change lookupRows rows key = latest d.pending key
          simp [rows, rows_lookup, mem, replay_lookup]
        let committed := d.flush stored id rows fresh bound sameVersion contents ordered fit
        let proposed := proposal (selected s) id
        have issued := laws.publish allocated proposed (proposal_valid d fresh)
        have sameProposal : (⟨id :: session.version.tables, (selected s).view.tail.toUInt64⟩ :
            L0Manifest.Version) = proposed := by simp [proposed, proposal, version]
        cases published : ops.manifest.publish proposed allocated with
        | error error after =>
          rw [published] at issued
          simp [flush, empty, Bind.bind, EStateM.bind, scanned, fit, rows, made, sameProposal, published]
          rcases issued with old | new
          · exact ⟨old ▸ stored⟩
          · exact ⟨new ▸ committed⟩
        | ok value after =>
          rw [published] at issued
          simp [flush, empty, Bind.bind, EStateM.bind, scanned, fit, rows, made, sameProposal,
            published, Pure.pure, EStateM.pure]
          rw [issued]
          exact ⟨committed, rfl, rfl⟩
    · simp [flush, empty, Bind.bind, EStateM.bind, scanned, fit]
      exact ⟨frame ▸ d⟩

private theorem lookup_refines (laws : ComponentLaws ops selected) (s : σ) (key : UInt64)
    (ids : List UInt64) (bound : ids.mapM (selected s).tables = some runs) :
    match lookupTables ops.tables key ids s with
    | .ok found after => found = overlay runs key ∧ selected after = selected s
    | .error _ after => selected after = selected s := by
  induction ids generalizing s runs with
  | nil =>
    simp at bound
    subst runs
    exact ⟨rfl, rfl⟩
  | cons id ids ih =>
    cases head : (selected s).tables id with
    | none => simp [List.mapM_cons, head] at bound
    | some rows =>
      cases tail : ids.mapM (selected s).tables with
      | none => simp [List.mapM_cons, head, tail] at bound
      | some older =>
        simp [List.mapM_cons, head, tail] at bound
        subst runs
        have read := laws.lookup s id key rows head
        cases probed : ops.tables.lookup id key s with
        | error error after =>
          simpa [lookupTables, Bind.bind, EStateM.bind, probed] using read
        | ok value middle =>
          rw [probed] at read
          obtain ⟨rfl, frame⟩ := read
          cases miss : lookupRows rows key with
          | none =>
            have next := ih middle (by rw [frame]; exact tail)
            cases deeper : lookupTables ops.tables key ids middle <;>
              simp_all [lookupTables, Bind.bind, EStateM.bind, overlay]
          | some mutation =>
            simp [lookupTables, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure, probed,
              overlay, miss, frame]

theorem get_refines (laws : ComponentLaws ops selected) (s : σ) (session : Session)
    (prior : Installed session (selected s) history) (key : UInt64) :
    match get ops session key s with
    | .ok value after => value = denote history key ∧ selected after = selected s
    | .error _ after => selected after = selected s := by
  obtain ⟨d, version, mem⟩ := prior
  have logical : denote history key =
      ((latest d.pending key).or (latest d.flushed key)).bind Mutation.value := by
    unfold denote
    exact congrArg (·.bind Mutation.value)
      ((congrArg (fun rows => latest rows key) d.split).trans (latest_append ..))
  rw [logical]
  unfold get
  rw [mem, replay_lookup, version]
  cases latest d.pending key with
  | some mutation => exact ⟨rfl, rfl⟩
  | none =>
    have read := lookup_refines laws s key (selected s).version.tables d.bindings
    cases scanned : lookupTables ops.tables key (selected s).version.tables s <;>
      simp_all [Bind.bind, EStateM.bind, Pure.pure, EStateM.pure, d.covered]

end ExperimentalL0
