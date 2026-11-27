import Alvoki.Experiments.L0.Proofs
import Alvoki.Experiments.L0.ComponentProofs

namespace ExperimentalL0
open WalRecoverySlice.Segmented Model

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

/-- The flushed is proof-only. Released positions are not needed by replay. -/
structure Durable (image : Image) (history : Rows) where
  flushed : Rows
  pending : Rows
  split : history = flushed ++ pending
  base : image.view.base ≤ flushed.length
  boundary : image.version.flushedThrough.toNat = flushed.length
  wal : image.view.batches = ((flushed.drop image.view.base) ++ pending).map encode
  unique : image.version.Valid
  runs : List Rows
  bindings : image.version.tables.mapM (fun id => image.catalog[id.toNat]?) = some runs
  covered : ∀ key, overlay runs key = latest flushed key
  ordered : ∀ rows ∈ runs, Rows.Ordered rows

def Installed (session : Session) (image : Image) (history : Rows) : Prop :=
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

private theorem Durable.replay_pending (d : Durable image history) :
    (image.view.batches.drop (image.version.flushedThrough.toNat - image.view.base)).mapM decode =
      some d.pending := by
  rw [d.boundary, d.wal, ← List.map_drop]
  rw [List.drop_append_of_le_length (by simp)]
  rw [List.drop_drop, Nat.add_sub_of_le d.base]
  simp only [List.drop_length, List.nil_append, decode_batches]

private theorem check_bound (faults : Faults) (image : Image) (ids : List UInt64)
    (bound : ids.mapM (fun id => image.catalog[id.toNat]?) = some runs) :
    checkTables (components faults).tables ids image = .ok () image := by
  induction ids generalizing runs with
  | nil => rfl
  | cons id ids ih =>
    simp only [List.mapM_cons] at bound
    cases hit : image.catalog[id.toNat]? with
    | none => simp [hit] at bound
    | some rows =>
      have inside : id.toNat < image.catalog.length := List.getElem?_eq_some_iff.mp hit |>.choose
      cases found : ids.mapM (fun id => image.catalog[id.toNat]?) with
      | none => simp [hit, found] at bound
      | some rest =>
        have tail := ih found
        simp [checkTables, components, tableOps, inside, Bind.bind, EStateM.bind]
        exact tail

theorem recover_healthy (image : Image) (faults : Faults) (d : Durable image history)
    (manifestReady : faults.openManifest = true) (walReady : faults.openWal = true) :
    recover (components faults) image = .ok ⟨image.version, replay d.pending⟩ image := by
  have check := check_bound faults image image.version.tables d.bindings
  simp [recover, components, manifestReady, walReady, Bind.bind, EStateM.bind, Pure.pure,
    EStateM.pure, d.bounds, d.replay_pending,
    show checkTables (tableOps faults.create) image.version.tables image = .ok () image from check]

theorem recover_refines (image : Image) (faults : Faults) (d : Durable image history) :
    match recover (components faults) image with
    | .ok session after => after = image ∧ Installed session after history
    | .error _ after => after = image := by
  by_cases manifestReady : faults.openManifest = true
  · by_cases walReady : faults.openWal = true
    · rw [recover_healthy image faults d manifestReady walReady]
      exact ⟨rfl, d, rfl, rfl⟩
    · simp [recover, components, manifestReady, walReady, Bind.bind, EStateM.bind]
  · simp [recover, components, manifestReady, Bind.bind, EStateM.bind]

private theorem lookup_bound (faults : Faults) (image : Image) (ids : List UInt64)
    (bound : ids.mapM (fun id => image.catalog[id.toNat]?) = some runs) (key : UInt64) :
    lookupTables (components faults).tables key ids image = .ok (overlay runs key) image := by
  induction ids generalizing runs with
  | nil =>
    simp at bound
    subst runs
    rfl
  | cons id ids ih =>
    simp only [List.mapM_cons] at bound
    cases hit : image.catalog[id.toNat]? with
    | none => simp [hit] at bound
    | some rows =>
      cases found : ids.mapM (fun id => image.catalog[id.toNat]?) with
      | none => simp [hit, found] at bound
      | some rest =>
        simp [hit, found] at bound
        subst runs
        cases winner : lookupRows rows key <;>
          simp [lookupTables, components, tableOps, hit, Bind.bind, EStateM.bind, Pure.pure,
          EStateM.pure, overlay, winner]
        exact ih found

theorem get_refines (image : Image) (faults : Faults) (session : Session)
    (prior : Installed session image history) (key : UInt64) :
    get (components faults) session key image = .ok (denote history key) image := by
  obtain ⟨d, version, mem⟩ := prior
  have lookup := lookup_bound faults image image.version.tables d.bindings key
  have logical : denote history key =
      ((latest d.pending key).or (latest d.flushed key)).bind Mutation.value := by
    unfold denote
    exact congrArg (·.bind Mutation.value)
      ((congrArg (fun rows => latest rows key) d.split).trans (latest_append ..))
  rw [logical]
  unfold get
  rw [mem, replay_lookup, version]
  cases latest d.pending key <;>
    simp [ Bind.bind, EStateM.bind, Pure.pure, EStateM.pure, lookup, d.covered]

private def Durable.append (d : Durable image history) (change : Change) :
    Durable (image.append (encode change)) (history ++ [change]) := by
  refine ⟨d.flushed, d.pending ++ [change], ?_, d.base, d.boundary, ?_, d.unique,
    d.runs, d.bindings, d.covered, d.ordered⟩
  · exact (congrArg (· ++ [change]) d.split).trans (List.append_assoc ..)
  · simp [Image.append, Contract.View.append, d.wal, List.map_append, List.append_assoc]

theorem write_refines (image : Image) (faults : Faults) (session : Session)
    (prior : Installed session image history) (change : Change) :
    match write (components faults) session change image with
    | .ok next after => Installed next after (history ++ [change])
    | .error _ after => Nonempty (Durable after history) ∨ Nonempty (Durable after (history ++ [change])) := by
  obtain ⟨d, version, mem⟩ := prior
  let extended := d.append change
  by_cases fit : image.view.tail + 1 < UInt64.size
  · cases result : faults.append <;>
      simp [write, components, fit, result, effect, Bind.bind, EStateM.bind, Pure.pure,
        EStateM.pure]
    · exact ⟨extended, version, by
        change insert session.mem change = replay (d.pending ++ [change])
        simp [mem, replay, List.foldl_append]⟩
    · exact Or.inl ⟨d⟩
    · exact Or.inr ⟨extended⟩
  · simp [write, components, fit, Bind.bind, EStateM.bind]
    exact Or.inl ⟨d⟩

private theorem store_bindings (image : Image) (rows : Rows) (ids : List UInt64)
    (holds : ids.mapM (fun id => image.catalog[id.toNat]?) = some runs) :
    ids.mapM (fun id => (image.store rows).catalog[id.toNat]?) = some runs ∧
      ∀ id ∈ ids, id.toNat < image.catalog.length := by
  induction ids generalizing runs with
  | nil => exact ⟨holds, by simp⟩
  | cons id ids ih =>
    simp only [List.mapM_cons] at holds
    cases hit : image.catalog[id.toNat]? with
    | none => simp [hit] at holds
    | some old =>
      cases rest : ids.mapM (fun id => image.catalog[id.toNat]?) with
      | none => simp [hit, rest] at holds
      | some older =>
        simp [hit, rest] at holds
        subst runs
        have inside := (List.getElem?_eq_some_iff.mp hit).choose
        have kept := ih rest
        refine ⟨?_, ?_⟩
        · have same := image.store_preserves rows id old hit
          simp [List.mapM_cons, Image.tables] at same ⊢
          simp [same, kept.1]
        · intro key member
          rcases List.mem_cons.mp member with same | member
          · simpa [same] using inside
          · exact kept.2 key member

private def Durable.store (d : Durable image history) (rows : Rows) :
    Durable (image.store rows) history :=
  { d with bindings := (store_bindings image rows _ d.bindings).1 }

private def flushVersion (image : Image) : L0Manifest.Version :=
  ⟨image.catalog.length.toUInt64 :: image.version.tables, image.view.tail.toUInt64⟩

private def Durable.flush (d : Durable image history) (rows : Rows)
    (contents : ∀ key, lookupRows rows key = latest d.pending key)
    (ordered : Rows.Ordered rows)
    (fits : image.view.tail < UInt64.size) (room : image.catalog.length < UInt64.size) :
    Durable ((image.store rows).select (flushVersion image)) history := by
  have idNat : image.catalog.length.toUInt64.toNat = image.catalog.length :=
    UInt64.toNat_ofNat_of_lt' room
  have kept := store_bindings image rows _ d.bindings
  refine ⟨history, [], by simp, ?_, ?_, ?_, ?_, rows :: d.runs, ?_, ?_, ?_⟩
  · exact Nat.le_trans d.base (by have h := congrArg List.length d.split; simp at h; omega)
  · exact (UInt64.toNat_ofNat_of_lt' fits).trans d.tail_eq
  · change image.view.batches = (history.drop image.view.base ++ []).map encode
    rw [d.wal, List.append_nil]
    have dropped := congrArg (List.drop image.view.base) d.split
    rw [dropped, List.drop_append_of_le_length d.base]
  · change (image.catalog.length.toUInt64 :: image.version.tables).Nodup
    refine List.nodup_cons.mpr ⟨?_, d.unique⟩
    intro member
    have impossible := kept.2 _ member
    omega
  · change (image.catalog.length.toUInt64 :: image.version.tables).mapM
      (fun id => (image.store rows).catalog[id.toNat]?) = _
    have fresh : (image.store rows).catalog[image.catalog.length]? = some rows := by
      simp [Image.store]
    simp [List.mapM_cons, idNat, fresh, kept.1]
  · intro key
    exact (show overlay (rows :: d.runs) key = latest history key by
      simp only [overlay, contents, d.covered]
      exact (latest_append d.flushed d.pending key).symm.trans
        (congrArg (fun changes => latest changes key) d.split).symm)
  · intro table member
    rcases List.mem_cons.mp member with rfl | older
    · exact ordered
    · exact d.ordered table older

theorem flush_refines (image : Image) (faults : Faults) (session : Session)
    (prior : Installed session image history) :
    match flush (components faults) session image with
    | .ok next after => Installed next after history
    | .error _ after => Nonempty (Durable after history) := by
  obtain ⟨d, version, mem⟩ := prior
  by_cases empty : session.mem.isEmpty = true
  · simpa [flush, empty, Pure.pure, EStateM.pure] using
      (show Installed session image history from ⟨d, version, mem⟩)
  by_cases fit : image.view.tail < UInt64.size
  · by_cases room : image.catalog.length < UInt64.size
    · let rows := session.mem.toList
      have contents (key : UInt64) : lookupRows rows key = latest d.pending key := by
        simp [rows, rows_lookup, mem, replay_lookup]
      let stored := d.store rows
      let committed := d.flush rows contents (rows_ordered session.mem) fit room
      cases create : faults.create with
      | beforeEffect =>
        simp [flush, empty, components, fit, tableOps, room, create, effect, Bind.bind, EStateM.bind]
        exact ⟨d⟩
      | afterEffect =>
        simp [flush, empty, components, fit, tableOps, room, create, effect, Bind.bind, EStateM.bind]
        exact ⟨stored⟩
      | ok =>
        cases pub : faults.publish <;>
          simp [flush, empty, components, fit, tableOps, room, create, pub, effect, version,
            Bind.bind, EStateM.bind, Pure.pure, EStateM.pure]
        · exact ⟨committed, rfl, rfl⟩
        · exact ⟨stored⟩
        · exact ⟨committed⟩
    · simp [flush, empty, components, fit, tableOps, room, Bind.bind, EStateM.bind]
      exact ⟨d⟩
  · simp [flush, empty, components, fit, Bind.bind, EStateM.bind]
    exact ⟨d⟩

end ExperimentalL0
