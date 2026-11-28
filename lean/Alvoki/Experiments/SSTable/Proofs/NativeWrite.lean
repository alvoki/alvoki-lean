import Alvoki.Experiments.SSTable.UnifiedNative
import Alvoki.Experiments.SSTable.Proofs.BuilderRelation
import Alvoki.Experiments.SSTable.Proofs.UnifiedBuilder

namespace ImmutableSSTable.Unified

/-- The observation of one exclusively owned output. `appended` is the
logical byte stream accepted by the descriptor, including bytes still held
by stdio. The description records the descriptor used during the schedule.
Its presence here does not extend the lifetime of the actual handle. -/
structure NativeWriteState (handle inode : Type) where
  binding : Option (System.FilePath × inode) := none
  description : Option (handle × inode) := none
  rows : List Entry := []
  appended : ByteArray := .empty
  flushed : Bool := false
  durable : Option (inode × ByteArray) := none

def NativeWriteState.BoundTo (state : NativeWriteState handle inode)
    (path : System.FilePath) (output : handle) (identity : inode) : Prop :=
  state.binding = some (path, identity) ∧ state.description = some (output, identity)

abbrev NativeWriteM (handle inode : Type) := EStateM String (NativeWriteState handle inode)

/-- Successful primitive reports for the shared native schedule. Exclusive
create starts a fresh byte stream and relates the path and new descriptor to
the same inode. Append and flush operate on that description. Successful fsync
of the flushed stream makes the inode's contents durable. A row callback
consumes one row and does not change this reserved output. No directory
barrier or behavior on a failed primitive is assumed here. -/
structure NativeWriteEffects {handle inode : Type}
    (ops : OutputOps (NativeWriteM handle inode) handle) (path : System.FilePath)
    (nextRow : NativeWriteM handle inode (Option Entry)) : Prop where
  create : ∀ before after output, (ops.openFile path .writeNew).run before = .ok output after →
    before.binding = none ∧ ∃ identity, after =
      { before with
        binding := some (path, identity)
        description := some (output, identity)
        appended := .empty
        flushed := false
        durable := none }
  append : ∀ output identity bytes before after, before.BoundTo path output identity →
    (ops.append output bytes).run before = .ok () after →
    after = { before with appended := before.appended ++ bytes, flushed := false }
  flush : ∀ output identity before after, before.BoundTo path output identity →
    (ops.flush output).run before = .ok () after →
    after = { before with flushed := true }
  sync : ∀ output identity before after, before.BoundTo path output identity →
    before.flushed = true → (ops.sync output).run before = .ok () after →
    after = { before with durable := some (identity, before.appended) }
  next : ∀ output identity before after row, before.BoundTo path output identity →
    nextRow.run before = .ok row after →
    row = before.rows.head? ∧ after = { before with rows := before.rows.tail }

private def NativeWriteState.project (state : NativeWriteState handle inode) : ModelFile :=
  ⟨state.rows, state.appended⟩

private def Simulates (before after : NativeWriteState handle inode → Prop)
    (actual : NativeWriteM handle inode α) (exactModel : ModelM α) : Prop :=
  ∀ s t value, before s → actual.run s = .ok value t →
    exactModel.run s.project = .ok (value, t.project) ∧ after t

private theorem actual_bind_ok {action : NativeWriteM handle inode α}
    {rest : α → NativeWriteM handle inode β} {before after : NativeWriteState handle inode}
    {result : β} (run : (action >>= rest).run before = .ok result after) :
    ∃ value middle, action.run before = .ok value middle ∧
      (rest value).run middle = .ok result after := by
  cases observed : action.run before with
  | error error reached =>
    change action before = _ at observed
    change EStateM.bind action rest before = _ at run
    simp [EStateM.bind, observed] at run
  | ok value middle =>
    refine ⟨value, middle, rfl, ?_⟩
    change action before = _ at observed
    change EStateM.bind action rest before = _ at run
    change rest value middle = _
    simpa [EStateM.bind, observed] using run

private theorem Simulates.bind {p q r : NativeWriteState handle inode → Prop}
    {actual : NativeWriteM handle inode α} {exactModel : ModelM α}
    {next : α → NativeWriteM handle inode β} {modelNext : α → ModelM β}
    (first : Simulates p q actual exactModel)
    (rest : ∀ value, Simulates q r (next value) (modelNext value)) :
    Simulates p r (actual >>= next) (exactModel >>= modelNext) := by
  intro before after result initial run
  obtain ⟨value, middle, firstRun, restRun⟩ := actual_bind_ok run
  obtain ⟨firstModel, middleFacts⟩ := first before middle value initial firstRun
  obtain ⟨restModel, finalFacts⟩ := rest value middle after result middleFacts restRun
  refine ⟨?_, finalFacts⟩
  change ((exactModel.run before.project).bind _) = _
  rw [firstModel]
  exact restModel

private theorem Simulates.pure {condition : NativeWriteState handle inode → Prop} (value : α) :
    Simulates condition condition (pure value) (pure value) := by
  intro before after result initial run
  cases run
  exact ⟨rfl, initial⟩

private theorem Simulates.throw {p q : NativeWriteState handle inode → Prop}
    (error : String) (action : ModelM α) : Simulates p q (throw error) action := by
  intro before after result initial run
  cases run

private theorem append_sim {ops : OutputOps (NativeWriteM handle inode) handle}
    {path : System.FilePath} {nextRow : NativeWriteM handle inode (Option Entry)}
    (effects : NativeWriteEffects ops path nextRow) (output : handle) (identity : inode)
    (bytes : ByteArray) :
    Simulates (·.BoundTo path output identity) (·.BoundTo path output identity)
      (ops.append output bytes) (modelSink.write bytes) := by
  intro before after value same run
  cases value
  rw [effects.append output identity bytes before after same run]
  exact ⟨rfl, same⟩

private theorem flush_sim {ops : OutputOps (NativeWriteM handle inode) handle}
    {path : System.FilePath} {nextRow : NativeWriteM handle inode (Option Entry)}
    (effects : NativeWriteEffects ops path nextRow) (output : handle) (identity : inode) :
    Simulates (·.BoundTo path output identity)
      (fun state => state.BoundTo path output identity ∧ state.flushed = true)
      (ops.flush output) modelSink.flush := by
  intro before after value same run
  cases value
  rw [effects.flush output identity before after same run]
  exact ⟨rfl, same, rfl⟩

private theorem next_sim {ops : OutputOps (NativeWriteM handle inode) handle}
    {path : System.FilePath} {nextRow : NativeWriteM handle inode (Option Entry)}
    (effects : NativeWriteEffects ops path nextRow) (output : handle) (identity : inode) :
    Simulates (·.BoundTo path output identity) (·.BoundTo path output identity) nextRow modelNext := by
  intro before after row same run
  obtain ⟨returned, state⟩ := effects.next output identity before after row same run
  rw [returned, state]
  refine ⟨?_, same⟩
  cases rows : before.rows <;> simp [modelNext, NativeWriteState.project, rows, StateT.run]

private structure SinkSimulation {handle inode : Type} (sink : Sink (NativeWriteM handle inode))
    (bound ready : NativeWriteState handle inode → Prop) : Prop where
  append : ∀ bytes, Simulates bound bound (sink.write bytes) (modelSink.write bytes)
  flush : Simulates bound ready sink.flush modelSink.flush

private theorem buildStream_sim (crc : Checksum) (layout : Layout) (options : BuildOptions)
    {sink : Sink (NativeWriteM handle inode)} {bound ready : NativeWriteState handle inode → Prop}
    (agreement : SinkSimulation sink bound ready) (supply : NativeWriteM handle inode (Option Entry))
    (supplied : Simulates bound bound supply modelNext) :
    Simulates bound ready (buildStream crc layout sink supply id options)
      (buildStream crc layout modelSink modelNext id options) := by
  let stage (b : Bool) := if b then ready else bound
  let law : BuilderRelation.Rules (NativeWriteM handle inode) ModelM (id : String → String) id :=
    { rel := fun p q => Simulates (stage p) (stage q)
      ret := Simulates.pure
      seq := Simulates.bind
      raise := fun e => Simulates.throw e _
      abort := fun _ _ _ _ _ _ _ ran => by cases ran }
  exact BuilderRelation.stream crc layout options (law := law) ⟨agreement.append, agreement.flush⟩ supply modelNext supplied

/-- Cleanup cannot turn a failed write or sync into success. It starts from
the reached state and keeps the primary error even if removal also fails. -/
private def failedOutput (ops : OutputOps (NativeWriteM handle inode) handle)
    (path : System.FilePath) (error : String) (reached : NativeWriteState handle inode) :
    EStateM.Result String (NativeWriteState handle inode) Nat :=
  match (ops.remove path).run reached with
  | .ok _ after | .error _ after => .error error after

private theorem freshOutput_result (ops : OutputOps (NativeWriteM handle inode) handle)
    (path : System.FilePath) (writeImage : handle → NativeWriteM handle inode Nat)
    (before : NativeWriteState handle inode) :
    (withFreshOutputWith (ε := String) ops path writeImage).run before =
      match (ops.openFile path .writeNew).run before with
      | .error error reached => .error error reached
      | .ok output created =>
        match (writeImage output).run created with
        | .error error reached => failedOutput ops path error reached
        | .ok count written =>
          match (ops.sync output).run written with
          | .error error reached => failedOutput ops path error reached
          | .ok _ after => .ok count after := by
  cases create : ops.openFile path .writeNew before with
  | error error reached =>
    simp [withFreshOutputWith, EStateM.run, Bind.bind, EStateM.bind, create]
  | ok output created =>
    cases write : writeImage output created with
    | error error reached =>
      cases cleanup : ops.remove path reached <;>
        simp [withFreshOutputWith, EStateM.run, Bind.bind, EStateM.bind, create, write,
          tryCatchThe, MonadExceptOf.tryCatch, EStateM.tryCatch, failedOutput, cleanup, EStateM.pure,
          Pure.pure, throwThe, MonadExceptOf.throw, EStateM.throw,
          EStateM.Backtrackable.restore, EStateM.dummyRestore]
    | ok count written =>
      cases sync : ops.sync output written with
      | error error reached =>
        cases cleanup : ops.remove path reached <;>
          simp [withFreshOutputWith, EStateM.run, Bind.bind, EStateM.bind, create, write, sync,
            tryCatchThe, MonadExceptOf.tryCatch, EStateM.tryCatch, failedOutput, cleanup, EStateM.pure,
            Pure.pure, throwThe, MonadExceptOf.throw, EStateM.throw,
          EStateM.Backtrackable.restore, EStateM.dummyRestore]
      | ok value after =>
        simp [withFreshOutputWith, EStateM.run, Bind.bind, EStateM.bind, create, write, sync,
          tryCatchThe, MonadExceptOf.tryCatch, EStateM.tryCatch, EStateM.pure, Pure.pure]

private theorem freshOutput_ok {ops : OutputOps (NativeWriteM handle inode) handle}
    {path : System.FilePath} {writeImage : handle → NativeWriteM handle inode Nat}
    {before after : NativeWriteState handle inode} {count : Nat}
    (run : (withFreshOutputWith (ε := String) ops path writeImage).run before = .ok count after) :
    ∃ output created written, (ops.openFile path .writeNew).run before = .ok output created ∧
      (writeImage output).run created = .ok count written ∧ (ops.sync output).run written = .ok () after := by
  rw [freshOutput_result] at run
  cases create : (ops.openFile path .writeNew).run before with
  | error error reached => simp [create] at run
  | ok output created =>
    simp only [create] at run
    cases write : (writeImage output).run created with
    | error error reached =>
      simp only [write, failedOutput] at run
      split at run <;> cases run
    | ok n written =>
      simp only [write] at run
      cases sync : (ops.sync output).run written with
      | error error reached =>
        simp only [sync, failedOutput] at run
        split at run <;> cases run
      | ok value finished =>
        cases value
        rw [sync] at run
        cases run
        exact ⟨output, created, written, rfl, write, sync⟩

/-- The successful interpretation of the same schedule as `buildFileSynced`.
The original exclusive descriptor is the one appended, flushed and synced.
The barrier persists that inode's contents, while publication of its name is
a separate directory operation. -/
theorem buildFileWith_refines {ops : OutputOps (NativeWriteM handle inode) handle}
    {path : System.FilePath} {nextRow : NativeWriteM handle inode (Option Entry)}
    {crc : Checksum} {layout : Layout} {options : BuildOptions}
    {before after : NativeWriteState handle inode} {count : Nat}
    (effects : NativeWriteEffects ops path nextRow)
    (run : (buildFileWith ops crc path layout nextRow id options).run before = .ok count after) :
    before.binding = none ∧ count = before.rows.length ∧ Image crc layout before.rows after.appended ∧
      ∃ output identity, after.BoundTo path output identity ∧ after.flushed = true ∧
        after.durable = some (identity, after.appended) ∧
        modelBuild crc layout before.rows options = .ok (count, after.appended) := by
  obtain ⟨output, created, written, openRan, writeRan, syncRan⟩ := freshOutput_ok run
  obtain ⟨fresh, identity, createdState⟩ := effects.create before created output openRan
  have owned : created.BoundTo path output identity := by simp [createdState, NativeWriteState.BoundTo]
  let agreement : SinkSimulation (ops.sink output)
      (·.BoundTo path output identity)
      (fun state => state.BoundTo path output identity ∧ state.flushed = true) :=
    ⟨append_sim effects output identity, flush_sim effects output identity⟩
  obtain ⟨exact, bound, flushed⟩ := buildStream_sim crc layout options agreement nextRow
    (next_sim effects output identity) created written count owned writeRan
  have durable := effects.sync output identity written after bound flushed syncRan
  have model : modelBuild crc layout before.rows options = .ok (count, written.appended) := by
    have initially : created.project = { rows := before.rows } := by
      rw [createdState]
      rfl
    rw [initially] at exact
    unfold modelBuild
    rw [exact]
    rfl
  obtain ⟨rowCount, image⟩ := modelBuild_ok model
  rw [durable]
  exact ⟨fresh, rowCount, image, output, identity, bound, flushed, rfl, model⟩

/-- Sync can fail before or after persisting content. The error observation
supplies the reached state, and cleanup runs from that state. This equation
preserves the original error without ruling out a completed fsync effect. -/
theorem buildFileWith_syncError {ops : OutputOps (NativeWriteM handle inode) handle}
    {path : System.FilePath} {nextRow : NativeWriteM handle inode (Option Entry)}
    {crc : Checksum} {layout : Layout} {options : BuildOptions} {output : handle}
    {before created written reached : NativeWriteState handle inode} {count : Nat} {error : String}
    (openRan : (ops.openFile path .writeNew).run before = .ok output created)
    (writeRan : (buildStream crc layout (ops.sink output) nextRow id options).run created =
      .ok count written)
    (syncRan : (ops.sync output).run written = .error error reached) :
    (buildFileWith ops crc path layout nextRow id options).run before =
      match (ops.remove path).run reached with
      | .ok _ after | .error _ after => .error error after := by
  unfold buildFileWith
  rw [freshOutput_result]
  simp only [openRan, writeRan, syncRan, failedOutput]

end ImmutableSSTable.Unified
