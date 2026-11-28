import Alvoki.Experiments.SSTable.UnifiedNative
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

/-- Observe the writer alongside other state, such as the source cursors.
The laws constrain one reached output primitive. -/
structure NativeWritePrimitivesOn {handle inode σ : Type}
    (observe : σ → NativeWriteState handle inode)
    (ops : OutputOps (EStateM ε σ) handle) (path : System.FilePath) : Prop where
  create : ∀ before after output, (ops.openFile path .writeNew).run before = .ok output after →
    (observe before).binding = none ∧ ∃ identity, observe after =
      { observe before with
        binding := some (path, identity)
        description := some (output, identity)
        appended := .empty
        flushed := false
        durable := none }
  append : ∀ output identity bytes before after, (observe before).BoundTo path output identity →
    (ops.append output bytes).run before = .ok () after →
    observe after =
      { observe before with appended := (observe before).appended ++ bytes, flushed := false }
  flush : ∀ output identity before after, (observe before).BoundTo path output identity →
    (ops.flush output).run before = .ok () after →
    observe after = { observe before with flushed := true }
  sync : ∀ output identity before after, (observe before).BoundTo path output identity →
    (observe before).flushed = true → (ops.sync output).run before = .ok () after →
    observe after = { observe before with durable := some (identity, (observe before).appended) }
structure NativeWriteEffectsOn {handle inode σ : Type}
    (observe : σ → NativeWriteState handle inode)
    (ops : OutputOps (EStateM ε σ) handle) (path : System.FilePath)
    (nextRow : EStateM ε σ (Option Entry)) : Prop
    extends NativeWritePrimitivesOn observe ops path where
  next : ∀ output identity before after row, (observe before).BoundTo path output identity →
    nextRow.run before = .ok row after →
    row = (observe before).rows.head? ∧
      observe after = { observe before with rows := (observe before).rows.tail }

private def NativeWriteState.project (state : NativeWriteState handle inode) : ModelFile :=
  ⟨state.rows, state.appended⟩

private def Simulates (observe : σ → NativeWriteState handle inode) (before after : σ → Prop)
    (actual : EStateM ε σ α) (exactModel : ModelM α) : Prop :=
  ∀ s t value, before s → actual.run s = .ok value t →
    exactModel.run (observe s).project = .ok (value, (observe t).project) ∧ after t

private theorem actual_bind_ok {action : EStateM ε σ α}
    {rest : α → EStateM ε σ β} {before after : σ}
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

variable {observe : σ → NativeWriteState handle inode}

private theorem Simulates.bind {p q r : σ → Prop}
    {actual : EStateM ε σ α} {exactModel : ModelM α}
    {next : α → EStateM ε σ β} {modelNext : α → ModelM β}
    (first : Simulates observe p q actual exactModel)
    (rest : ∀ value, Simulates observe q r (next value) (modelNext value)) :
    Simulates observe p r (actual >>= next) (exactModel >>= modelNext) := by
  intro before after result initial run
  obtain ⟨value, middle, firstRun, restRun⟩ := actual_bind_ok run
  obtain ⟨firstModel, middleFacts⟩ := first before middle value initial firstRun
  obtain ⟨restModel, finalFacts⟩ := rest value middle after result middleFacts restRun
  refine ⟨?_, finalFacts⟩
  change ((exactModel.run (observe before).project).bind _) = _
  rw [firstModel]
  exact restModel

private theorem Simulates.pure {condition : σ → Prop} (value : α) :
    Simulates observe condition condition (pure value : EStateM ε σ α) (pure value) := by
  intro before after result initial run
  cases run
  exact ⟨rfl, initial⟩

private theorem Simulates.throw {p q : σ → Prop}
    (error : ε) (action : ModelM α) : Simulates observe p q (throw error) action := by
  intro before after result initial run
  cases run

private theorem append_sim {ops : OutputOps (EStateM ε σ) handle}
    {path : System.FilePath} {nextRow : EStateM ε σ (Option Entry)}
    (effects : NativeWriteEffectsOn observe ops path nextRow) (output : handle) (identity : inode)
    (bytes : ByteArray) :
    Simulates observe (fun s => (observe s).BoundTo path output identity)
      (fun s => (observe s).BoundTo path output identity)
      (ops.append output bytes) (modelSink.write bytes) := by
  intro before after value same run
  cases value
  change _ ∧ (observe after).BoundTo path output identity
  rw [effects.append output identity bytes before after same run]
  exact ⟨rfl, same⟩

private theorem flush_sim {ops : OutputOps (EStateM ε σ) handle}
    {path : System.FilePath} {nextRow : EStateM ε σ (Option Entry)}
    (effects : NativeWriteEffectsOn observe ops path nextRow) (output : handle) (identity : inode) :
    Simulates observe (fun s => (observe s).BoundTo path output identity)
      (fun state => (observe state).BoundTo path output identity ∧ (observe state).flushed = true)
      (ops.flush output) modelSink.flush := by
  intro before after value same run
  cases value
  change _ ∧ (observe after).BoundTo path output identity ∧ (observe after).flushed = true
  rw [effects.flush output identity before after same run]
  exact ⟨rfl, same, rfl⟩

private theorem next_sim {ops : OutputOps (EStateM ε σ) handle}
    {path : System.FilePath} {nextRow : EStateM ε σ (Option Entry)}
    (effects : NativeWriteEffectsOn observe ops path nextRow) (output : handle) (identity : inode) :
    Simulates observe (fun s => (observe s).BoundTo path output identity)
      (fun s => (observe s).BoundTo path output identity) nextRow modelNext := by
  intro before after row same run
  obtain ⟨returned, state⟩ := effects.next output identity before after row same run
  change _ ∧ (observe after).BoundTo path output identity
  rw [returned, state]
  refine ⟨?_, same⟩
  cases rows : (observe before).rows <;> simp [modelNext, NativeWriteState.project, rows, StateT.run]

private structure SinkSimulation {handle inode : Type}
    (observe : σ → NativeWriteState handle inode)
    (sink : Sink (EStateM ε σ))
    (bound ready : σ → Prop) : Prop where
  append : ∀ bytes, Simulates observe bound bound (sink.write bytes) (modelSink.write bytes)
  flush : Simulates observe bound ready sink.flush modelSink.flush

private def nativeWriter (invalid : String → ε) (crc : Checksum) (layout : Layout) (options : BuildOptions)
    (sink : Sink (EStateM ε σ)) : Writer (EStateM ε σ) ε :=
  ⟨crc, layout, sink, invalid, options⟩

private theorem writePacket_sim (invalid : String → ε) (crc : Checksum) (layout : Layout) (options : BuildOptions)
    {sink : Sink (EStateM ε σ)} {bound ready : σ → Prop}
    (agreement : SinkSimulation observe sink bound ready) (kind : UInt64) (offset : Nat) (body : ByteArray) :
    Simulates observe bound bound ((nativeWriter invalid crc layout options sink).writePacket kind offset body)
      ((modelWriter crc layout options).writePacket kind offset body) := by
  by_cases packet : body.size + checksumSize ≤ maxRowSize
  · by_cases file : offset + (body.size + checksumSize) + footerPacketSize ≤ maxFileSize
    · simp only [Writer.writePacket, packet, file, ↓reduceIte, nativeWriter, modelWriter]
      exact (agreement.append _).bind (fun _ => .pure _)
    · simp only [Writer.writePacket, packet, file, ↓reduceIte, nativeWriter, modelWriter]
      intro before after value initial run
      cases run
  · simp only [Writer.writePacket, packet, ↓reduceIte, nativeWriter, modelWriter]
    intro before after value initial run
    cases run

private theorem flushLeaf_sim (invalid : String → ε) (crc : Checksum) (layout : Layout) (options : BuildOptions)
    {sink : Sink (EStateM ε σ)} {bound ready : σ → Prop}
    (agreement : SinkSimulation observe sink bound ready) (state : BuilderState) :
    Simulates observe bound bound ((nativeWriter invalid crc layout options sink).flushLeaf state)
      ((modelWriter crc layout options).flushLeaf state) := by
  cases head : state.leaf[0]? with
  | none => simpa only [Writer.flushLeaf, head] using (Simulates.pure (condition := bound) state)
  | some first =>
    cases tail : state.leaf.back? with
    | none =>
      simpa only [Writer.flushLeaf, head, tail] using (Simulates.pure (condition := bound) state)
    | some last =>
      by_cases fits : state.rootBytes + indexEntrySize last.lastKey + checksumSize ≤ maxRowSize
      · simp only [Writer.flushLeaf, head, tail, fits, ↓reduceIte]
        exact (writePacket_sim invalid crc layout options agreement 2 state.offset _).bind (fun _ => .pure _)
      · simp only [Writer.flushLeaf, head, tail, fits, ↓reduceIte, nativeWriter]
        intro before after value initial run
        cases run

private theorem flushData_sim (invalid : String → ε) (crc : Checksum) (layout : Layout) (options : BuildOptions)
    {sink : Sink (EStateM ε σ)} {bound ready : σ → Prop}
    (agreement : SinkSimulation observe sink bound ready) (state : BuilderState) :
    Simulates observe bound bound ((nativeWriter invalid crc layout options sink).flushData state)
      ((modelWriter crc layout options).flushData state) := by
  cases tail : state.data.back? with
  | none => simpa only [Writer.flushData, tail] using (Simulates.pure (condition := bound) state)
  | some last =>
    simp only [Writer.flushData, tail,
      show (nativeWriter invalid crc layout options sink).layout = layout from rfl,
      show (modelWriter crc layout options).layout = layout from rfl,
      show (nativeWriter invalid crc layout options sink).options = options from rfl,
      show (modelWriter crc layout options).options = options from rfl]
    apply Simulates.bind
    · by_cases flush : (!state.leaf.isEmpty &&
          decide (state.leafBytes + indexEntrySize last.key + checksumSize > options.leafTarget)) = true
      · simpa only [flush, ↓reduceIte] using flushLeaf_sim invalid crc layout options agreement state
      · simpa only [flush, Bool.false_eq_true, ↓reduceIte] using (Simulates.pure (condition := bound) state)
    · intro current
      exact (writePacket_sim invalid crc layout options agreement 1 current.offset _).bind (fun _ => .pure _)

private theorem accept_sim (invalid : String → ε) (crc : Checksum) (layout : Layout) (options : BuildOptions)
    {sink : Sink (EStateM ε σ)} {bound ready : σ → Prop}
    (agreement : SinkSimulation observe sink bound ready) (state : BuilderState) (row : Entry) :
    Simulates observe bound bound ((nativeWriter invalid crc layout options sink).accept state row)
      ((modelWriter crc layout options).accept state row) := by
  have actualLayout : (nativeWriter invalid crc layout options sink).layout = layout := rfl
  have modelLayout : (modelWriter crc layout options).layout = layout := rfl
  have actualOptions : (nativeWriter invalid crc layout options sink).options = options := rfl
  have modelOptions : (modelWriter crc layout options).options = options := rfl
  cases check : state.checkRow layout row with
  | error error =>
    simp only [Writer.accept, actualLayout, modelLayout, check]
    exact Simulates.throw _ _
  | ok accepted =>
    cases accepted
    simp only [Writer.accept, actualLayout, modelLayout, actualOptions, modelOptions, check]
    apply Simulates.bind
    · by_cases flush : (!state.data.isEmpty &&
          decide (dataSize layout (state.data.size + 1)
            (state.payloadBytes + entrySize layout row) > options.dataTarget)) = true
      · simpa only [flush, ↓reduceIte] using flushData_sim invalid crc layout options agreement state
      · simpa only [flush, Bool.false_eq_true, ↓reduceIte] using (Simulates.pure (condition := bound) state)
    · intro current
      exact Simulates.pure _

private theorem streamRows_sim (invalid : String → ε) (crc : Checksum) (layout : Layout) (options : BuildOptions)
    {sink : Sink (EStateM ε σ)} {bound ready : σ → Prop}
    (agreement : SinkSimulation observe sink bound ready) (supply : EStateM ε σ (Option Entry))
    (supplied : Simulates observe bound bound supply modelNext) (state : BuilderState) (room : Nat) :
    Simulates observe bound bound ((nativeWriter invalid crc layout options sink).streamRows supply state room)
      ((modelWriter crc layout options).streamRows modelNext state room) := by
  induction room generalizing state with
  | zero =>
    simp only [Writer.streamRows]
    exact supplied.bind fun option => by
      cases option with
      | none => exact Simulates.pure _
      | some row =>
        intro before after value initial run
        cases run
  | succ room induction =>
    simp only [Writer.streamRows]
    refine supplied.bind ?_
    intro option
    cases option with
    | none => exact Simulates.pure _
    | some row =>
      exact (accept_sim invalid crc layout options agreement state row).bind
        (fun current => induction current)

private theorem finish_sim (invalid : String → ε) (crc : Checksum) (layout : Layout) (options : BuildOptions)
    {sink : Sink (EStateM ε σ)} {bound ready : σ → Prop}
    (agreement : SinkSimulation observe sink bound ready) (state : BuilderState) :
    Simulates observe bound ready ((nativeWriter invalid crc layout options sink).finish state)
      ((modelWriter crc layout options).finish state) := by
  simp only [Writer.finish]
  refine (flushData_sim invalid crc layout options agreement state).bind fun afterData =>
    (flushLeaf_sim invalid crc layout options agreement afterData).bind fun afterLeaf => ?_
  apply Simulates.bind
  · by_cases empty : afterLeaf.root.isEmpty = true
    · simpa only [empty, ↓reduceIte] using
        (Simulates.pure (condition := bound) ((0, 0) : Nat × Nat))
    · simp only [empty]
      exact (writePacket_sim invalid crc layout options agreement 3 afterLeaf.offset _).bind
        (fun _ => .pure _)
  · intro root
    cases root
    exact (agreement.append _).bind fun _ => agreement.flush.bind fun _ => .pure _

private theorem buildStream_sim (invalid : String → ε) (crc : Checksum) (layout : Layout) (options : BuildOptions)
    {sink : Sink (EStateM ε σ)} {bound ready : σ → Prop}
    (agreement : SinkSimulation observe sink bound ready) (supply : EStateM ε σ (Option Entry))
    (supplied : Simulates observe bound bound supply modelNext) :
    Simulates observe bound ready (buildStream crc layout sink supply invalid options)
      (buildStream crc layout modelSink modelNext id options) := by
  by_cases valid : layout.Valid
  · by_cases targets : 0 < options.dataTarget ∧ options.dataTarget ≤ maxRowSize ∧
        0 < options.leafTarget ∧ options.leafTarget ≤ maxRowSize
    · simp only [buildStream, valid, targets, ↓reduceIte]
      exact (streamRows_sim invalid crc layout options agreement supply supplied {} maxFileSize).bind
        (fun current => finish_sim invalid crc layout options agreement current)
    · simp only [buildStream, valid, targets, ↓reduceIte]
      intro before after value initial run
      cases run
  · simp only [buildStream, valid, ↓reduceIte]
    intro before after value initial run
    cases run

/-- Cleanup cannot turn a failed write or sync into success. It starts from
the reached state and keeps the primary error even if removal also fails. -/
private def failedOutput (ops : OutputOps (EStateM ε σ) handle)
    (path : System.FilePath) (error : ε) (reached : σ) :
    EStateM.Result ε σ Nat :=
  match (ops.remove path).run reached with
  | .ok _ after | .error _ after => .error error after

private theorem freshOutput_result (ops : OutputOps (EStateM ε σ) handle)
    (path : System.FilePath) (writeImage : handle → EStateM ε σ Nat)
    (before : σ) :
    (withFreshOutputWith (ε := ε) ops path writeImage).run before =
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

private theorem freshOutput_ok {ops : OutputOps (EStateM ε σ) handle}
    {path : System.FilePath} {writeImage : handle → EStateM ε σ Nat}
    {before after : σ} {count : Nat}
    (run : (withFreshOutputWith (ε := ε) ops path writeImage).run before = .ok count after) :
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

private theorem streamRows_eof {writer : Writer (EStateM ε σ) ε}
    {nextRow : EStateM ε σ (Option Entry)} {state last : BuilderState}
    {start consumed : σ} (room : Nat)
    (ran : (writer.streamRows nextRow state room).run start = .ok last consumed) :
    ∃ atEOF, nextRow atEOF = .ok none consumed := by
  cases room with
  | zero =>
    simp only [Writer.streamRows] at ran
    obtain ⟨item, reached, pulled, rest⟩ := actual_bind_ok ran
    cases item with
    | none =>
      cases rest
      exact ⟨start, pulled⟩
    | some row => cases rest
  | succ room =>
    simp only [Writer.streamRows] at ran
    obtain ⟨item, reached, pulled, rest⟩ := actual_bind_ok ran
    cases item with
    | none =>
      cases rest
      exact ⟨start, pulled⟩
    | some row =>
      obtain ⟨_, _, _, loop⟩ := actual_bind_ok rest
      exact streamRows_eof room loop
termination_by room

/-- A completed native writer ran its callback through the final EOF.
The final streamRows state is the state returned by that callback, before
finalizing the image and syncing its inode. -/
theorem buildFileWith_eofWith {ops : OutputOps (EStateM ε σ) handle}
    {path : System.FilePath} {nextRow : EStateM ε σ (Option Entry)}
    {crc : Checksum} {layout : Layout} {options : BuildOptions}
    {before after : σ} {count : Nat}
    {invalid : String → ε}
    (built : buildFileWith ops crc path layout nextRow invalid options before = .ok count after) :
    ∃ atEOF consumed, nextRow atEOF = .ok none consumed := by
  obtain ⟨output, created, written, _, builtStream, _⟩ := freshOutput_ok built
  by_cases valid : layout.Valid
  · by_cases targets : 0 < options.dataTarget ∧ options.dataTarget ≤ maxRowSize ∧
        0 < options.leafTarget ∧ options.leafTarget ≤ maxRowSize
    · simp only [buildStream, valid, targets, ↓reduceIte] at builtStream
      obtain ⟨_, consumed, rows, _⟩ := actual_bind_ok builtStream
      obtain ⟨atEOF, eof⟩ := streamRows_eof maxFileSize rows
      exact ⟨atEOF, consumed, eof⟩
    · simp only [buildStream, valid, targets, ↓reduceIte] at builtStream
      cases builtStream
  · simp only [buildStream, valid, ↓reduceIte] at builtStream
    cases builtStream

theorem buildFileWith_eof {ops : OutputOps (EStateM String σ) handle}
    {path : System.FilePath} {nextRow : EStateM String σ (Option Entry)}
    {crc : Checksum} {layout : Layout} {options : BuildOptions}
    {before after : σ} {count : Nat}
    (built : buildFileWith ops crc path layout nextRow id options before = .ok count after) :
    ∃ atEOF consumed, nextRow atEOF = .ok none consumed :=
  buildFileWith_eofWith built

/-- The successful interpretation of the same schedule as `buildFileSynced`.
The original exclusive descriptor is the one appended, flushed and synced.
The barrier persists that inode's contents, while publication of its name is
a separate directory operation. -/
theorem buildFileWith_refinesOn {ops : OutputOps (EStateM ε σ) handle}
    {path : System.FilePath} {nextRow : EStateM ε σ (Option Entry)}
    {crc : Checksum} {layout : Layout} {options : BuildOptions}
    {before after : σ} {count : Nat}
    {invalid : String → ε}
    (effects : NativeWriteEffectsOn observe ops path nextRow)
    (run : (buildFileWith ops crc path layout nextRow invalid options).run before = .ok count after) :
    (observe before).binding = none ∧ count = (observe before).rows.length ∧
      Image crc layout (observe before).rows (observe after).appended ∧
      ∃ output identity, (observe after).BoundTo path output identity ∧ (observe after).flushed = true ∧
        (observe after).durable = some (identity, (observe after).appended) ∧
        modelBuild crc layout (observe before).rows options = .ok (count, (observe after).appended) := by
  obtain ⟨output, created, written, openRan, writeRan, syncRan⟩ := freshOutput_ok run
  obtain ⟨fresh, identity, createdState⟩ := effects.create before created output openRan
  have owned : (observe created).BoundTo path output identity := by
    simp [createdState, NativeWriteState.BoundTo]
  let agreement : SinkSimulation observe (ops.sink output)
      (fun s => (observe s).BoundTo path output identity)
      (fun state => (observe state).BoundTo path output identity ∧ (observe state).flushed = true) :=
    ⟨append_sim effects output identity, flush_sim effects output identity⟩
  obtain ⟨exact, bound, flushed⟩ := buildStream_sim invalid crc layout options agreement nextRow
    (next_sim effects output identity) created written count owned writeRan
  have durable := effects.sync output identity written after bound flushed syncRan
  have model : modelBuild crc layout (observe before).rows options = .ok (count, (observe written).appended) := by
    have initially : (observe created).project = { rows := (observe before).rows } := by
      rw [createdState]
      rfl
    rw [initially] at exact
    unfold modelBuild
    rw [exact]
    rfl
  obtain ⟨rowCount, image⟩ := modelBuild_ok model
  rw [durable]
  exact ⟨fresh, rowCount, image, output, identity, bound, flushed, rfl, model⟩

theorem buildFileWith_refines_on {ops : OutputOps (EStateM String σ) handle}
    {path : System.FilePath} {nextRow : EStateM String σ (Option Entry)}
    {crc : Checksum} {layout : Layout} {options : BuildOptions}
    {before after : σ} {count : Nat}
    (effects : NativeWriteEffectsOn observe ops path nextRow)
    (run : (buildFileWith ops crc path layout nextRow id options).run before = .ok count after) :
    (observe before).binding = none ∧ count = (observe before).rows.length ∧
      Image crc layout (observe before).rows (observe after).appended ∧
      ∃ output identity, (observe after).BoundTo path output identity ∧ (observe after).flushed = true ∧
        (observe after).durable = some (identity, (observe after).appended) ∧
        modelBuild crc layout (observe before).rows options = .ok (count, (observe after).appended) :=
  buildFileWith_refinesOn effects run

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
  exact buildFileWith_refines_on (observe := id)
    ⟨⟨effects.create, effects.append, effects.flush, effects.sync⟩, effects.next⟩ run

/-- A failed streaming write calls cleanup from the reached state, without
issuing sync and without losing the original failure. -/
theorem buildFileWith_writeErrorWith {ops : OutputOps (EStateM ε σ) handle}
    {path : System.FilePath} {nextRow : EStateM ε σ (Option Entry)}
    {crc : Checksum} {layout : Layout} {options : BuildOptions} {output : handle}
    {before created reached : σ} {error : ε}
    {invalid : String → ε}
    (openRan : ops.openFile path .writeNew before = .ok output created)
    (writeRan : buildStream crc layout (ops.sink output) nextRow invalid options created =
      .error error reached) :
    buildFileWith ops crc path layout nextRow invalid options before =
      match ops.remove path reached with
      | .ok _ after | .error _ after => .error error after := by
  change (buildFileWith ops crc path layout nextRow invalid options).run before = _
  unfold buildFileWith
  rw [freshOutput_result]
  simp only [openRan, writeRan, failedOutput, EStateM.run]

theorem buildFileWith_writeError {ops : OutputOps (EStateM String σ) handle}
    {path : System.FilePath} {nextRow : EStateM String σ (Option Entry)}
    {crc : Checksum} {layout : Layout} {options : BuildOptions} {output : handle}
    {before created reached : σ} {error : String}
    (openRan : ops.openFile path .writeNew before = .ok output created)
    (writeRan : buildStream crc layout (ops.sink output) nextRow id options created =
      .error error reached) :
    buildFileWith ops crc path layout nextRow id options before =
      match ops.remove path reached with
      | .ok _ after | .error _ after => .error error after := by
  rw [buildFileWith_writeErrorWith openRan writeRan]
  cases ops.remove path reached <;> rfl

/-- The actual successful pulls and accepts before a required callback.
This relation stops at the callback, before any EOF, finish or sync. -/
inductive Writer.InputReached (writer : Writer (EStateM ε σ) ε)
    (supply : EStateM ε σ (Option Entry)) (target : σ) : Nat → BuilderState → σ → Prop where
  | here : InputReached writer supply target room state target
  | later : supply start = .ok (some row) pulled →
      writer.accept state row pulled = .ok next accepted →
      InputReached writer supply target room next accepted →
      InputReached writer supply target (room + 1) state start

theorem Writer.InputReached.aborts {writer : Writer (EStateM ε σ) ε}
    {supply : EStateM ε σ (Option Entry)}
    (stages : writer.InputReached supply target room state start)
    (failed : supply target = .error error reached) :
    writer.streamRows supply state room start = .error error reached := by
  have immediate (amount : Nat) (current : BuilderState) :
      writer.streamRows supply current amount target = .error error reached := by
    cases amount <;> simp only [Writer.streamRows, Bind.bind, EStateM.bind, failed]
  induction stages with
  | here => exact immediate _ _
  | later pulled accepted _ ih =>
    rw [Writer.streamRows]
    simpa [Bind.bind, EStateM.bind, pulled, accepted] using ih

/-- A failure at any required input after exclusive creation skips finish,
EOF and sync. Only removal is run, on the exact state of the failed pull. -/
theorem buildFileWith_inputError {ops : OutputOps (EStateM ε σ) handle}
    {path : System.FilePath} {nextRow : EStateM ε σ (Option Entry)}
    {crc : Checksum} {layout : Layout} {options : BuildOptions} {output : handle}
    {before created atRead reached : σ} {error : ε} {invalid : String → ε}
    (opened : ops.openFile path .writeNew before = .ok output created)
    (valid : layout.Valid)
    (targets : 0 < options.dataTarget ∧ options.dataTarget ≤ maxRowSize ∧
      0 < options.leafTarget ∧ options.leafTarget ≤ maxRowSize)
    (stages : (Writer.mk crc layout (ops.sink output) invalid options).InputReached
      nextRow atRead maxFileSize {} created)
    (failed : nextRow atRead = .error error reached) :
    buildFileWith ops crc path layout nextRow invalid options before =
      match ops.remove path reached with
      | .ok _ after | .error _ after => .error error after := by
  apply buildFileWith_writeErrorWith opened
  simp [buildStream, valid, targets, Bind.bind, EStateM.bind, stages.aborts failed]

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
  change ops.openFile path .writeNew before = _ at openRan
  change buildStream crc layout (ops.sink output) nextRow id options created = _ at writeRan
  change ops.sync output written = _ at syncRan
  simp only [EStateM.run, openRan, writeRan, syncRan, failedOutput]
  cases ops.remove path reached <;> rfl

end ImmutableSSTable.Unified
