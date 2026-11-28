import Alvoki.Experiments.SSTable.Proofs.UnifiedNativeEndToEnd
import Alvoki.Experiments.SSTable.Proofs.Typed
import Alvoki.Experiments.SSTable.Recursive.NativeReadProofs
import Alvoki.Experiments.SSTable.Recursive.WriterProofs

namespace ImmutableSSTable.Recursive

open Unified (Checksum Layout Ref NativeWriteEffects NativeWriteM NativeWriteState
  ModelFile ModelM modelSink modelNext checksumSize dataSize entrySize)

private def project (state : NativeWriteState handle inode) : ModelFile :=
  ⟨state.rows, state.appended⟩

private def Simulates (before after : NativeWriteState handle inode → Prop)
    (actual : NativeWriteM handle inode α) (exactModel : ModelM α) : Prop :=
  ∀ s t value, before s → actual.run s = .ok value t →
    exactModel.run (project s) = .ok (value, (project t)) ∧ after t

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
  change ((exactModel.run (project before)).bind _) = _
  rw [firstModel]
  exact restModel

private theorem Simulates.post
    {p q r : NativeWriteState handle inode → Prop}
    {actual : NativeWriteM handle inode α} {exactModel : ModelM α}
    (sim : Simulates p q actual exactModel) (implies : ∀ state, q state → r state) :
    Simulates p r actual exactModel := fun s t value initial run =>
  let ⟨exact, reached⟩ := sim s t value initial run
  ⟨exact, implies t reached⟩

private theorem Simulates.pure {condition : NativeWriteState handle inode → Prop} (value : α) :
    Simulates condition condition (pure value) (pure value) := by
  intro before after result initial run
  cases run
  exact ⟨rfl, initial⟩

private theorem Simulates.throw {p q : NativeWriteState handle inode → Prop}
    (error : String) (action : ModelM α) : Simulates p q (throw error) action := by
  intro before after result initial run
  cases run

private def OwnsWithRows (path : System.FilePath) (output : handle) (identity : inode)
    (rowsInv : List Entry → Prop) (state : NativeWriteState handle inode) : Prop :=
  state.BoundTo path output identity ∧ rowsInv state.rows

private theorem append_sim {ops : OutputOps (NativeWriteM handle inode) handle}
    {path : System.FilePath} {nextRow : NativeWriteM handle inode (Option Entry)}
    (effects : NativeWriteEffects ops path nextRow) (output : handle) (identity : inode)
    (rowsInv : List Entry → Prop) (bytes : ByteArray) :
    Simulates (OwnsWithRows path output identity rowsInv) (OwnsWithRows path output identity rowsInv)
      (ops.append output bytes) (modelSink.write bytes) := by
  intro before after value same run
  cases value
  rw [effects.append output identity bytes before after same.1 run]
  exact ⟨rfl, same⟩

private theorem flush_sim {ops : OutputOps (NativeWriteM handle inode) handle}
    {path : System.FilePath} {nextRow : NativeWriteM handle inode (Option Entry)}
    (effects : NativeWriteEffects ops path nextRow) (output : handle) (identity : inode)
    (rowsInv : List Entry → Prop) :
    Simulates (OwnsWithRows path output identity rowsInv)
      (fun state => OwnsWithRows path output identity rowsInv state ∧ state.flushed = true)
      (ops.flush output) modelSink.flush := by
  intro before after value same run
  cases value
  rw [effects.flush output identity before after same.1 run]
  exact ⟨rfl, same, rfl⟩

private theorem next_sim {ops : OutputOps (NativeWriteM handle inode) handle}
    {path : System.FilePath} {nextRow : NativeWriteM handle inode (Option Entry)}
    (effects : NativeWriteEffects ops path nextRow) (output : handle) (identity : inode) :
    Simulates (OwnsWithRows path output identity (fun _ => True))
      (OwnsWithRows path output identity (fun _ => True)) nextRow modelNext := by
  intro before after row same run
  obtain ⟨returned, state⟩ := effects.next output identity before after row same.1 run
  rw [returned, state]
  refine ⟨?_, same⟩
  cases rows : before.rows <;> simp [modelNext, project, rows, StateT.run]

private structure SinkSimulation {handle inode : Type} (sink : Sink (NativeWriteM handle inode))
    (bound ready : NativeWriteState handle inode → Prop) : Prop where
  append : ∀ bytes, Simulates bound bound (sink.write bytes) (modelSink.write bytes)
  flush : Simulates bound ready sink.flush modelSink.flush

private def modelWriter (crc : Checksum) (layout : Layout) (options : BuildOptions) :
    Writer ModelM String :=
  ⟨crc, layout, modelSink, id, options⟩

private def nativeWriter (crc : Checksum) (layout : Layout) (options : BuildOptions)
    (sink : Sink (NativeWriteM handle inode)) : Writer (NativeWriteM handle inode) String :=
  ⟨crc, layout, sink, id, options⟩

private theorem writePacket_sim (crc : Checksum) (layout : Layout) (options : BuildOptions)
    {sink : Sink (NativeWriteM handle inode)} {bound ready : NativeWriteState handle inode → Prop}
    (agreement : SinkSimulation sink bound ready) (kind : UInt64) (limit offset : Nat)
    (body : ByteArray) :
    Simulates bound bound ((nativeWriter crc layout options sink).writePacket kind limit offset body)
      ((modelWriter crc layout options).writePacket kind limit offset body) := by
  by_cases packet : body.size + checksumSize ≤ limit
  · by_cases file : offset + (body.size + checksumSize) + footerPacketSize ≤ maxFileSize
    · simp only [Writer.writePacket, packet, file, ↓reduceIte, nativeWriter, modelWriter]
      exact (agreement.append _).bind (fun _ => .pure _)
    · simp only [Writer.writePacket, packet, file, ↓reduceIte, nativeWriter, modelWriter]
      intro before after value initial run
      cases run
  · simp only [Writer.writePacket, packet, ↓reduceIte, nativeWriter, modelWriter]
    intro before after value initial run
    cases run

private theorem writePage_sim (crc : Checksum) (layout : Layout) (options : BuildOptions)
    {sink : Sink (NativeWriteM handle inode)} {bound ready : NativeWriteState handle inode → Prop}
    (agreement : SinkSimulation sink bound ready) (height offset : Nat) (page : Page) :
    Simulates bound bound ((nativeWriter crc layout options sink).writePage height offset page)
      ((modelWriter crc layout options).writePage height offset page) := by
  unfold Writer.writePage
  split
  · split
    · exact (writePacket_sim crc layout options agreement _ _ _ _).bind (fun _ => .pure _)
    · exact Simulates.throw _ _
  · exact Simulates.throw _ _

private theorem push_sim (crc : Checksum) (layout : Layout) (options : BuildOptions)
    {sink : Sink (NativeWriteM handle inode)} {bound ready : NativeWriteState handle inode → Prop}
    (agreement : SinkSimulation sink bound ready) (height offset : Nat) (ref : Ref)
    (pages : List Page) (fuel : Nat) :
    Simulates bound bound ((nativeWriter crc layout options sink).push height offset ref pages fuel)
      ((modelWriter crc layout options).push height offset ref pages fuel) := by
  induction fuel generalizing height offset ref pages with
  | zero =>
    simp only [Writer.push, nativeWriter, modelWriter]
    exact Simulates.throw _ _
  | succ fuel ih =>
    cases pages with
    | nil => exact Simulates.pure _
    | cons page upper =>
      by_cases flush : page.shouldFlush ref options.indexTarget = true
      · simp only [Writer.push, show (nativeWriter crc layout options sink).options = options from rfl,
          show (modelWriter crc layout options).options = options from rfl, flush, ↓reduceIte]
        apply (writePage_sim crc layout options agreement height offset page).bind
        rintro ⟨promoted, next⟩
        exact (ih (height + 1) next promoted upper).bind (fun _ => .pure _)
      · simpa only [Writer.push, show (nativeWriter crc layout options sink).options = options from rfl,
          show (modelWriter crc layout options).options = options from rfl, flush, Bool.false_eq_true, ↓reduceIte]
          using (Simulates.pure (condition := bound) (offset, page.add ref :: upper))

private theorem flushData_sim (crc : Checksum) (layout : Layout) (options : BuildOptions)
    {sink : Sink (NativeWriteM handle inode)} {bound ready : NativeWriteState handle inode → Prop}
    (agreement : SinkSimulation sink bound ready) (state : BuilderState) :
    Simulates bound bound ((nativeWriter crc layout options sink).flushData state)
      ((modelWriter crc layout options).flushData state) := by
  cases tail : state.data.back? with
  | none => simpa only [Writer.flushData, tail] using (Simulates.pure (condition := bound) state)
  | some last =>
    simp only [Writer.flushData, tail,
      show (nativeWriter crc layout options sink).layout = layout from rfl,
      show (modelWriter crc layout options).layout = layout from rfl]
    apply (writePacket_sim crc layout options agreement dataKind maxRowSize state.offset _).bind
    intro next
    exact (push_sim crc layout options agreement 1 next _ state.pages maxHeight).bind
      (fun _ => .pure _)

private theorem accept_sim (crc : Checksum) (layout : Layout) (options : BuildOptions)
    {sink : Sink (NativeWriteM handle inode)} {bound ready : NativeWriteState handle inode → Prop}
    (agreement : SinkSimulation sink bound ready) (state : BuilderState) (row : Entry) :
    Simulates bound bound ((nativeWriter crc layout options sink).accept state row)
      ((modelWriter crc layout options).accept state row) := by
  have actualLayout : (nativeWriter crc layout options sink).layout = layout := rfl
  have modelLayout : (modelWriter crc layout options).layout = layout := rfl
  have actualOptions : (nativeWriter crc layout options sink).options = options := rfl
  have modelOptions : (modelWriter crc layout options).options = options := rfl
  cases check : ({ lastKey := state.lastKey } : Unified.BuilderState).checkRow layout row with
  | error error =>
    simp only [Writer.accept, actualLayout, modelLayout, check]
    exact Simulates.throw _ _
  | ok accepted =>
    cases accepted
    simp only [Writer.accept, actualLayout, modelLayout, actualOptions, modelOptions, check]
    by_cases flush : (!state.data.isEmpty &&
        decide (dataSize layout (state.data.size + 1)
          (state.payloadBytes + entrySize layout row) > options.dataTarget)) = true
    · rw [ite_eq_left flush, ite_eq_left flush]
      exact (flushData_sim crc layout options agreement state).bind (fun _ => .pure _)
    · rw [ite_eq_right flush, ite_eq_right flush]
      exact (Simulates.pure state).bind (fun _ => .pure _)

private theorem bind_supplier {bound ready : NativeWriteState handle inode → Prop}
    {supply : NativeWriteM handle inode (Option Entry)}
    {next : Option Entry → NativeWriteM handle inode α}
    {nextModel : Option Entry → ModelM α}
    (observed : Simulates bound bound supply modelNext)
    (continuation : ∀ opt, Simulates (fun state => bound state ∧ (opt = none → state.rows = []))
      ready (next opt) (nextModel opt)) :
    Simulates bound ready (supply >>= next) (modelNext >>= nextModel) := by
  intro before after result initial run
  obtain ⟨opt, middle, supplied, continued⟩ := actual_bind_ok run
  obtain ⟨modelSupplied, held⟩ := observed before middle opt initial supplied
  have eof : opt = none → middle.rows = [] := by
    intro none
    subst opt
    cases rows : before.rows with
    | nil =>
      have same : project before = project middle := by
        simpa [modelNext, StateT.run, project, rows] using modelSupplied
      exact (congrArg ModelFile.rows same.symm).trans rows
    | cons row rest =>
      simp [modelNext, StateT.run, project, rows] at modelSupplied
  obtain ⟨modelContinued, done⟩ := continuation opt middle after result ⟨held, eof⟩ continued
  refine ⟨?_, done⟩
  change ((modelNext.run (project before)).bind _) = _
  rw [modelSupplied]
  exact modelContinued

private theorem streamRows_sim (crc : Checksum) (layout : Layout) (options : BuildOptions)
    {sink : Sink (NativeWriteM handle inode)} {bound ready : NativeWriteState handle inode → Prop}
    (agreement : SinkSimulation sink bound ready) (supply : NativeWriteM handle inode (Option Entry))
    (supplied : Simulates bound bound supply modelNext) (state : BuilderState) (room : Nat) :
    Simulates bound (fun state => bound state ∧ state.rows = [])
      ((nativeWriter crc layout options sink).streamRows supply state room)
      ((modelWriter crc layout options).streamRows modelNext state room) := by
  induction room generalizing state with
  | zero =>
    simp only [Writer.streamRows]
    apply bind_supplier supplied
    intro opt before after value initial run
    cases opt
    · cases run
      exact ⟨rfl, initial.1, initial.2 rfl⟩
    · cases run
  | succ room ih =>
    simp only [Writer.streamRows]
    apply bind_supplier supplied
    intro opt
    cases opt with
    | none =>
      intro before after value initial run
      cases run
      exact ⟨rfl, initial.1, initial.2 rfl⟩
    | some row =>
      intro before after value initial run
      exact ((accept_sim crc layout options agreement state row).bind (fun current => ih current))
        before after value initial.1 run

private theorem finishPages_sim (crc : Checksum) (layout : Layout) (options : BuildOptions)
    {sink : Sink (NativeWriteM handle inode)} {bound ready : NativeWriteState handle inode → Prop}
    (agreement : SinkSimulation sink bound ready) (height offset : Nat) (pages : List Page)
    (fuel : Nat) :
    Simulates bound bound ((nativeWriter crc layout options sink).finishPages height offset pages fuel)
      ((modelWriter crc layout options).finishPages height offset pages fuel) := by
  induction fuel generalizing height offset pages with
  | zero =>
    simp only [Writer.finishPages, nativeWriter, modelWriter]
    exact Simulates.throw _ _
  | succ fuel ih =>
    cases pages with
    | nil => exact Simulates.pure _
    | cons page upper =>
      simp only [Writer.finishPages]
      apply (writePage_sim crc layout options agreement height offset page).bind
      rintro ⟨ref, next⟩
      by_cases empty : upper.isEmpty = true
      · simpa only [empty, ↓reduceIte] using
          (Simulates.pure (condition := bound) (height, ref.offset, ref.size))
      · simp only [empty]
        apply (push_sim crc layout options agreement (height + 1) next ref upper fuel).bind
        rintro ⟨stop, remaining⟩
        exact ih (height + 1) stop remaining

private theorem buildStream_sim (crc : Checksum) (layout : Layout) (options : BuildOptions)
    {sink : Sink (NativeWriteM handle inode)}
    {bound streamingReady drained ready : NativeWriteState handle inode → Prop}
    (streaming : SinkSimulation sink bound streamingReady)
    (finishing : SinkSimulation sink drained ready)
    (afterEOF : ∀ state, bound state → state.rows = [] → drained state)
    (supply : NativeWriteM handle inode (Option Entry))
    (supplied : Simulates bound bound supply modelNext) :
    Simulates bound ready (buildStream crc layout sink supply id options)
      (buildStream crc layout modelSink modelNext id options) := by
  by_cases valid : layout.Valid
  · by_cases targets : 0 < options.dataTarget ∧ options.dataTarget ≤ maxRowSize ∧
        0 < options.indexTarget ∧ options.indexTarget ≤ maxRowSize
    · simp only [buildStream, valid, targets, ↓reduceIte]
      have streamed := (streamRows_sim crc layout options streaming supply supplied {} maxFileSize).post
        (fun state observed => afterEOF state observed.1 observed.2)
      refine streamed.bind fun state =>
        (flushData_sim crc layout options finishing state).bind fun flushed =>
          (finishPages_sim crc layout options finishing 1 flushed.offset flushed.pages maxHeight).bind ?_
      rintro ⟨height, offset, size⟩
      exact (finishing.append _).bind fun _ => finishing.flush.bind fun _ => .pure _
    · simp only [buildStream, valid, targets, ↓reduceIte]
      intro before after value initial run
      cases run
  · simp only [buildStream, valid, ↓reduceIte]
    intro before after value initial run
    cases run

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

/-- Every successful native build follows the same recursive writer schedule
in the append-only model. The recorded inode belongs to the descriptor
returned at exclusive creation, and its synchronized bytes are exactly the
bytes appended after consuming the original supplier through EOF. -/
theorem buildFileWith_exact {ops : OutputOps (NativeWriteM handle inode) handle}
    {path : System.FilePath} {nextRow : NativeWriteM handle inode (Option Entry)}
    {crc : Checksum} {layout : Layout} {options : BuildOptions}
    {before after : NativeWriteState handle inode} {count : Nat}
    (effects : NativeWriteEffects ops path nextRow)
    (run : (buildFileWith ops crc path layout nextRow id options).run before = .ok count after) :
    before.binding = none ∧ after.rows = [] ∧ after.flushed = true ∧
      (buildStream crc layout modelSink modelNext id options).run { rows := before.rows } =
        .ok (count, { rows := [], bytes := after.appended }) ∧
      ∃ output identity created, (ops.openFile path .writeNew).run before = .ok output created ∧
        after.BoundTo path output identity ∧ after.durable = some (identity, after.appended) := by
  obtain ⟨output, created, written, openRan, writeRan, syncRan⟩ := freshOutput_ok run
  obtain ⟨fresh, identity, createdState⟩ := effects.create before created output openRan
  have owned : OwnsWithRows path output identity (fun _ => True) created := by
    simp [createdState, OwnsWithRows, NativeWriteState.BoundTo]
  let streaming : SinkSimulation (ops.sink output)
      (OwnsWithRows path output identity (fun _ => True))
      (fun state => OwnsWithRows path output identity (fun _ => True) state ∧ state.flushed = true) :=
    ⟨append_sim effects output identity _, flush_sim effects output identity _⟩
  let finishing : SinkSimulation (ops.sink output)
      (OwnsWithRows path output identity (· = []))
      (fun state => OwnsWithRows path output identity (· = []) state ∧ state.flushed = true) :=
    ⟨append_sim effects output identity _, flush_sim effects output identity _⟩
  obtain ⟨exact, ⟨held, eof⟩, flushed⟩ :=
    buildStream_sim crc layout options streaming finishing (fun _ live empty => ⟨live.1, empty⟩)
      nextRow (next_sim effects output identity) created written count owned writeRan
  have durable := effects.sync output identity written after held flushed syncRan
  have initially : project created = { rows := before.rows } := by rw [createdState]; rfl
  have finalProjection : project written = { rows := [], bytes := written.appended } := by simp [project, eof]
  rw [initially, finalProjection] at exact
  rw [durable]
  exact ⟨fresh, eof, flushed, exact, output, identity, created, openRan, held, rfl⟩

/-- The original sync failure is returned after cleanup from the reached
state, including a failure observed after the barrier has taken effect. -/
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

/-- A successful sync establishes the recursive image of the original
supplier at the inode of the descriptor returned by exclusive creation. -/
theorem buildFileWith_refines {ops : OutputOps (NativeWriteM writer inode) writer}
    {path : System.FilePath} {nextRow : NativeWriteM writer inode (Option Entry)}
    {crc : Checksum} {layout : Layout} {options : BuildOptions}
    {before after : NativeWriteState writer inode} {count : Nat}
    (effects : NativeWriteEffects ops path nextRow)
    (run : (buildFileWith ops crc path layout nextRow id options).run before = .ok count after) :
    before.binding = none ∧ after.rows = [] ∧ count = before.rows.length ∧
      Image layout crc after.appended before.rows ∧
      ∃ output identity, after.BoundTo path output identity ∧ after.flushed = true ∧
        after.durable = some (identity, after.appended) := by
  obtain ⟨fresh, exhausted, flushed, exact, output, identity, _, _, bound, durable⟩ :=
    buildFileWith_exact effects run
  have model : modelBuild crc layout before.rows options = .ok (count, after.appended) := by
    unfold modelBuild
    rw [exact]
    rfl
  obtain ⟨countEq, image⟩ := modelBuild_ok model
  exact ⟨fresh, exhausted, countEq, image, output, identity, bound, flushed, durable⟩

/-- Local read contracts are supplied for the inode and bytes actually
established by the writer. The frame survives successful and failed reads. -/
theorem buildFileWith_lookup_framed {outputOps : OutputOps (NativeWriteM writer inode) writer}
    {path readPath : System.FilePath} {nextRow : NativeWriteM writer inode (Option Entry)}
    {crc : Checksum} {layout : Layout} {options : BuildOptions}
    {before after : NativeWriteState writer inode} {count : Nat}
    {readOps : ReadPrimitives (ReadM σ) reader} {frame : σ → Prop}
    {inodeAt : reader → σ → Option inode}
    (effects : NativeWriteEffects outputOps path nextRow)
    (built : (buildFileWith outputOps crc path layout nextRow id options).run before = .ok count after)
    (reads : ∀ identity bytes, after.durable = some (identity, bytes) →
      ReadEffects readOps readPath frame (fun held state => inodeAt held state = some identity) bytes)
    (key : ByteArray) :
    ReadPost frame
      (openCheckedWith readOps crc readPath layout.tableId >>= fun handle => handle.table.lookup key)
      (· = Contents.lookup before.rows key) := by
  obtain ⟨_, _, _, image, _, identity, _, _, durable⟩ := buildFileWith_refines effects built
  exact checkedNativeLookup (reads identity after.appended durable) image key

/-- The healthy reader interprets the durable contents of the inode selected
by its acquired description. All three public operations use that image. -/
theorem buildFileWith_open_represents [DecidableEq inode]
    {outputOps : OutputOps (NativeWriteM writer inode) writer}
    {path readPath : System.FilePath} {nextRow : NativeWriteM writer inode (Option Entry)}
    {crc : Checksum} {layout : Layout} {options : BuildOptions}
    {before after : NativeWriteState writer inode} {count : Nat}
    {acquire : System.FilePath → IO.FS.Mode → ReadM σ reader}
    {start acquired : σ} {held : reader} {inodeAt : reader → Option inode}
    (effects : NativeWriteEffects outputOps path nextRow)
    (built : (buildFileWith outputOps crc path layout nextRow id options).run before = .ok count after)
    (opened : acquire readPath .read start = .ok held acquired)
    (selected : ∀ output identity, after.BoundTo path output identity → inodeAt held = some identity) :
    count = before.rows.length ∧
    ∃ handle, openCheckedWith ((after.readSnapshot inodeAt).primitives acquire)
      crc readPath layout.tableId start = .ok handle acquired ∧
      handle.table.Represents before.rows := by
  obtain ⟨_, _, countEq, image, output, identity, bound, _, durable⟩ :=
    buildFileWith_refines effects built
  let snapshot := after.readSnapshot inodeAt
  have contents : snapshot.contents identity = some after.appended := by
    simp [snapshot, NativeWriteState.readSnapshot, durable]
  have observed := snapshot.readsExactly acquire (selected output identity bound) contents image.extent
  obtain ⟨handle, checked, represents⟩ := image.open_represents (observed.source_serves image.extent)
  refine ⟨countEq, handle, ?_, represents⟩
  have accepted : (snapshot.primitives acquire).openFile readPath .read start = .ok held acquired := opened
  change openCheckedWith (snapshot.primitives acquire) crc readPath layout.tableId start =
    .ok handle acquired
  simp [openCheckedWith, Bind.bind, EStateM.bind, accepted, checked, EStateM.pure, Pure.pure]

theorem buildFileWith_open_typed_represents [DecidableEq κ] [DecidableEq inode]
    {outputOps : OutputOps (NativeWriteM writer inode) writer}
    {path readPath : System.FilePath} {nextRow : NativeWriteM writer inode (Option Entry)}
    {crc : Checksum} {layout : Layout} {options : BuildOptions}
    {before after : NativeWriteState writer inode} {count : Nat}
    {acquire : System.FilePath → IO.FS.Mode → ReadM σ reader}
    {start acquired : σ} {held : reader} {inodeAt : reader → Option inode}
    (effects : NativeWriteEffects outputOps path nextRow)
    (built : (buildFileWith outputOps crc path layout nextRow id options).run before = .ok count after)
    (opened : acquire readPath .read start = .ok held acquired)
    (selected : ∀ output identity, after.BoundTo path output identity → inodeAt held = some identity)
    {rows : List (κ × ν)} {less : κ → κ → Prop} {keys : Codec κ} {values : Codec ν}
    (supplier : before.rows = rows.map (Entry.encode keys values))
    (keyLaw : keys.Roundtrips) (valueLaw : values.Roundtrips) (orderLaw : keys.PreservesOrder less) :
    count = rows.length ∧
    ∃ handle, openCheckedWith ((after.readSnapshot inodeAt).primitives acquire)
      crc readPath layout.tableId start = .ok handle acquired ∧
      (TypedTable.mk handle.table keys values).Represents less rows := by
  obtain ⟨countEq, handle, checked, represents⟩ :=
    buildFileWith_open_represents effects built opened selected
  refine ⟨by simpa [supplier] using countEq, handle, checked, ?_⟩
  exact TypedTable.represents_of_bytes (supplier ▸ represents) keyLaw valueLaw orderLaw

/-- A fault reading the footer propagates its original error and state
through checked open and the lookup continuation. -/
private theorem checkedLookup_footerError
    {readOps : ReadPrimitives (ReadM σ) reader} {path : System.FilePath}
    {crc : Checksum} {id : UInt64} {key : ByteArray}
    {start opened sized reached : σ} {held : reader} {size : Nat} {error : String}
    (openRan : readOps.openFile path .read start = .ok held opened)
    (sizeRan : readOps.size held opened = .ok size sized)
    (fits : footerPacketSize ≤ size ∧ size ≤ maxFileSize)
    (failed : readOps.pread held (size - footerPacketSize).toUInt64 footerPacketSize.toUSize sized =
      .error error reached) :
    (openCheckedWith readOps crc path id >>= fun handle => handle.table.lookup key) start =
      .error error reached := by
  have sourceSize : (readOps.source held).size opened = .ok size sized := sizeRan
  have sourceFailure := ReadPrimitives.source_pread_error (by decide : footerPacketSize ≤ maxRowSize)
    (show size - footerPacketSize + footerPacketSize ≤ maxFileSize by omega) failed
  have exactFailure : readExact (readOps.source held) (size - footerPacketSize) footerPacketSize sized =
      .error error reached := by
    simp [readExact, Bind.bind, EStateM.bind, sourceFailure]
  have footerFailure : readFooter (readOps.source held) crc opened = .error error reached := by
    simp [readFooter, Bind.bind, EStateM.bind, sourceSize, fits, exactFailure]
  have checkedFailure : openChecked (readOps.source held) crc id opened = .error error reached := by
    simp [openChecked, Bind.bind, EStateM.bind, footerFailure]
  simp [openCheckedWith, Bind.bind, EStateM.bind, openRan, checkedFailure]

theorem buildFileWith_lookup_footerError {outputOps : OutputOps (NativeWriteM writer inode) writer}
    {path readPath : System.FilePath} {nextRow : NativeWriteM writer inode (Option Entry)}
    {crc : Checksum} {layout : Layout} {options : BuildOptions}
    {before after : NativeWriteState writer inode} {count : Nat}
    {readOps : ReadPrimitives (ReadM σ) reader} {frame : σ → Prop}
    {inodeAt : reader → σ → Option inode} {key : ByteArray}
    {start opened sized reached : σ} {held : reader} {size : Nat} {error : String}
    (effects : NativeWriteEffects outputOps path nextRow)
    (built : (buildFileWith outputOps crc path layout nextRow id options).run before = .ok count after)
    (reads : ∀ identity bytes, after.durable = some (identity, bytes) →
      ReadEffects readOps readPath frame (fun held state => inodeAt held state = some identity) bytes)
    (initialFrame : frame start)
    (openRan : readOps.openFile readPath .read start = .ok held opened)
    (sizeRan : readOps.size held opened = .ok size sized)
    (fits : footerPacketSize ≤ size ∧ size ≤ maxFileSize)
    (failed : readOps.pread held (size - footerPacketSize).toUInt64 footerPacketSize.toUSize sized =
      .error error reached) :
    (openCheckedWith readOps crc readPath layout.tableId >>= fun handle => handle.table.lookup key) start =
      .error error reached ∧ frame reached := by
  have surfaced := checkedLookup_footerError (crc := crc) (id := layout.tableId) (key := key)
    openRan sizeRan fits failed
  have framed := buildFileWith_lookup_framed effects built reads key start initialFrame
  rw [surfaced] at framed
  exact ⟨surfaced, framed⟩

end ImmutableSSTable.Recursive
