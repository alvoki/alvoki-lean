import Alvoki.Experiments.SSTable.UnifiedBuilder

namespace ImmutableSSTable.Unified.BuilderRelation

/-- A relation on two executions of the streaming writer. The stage becomes
true only at the final flush. All control decisions are shared pure code. -/
structure Rules (m n : Type → Type) [Monad m] [Monad n] [MonadExceptOf ε m] [MonadExceptOf δ n]
    (invalid : String → ε) (problem : String → δ) where
  rel : {α : Type} → Bool → Bool → m α → n α → Prop
  ret : ∀ {α p} (x : α), rel p p (pure x) (pure x)
  seq : ∀ {α β p q r} {a : m α} {b : n α} {f : α → m β} {g : α → n β},
    rel p q a b → (∀ x, rel q r (f x) (g x)) → rel p r (a >>= f) (b >>= g)
  raise : ∀ {α p q} (e : String), rel (α := α) p q (throw (invalid e)) (throw (problem e))

  abort : ∀ {α p q} (e : String) (f : Unit → m α) (g : Unit → n α),
    rel p q (throw (invalid e) >>= f) (throw (problem e) >>= g)

variable {m n : Type → Type} [Monad m] [Monad n] [MonadExceptOf ε m] [MonadExceptOf δ n]
variable {invalid : String → ε} {problem : String → δ}
variable {law : Rules m n invalid problem} {left : Sink m} {right : Sink n}

structure SinkAgreement (law : Rules m n invalid problem) (left : Sink m) (right : Sink n) : Prop where
  append : ∀ bytes, law.rel false false (left.write bytes) (right.write bytes)
  flush : law.rel false true left.flush right.flush

private def writer [Monad f] (crc : Checksum) (layout : Layout) (options : BuildOptions)
    (sink : Sink f) (error : String → e) : Writer f e := ⟨crc,layout,sink,error,options⟩

private theorem writePacket_sim (crc : Checksum) (layout : Layout) (options : BuildOptions)
    (agreement : SinkAgreement law left right) (kind : UInt64) (offset : Nat) (body : ByteArray) :
    law.rel false false ((writer crc layout options left invalid).writePacket kind offset body)
      ((writer crc layout options right problem).writePacket kind offset body) := by
  by_cases packet : body.size + checksumSize ≤ maxRowSize
  · by_cases file : offset + (body.size + checksumSize) + footerPacketSize ≤ maxFileSize
    · simp only [Writer.writePacket, packet, file, ↓reduceIte, writer]
      exact law.seq (agreement.append _) (fun _ => law.ret _)
    · simp only [Writer.writePacket, packet, file, ↓reduceIte, writer]
      exact law.abort _ _ _
  · simp only [Writer.writePacket, packet, ↓reduceIte, writer]
    exact law.abort _ _ _

private theorem flushLeaf_sim (crc : Checksum) (layout : Layout) (options : BuildOptions)
    (agreement : SinkAgreement law left right) (state : BuilderState) :
    law.rel false false ((writer crc layout options left invalid).flushLeaf state)
      ((writer crc layout options right problem).flushLeaf state) := by
  cases head : state.leaf[0]? with
  | none => simpa only [Writer.flushLeaf, head] using (law.ret (p := false) state)
  | some first =>
    cases tail : state.leaf.back? with
    | none =>
      simpa only [Writer.flushLeaf, head, tail] using (law.ret (p := false) state)
    | some last =>
      by_cases fits : state.rootBytes + indexEntrySize last.lastKey + checksumSize ≤ maxRowSize
      · simp only [Writer.flushLeaf, head, tail, fits, ↓reduceIte]
        exact law.seq (writePacket_sim crc layout options agreement 2 state.offset _) (fun _ => law.ret _)
      · simp only [Writer.flushLeaf, head, tail, fits, ↓reduceIte, writer]
        exact law.abort _ _ _

private theorem flushData_sim (crc : Checksum) (layout : Layout) (options : BuildOptions)
    (agreement : SinkAgreement law left right) (state : BuilderState) :
    law.rel false false ((writer crc layout options left invalid).flushData state)
      ((writer crc layout options right problem).flushData state) := by
  cases tail : state.data.back? with
  | none => simpa only [Writer.flushData, tail] using (law.ret (p := false) state)
  | some last =>
    simp only [Writer.flushData, tail,
      show (writer crc layout options left invalid).layout = layout from rfl,
      show (writer crc layout options right problem).layout = layout from rfl,
      show (writer crc layout options left invalid).options = options from rfl,
      show (writer crc layout options right problem).options = options from rfl]
    apply law.seq
    · by_cases flush : (!state.leaf.isEmpty &&
          decide (state.leafBytes + indexEntrySize last.key + checksumSize > options.leafTarget)) = true
      · simpa only [flush, ↓reduceIte] using flushLeaf_sim crc layout options agreement state
      · simpa only [flush, Bool.false_eq_true, ↓reduceIte] using (law.ret (p := false) state)
    · intro current
      exact law.seq (writePacket_sim crc layout options agreement 1 current.offset _) (fun _ => law.ret _)

private theorem accept_sim (crc : Checksum) (layout : Layout) (options : BuildOptions)
    (agreement : SinkAgreement law left right) (state : BuilderState) (row : Entry) :
    law.rel false false ((writer crc layout options left invalid).accept state row)
      ((writer crc layout options right problem).accept state row) := by
  have actualLayout : (writer crc layout options left invalid).layout = layout := rfl
  have modelLayout : (writer crc layout options right problem).layout = layout := rfl
  have actualOptions : (writer crc layout options left invalid).options = options := rfl
  have modelOptions : (writer crc layout options right problem).options = options := rfl
  cases check : state.checkRow layout row with
  | error error =>
    simp only [Writer.accept, actualLayout, modelLayout, check]
    exact law.raise _
  | ok accepted =>
    cases accepted
    simp only [Writer.accept, actualLayout, modelLayout, actualOptions, modelOptions, check]
    apply law.seq
    · by_cases flush : (!state.data.isEmpty &&
          decide (dataSize layout (state.data.size + 1)
            (state.payloadBytes + entrySize layout row) > options.dataTarget)) = true
      · simpa only [flush, ↓reduceIte] using flushData_sim crc layout options agreement state
      · simpa only [flush, Bool.false_eq_true, ↓reduceIte] using (law.ret (p := false) state)
    · intro current
      exact law.ret _

private theorem streamRows_sim (crc : Checksum) (layout : Layout) (options : BuildOptions)
    (agreement : SinkAgreement law left right) (supply : m (Option Entry)) (modelNext : n (Option Entry))
    (supplied : law.rel false false supply modelNext) (state : BuilderState) (room : Nat) :
    law.rel false false ((writer crc layout options left invalid).streamRows supply state room)
      ((writer crc layout options right problem).streamRows modelNext state room) := by
  induction room generalizing state with
  | zero =>
    simp only [Writer.streamRows]
    exact law.seq supplied fun option => by
      cases option with
      | none => exact law.ret _
      | some row =>
        exact law.abort _ _ _
  | succ room induction =>
    simp only [Writer.streamRows]
    refine law.seq supplied ?_
    intro option
    cases option with
    | none => exact law.ret _
    | some row =>
      exact law.seq (accept_sim crc layout options agreement state row)
        (fun current => induction current)

private theorem finish_sim (crc : Checksum) (layout : Layout) (options : BuildOptions)
    (agreement : SinkAgreement law left right) (state : BuilderState) :
    law.rel false true ((writer crc layout options left invalid).finish state)
      ((writer crc layout options right problem).finish state) := by
  simp only [Writer.finish]
  refine law.seq (flushData_sim crc layout options agreement state) fun afterData =>
    law.seq (flushLeaf_sim crc layout options agreement afterData) fun afterLeaf => ?_
  apply law.seq
  · by_cases empty : afterLeaf.root.isEmpty = true
    · simpa only [empty, ↓reduceIte] using
        (law.ret (p := false) ((0, 0) : Nat × Nat))
    · simp only [empty]
      exact law.seq (writePacket_sim crc layout options agreement 3 afterLeaf.offset _)
        (fun _ => law.ret _)
  · intro root
    cases root
    exact law.seq (agreement.append _) fun _ => law.seq agreement.flush fun _ => law.ret _

theorem stream (crc : Checksum) (layout : Layout) (options : BuildOptions)
    (agreement : SinkAgreement law left right) (supply : m (Option Entry)) (modelNext : n (Option Entry))
    (supplied : law.rel false false supply modelNext) :
    law.rel false true (buildStream crc layout left supply invalid options)
      (buildStream crc layout right modelNext problem options) := by
  by_cases valid : layout.Valid
  · by_cases targets : 0 < options.dataTarget ∧ options.dataTarget ≤ maxRowSize ∧
        0 < options.leafTarget ∧ options.leafTarget ≤ maxRowSize
    · simp only [buildStream, valid, targets, ↓reduceIte]
      exact law.seq (streamRows_sim crc layout options agreement supply modelNext supplied {} maxFileSize)
        (fun current => finish_sim crc layout options agreement current)
    · simp only [buildStream, valid, targets, ↓reduceIte]
      exact law.abort _ _ _
  · simp only [buildStream, valid, ↓reduceIte]
    exact law.abort _ _ _

end ImmutableSSTable.Unified.BuilderRelation
