import Init

namespace FileRead

abbrev World := Void IO.RealWorld

/-- A read-only primitive may advance the runtime, including a descriptor
cursor. It preserves the protected namespaces and their selected storage state. -/
def Effect (owned : World → Prop) (state : World → σ)
    (action : IO α) (value : World → α → World → Prop) (start : World) : Prop :=
  match action start with
  | .ok x t => owned t ∧ state t = state start ∧ value start x t
  | .error _ t => owned t ∧ state t = state start

/-- A pathname open binds a fresh cursor to the protected contents. The
Lean 4.36 standard library EOF loop is partial; its local runtime
contract concerns the remaining bytes of that same descriptor. -/
structure Primitives (path : System.FilePath) (owned : World → Prop)
    (state : World → σ) (contents : σ → ByteArray) where
  source : IO.FS.Handle → ByteArray → Nat → World → Prop
  metadata : ∀ w, owned w →
    Effect owned state path.metadata (fun _ _ _ => True) w
  openFile : ∀ w, owned w → Effect owned state (IO.FS.Handle.mk path .read)
    (fun start h after => source h (contents (state start)) 0 after) w
  chunk : ∀ h bytes (n : USize) w, owned w → source h bytes 0 w →
    Effect owned state (h.read n) (fun _ headBytes t =>
      headBytes.size ≤ bytes.size ∧ headBytes = bytes.extract 0 headBytes.size ∧
      source h bytes headBytes.size t) w
  eof : ∀ h bytes pos acc w, owned w → source h bytes pos w →
    Effect owned state (h.readBinToEndInto acc) (fun _ result _ =>
      result = acc ++ bytes.extract pos bytes.size) w

private theorem Effect.bind {a : IO α} {f : α → IO β}
    (step : Effect P state a q w)
    (next : ∀ x t, P t → state t = state w → q w x t →
      Effect P state (f x) (fun _ y after => r w y after) t) :
    Effect P state (a >>= f) r w := by
  unfold Effect at step ⊢
  simp only [Bind.bind, instMonadEIO._aux_13, EST.bind]
  cases ran : a w with
  | error e t => simpa only [ran] using step
  | ok x t =>
    rw [ran] at step
    obtain ⟨pt, eq, value⟩ := step
    have cont := next x t pt eq value
    unfold Effect at cont
    dsimp only
    cases done : f x t with
    | error e u =>
      rw [done] at cont
      exact ⟨cont.1, cont.2.trans eq⟩
    | ok y u =>
      rw [done] at cont
      exact ⟨cont.1, cont.2.1.trans eq, cont.2.2⟩

theorem readBinFile (p : Primitives path P state contents) (start : P w) :
    Effect P state (IO.FS.readBinFile path)
      (fun s bytes _ => bytes = contents (state s)) w := by
  unfold IO.FS.readBinFile
  apply Effect.bind (p.metadata w start)
  intro md t pt mt _
  apply Effect.bind (p.openFile t pt)
  intro h u pu mu held
  let bytes := contents (state t)
  have initial : Effect P state
      (if md.byteSize.toUSize > 0 then h.read md.byteSize.toUSize
       else pure (ByteArray.emptyWithCapacity 0))
      (fun _ (headBytes : ByteArray) s =>
        headBytes.size ≤ bytes.size ∧ headBytes = bytes.extract 0 headBytes.size ∧
          p.source h bytes headBytes.size s) u := by
    split
    · exact p.chunk h bytes _ u pu held
    · exact ⟨pu, rfl, Nat.zero_le _, by exact (ByteArray.extract_same (b := bytes) (i := 0)).symm, held⟩
  have continuation : Effect P state
      ((if md.byteSize.toUSize > 0 then h.read md.byteSize.toUSize else pure (ByteArray.emptyWithCapacity 0))
        >>= fun buf => h.readBinToEndInto buf) (fun _ value _ => value = contents (state w)) u := by
    apply Effect.bind initial
    intro headBytes s ps _ chunk
    have final := p.eof h bytes headBytes.size headBytes s ps chunk.2.2
    unfold Effect at final ⊢
    cases ran : h.readBinToEndInto headBytes s with
    | error e v => simpa only [ran] using final
    | ok result v =>
      rw [ran] at final
      refine ⟨final.1, final.2.1, ?_⟩
      change result = contents (state w)
      rw [final.2.2, congrArg (· ++ bytes.extract headBytes.size bytes.size) chunk.2.1,
        ← ByteArray.extract_eq_extract_append_extract headBytes.size (Nat.zero_le _) chunk.1,
        ByteArray.extract_zero_size]
      exact congrArg contents mt

  by_cases positive : md.byteSize.toUSize > 0 <;> simpa only [positive, ite_true, ite_false] using continuation

/-- The preallocation hint may be zero or larger than the first chunk.
In either case the real stdlib operation resumes the EOF loop at the
world and buffer returned by that branch. -/
theorem readBinFile_atEOF {path : System.FilePath}
    (metadata : path.metadata start = .ok md checked)
    (openFile : IO.FS.Handle.mk path .read checked = .ok h entered)
    (initial : (if md.byteSize.toUSize > 0 then h.read md.byteSize.toUSize
      else pure (ByteArray.emptyWithCapacity 0) : IO ByteArray) entered = .ok acc filled) :
    IO.FS.readBinFile path start = h.readBinToEndInto acc filled := by
  unfold IO.FS.readBinFile
  simp only [Bind.bind, instMonadEIO._aux_13, EST.bind, metadata, openFile]
  change (if md.byteSize.toUSize > 0 then (h.read md.byteSize.toUSize >>= h.readBinToEndInto)
    else ((pure (ByteArray.emptyWithCapacity 0) : IO ByteArray) >>= h.readBinToEndInto)) entered = _
  by_cases test : md.byteSize.toUSize > 0 <;>
    simp only [test, ite_true, ite_false] at initial ⊢ <;>
    simp only [Bind.bind, instMonadEIO._aux_13, EST.bind, initial]

end FileRead
