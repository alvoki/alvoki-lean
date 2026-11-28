import Alvoki.Experiments.WAL.Segmented.Proofs.PrepareCutIO

namespace WalRecoverySlice.Segmented.Native.CreateCutIO
open System Alvoki.NativePost
open SingleFile (Handle Opened AppendFiles)
abbrev Ready := Opened IO.FS.Handle (AppendFiles IO.FS.Handle)

inductive Leaf where
  | openFile (path : FilePath) (mode : IO.FS.Mode)
  | tryLock (h : IO.FS.Handle) | unlock (h : IO.FS.Handle)
  | list (dir : FilePath)
  | unbuffer (h : IO.FS.Handle) | write (h : IO.FS.Handle) (bytes : ByteArray)
  | flush (h : IO.FS.Handle) | fsync (h : IO.FS.Handle) | rewind (h : IO.FS.Handle)
  | readEOF (h : IO.FS.Handle) | readChunk (h : IO.FS.Handle) | truncate (h : IO.FS.Handle) (size : Nat)
  | ref (ready : Ready) | mutex

def Leaf.Result : Leaf → Type
  | .openFile .. => IO.FS.Handle
  | .tryLock _ => Bool
  | .list _ => Array IO.FS.DirEntry
  | .readEOF _ | .readChunk _ => ByteArray
  | .truncate .. => Except String Unit
  | .ref _ => SingleFile.ConcreteRecovery.Ref
  | .mutex => Std.BaseMutex
  | _ => Unit

def Leaf.action : (op : Leaf) → IO op.Result
  | .openFile f m => IO.FS.Handle.mk f m
  | .tryLock h => h.tryLock
  | .unlock h => h.unlock
  | .list dir => SingleFile.Internal.readDirChecked dir
  | .unbuffer h => SingleFile.Internal.disableBuffering h
  | .write h bytes => h.write bytes
  | .flush h => h.flush
  | .fsync h => SingleFile.Internal.syncHandle h
  | .rewind h => h.rewind
  | .readEOF h => SingleFile.Internal.readChunks h .empty
  | .readChunk h => SingleFile.Internal.checkedChunk h 1024
  | .truncate h size => (SingleFile.nativeRecovery.truncateAt h size).run
  | .ref ready => IO.mkRef ready.phase
  | .mutex => Std.BaseMutex.new

def world : EST.Out IO.Error IO.RealWorld α → W
  | .ok _ w | .error _ w => w

/-- Enrich a native IO action with its actually reachable primitive calls.
The operand and the reached world are retained. Sequencing visits a second
action only after a successful return. Handlers require a returned error. -/
structure Trace (α : Type) where
  run : IO α
  visits : W → Leaf → W → Prop
  fold : ∀ (P : W → Prop) w, P w →
    (∀ leaf t, visits w leaf t → P t → P (world (leaf.action t))) →
    P (world (run w)) ∧ ∀ leaf t, visits w leaf t → P t

private def Trace.unit (value : α) : Trace α :=
  ⟨pure value, fun _ _ _ => False, fun _ _ start _ => ⟨start, fun _ _ => False.elim⟩⟩

private def Trace.bind (a : Trace α) (f : α → Trace β) : Trace β where
  run := a.run >>= fun x => (f x).run
  visits w leaf t := a.visits w leaf t ∨ ∃ x v, a.run w = .ok x v ∧ (f x).visits v leaf t
  fold P w start step := by
    obtain ⟨first, seen⟩ := a.fold P w start (fun op t used => step op t (.inl used))
    cases ran : a.run w with
    | error e v =>
      rw [ran] at first
      refine ⟨?_, ?_⟩
      · simpa [world, Bind.bind, instMonadEIO._aux_13, EST.bind, ran] using first
      · rintro op t (other | ⟨_, _, eq, _⟩)
        · exact seen op t other
        · simp at eq
    | ok x v =>
      rw [ran] at first
      obtain ⟨last, later⟩ := (f x).fold P v first (fun op t used => step op t (.inr ⟨x,v,ran,used⟩))
      refine ⟨?_, ?_⟩
      · simpa [world, Bind.bind, instMonadEIO._aux_13, EST.bind, ran] using last
      · rintro op t (other | ⟨_, _, eq, cut⟩)
        · exact seen op t other
        · cases eq; exact later op t cut

private def Trace.raised (e : IO.Error) : Trace α :=
  ⟨throw e, fun _ _ _ => False, fun _ _ start _ => ⟨start, fun _ _ => False.elim⟩⟩

private def Trace.caught (a : Trace α) (f : IO.Error → Trace α) : Trace α where
  run := tryCatchThe IO.Error a.run fun e => (f e).run
  visits w leaf t := a.visits w leaf t ∨ ∃ e v, a.run w = .error e v ∧ (f e).visits v leaf t
  fold P w start step := by
    obtain ⟨first, seen⟩ := a.fold P w start (fun op t used => step op t (.inl used))
    cases ran : a.run w with
    | ok x v =>
      rw [ran] at first
      refine ⟨?_, ?_⟩
      · simpa [tryCatchThe, MonadExceptOf.tryCatch, instMonadExceptOfEIO._aux_3, EST.tryCatch, ran] using first
      · rintro op t (other | ⟨_, _, eq, _⟩)
        · exact seen op t other
        · simp at eq
    | error e v =>
      rw [ran] at first
      obtain ⟨last, later⟩ := (f e).fold P v first (fun op t used => step op t (.inr ⟨e,v,ran,used⟩))
      refine ⟨?_, ?_⟩
      · simpa [tryCatchThe, MonadExceptOf.tryCatch, instMonadExceptOfEIO._aux_3, EST.tryCatch, ran] using last
      · rintro op t (other | ⟨_, _, eq, cut⟩)
        · exact seen op t other
        · cases eq; exact later op t cut

instance : Monad Trace where
  pure := Trace.unit
  bind := Trace.bind

instance : MonadExceptOf IO.Error Trace where
  throw := Trace.raised
  tryCatch := Trace.caught

private def call (l : Leaf) : Trace l.Result where
  run := l.action
  visits w op t := op = l ∧ t = w
  fold _ w start step := ⟨step l w ⟨rfl,rfl⟩ start, fun _ _ h => h.2 ▸ start⟩

/-- A prefix of the executable chunk loop. An empty chunk or an IO
exception terminates the loop and cannot authorize a subsequent read. -/
inductive ChunkPrefix (h : IO.FS.Handle) (origin : W) : ByteArray → W → Prop where
  | first : ChunkPrefix h origin .empty origin
  | next : ChunkPrefix h origin acc w → SingleFile.Internal.checkedChunk h 1024 w = .ok bytes t →
      bytes.isEmpty = false → ChunkPrefix h origin (acc ++ bytes) t

theorem ChunkPrefix.remaining (path : ChunkPrefix h origin acc w) :
    SingleFile.Internal.readChunks h .empty origin = SingleFile.Internal.readChunks h acc w := by
  induction path with
  | first => rfl
  | next _ ran more ih =>
    rw [ih, SingleFile.Internal.readChunks.eq_1]
    simp [Bind.bind, instMonadEIO._aux_13, EST.bind, ran, more]

private def readEOF (h : IO.FS.Handle) : Trace ByteArray where
  run := SingleFile.Internal.readChunks h .empty
  visits origin op t := (op = .readEOF h ∧ t = origin) ∨
    (op = .readChunk h ∧ ∃ acc, ChunkPrefix h origin acc t)
  fold P origin start step := by
    refine ⟨step (.readEOF h) origin (.inl ⟨rfl,rfl⟩) start, ?_⟩
    rintro op t (⟨_,rfl⟩ | ⟨_, acc, path⟩)
    · exact start
    · induction path with
      | first => exact start
      | next path ran _ ih =>
        have next := step (.readChunk h) _ (.inr ⟨rfl,_,path⟩) ih
        simpa only [Leaf.action, ran, world] using next

private abbrev F := ExceptT String Trace

private def opening : SingleFile.OpenIO F IO.FS.Handle where
  openFile _ path mode := liftM <| call (.openFile path mode)
  unbuffered h := liftM <| call (.unbuffer h)
  readPolicy path h := do
    let bytes ← liftM (readEOF h)
    match String.fromUTF8? bytes with
    | some text => return text
    | none => throw s!"Tried to read file '{path}' containing non UTF-8 data."
  tryLock h := liftM <| call (.tryLock h)
  unlock h := liftM <| call (.unlock h)
  sync h := liftM <| call (.fsync h)

private def recovery : SingleFile.RecoveryIO F IO.FS.Handle where
  readFromStart h := liftM (do
    let _ ← call (.rewind h)
    return (← readEOF h).data.toList : Trace _)
  truncateAt h n := ExceptT.mk (call (.truncate h n))
  sync h := liftM <| call (.fsync h)

private def checked (a : F α) : Trace α := do
  match ← a.run with
  | .ok x => return x
  | .error msg => throw (IO.userError msg)

private def allocate (ready : Ready) : Trace SingleFile.Handle where
  run := SingleFile.Internal.installReady ready
  visits w op t := (op = .ref ready ∧ t = w) ∨ (op = .mutex ∧ t = ((IO.mkRef ready.phase : BaseIO _) w).state)
  fold P w start step := by
    let cell := (IO.mkRef ready.phase : BaseIO _) w
    have allocated : P cell.state := step (.ref ready) w (.inl ⟨rfl,rfl⟩) start
    have guard := step .mutex cell.state (.inr ⟨rfl,rfl⟩) allocated
    obtain ⟨_, ran, _⟩ := SingleFile.installReady_run ready w
    rw [ran]
    exact ⟨guard, fun _ _ h => h.elim (fun z => z.2 ▸ start) (fun z => z.2 ▸ allocated)⟩

def program (dir : FilePath) (p : Policy) : Trace SingleFile.Handle :=
  SingleFile.createWith (error := IO.Error) IO.userError (checked (SingleFile.acquireWith opening dir))
    (fun h => call (.unlock h)) (fun path => do return (← call (.list path)).map (·.fileName))
    (fun path bytes => do
      let h ← call (.openFile path .writeNew)
      let _ ← call (.unbuffer h)
      let _ ← call (.write h bytes)
      let _ ← call (.flush h)
      call (.fsync h))
    (fun path lock => checked (SingleFile.installWith opening
      (fun policy reader _ markers => SingleFile.recoverWith recovery reader markers policy)
      SingleFile.appendFiles path lock) >>= allocate) dir p

private abbrev NF := ExceptT String IO
private def Same (a : F α) (b : NF α) : Prop := a.run.run = b.run

private theorem sameBind {a : F α} {b : NF α} (same : Same a b)
    {f : α → F β} {g : α → NF β} (all : ∀ x, Same (f x) (g x)) :
    Same (a >>= f) (b >>= g) := by
  unfold Same at *
  rw [ExceptT.run_bind, ExceptT.run_bind]
  change (a.run.run >>= _) = _
  rw [same]
  congr 1
  funext x
  cases x with
  | ok x => exact all x
  | error => rfl

private theorem sameAcquire (dir : FilePath) :
    Same (SingleFile.acquireWith opening dir) (SingleFile.acquireWith SingleFile.nativeOpen dir) := by
  unfold SingleFile.acquireWith
  apply sameBind (by rfl)
  intro h
  apply sameBind (by rfl)
  intro granted
  cases granted <;> rfl

private theorem sameFiles (dir : FilePath) :
    Same (SingleFile.openFilesWith opening dir) (SingleFile.openFilesWith SingleFile.nativeOpen dir) := by
  unfold SingleFile.openFilesWith
  repeat' first
    | rfl
    | apply sameBind; rotate_left
    | intro x
    | split
  all_goals simp_all [Same] <;> try rfl

private theorem sameSettle (dir : FilePath) (h : IO.FS.Handle) :
    Same (SingleFile.settleWith opening dir h) (SingleFile.settleWith SingleFile.nativeOpen dir h) := by
  unfold SingleFile.settleWith
  apply sameBind (by rfl)
  intro _
  apply sameBind (by rfl)
  intro _
  rfl

private theorem sameRecover (p : Policy) (reader writer : IO.FS.Handle) (markers : Option (IO.FS.Handle × IO.FS.Handle)) :
    Same (SingleFile.recoverWith recovery reader markers p) (SingleFile.recoverNative p reader writer markers) := by
  unfold SingleFile.recoverNative SingleFile.recoverWith WalRecoverySlice.reopen
  dsimp only
  repeat' first
    | rfl
    | apply sameBind; rotate_left
    | intro x
    | split
  all_goals simp_all [Same] <;> cases markers <;> rfl

private theorem sameInstall (dir : FilePath) (lock : IO.FS.Handle) :
    Same (SingleFile.installWith opening
      (fun policy reader _ markers => SingleFile.recoverWith recovery reader markers policy)
      SingleFile.appendFiles dir lock)
      (SingleFile.installWith SingleFile.nativeOpen SingleFile.recoverNative SingleFile.appendFiles dir lock) := by
  unfold SingleFile.installWith
  apply sameBind (sameFiles dir)
  intro files
  apply sameBind (sameRecover ..)
  intro decoded
  exact sameBind (sameSettle ..) (fun _ => rfl)

private theorem sameChecked (h : Same a b) : (checked a).run = SingleFile.checked b := by
  unfold Same at h
  change (a.run.run >>= _) = (b.run >>= _)
  rw [h]
  congr 1
  funext value
  cases value <;> rfl

private theorem sameIOBind {a : Trace α} {b : IO α} (same : a.run = b)
    {f : α → Trace β} {g : α → IO β} (rest : ∀ x, (f x).run = g x) :
    (a >>= f).run = (b >>= g) := by
  change (a.run >>= fun x => (f x).run) = _
  rw [same, funext rest]

private theorem sameCatch {a : Trace α} {b : IO α} (same : a.run = b)
    {f : IO.Error → Trace α} {g : IO.Error → IO α} (rest : ∀ e, (f e).run = g e) :
    (tryCatchThe IO.Error a f).run = tryCatchThe IO.Error b g := by
  change tryCatchThe IO.Error a.run (fun e => (f e).run) = _
  rw [same, funext rest]

private theorem writeRun (path : FilePath) (bytes : ByteArray) :
    ((do
      let h ← call (.openFile path .writeNew)
      let _ ← call (.unbuffer h)
      let _ ← call (.write h bytes)
      let _ ← call (.flush h)
      call (.fsync h)) : Trace _).run = SingleFile.Internal.writeAndSync path bytes := by
  funext w
  unfold SingleFile.Internal.writeAndSync SingleFile.Internal.openStream
  change (IO.FS.Handle.mk path .writeNew >>= _) w = _
  simp only [Bind.bind, instMonadEIO._aux_13, EST.bind, Pure.pure, instMonadEIO._aux_5, EST.pure]
  cases first : IO.FS.Handle.mk path .writeNew w <;> simp_all only
  rename_i h t
  cases buf : SingleFile.Internal.disableBuffering h t <;> simp [Trace.bind, call, Leaf.action, Bind.bind, instMonadEIO._aux_13, EST.bind, buf]
  all_goals rfl

/-- Erasure is the executable SingleFile.create including the real
installer and failure-unlock handler, for both WAL policies. -/
theorem program_run (dir : FilePath) (p : Policy) : (program dir p).run = SingleFile.create dir p := by
  unfold program SingleFile.create SingleFile.createWith
  apply sameIOBind (sameChecked (sameAcquire dir))
  intro lock
  apply sameCatch
  · apply sameIOBind
    · unfold SingleFile.prepareCreateWith
      apply sameIOBind (by rfl)
      intro names
      split
      · rfl
      · unfold SingleFile.initializeFilesWith
        repeat' first
          | rfl
          | apply sameIOBind (writeRun ..); intro x
          | apply writeRun
          | split
    · intro _
      apply sameIOBind (sameChecked (sameInstall ..))
      intro _
      rfl
  · intro e
    apply sameIOBind
    · apply sameCatch (by rfl)
      intro _; rfl
    · intro _; rfl

structure Primitives (s : Store) (c : Control) (origin : W) (disk : W → Model.Disk)
    (stop : ControlCutIO.Stops) : Prop where
  returned : ∀ leaf t, (program (PrepareCutIO.successorDir s c) c.policy).visits origin leaf t →
    PrepareCutIO.Frame c (disk t) (disk (world (leaf.action t)))
  interrupted : ∀ leaf t, (program (PrepareCutIO.successorDir s c) c.policy).visits origin leaf t →
    ∀ reached, stop leaf.action t reached → PrepareCutIO.Frame c (disk t) reached

/-- Only a successful concrete cleanup and mkdir enter creation. Every
later interruption inside this invocation frames the previously selected
child, including errors caught by the lock-release handler. -/
theorem interrupted (outer : PrepareCutIO.Primitives s c start disk stop)
    (entry : PrepareCutIO.Prefix (PrepareCutIO.successorDir s c) start .create origin)
    (ops : Primitives s c origin disk stop)
    (issued : (program (PrepareCutIO.successorDir s c) c.policy).visits origin leaf t)
    (cut : stop leaf.action t reached) : PrepareCutIO.Frame c (disk start) reached := by
  let run := program (PrepareCutIO.successorDir s c) c.policy
  have initial := entry.frame outer
  have states := run.fold (fun w => PrepareCutIO.Frame c (disk start) (disk w)) origin initial
    (fun site w used frame => frame.trans (ops.returned site w used))
  exact (states.2 _ _ issued).trans (ops.interrupted _ _ issued _ cut)

end WalRecoverySlice.Segmented.Native.CreateCutIO
