import Alvoki.Experiments.WAL.Segmented.Proofs.CutRuntime

namespace WalRecoverySlice.Segmented.Native.ChildCutIO
open Alvoki.NativePost (W)
open Model (Disk)
open SingleFile (AppendFiles)
open SingleFile.ConcreteRecovery (Op Program programOps)
open SingleFile.ConcreteAppend (nativeOps poisonAt)
open SingleFile.ConcreteAppendCut (Issued Terminal Site)
open AppendCut (Observed ChildStop Stop)

private local instance : MonadExceptOf String Observed where
  throw e := throw (IO.userError e)
  tryCatch a f := tryCatchThe IO.Error a fun e => f e.toString

private def leaf (stop : Stop) (a : IO Unit) : Observed Unit := ⟨a, stop a⟩

private def raw (stop : Stop) : SingleFile.AppendIO Observed IO.FS.Handle where
  appendFlushed h b := SingleFile.writeFlushedWith (leaf stop (h.write ⟨b.toArray⟩)) (leaf stop h.flush)
  writeFromStart h b := SingleFile.writeFromStartWith (leaf stop h.rewind)
    (SingleFile.writeFlushedWith (leaf stop (h.write ⟨b.toArray⟩)) (leaf stop h.flush))
  sync h := leaf stop (SingleFile.Internal.syncHandle h)

/-- Follow the generic append program. Completed operations use the real IO
outcome; the interrupted one uses its shared write/rewind/flush schedule. -/
def visits (files : AppendFiles IO.FS.Handle) (stop : Stop) : Program α → W → Disk → Prop
  | .ret _, _, _ | .stop _, _, _ => False
  | .call op k, w, d =>
    (op.eval (SingleFile.appendOps (raw stop) files)).cuts w d ∨
      ∃ x t, (op.eval (nativeOps files)).run w = .ok (.ok x) t ∧ visits files stop (k x) t d

private theorem leafCovered (files : AppendFiles IO.FS.Handle) (op : Op) (stop : Stop)
    (hit : (op.eval (SingleFile.appendOps (raw stop) files)).cuts w d) :
    ∃ a t, Site files op w a t ∧ stop a t d := by
  cases op with
  | readData | readMarker | truncate => exact False.elim hit
  | syncData => exact ⟨_,_,.dataSync,hit⟩
  | append b =>
    rcases hit with early | ⟨⟨⟩, t, written, late⟩
    · exact ⟨_,_,.data,early⟩
    · exact ⟨_,_,.dataFlush written,late⟩
  | syncMarker slot =>
    cases markers : files.markers with
    | none =>
      simp only [Op.eval,SingleFile.appendOps,SingleFile.markerHandle,markers] at hit
      rcases hit with impossible | ⟨x,t,ran,_⟩
      · exact False.elim impossible
      · change EST.Out.error (IO.userError "marker unavailable") w = EST.Out.ok x t at ran
        contradiction
    | some ab =>
      obtain ⟨a,b⟩ := ab
      simp only [Op.eval,SingleFile.appendOps,SingleFile.markerHandle,markers] at hit
      rcases hit with wrong | ⟨h,t,picked,stop⟩
      · exact False.elim wrong
      · change EST.Out.ok (if slot == 0 then a else b) w = EST.Out.ok h t at picked
        cases picked
        exact ⟨_,_,.markerSync markers rfl,stop⟩
  | writeMarker slot bytes =>
    cases markers : files.markers with
    | none =>
      simp only [Op.eval,SingleFile.appendOps,SingleFile.markerHandle,markers] at hit
      rcases hit with impossible | ⟨x,t,ran,_⟩
      · exact False.elim impossible
      · change EST.Out.error (IO.userError "marker unavailable") w = EST.Out.ok x t at ran
        contradiction
    | some ab =>
      obtain ⟨a,b⟩ := ab
      simp only [Op.eval,SingleFile.appendOps,SingleFile.markerHandle,markers] at hit
      rcases hit with wrong | ⟨h,t,picked,stop⟩
      · exact False.elim wrong
      · change EST.Out.ok (if slot == 0 then a else b) w = EST.Out.ok h t at picked
        cases picked
        rcases stop with rewind | ⟨⟨⟩,u,rewound,write | ⟨⟨⟩,v,written,flush⟩⟩
        · exact ⟨_,_,.rewind markers rfl,rewind⟩
        · exact ⟨_,_,.marker markers rfl rewound,write⟩
        · exact ⟨_,_,.markerFlush markers rfl rewound written,flush⟩

private theorem workerCovered (a : Operand h start) (rest : Program Cursor)
    (earlier : Issued (nativeOps a.files)
      (appendBatch programOps a.policy (Persistence.historyCursor a.known) batch)
      (poisonAt a.cell a.fd a.mutex start) rest w)
    (hit : visits a.files stop rest w d) : ChildStop stop h batch start d := by
  induction rest generalizing w with
  | ret | stop => exact False.elim hit
  | call op k ih =>
    rcases hit with here | ⟨x,t,returned,later⟩
    · obtain ⟨raw,t,site,cut⟩ := leafCovered a.files op stop here
      exact .inside ⟨a.policy,a.known,a.cell,a.mutex,a.fd,a.files,a.assembled,a.active,op,k,_,earlier,raw,t,site,cut⟩
    · exact ih x (earlier.next returned) later

/-- For every actual worker outcome there is a finite terminal prefix.
A returned IO failure or protocol rejection has no success continuation. -/
theorem terminalCovered (actual : WalRecoverySlice.Ops SingleFile.ConcreteRecovery.F) (program : Program Cursor)
    (prior : Issued actual entry origin program w) :
    ∃ rest t, Nonempty (Issued actual entry origin rest t) ∧
      match (program.eval actual).run w with
      | .error e v => Terminal actual rest t (.error e) v
      | .ok answer v => Terminal actual rest t (.ok answer) v := by
  induction program generalizing w with
  | ret val => exact ⟨_,_,⟨prior⟩,.ok val⟩
  | stop msg => exact ⟨_,_,⟨prior⟩,.rejected msg⟩
  | call op k ih =>
    simp only [Program.eval, ExceptT.run_bind]
    simp only [Bind.bind, instMonadEIO._aux_13, EST.bind]
    cases ran : (op.eval actual).run w with
    | error e t => exact ⟨_,_,⟨prior⟩,.error ran⟩
    | ok result t => cases result with
      | error fault => exact ⟨_,_,⟨prior⟩,.fault ran⟩
      | ok value => exact ih value (prior.next ran)

private theorem finished {stop : Stop} (a : Operand h w) (batch : Bytes)
    (ended : let body := appendBatch programOps a.policy (Persistence.historyCursor a.known) batch
      let began := poisonAt a.cell a.fd a.mutex w
      match (body.eval (nativeOps a.files)).run began with
      | .error e t => ∃ (α : Type) (op : IO α) (v : W), After a batch t (.error e) op v ∧ stop op v d
      | .ok reply t => ∃ (α : Type) (op : IO α) (v : W), After a batch t (.ok reply) op v ∧ stop op v d) :
    ChildStop stop h batch w d := by
  let actual := nativeOps a.files
  let body := appendBatch programOps a.policy (Persistence.historyCursor a.known) batch
  let began := poisonAt a.cell a.fd a.mutex w
  obtain ⟨rest,t,⟨path⟩,done⟩ := terminalCovered actual body (origin := began) .start
  change (match (body.eval actual).run began with | .error e t => _ | .ok reply t => _) at ended
  cases ran : (body.eval actual).run began <;> rw [ran] at ended done <;>
    obtain ⟨α,op,v,site,hit⟩ := ended <;>
    exact .after ⟨a,rest,t,path,_,_,done,α,op,v,site,hit⟩

private noncomputable def fileWorker (policy : Policy) (batch : Bytes) (stop : Stop) (files : AppendFiles IO.FS.Handle)
    (pos : Cursor) : Observed Cursor :=
  let code := appendBatch programOps policy pos batch
  ⟨checked (code.eval (nativeOps files)), visits files stop code⟩

private noncomputable def phaseBody (policy : Policy) (cell : SingleFile.ConcreteAppend.PhaseRef) (batch : Bytes)
    (stop : Stop) : Observed Unit := do
  SingleFile.appendWith (← Observed.leaf stop (cell.get : IO _))
    (fun ph => Observed.leaf stop (cell.set ph : IO Unit)) (fileWorker policy batch stop) batch

noncomputable def childProgram (policy : Policy) (cell : SingleFile.ConcreteAppend.PhaseRef)
    (mutex : Std.BaseMutex) (batch : Bytes) (stop : Stop) : Observed Unit := do
  let _ ← Observed.leaf stop (liftM mutex.lock : IO Unit)
  Observed.finallyUnlock (phaseBody policy cell batch stop) mutex stop

/-- Only the private identity of the public child is part of this
observation. Its phase read, every guard, and whether the finalizer follows
an error are determined by the same executable appendWith. -/
def source (stop : Stop) (h : SingleFile.Handle) (batch : Bytes) (w : W) (d : Disk) : Prop :=
  ∃ p r m, h.Assembled p r m ∧
    (childProgram p r m batch stop).cuts w d

private theorem checkedOut (a : ExceptT String IO α) (w : W) :
    checked a w = match a.run w with
      | .error e t => .error e t
      | .ok (.error msg) t => .error (IO.userError msg) t
      | .ok (.ok x) t => .ok x t := by
  unfold checked
  cases ran : a.run w with
  | error => simp [Bind.bind,instMonadEIO._aux_13,EST.bind,ran]
  | ok answer => cases answer <;> simp [Bind.bind,instMonadEIO._aux_13,EST.bind,ran] <;> rfl

theorem childProgram_run (bound : h.Assembled p r m) (batch : Bytes) (stop : Stop)
    (active : (SingleFile.ConcreteAppend.readAt r m w).val = .active fd files pos known) :
    (childProgram p r m batch stop).run w = SingleFile.append h batch w := by
  rw [SingleFile.append_active_run bound w active]
  let got := SingleFile.ConcreteAppend.readAt r m w
  have read : (Observed.leaf stop (r.get : IO _)).run (m.lock w).state =
      .ok (.active fd files pos known) got.state := by rw [← active]; rfl
  have lock : (Observed.leaf stop (liftM m.lock : IO Unit)).run w = .ok () (m.lock w).state := rfl
  have poison : (Observed.leaf stop (r.set (.poisoned fd) : IO Unit)).run got.state =
      .ok () ((r.set (.poisoned fd) : BaseIO Unit) got.state).state := rfl
  simp only [childProgram,Observed.bindRun,lock,Observed.finallyUnlock_run,phaseBody,read,SingleFile.appendWith,poison,
    fileWorker,SingleFile.ConcreteAppend.eval_append (nativeOps files) p pos batch (fun _ _ => rfl),checkedOut]
  dsimp only [got, SingleFile.ConcreteAppend.readAt]
  cases (appendBatch (nativeOps files) p pos batch).run
      ((r.set (.poisoned fd) : BaseIO Unit) ((r.get : BaseIO _) (m.lock w).state).state).state with
  | error => rfl
  | ok answer => cases answer <;> rfl

theorem sourceCovered (rawCut : source stop h batch w d) (owned : Nonempty (Operand h w)) :
    ChildStop stop h batch w d := by
  obtain ⟨p,r,m,bound,hit⟩ := rawCut
  obtain ⟨a⟩ := owned
  obtain ⟨rfl,rfl,rfl⟩ := a.assembled.unique bound
  let r := a.cell
  let m := a.mutex
  let p := a.policy
  have binds : h.Binds r m := by
    unfold SingleFile.Handle.Assembled at bound
    unfold SingleFile.Handle.Binds
    constructor <;> apply congrArg _ bound
  unfold childProgram at hit
  rw [Observed.bindCuts] at hit
  rcases hit with lock | portion
  · exact .entry (.mutex binds) lock
  let got := SingleFile.ConcreteAppend.readAt r m w
  let code := appendBatch programOps p (Persistence.historyCursor a.known) batch
  let began := poisonAt r a.fd m w
  have read : (Observed.leaf stop (r.get : IO _)).run (m.lock w).state =
      .ok (.active a.fd a.files (Persistence.historyCursor a.known) a.known) got.state := by
    rw [← a.active]
    rfl
  change (phaseBody p r batch stop).cuts _ d ∨ stop _ (returnedWorld ((phaseBody p r batch stop).run _)) d at portion
  dsimp only [r,m,p] at read portion
  simp only [phaseBody,Observed.bindCuts,Observed.bindRun,read,SingleFile.appendWith] at portion
  have poison : (Observed.leaf stop (a.cell.set (.poisoned a.fd) : IO Unit)).run got.state =
      .ok () began := rfl
  have atFile : (fileWorker a.policy batch stop a.files (Persistence.historyCursor a.known)).run began =
      checked (code.eval (nativeOps a.files)) began := rfl
  simp only [poison,atFile,checkedOut] at portion
  rcases portion with (early | storage) | leaving
  · exact .entry (.read binds) early
  · rcases storage with poisoning | inner
    · exact .before a .poison poisoning
    · rcases inner with inside | installed
      · exact workerCovered a code .start inside
      · apply finished a batch
        change (match (code.eval (nativeOps a.files)).run began with | .error e t => _ | .ok reply t => _)
        cases ran : (code.eval (nativeOps a.files)).run began with
        | error => rw [ran] at installed; contradiction
        | ok answer u =>
          rw [ran] at installed
          cases answer with
          | error => contradiction
          | ok => exact ⟨_,_,_,.install,installed⟩
  · apply finished a batch
    change (match (code.eval (nativeOps a.files)).run began with | .error e t => _ | .ok reply t => _)
    cases ran : (code.eval (nativeOps a.files)).run began with
    | error e t => rw [ran] at leaving; exact ⟨_,_,_,.failed,leaving⟩
    | ok answer t =>
      rw [ran] at leaving
      cases answer with
      | error msg => exact ⟨_,_,_,.rejected,leaving⟩
      | ok next => exact ⟨_,_,_,.leave,leaving⟩

end WalRecoverySlice.Segmented.Native.ChildCutIO
