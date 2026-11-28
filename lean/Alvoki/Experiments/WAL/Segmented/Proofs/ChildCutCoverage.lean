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

/-- Early stops need only handle bindings. A reached active phase supplies
its exact private operands for the worker and its actual return for cleanup. -/
def source (stop : Stop) (h : SingleFile.Handle) (batch : Bytes) (start : W) (d : Disk) : Prop :=
  (∃ (α : Type) (op : IO α) (w : W), AppendCut.ChildEntry h start op w ∧ stop op w d) ∨
  ∃ a : Operand h start,
    let body := appendBatch programOps a.policy (Persistence.historyCursor a.known) batch
    let began := poisonAt a.cell a.fd a.mutex start
    (∃ (α : Type) (op : IO α) (w : W), Before a op w ∧ stop op w d) ∨ visits a.files stop body began d ∨
      match (body.eval (nativeOps a.files)).run began with
      | .error e t => ∃ (α : Type) (op : IO α) (w : W), After a batch t (.error e) op w ∧ stop op w d
      | .ok reply t => ∃ (α : Type) (op : IO α) (w : W), After a batch t (.ok reply) op w ∧ stop op w d

theorem sourceCovered (cut : source stop h batch w d) : ChildStop stop h batch w d := by
  rcases cut with ⟨_,_,_,site,hit⟩ | ⟨a,early | inner | ended⟩
  · exact .entry site hit
  · obtain ⟨_,_,_,site,hit⟩ := early
    exact .before a site hit
  · exact workerCovered a _ .start inner
  · let actual := nativeOps a.files
    let body := appendBatch programOps a.policy (Persistence.historyCursor a.known) batch
    let began := poisonAt a.cell a.fd a.mutex w
    have terminal := terminalCovered actual body (origin := began) .start
    change (match (body.eval actual).run began with | .error e t => _ | .ok reply t => _) at ended
    obtain ⟨rest,t,⟨path⟩,done⟩ := terminal
    cases ran : (body.eval actual).run began <;> rw [ran] at ended done <;>
      obtain ⟨α,op,v,site,hit⟩ := ended <;>
      exact .after ⟨a,rest,t,path,_,_,done,α,op,v,site,hit⟩

end WalRecoverySlice.Segmented.Native.ChildCutIO
