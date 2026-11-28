import Alvoki.Experiments.WAL.Segmented.Proofs.NativeRootIO

namespace WalRecoverySlice.Segmented.Native
open System Alvoki.NativePost

/-- The checked policy file is read through one bound descriptor. Carry
its returned bytes to the leaf opener, including when the physical state
can differ between separate public calls. -/
private theorem policyRead {path : FilePath} {state : W → σ} {contents : σ → ByteArray}
    (file : FileRead.Primitives path P state contents) (held : P w) :
    IOReturns (IO.FS.readFile path) w
      (fun value t => P t ∧ contents (state t) = value.toUTF8) P := by
  have bytes := FileRead.readBinFile file held
  unfold IO.FS.readFile
  apply IOReturns.bind (middle := fun b t => P t ∧ contents (state t) = b)
  · unfold IOReturns FileRead.Effect at *
    cases ran : IO.FS.readBinFile path w with
    | error => rw [ran] at bytes; exact bytes.1
    | ok b t => rw [ran] at bytes; exact ⟨bytes.1, bytes.2.1 ▸ bytes.2.2.symm⟩
  · rintro b t ⟨pt, eq⟩
    cases h : String.fromUTF8? b with
    | none => exact pt
    | some s =>
      unfold String.fromUTF8? at h
      split at h
      · cases h
        exact ⟨pt, eq⟩
      · contradiction

private theorem checkedIO {a : F α} (proof : Returns a w ok bad) :
    IOReturns (checked a) w ok bad := by
  unfold checked Returns IOReturns at *
  cases ran : a.run w with
  | error e t => simpa [Bind.bind, instMonadEIO._aux_13, EST.bind, ran] using proof
  | ok v t =>
    cases v <;> simpa [Bind.bind, instMonadEIO._aux_13, EST.bind, ran, Pure.pure,
      instMonadEIO._aux_5, EST.pure, throw, throwThe, MonadExceptOf.throw,
      instMonadExceptOfEIO._aux_1, EST.throw] using proof

/-- A rejected child directory, failed pathname check, or policy mismatch
keeps the protected ownership. A validated child's actual policy bytes
are available at the exact world where its public single-file open starts. -/
theorem Store.acquireChild_post (s : Store) (p : Policy) (id : Nat)
    {P : W → Prop} {state : W → σ} {contents : σ → ByteArray} (held : P w)
    (stat : ∀ path : FilePath, Keeps P path.symlinkMetadata)
    (list : Keeps P (entries (segmentPath s.root id)))
    (file : FileRead.Primitives (segmentPath s.root id / "policy") P state contents)
    (leaf : ∀ t, P t → contents (state t) = (policyStamp p).toUTF8 →
      IOReturns (SingleFile.openExisting (segmentPath s.root id)) t ok bad)
    (fail : ∀ t, P t → bad t) :
    IOReturns (s.acquireChild p id) w ok bad := by
  let dir := segmentPath s.root id
  unfold Store.acquireChild
  apply IOReturns.bind (middle := fun _ t => P t ∧ contents (state t) = (policyStamp p).toUTF8)
  · apply checkedIO
    unfold validateChildWith
    apply Returns.bind (middle := fun _ t => P t)
    · apply Returns.bind (middle := fun _ t => P t)
      · apply (Returns.liftIO (inspectChild_io dir (fun _ => True) stat _ held)).mapPost
        · exact fun _ _ h => h.1
        · exact fail
        · intro u hu
          have listed := list u hu
          unfold IOReturns at *
          cases ran : entries dir u with
          | error => rw [ran] at listed; exact listed
          | ok => rw [ran] at listed; exact ⟨listed, trivial⟩
      · intro _ _ pt
        exact pt
    · intro names t pt
      split
      · apply Returns.bind (middle := fun _ t => P t)
        · have md := file.metadata t pt
          apply Returns.bind (middle := fun _ t => P t)
          · apply Returns.liftIO
            unfold IOReturns FileRead.Effect at *
            cases ran : (dir / "policy").metadata t with
            | error => rw [ran] at md; exact fail _ md.1
            | ok => rw [ran] at md; exact md.1
          · intro _ _ pt
            exact pt
        · intro size u hu
          apply ((Returns.liftIO (policyRead file hu)).mapPost (fun _ _ h => h) fail).bind
          rintro value v ⟨pv, eq⟩
          split
          · rename_i matchPolicy
            simp only [Bool.and_eq_true, beq_iff_eq] at matchPolicy
            exact ⟨pv, eq.trans (congrArg String.toUTF8 matchPolicy.2)⟩
          · exact fail _ pv
      · exact fail _ pt
  · exact fun _ t h => leaf t h.1 h.2

end WalRecoverySlice.Segmented.Native
