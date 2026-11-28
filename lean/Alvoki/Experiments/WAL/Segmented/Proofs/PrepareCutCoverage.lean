import Alvoki.Experiments.WAL.Segmented.Proofs.CreateCutIO
import Alvoki.Experiments.WAL.Segmented.Proofs.ControlCutCoverage

namespace WalRecoverySlice.Segmented.Native.PrepareCutIO
open System Model Alvoki.NativePost AppendCut
open Observed (leaf)

private def regularCheck (path : FilePath) (md : IO.FS.Metadata) : Observed Unit :=
  ⟨regular path md, fun _ _ => False⟩

private def inspect (stop : ControlCutIO.Stops) (dir : FilePath) :=
  inspectChildWith (fun f => leaf stop f.symlinkMetadata) (fun f => leaf stop (entries f)) regularCheck dir

private def creation (stop : ControlCutIO.Stops) (dir : FilePath) (p : Policy) : Observed SingleFile.Handle :=
  ⟨SingleFile.create dir p, fun w d =>
    ∃ leaf t, (CreateCutIO.program dir p).visits w leaf t ∧ stop leaf.action t d⟩

/-- The source chooses the dirent order, metadata and policy guards, exact
unlink operands, mkdir and create. Returned failures stop before continuation. -/
def program (s : Store) (policy : Policy) (id : Nat) (stop : ControlCutIO.Stops) : Observed SingleFile.Handle :=
  prepareChildWith (removeSegmentWith
    (fun dir => ⟨PrepareIO.presenceIO dir, stop dir.symlinkMetadata⟩) (inspect stop) (·.fileName)
    (fun path => leaf stop (IO.FS.removeFile path)) (fun dir => leaf stop (IO.FS.removeDir dir)) s.root)
    (fun dir => leaf stop (IO.FS.createDir dir)) (creation stop) s.root policy id

private theorem inspect_run (stop : ControlCutIO.Stops) (dir : FilePath) : (inspect stop dir).run = inspectChild dir := by
  unfold inspect inspectChild inspectChildWith
  rw [Observed.run_bind]
  apply congrArg (Bind.bind dir.symlinkMetadata)
  funext md
  split
  · rw [Observed.run_bind]
    apply congrArg (Bind.bind (entries dir))
    funext xs
    rw [Observed.run_bind, ← Array.forIn_toList, Observed.run_forIn, Array.forIn_toList]
    congr 2
    funext entry _
    dsimp only
    split <;> rfl
  · rfl

theorem program_run (s : Store) (policy : Policy) (id : Nat) (stop : ControlCutIO.Stops) :
    (program s policy id stop).run = s.prepareChild policy id := by
  unfold program Store.prepareChild prepareChildWith removeSegment removeSegmentWith
  simp only [Observed.run_bind]
  congr 1
  apply congrArg (Bind.bind (PrepareIO.presenceIO (segmentPath s.root id)))
  funext present
  split
  · rw [Observed.run_bind, inspect_run]
    apply congrArg (Bind.bind (inspectChild (segmentPath s.root id)))
    funext xs
    cases xs with
    | mk items =>
      change (forM items.toArray _ >>= _ : Observed Unit).run = (forM items.toArray _ >>= _ : IO Unit)
      rw [List.forM_toArray,List.forM_toArray,Observed.run_bind]
      exact congrArg (fun op : IO PUnit => op >>= fun _ => IO.FS.removeDir (segmentPath s.root id))
        (Observed.run_forM items (fun item => leaf stop (IO.FS.removeFile (segmentPath s.root id / item.fileName))))
  · rfl

abbrev Witness (dir : FilePath) (policy : Policy) (stop : ControlCutIO.Stops) (origin : W) (d : Disk) :=
  (∃ (p : Point) (t : W) (α : Type) (a : IO α), Prefix dir origin p t ∧ Issued dir p a ∧ stop a t d) ∨
    ∃ v leaf t, Prefix dir origin .create v ∧ (CreateCutIO.program dir policy).visits v leaf t ∧ stop leaf.action t d

private abbrev SafeAt (dir : FilePath) (policy : Policy) (stop : ControlCutIO.Stops) (origin : W)
    (a : Observed α) (w : W) (ok : α → W → Prop) :=
  Safe a w ok (fun _ => True) (Witness dir policy stop origin)

private theorem callSafe (stop : ControlCutIO.Stops) {a : IO α} (path : Prefix dir origin p w)
    (issued : Issued dir p a) (ok : ∀ x t, a w = .ok x t → post x t) :
    SafeAt dir policy stop origin (leaf stop a) w post := by
  constructor
  · unfold IOReturns
    change match a w with | .ok x t => post x t | .error .. => True
    cases ran : a w with
    | error => trivial
    | ok x t => exact ok x t ran
  · exact fun _ cut => .inl ⟨_,_,_,_,path,issued,cut⟩

private theorem trivialReturn (ok : post x w) : SafeAt dir policy stop origin (pure x) w post :=
  ⟨ok,fun _ f => False.elim f⟩

private theorem rejected (e : IO.Error) (next : α → Observed β) :
    SafeAt dir policy stop origin (throw e >>= next) w post := by
  apply Safe.bind (mid := fun _ _ => False)
  · exact ⟨trivial, fun _ f => False.elim f⟩
  · intro _ _ h; contradiction

private def member (stop : ControlCutIO.Stops) (dir : FilePath) (item : IO.FS.DirEntry) (_ : PUnit) :
    Observed (ForInStep PUnit) := do
  let path := dir / item.fileName
  unless childName item.fileName do throw (IO.userError s!"unexpected child {path}")
  regularCheck path (← leaf stop path.symlinkMetadata)
  return .yield ()

private theorem validate (rest : List IO.FS.DirEntry) (path : Prefix dir origin (.validate all rest) w) :
    SafeAt dir policy stop origin (forIn rest () (member stop dir)) w (fun _ t => Prefix dir origin (.erase all) t) := by
  induction rest generalizing w with
  | nil => exact trivialReturn (.more path .validated)
  | cons item rest ih =>
    rw [List.forIn_cons]
    apply Safe.bind (mid := fun step t => step = .yield () ∧ Prefix dir origin (.validate all rest) t)
    · unfold member
      split
      · rename_i named
        apply Safe.bind (callSafe stop path (.member named) (fun md _ ran => ran))
        intro md t ran
        by_cases good : ControlIO.Regular md
        · apply Safe.bind (mid := fun _ v => v = t)
          · constructor
            · change IOReturns (regular _ _) _ _ _
              simp [IOReturns, regular, good, Pure.pure,instMonadEIO._aux_5,EST.pure]
            · exact fun _ f => False.elim f
          · rintro _ _ rfl
            exact trivialReturn ⟨rfl, .more path (.checked named ran good)⟩
        · apply Safe.bind (mid := fun _ _ => False)
          · constructor
            · change IOReturns (regular _ _) _ _ _
              simp [IOReturns,regular,good,throw,throwThe,MonadExceptOf.throw,instMonadExceptOfEIO._aux_1,EST.throw]
            · exact fun _ f => False.elim f
          · intro _ _ h; contradiction
      · apply rejected
    · rintro _ _ ⟨rfl, reached⟩
      exact ih reached

private theorem inspectSafe (path : Prefix dir origin .dirStat w) :
    SafeAt dir policy stop origin (inspect stop dir) w (fun xs t => Prefix dir origin (.erase xs.toList) t) := by
  unfold inspect inspectChildWith
  apply Safe.bind (callSafe stop path .dirStat (fun _ _ ran => ran))
  intro md t ran
  split
  · rename_i good
    have checked := path.more (.checkedDir ran good)
    apply Safe.bind (callSafe stop checked .list (fun _ _ listed => checked.more (.listed listed)))
    intro xs v listed
    apply Safe.bind (mid := fun _ u => Prefix dir origin (.erase xs.toList) u)
    · rw [← Array.forIn_toList]
      exact validate xs.toList listed
    · intro _ _ valid
      exact trivialReturn valid
  · apply rejected

private theorem erase (rest : List IO.FS.DirEntry) (path : Prefix dir origin (.erase rest) w) :
    SafeAt dir policy stop origin (forM rest (fun item => leaf stop (IO.FS.removeFile (dir / item.fileName)))) w
      (fun _ t => Prefix dir origin (.erase []) t) := by
  induction rest generalizing w with
  | nil => exact trivialReturn path
  | cons item rest ih =>
    rw [List.forM_cons]
    apply Safe.bind (callSafe stop path .erase (fun _ _ ran => path.more (.unlinked ran)))
    intro _ _ next
    exact ih next

private theorem present (dir : FilePath) (w : W) :
    PrepareIO.presenceIO dir w =
      match dir.symlinkMetadata w with
      | .ok _ t => .ok true t
      | .error (.noFileOrDirectory ..) t => .ok false t
      | .error e t => .error e t := by
  unfold PrepareIO.presenceIO metadata?
  simp only [tryCatchThe, MonadExceptOf.tryCatch, instMonadExceptOfEIO._aux_3, EST.tryCatch,
    Functor.map, instMonadEIO._aux_1, EST.bind, Function.comp_apply, EST.pure,
    Bind.bind,instMonadEIO._aux_13]
  cases dir.symlinkMetadata w with
  | ok => rfl
  | error e => cases e <;> rfl

theorem covered (hit : (program s c.policy (c.active + 1) stop).cuts w d) : Witness (successorDir s c) c.policy stop w d := by
  let dir := successorDir s c
  suffices all : SafeAt dir c.policy stop w (program s c.policy (c.active + 1) stop) w (fun _ _ => True) from all.cut d hit
  unfold program prepareChildWith removeSegmentWith
  apply Safe.bind (mid := fun _ t => Prefix dir w .mkdir t)
  · apply Safe.bind (mid := fun present t => Prefix dir w (if present then .dirStat else .mkdir) t)
    · constructor
      · change IOReturns (PrepareIO.presenceIO dir) w _ _
        unfold IOReturns
        rw [present]
        cases stat : dir.symlinkMetadata w with
        | ok md t => exact .more .start (.present stat)
        | error e t => cases e <;> first | trivial | exact .more .start (.absent stat)
      · exact fun _ cut => .inl ⟨_,_,_,_,.start,.presence,cut⟩
    · intro yes t path
      cases yes with
      | false => exact trivialReturn path
      | true =>
        apply Safe.bind (inspectSafe path)
        intro xs _ inspected
        apply Safe.bind (mid := fun _ t => Prefix dir w (.erase []) t)
        · cases xs with
          | mk xs =>
            change Safe (forM xs.toArray (fun item => leaf stop (IO.FS.removeFile (dir / item.fileName)))) _ _ _ _
            rw [List.forM_toArray]
            exact erase xs inspected
        · intro _ _ p
          exact callSafe stop p .rmdir fun _ _ ran => p.more (.removed ran)
  · intro _ t p
    apply Safe.bind (callSafe stop p .mkdir (fun _ _ ran => p.more (.made ran)))
    intro _ v entered
    constructor
    · unfold IOReturns
      split <;> trivial
    · rintro d ⟨leaf,t,visit,cut⟩
      exact .inr ⟨_,_,_,entered,visit,cut⟩

end WalRecoverySlice.Segmented.Native.PrepareCutIO
