import Alvoki.Experiments.L0.NativeTableCreate

namespace ExperimentalL0.NativeTableCreate.Schedule
open System NativeScope
open NativeTableWriter (ObservedAt)

/-- The outer allocator and directory operations, together with the existing
streaming writer markers. Each site records its concrete primitive. -/
inductive Leaf where
  | stat (path : FilePath)
  | writer (inner : NativeTableWriter.Leaf)
  | openDirectory (dir : FilePath)
  | barrier (fd : IO.FS.Handle)

def Leaf.Result : Leaf → Type
  | .stat _ => IO.FS.Metadata
  | .writer inner => inner.Result
  | .openDirectory _ => IO.FS.Handle
  | .barrier _ => Unit

def Leaf.action : (l : Leaf) → IO l.Result
  | .stat path => path.symlinkMetadata
  | .writer inner => inner.action
  | .openDirectory dir => IO.FS.Handle.mk dir .read
  | .barrier fd => Native.syncHandle fd

abbrev O := ObservedAt Leaf
abbrev M := ExceptT String O

def issue (l : Leaf) : O l.Result := ⟨l.action,fun w site t => site = l ∧ t = w⟩

def existsAt (path : FilePath) : O Bool :=
  tryCatchThe IO.Error (issue (.stat path) >>= fun _ => pure true)
    (fun e => match e with | .noFileOrDirectory .. => pure false | other => throw other)

private theorem exists_run (p : FilePath) : (existsAt p).run = Native.pathExists p := by
  unfold existsAt Native.pathExists
  change tryCatchThe IO.Error (_ >>= _) _ = tryCatchThe IO.Error (_ >>= _) _
  congr 1
  funext e
  cases e <;> rfl

def file (path : FilePath) (id : UInt64) (rows : Rows) : O Unit :=
  ⟨(NativeTableWriter.schedule path id rows).run, fun w site t =>
    ∃ inner, site = .writer inner ∧ NativeTableWriter.Visits path id rows w inner t⟩

def parent (dir : FilePath) : O Unit := do
  let h ← issue (.openDirectory dir)
  issue (.barrier h)

def liftOp (a : O α) : M α :=
  ExceptT.mk ⟨Except.ok <$> a.run,a.visits⟩

def trace (dir : FilePath) (rows : Rows) : M UInt64 :=
  createTableUnder dir (fun path => liftOp (existsAt path)) (fun path id xs => liftOp (file path id xs))
    (fun d => liftOp (parent d)) rows

abbrev Prefix (dir : FilePath) (rows : Rows) := (trace dir rows).run.visits

def project (a : M α) : ExceptT String IO α := ExceptT.mk a.run.run

private theorem project_bind (a : M α) (f : α → M β) :
    project (a >>= f) = (project a >>= fun x => project (f x)) := by
  apply ExceptT.ext
  rw [ExceptT.run_bind]
  unfold project
  rw [ExceptT.run_bind]
  apply congrArg (Bind.bind a.run.run)
  funext x
  cases x <;> rfl

private theorem project_lift (a : O α) : project (liftOp a) = (liftM a.run : ExceptT String IO α) := rfl

private theorem project_free (dir : FilePath) (n : Nat) :
    project (freeTableId (fun id => liftOp (existsAt (tablePath dir id))) n) =
      freeTableId (occupied dir) n := by
  rw [freeTableId]
  conv => rhs; rw [freeTableId]
  split
  · rfl
  · rw [project_bind, project_lift, exists_run]
    apply congrArg (Bind.bind _)
    funext result
    cases result
    · rfl
    · exact project_free dir (n+1)
termination_by UInt64.size - n
decreasing_by omega

/-- Both typed and native errors erase to the production table creator. -/
theorem erase (dir : FilePath) (rows : Rows) : project (trace dir rows) = Native.createTable dir rows := by
  unfold trace Native.createTable createTableUnder createTableAt
  rw [project_bind, project_free]
  apply congrArg (Bind.bind _)
  funext id
  rw [project_bind, project_lift]
  change (liftM ((NativeTableWriter.schedule _ _ _).run) : ExceptT String IO Unit) >>= _ = _
  rw [NativeTableWriter.erase]
  apply congrArg (Bind.bind _)
  funext _
  rw [project_bind, project_lift]
  rfl

private theorem visits_bind {a : M α} {f : α → M β} (hit : (a >>= f).run.visits w site last) :
    a.run.visits w site last ∨ ∃ x t, (project a).run w = .ok (.ok x) t ∧ (f x).run.visits t site last := by
  rw [ExceptT.run_bind] at hit
  rcases hit with first | ⟨x,t,ran,later⟩
  · exact .inl first
  · cases x with
    | error e => contradiction
    | ok x => exact .inr ⟨x,t,ran,later⟩

private theorem stat_only (hit : (existsAt path).visits w site last) : site = .stat path ∧ last = w := by
  rcases hit with (issued | ⟨_,_,_,impossible⟩) | ⟨e,_,_,handler⟩
  · exact issued
  · contradiction
  · cases e <;> contradiction

private theorem lift_report {a : O α} (ran : (project (liftOp a)).run w = .ok (.ok x) t) :
    a.run w = .ok x t := by
  change (Except.ok <$> a.run : IO (Except String _)) w = _ at ran
  cases out : a.run w with
  | error => simp [Functor.map,instMonadEIO._aux_1,EST.bind,out] at ran
  | ok y u =>
    simp [Functor.map,instMonadEIO._aux_1,EST.bind,EST.pure,out] at ran
    obtain ⟨rfl,rfl⟩ := ran
    rfl

private theorem free_cover {n : Nat} (prior : Visited dir start n w)
    (hit : (freeTableId (fun id => liftOp (existsAt (tablePath dir id))) n).run.visits w site last) :
    Visits dir rows start site.action last := by
  rw [freeTableId] at hit
  split at hit
  · contradiction
  · rename_i fits
    rcases visits_bind hit with probing | ⟨b,t,reported,later⟩
    · obtain ⟨rfl,rfl⟩ := stat_only probing
      exact .probe prior (by omega)
    · cases b with
      | false => contradiction
      | true =>
        have actual := lift_report reported
        rw [exists_run] at actual
        exact free_cover (prior.next (by omega) actual) later
termination_by UInt64.size - n
decreasing_by omega

private theorem checked_ok {a : ExceptT String IO α} (reported : a.run w = .ok (.ok x) t) :
    Native.checked a w = .ok x t := by
  simp only [Native.checked, Bind.bind, instMonadEIO._aux_13, EST.bind, reported,
    Pure.pure, instMonadEIO._aux_5, EST.pure]

private theorem cover_parent {dir : FilePath} {id : UInt64}
    (allocated : allocate dir 0 start = .ok id reserved)
    (wrote : Native.buildSynced (tablePath dir id) id rows reserved = .ok () built)
    (hit : (parent dir).visits built leaf last) : Visits dir rows start leaf.action last := by
  rcases hit with ⟨rfl,rfl⟩ | ⟨fd,entered,opened,rfl,rfl⟩
  · exact .directory allocated wrote
  · exact .sync allocated wrote opened

private theorem cover_file {dir : FilePath} {id : UInt64}
    (allocated : allocate dir 0 start = .ok id reserved)
    (hit : (file (tablePath dir id) id rows).visits reserved leaf last) : Visits dir rows start leaf.action last := by
  obtain ⟨inner,rfl,visit⟩ := hit
  exact .writer allocated visit

private def finish (dir : FilePath) (id : UInt64) : M UInt64 := do
  liftOp (parent dir)
  return id

private def writeAt (dir : FilePath) (id : UInt64) (rows : Rows) : M UInt64 := do
  liftOp (file (tablePath dir id) id rows)
  finish dir id

private theorem finish_cover {id : UInt64} (allocated : allocate dir 0 start = .ok id reserved)
    (wrote : Native.buildSynced (tablePath dir id) id rows reserved = .ok () built)
    (hit : (finish dir id).run.visits built leaf last) : Visits dir rows start leaf.action last := by
  rcases visits_bind (a := liftOp (parent dir)) (f := fun _ => pure id) hit with visited | ⟨_,_,_,impossible⟩
  · exact cover_parent allocated wrote visited
  · contradiction

private theorem write_cover {id : UInt64} (allocated : allocate dir 0 start = .ok id reserved)
    (hit : (writeAt dir id rows).run.visits reserved leaf last) : Visits dir rows start leaf.action last := by
  rcases visits_bind (a := liftOp (file (tablePath dir id) id rows)) (f := fun _ => finish dir id) hit with
    writing | ⟨_,built,build,dirVisit⟩
  · exact cover_file allocated writing
  · have wrote := lift_report build
    change (NativeTableWriter.schedule _ _ _).run _ = _ at wrote
    rw [NativeTableWriter.erase] at wrote
    exact finish_cover allocated wrote dirVisit

private theorem allocationReported {id : UInt64} {n : Nat}
    (chosen : (project (freeTableId (fun id => liftOp (existsAt (tablePath dir id))) n)).run w = .ok (.ok id) t) :
    allocate dir n w = .ok id t := by
  rw [project_free] at chosen
  exact checked_ok chosen

private theorem firstCover {n : Nat} (prior : Visited dir start n w)
    (hit : ((freeTableId (fun id => liftOp (existsAt (tablePath dir id))) n : M UInt64) >>= fun id =>
      writeAt dir id rows).run.visits w leaf last)
    (same : allocate dir 0 start = allocate dir n w) : Visits dir rows start leaf.action last := by
  rcases visits_bind (a := freeTableId (fun id => liftOp (existsAt (tablePath dir id))) n)
    (f := fun id => writeAt dir id rows) hit with search | ⟨_,_,chosen,rest⟩
  · exact free_cover prior search
  · exact write_cover (same.trans (allocationReported chosen)) rest

private theorem trace_shape (dir : FilePath) (rows : Rows) :
    trace dir rows = (freeTableId (fun id => liftOp (existsAt (tablePath dir id))) 0 >>= fun id => writeAt dir id rows) := by
  unfold trace createTableUnder createTableAt writeAt finish
  rfl

theorem cover (hit : Prefix dir rows start leaf last) : Visits dir rows start leaf.action last := by
  unfold Prefix at hit
  rw [trace_shape] at hit
  exact firstCover (.start : Visited dir start 0 start) hit rfl

end ExperimentalL0.NativeTableCreate.Schedule
