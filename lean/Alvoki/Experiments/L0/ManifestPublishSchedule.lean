import Alvoki.Experiments.L0.NativeManifestPublish

namespace ExperimentalL0.NativeManifestPublish
open System DurableBlob

inductive Leaf where
  | openFile (path : FilePath) (mode : IO.FS.Mode)
  | write (h : IO.FS.Handle) (bytes : ByteArray)
  | flush (h : IO.FS.Handle)
  | sync (h : IO.FS.Handle)
  | rename (src dst : FilePath)
  | read (path : FilePath)

def Leaf.Result : Leaf → Type
  | .openFile .. => IO.FS.Handle
  | .read _ => ByteArray
  | _ => Unit

def Leaf.io : (op : Leaf) → IO op.Result
  | .openFile path mode => IO.FS.Handle.mk path mode
  | .write h data => h.write data
  | .flush h => h.flush
  | .sync h => DurableBlob.syncHandle h
  | .rename src dst => IO.FS.rename src dst
  | .read path => IO.FS.readBinFile path

def leaf (dir : FilePath) (bytes : ByteArray) : Point → Leaf
  | .openWriter => .openFile (dir / "BLOB.next") .write
  | .write h => .write h bytes
  | .flush h => .flush h
  | .sync h => .sync h
  | .rename _ => .rename (dir / "BLOB.next") (dir / "BLOB")
  | .openDirectory _ => .openFile dir .read
  | .barrier _ fd => .sync fd

def reached : EST.Out IO.Error IO.RealWorld α → W
  | .ok _ w | .error _ w => w

structure Observed (α : Type) where
  run : IO α
  visit : W → Leaf → W → Prop
  boundary : W → W → Prop

instance : Monad Observed where
  pure x := ⟨pure x,fun _ _ _ => False,fun w t => t = w⟩
  bind a f := ⟨a.run >>= fun x => (f x).run,
    fun w op t => a.visit w op t ∨ ∃ x u, a.run w = .ok x u ∧ (f x).visit u op t,
    fun w t => a.boundary w t ∨ ∃ x u, a.run w = .ok x u ∧ (f x).boundary u t⟩

def issue (op : Leaf) : Observed op.Result :=
  ⟨op.io, fun w l t => l = op ∧ t = w, fun w t => t = w ∨ t = reached (op.io w)⟩

def observed : DurableBlob.Primitives Observed IO.FS.Handle :=
  ⟨fun path mode => issue (.openFile path mode), fun h bytes => issue (.write h bytes),
    fun h => issue (.flush h), fun h => issue (.sync h), fun src dst => issue (.rename src dst),
    fun path => issue (.read path)⟩

def schedule (dir : FilePath) (bytes : ByteArray) := (observed.backend dir).publish bytes

theorem schedule_erase (dir : FilePath) (bytes : ByteArray) :
    (schedule dir bytes).run = (native dir).publish bytes := rfl

inductive Boundary (dir : FilePath) (bytes : ByteArray) (origin : W) : W → Prop where
  | before : Prefix dir bytes origin p w → Boundary dir bytes origin w
  | after : Prefix dir bytes origin p w → Boundary dir bytes origin (reached (action dir bytes p w))

private structure Cover (dir : FilePath) (bytes : ByteArray) (origin w : W) (a : Observed α)
    (post : α → W → Prop) : Prop where
  visit : ∀ op t, a.visit w op t → ∃ p, Prefix dir bytes origin p t ∧ op = leaf dir bytes p
  boundary : ∀ t, a.boundary w t → Boundary dir bytes origin t
  returned : ∀ x t, a.run w = .ok x t → post x t

variable {bytes : ByteArray}

private theorem Cover.bind {f : α → Observed β} (one : Cover dir bytes origin w a middle)
    (next : ∀ x t, middle x t → Cover dir bytes origin t (f x) post) :
    Cover dir bytes origin w (a >>= f) post := by
  constructor
  · rintro op t (before | ⟨x,u,ran,h⟩)
    · exact one.visit op t before
    · exact (next x u (one.returned x u ran)).visit op t h
  · rintro t (before | ⟨x,u,ran,h⟩)
    · exact one.boundary t before
    · exact (next x u (one.returned x u ran)).boundary t h
  · intro x t ran
    change (a.run >>= _) w = .ok x t at ran
    simp only [Bind.bind, instMonadEIO._aux_13, EST.bind] at ran
    split at ran
    next y u eq => exact (next y u (one.returned y u eq)).returned x t ran
    next => contradiction

private theorem Cover.pure (pc : Boundary dir bytes origin w) (ok : post x w) :
    Cover dir bytes origin w (pure x) post :=
  ⟨fun _ _ h => h.elim, fun _ h => h ▸ pc, fun _ _ ran => by cases ran; exact ok⟩

private theorem Cover.issue (pc : Prefix dir bytes origin p w) :
    Cover dir bytes origin w (issue (leaf dir bytes p))
      (fun x t => (leaf dir bytes p).io w = .ok x t) := by
  constructor
  · rintro _ _ ⟨rfl,rfl⟩; exact ⟨p,pc,rfl⟩
  · rintro _ (rfl | rfl)
    · exact .before pc
    · cases p <;> exact .after pc
  · exact fun _ _ h => h

private theorem covered (dir : FilePath) (bytes : ByteArray) (w : W) :
    Cover dir bytes w w (schedule dir bytes) (fun _ _ => True) := by
  unfold schedule DurableBlob.Primitives.backend Files.backend DurableBlob.Primitives.files publishWith observed
  apply Cover.bind (middle := fun h t => Prefix dir bytes w (.sync h) t)
  · apply (Cover.issue (p := .openWriter) .initial).bind
    intro h t opened
    have writer := Prefix.next (dir := dir) (bytes := bytes) .initial opened (by rfl)
    apply (Cover.issue writer).bind
    intro _ u written
    have flushing := writer.next written (by rfl)
    apply (Cover.issue flushing).bind
    intro _ v flushed
    have syncing := flushing.next flushed (by rfl)
    exact Cover.pure (.before syncing) syncing
  intro h t syncedAt
  apply (Cover.issue syncedAt).bind
  intro _ u synced
  have replace := syncedAt.next synced (by rfl)
  apply (Cover.issue replace).bind
  intro _ v renamed
  have directory := replace.next renamed (by rfl)
  apply (Cover.issue directory).bind
  intro fd z opened
  have barrier := directory.next opened (by rfl)
  have finished := Cover.issue barrier
  exact ⟨finished.visit,finished.boundary,fun _ _ _ => trivial⟩

theorem schedule_visit (h : (schedule dir bytes).visit origin op t) :
    ∃ p, Prefix dir bytes origin p t ∧ op = leaf dir bytes p := (covered dir bytes origin).visit _ _ h

theorem schedule_boundary (h : (schedule dir bytes).boundary origin w) : Boundary dir bytes origin w :=
  (covered dir bytes origin).boundary _ h

/-- An observation is either between IO calls or inside the actual issued call. -/
inductive Cut (stop : Stop) (dir : FilePath) (bytes : ByteArray) (origin : W) : W → Prop where
  | boundary : (schedule dir bytes).boundary origin t → Cut stop dir bytes origin t
  | during : (schedule dir bytes).visit origin op w → stop op.io w t → Cut stop dir bytes origin t

theorem Cut.state (cut : Cut stop dir bytes origin t) (ops : Primitives dir bytes origin P image stop m)
    (start : P origin) (reserved : m.Private dir origin) (valid : (image origin).Stable old) :
    P t ∧ (image t).Admits old (some bytes) := by
  cases cut with
  | boundary b =>
    cases schedule_boundary b with
    | before pc =>
      obtain ⟨frame,_,entry⟩ := pc.state ops start reserved valid
      exact ⟨frame,entry.admits⟩
    | after pc =>
      have result := pc.report ops start reserved valid
      generalize eq : action _ _ _ _ = out at result ⊢
      cases out <;> exact result
  | during visit fault =>
    obtain ⟨p,pc,rfl⟩ := schedule_visit visit
    cases p <;> exact
      ⟨(interrupted ops start reserved valid pc fault).1,(interrupted ops start reserved valid pc fault).2.admits⟩

end ExperimentalL0.NativeManifestPublish
