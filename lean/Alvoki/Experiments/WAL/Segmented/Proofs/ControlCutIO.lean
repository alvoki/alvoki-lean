import Alvoki.Experiments.WAL.Segmented.Proofs.ControlIO

namespace WalRecoverySlice.Segmented.Native.ControlCutIO
open System Model Alvoki.NativePost

/-- A power cut is an observation inside one issued OS call. Lean IO
describes only calls which return a result. The interrupted call has no
return-value premise. -/
abbrev Stops := {α : Type} → IO α → W → Disk → Prop

inductive OpKind where
  | privateFile | publishName | syncRoot

/-- The segment files and their bindings are outside a CONTROL operation's
write set. Both controls can select the old segments and the freshly
prepared successor. Contents of other private paths are unconstrained. -/
structure Files (c : Control) (before after : Disk) : Prop where
  names : ∀ i, c.selects i ∨ i = c.active + 1 →
    (i ∈ before.liveNames → i ∈ after.liveNames) ∧ (i ∈ before.durableNames → i ∈ after.durableNames)
  data : ∀ i, c.selects i ∨ i = c.active + 1 → after.segment i = before.segment i
  cursor : ∀ i, i = c.active ∨ i = c.active + 1 → after.cursor i = before.cursor i

theorem Files.refl (c : Control) (d : Disk) : Files c d d :=
  ⟨fun _ _ => ⟨id, id⟩, fun _ _ => rfl, fun _ _ => rfl⟩

theorem Files.trans (a : Files c x y) (b : Files c y z) : Files c x z :=
  ⟨fun i sel => ⟨(b.names i sel).1 ∘ (a.names i sel).1, (b.names i sel).2 ∘ (a.names i sel).2⟩,
   fun i sel => (b.data i sel).trans (a.data i sel), fun i sel => (b.cursor i sel).trans (a.cursor i sel)⟩

def next (c : Control) := {c with active := c.active + 1}

/-- Report from an individual namespace operation: rename is atomic, its
directory entry may already have persisted, and a successful root fsync
makes the live binding durable. -/
def Effect (c : Control) (kind : OpKind) (completed : Bool) (before after : Disk) : Prop :=
  let same := after.liveControl = before.liveControl ∧ after.durableControl = before.durableControl
  match kind with
  | .privateFile => same
  | .publishName => (completed = false ∧ same) ∨
    (after.liveControl = some (next c) ∧ (after.durableControl = before.durableControl ∨ after.durableControl = some (next c)))
  | .syncRoot => after.liveControl = before.liveControl ∧
    ((completed = false ∧ after.durableControl = before.durableControl) ∨ after.durableControl = before.liveControl)

inductive Point
  | stat | unlink | openWriter | unbuffer (h : IO.FS.Handle) | write (h : IO.FS.Handle)
  | flush (h : IO.FS.Handle) | syncWriter (h : IO.FS.Handle) | rename (writer : IO.FS.Handle) | directory (writer : IO.FS.Handle) | done

inductive Issued (s : Store) (c : Control) : Point → {α : Type} → IO α → OpKind → Prop where
  | stat : Issued s c .stat (s.root / "CONTROL.next").symlinkMetadata .privateFile
  | unlink : Issued s c .unlink (IO.FS.removeFile (s.root / "CONTROL.next")) .privateFile
  | openWriter : Issued s c .openWriter (IO.FS.Handle.mk (s.root / "CONTROL.next") .writeNew) .privateFile
  | unbuffer h : Issued s c (.unbuffer h) (disableBuffering h) .privateFile
  | write h : Issued s c (.write h) (h.write (ControlCodec.encode (next c))) .privateFile
  | flush h : Issued s c (.flush h) h.flush .privateFile
  | syncWriter h : Issued s c (.syncWriter h) (syncHandle h) .privateFile
  | rename h : Issued s c (.rename h) (IO.FS.rename (s.root / "CONTROL.next") (s.root / "CONTROL")) .publishName
  | directory h : Issued s c (.directory h) (syncHandle s.directory) .syncRoot

/-- Only the concrete control-flow edges that continue the operation. A
missing staging path skips unlink. An invalid path cannot reach unlink. -/
inductive Step (s : Store) (c : Control) : Point → W → Point → W → Prop where
  | regular : (s.root / "CONTROL.next").symlinkMetadata w = .ok md t → ControlIO.Regular md → Step s c .stat w .unlink t
  | missing : (s.root / "CONTROL.next").symlinkMetadata w = .error (.noFileOrDirectory x y z) t →
      Step s c .stat w .openWriter t
  | cleared : IO.FS.removeFile (s.root / "CONTROL.next") w = .ok () t → Step s c .unlink w .openWriter t
  | opened : IO.FS.Handle.mk (s.root / "CONTROL.next") .writeNew w = .ok h t → Step s c .openWriter w (.unbuffer h) t
  | unbuffered : disableBuffering h w = .ok () t → Step s c (.unbuffer h) w (.write h) t
  | written : h.write (ControlCodec.encode (next c)) w = .ok () t → Step s c (.write h) w (.flush h) t
  | flushed : h.flush w = .ok () t → Step s c (.flush h) w (.syncWriter h) t
  | synced : syncHandle h w = .ok () t → Step s c (.syncWriter h) w (.rename h) t
  | renamed : IO.FS.rename (s.root / "CONTROL.next") (s.root / "CONTROL") w = .ok () t → Step s c (.rename h) w (.directory h) t
  | settled : syncHandle s.directory w = .ok () t → Step s c (.directory h) w .done t

inductive Prefix (s : Store) (c : Control) (origin : W) : Point → W → Prop where
  | start : Prefix s c origin .stat origin
  | more : Prefix s c origin atPoint w → Step s c atPoint w after t → Prefix s c origin after t

private def barrier (s : Store) := syncHandle s.directory
private def publish (s : Store) := IO.FS.rename (s.root / "CONTROL.next") (s.root / "CONTROL") >>= fun _ => barrier s
private def sync (s : Store) (h : IO.FS.Handle) := syncHandle h >>= fun _ => publish s
private def flush (s : Store) (h : IO.FS.Handle) := h.flush >>= fun _ => sync s h
private def write (s : Store) (c : Control) (h : IO.FS.Handle) := h.write (ControlCodec.encode (next c)) >>= fun _ => flush s h
private def unbuffer (s : Store) (c : Control) (h : IO.FS.Handle) := disableBuffering h >>= fun _ => write s c h
private def reserve (s : Store) (c : Control) := IO.FS.Handle.mk (s.root / "CONTROL.next") .writeNew >>= unbuffer s c

def remaining (s : Store) (c : Control) : Point → IO Unit
  | .stat => removeRegular (s.root / "CONTROL.next") >>= fun _ => reserve s c
  | .unlink => IO.FS.removeFile (s.root / "CONTROL.next") >>= fun _ => reserve s c
  | .openWriter => reserve s c
  | .unbuffer h => unbuffer s c h
  | .write h => write s c h
  | .flush h => flush s h
  | .syncWriter h => sync s h
  | .rename _ => publish s
  | .directory _ => barrier s
  | .done => pure ()

private theorem concrete (s : Store) (c : Control) (active : (next c).active ≤ ControlCodec.wordMax)
    (discarded : (next c).discarded ≤ ControlCodec.wordMax) :
    checked (s.callbacks.publishControl (next c)) = remaining s c .stat := by
  rw [s.publishControl_io _ active discarded]
  funext w
  unfold DurableBlob.publishWith Store.stageControl
  unfold remaining reserve unbuffer write flush sync publish barrier
  simp only [Bind.bind, instMonadEIO._aux_13, EST.bind, Pure.pure, instMonadEIO._aux_5, EST.pure]
  cases clear : removeRegular (s.root / "CONTROL.next") w <;> simp_all only
  rename_i t
  cases opened : IO.FS.Handle.mk (s.root / "CONTROL.next") .writeNew t <;> simp_all only
  rename_i h u
  cases mode : disableBuffering h u <;> simp_all only
  rename_i v
  cases data : h.write (ControlCodec.encode (next c)) v <;> simp_all only
  rename_i x
  cases flushed : h.flush x <;> simp_all only

private theorem Step.consume (edge : Step s c p w q t) : remaining s c p w = remaining s c q t := by
  cases edge with
  | regular observed valid =>
    simp only [ControlIO.Regular] at valid
    simp [remaining, removeRegular, removeRegularWith, Native.regular, metadata?, tryCatchThe, MonadExceptOf.tryCatch,
      instMonadExceptOfEIO._aux_3, EST.tryCatch, Functor.map, instMonadEIO._aux_1, EST.bind,
      Bind.bind, instMonadEIO._aux_13, observed, valid, Pure.pure, instMonadEIO._aux_5, EST.pure]
  | missing observed =>
    simp [remaining, removeRegular, removeRegularWith, metadata?, tryCatchThe, MonadExceptOf.tryCatch, instMonadExceptOfEIO._aux_3,
      EST.tryCatch, Functor.map, instMonadEIO._aux_1, EST.bind, Bind.bind, instMonadEIO._aux_13,
      observed, Pure.pure, instMonadEIO._aux_5, EST.pure]
  | _ =>
    simp_all [remaining, reserve, unbuffer, write, flush, sync, publish, barrier, Bind.bind, instMonadEIO._aux_13,
      EST.bind, Pure.pure, instMonadEIO._aux_5, EST.pure]

/-- Resumption at every enumerated prefix starts at the exact world
and descriptor used by the real callback. -/
theorem Prefix.continuation (path : Prefix s c origin p w) (active : (next c).active ≤ ControlCodec.wordMax)
    (discarded : (next c).discarded ≤ ControlCodec.wordMax) :
    checked (s.callbacks.publishControl (next c)) origin = remaining s c p w := by
  induction path with
  | start => rw [concrete s c active discarded]
  | more _ step ih => exact ih.trans step.consume

def Point.kind : Point → OpKind
  | .rename _ => .publishName
  | .directory _ => .syncRoot
  | _ => .privateFile

/-- Inode and selector evidence consumed by this one reached operation.
The rename carries the exclusive writer from open, with its exact synced
bytes. The directory barrier carries that same inode at its new name. -/
def Operand (m : ControlIO.Media) (s : Store) (c : Control) (disk : W → Disk) (w : W) : Point → Prop
  | .unbuffer h | .write h => m.bound h (s.root / "CONTROL.next") w
  | .flush h => m.Written h (s.root / "CONTROL.next") (next c) w
  | .syncWriter h => m.Written h (s.root / "CONTROL.next") (next c) w ∧ (disk w).staged = some (next c)
  | .rename h => m.Synced h (s.root / "CONTROL.next") (next c) w ∧ (disk w).staged = some (next c)
  | .directory h => m.Synced h (s.root / "CONTROL") (next c) w ∧ (disk w).liveControl = some (next c)
  | _ => True

private def ModelAt (_io : ControlIO.Primitives s (next c) r origin initial R disk) (w : W) : Point → Prop
  | .stat => w = origin
  | .unlink => ∃ md, (s.root / "CONTROL.next").symlinkMetadata origin = .ok md w ∧ ControlIO.Regular md
  | .openWriter => removeRegular (s.root / "CONTROL.next") origin = .ok () w
  | .unbuffer h => ControlIO.WriterStage s (next c) origin .opened h w
  | .write h => ControlIO.WriterStage s (next c) origin .unbuffered h w
  | .flush h => ControlIO.WriterStage s (next c) origin .written h w
  | .syncWriter h => ControlIO.WriterStage s (next c) origin .flushed h w ∧
      ∃ staged, (ControlIO.stage r (next c)).run initial = .ok (.ok ()) staged ∧ R w staged
  | .rename h => ControlIO.WriterStage s (next c) origin .synced h w ∧
      ∃ staged synced, (ControlIO.stage r (next c)).run initial = .ok (.ok ()) staged ∧
        (ControlIO.syncStage r).run staged = .ok (.ok ()) synced ∧ R w synced
  | _ => True

private theorem returned {a : IO α} {b : M β} (p : AppendIO.At a b w s ok bad) (ran : a w = .ok x t) :
    ∃ y v, b.run s = .ok (.ok y) v ∧ ok x y t v := by
  unfold AppendIO.At at p
  rw [ran] at p
  cases model : b.run s <;> rw [model] at p
  case ok reply v => cases reply <;> first | contradiction | exact ⟨_,_,rfl,p⟩
  case error => contradiction

private theorem clearMissing {path : FilePath} (stat : path.symlinkMetadata w = .error (.noFileOrDirectory x y z) t) :
    removeRegular path w = .ok () t := by
  simp [removeRegular, removeRegularWith, metadata?, tryCatchThe, MonadExceptOf.tryCatch, instMonadExceptOfEIO._aux_3,
    EST.tryCatch, Functor.map, instMonadEIO._aux_1, EST.bind, Bind.bind, instMonadEIO._aux_13,
    stat, Pure.pure, instMonadEIO._aux_5, EST.pure]

private theorem clearUnlinked {path : FilePath} (stat : path.symlinkMetadata w = .ok md t) (valid : ControlIO.Regular md)
    (unlinked : IO.FS.removeFile path t = .ok () v) : removeRegular path w = .ok () v := by
  simp [removeRegular, removeRegularWith, metadata?, Native.regular, ControlIO.Regular, tryCatchThe, MonadExceptOf.tryCatch, instMonadExceptOfEIO._aux_3,
    EST.tryCatch, Functor.map, instMonadEIO._aux_1, EST.bind, Bind.bind, instMonadEIO._aux_13,
    stat, valid, unlinked, Pure.pure, instMonadEIO._aux_5, EST.pure] at *

/-- The returning producer supplies the operands of every completed step
before the interrupted call. No return is needed from the last call. -/
theorem Prefix.operand (path : Prefix s c origin site w)
    (io : ControlIO.Primitives s (next c) r origin initial R disk) :
    Operand io.media s c disk w site := by
  suffices h : ModelAt io w site ∧ Operand io.media s c disk w site from h.2
  induction path with
  | start => exact ⟨rfl, trivial⟩
  | more prior edge ih =>
    obtain ⟨pc, inode⟩ := ih
    cases edge with
    | regular stat valid => exact ⟨⟨_, pc ▸ stat, valid⟩, trivial⟩
    | missing stat =>
      change _ = origin at pc
      rw [pc] at stat
      exact ⟨clearMissing stat, trivial⟩
    | cleared unlinked =>
      obtain ⟨md, stat, valid⟩ := pc
      exact ⟨clearUnlinked stat valid unlinked, trivial⟩
    | opened openRun =>
      have receipt := io.openWriter _ pc
      rw [IOReturns, openRun] at receipt
      exact ⟨.opened pc openRun, receipt⟩
    | unbuffered ran =>
      have receipt := io.unbuffered _ _ pc inode
      rw [IOReturns, ran] at receipt
      exact ⟨pc.unbuffered ran, receipt⟩
    | written ran =>
      have receipt := io.write _ _ pc inode
      rw [IOReturns, ran] at receipt
      exact ⟨pc.written ran, receipt⟩
    | flushed ran =>
      obtain ⟨⟨⟩, u, model, frame, physical⟩ := returned (io.flush _ _ pc inode) ran
      exact ⟨⟨pc.flushed ran, u, model, frame⟩, physical⟩
    | synced ran =>
      obtain ⟨opened, u, stageRun, frame⟩ := pc
      obtain ⟨⟨⟩, v, syncRun, stayed, physical⟩ := returned
        (io.syncWriter _ _ _ opened stageRun frame inode.1 inode.2) ran
      exact ⟨⟨opened.synced ran, u, v, stageRun, syncRun, stayed⟩, physical⟩
    | renamed ran =>
      obtain ⟨synced, u, v, stageRun, syncRun, frame⟩ := pc
      obtain ⟨⟨⟩, _, _, _, physical⟩ := returned
        (io.renameFile _ _ _ _ synced stageRun syncRun frame inode.1 inode.2) ran
      exact ⟨trivial, physical⟩
    | settled => exact ⟨trivial, trivial⟩

structure Primitives (s : Store) (c : Control) (origin : W) (disk : W → Disk) (stop : Stops) (media : ControlIO.Media) : Prop where
  returned : ∀ p w q t, Prefix s c origin p w → Step s c p w q t → Operand media s c disk w p →
    Files c (disk w) (disk t) ∧ Effect c p.kind true (disk w) (disk t)
  stopped : ∀ p w, Prefix s c origin p w → ∀ {α} (a : IO α) k, Issued s c p a k → Operand media s c disk w p →
    ∀ d, stop a w d → Files c (disk w) d ∧ Effect c k false (disk w) d

def Authority (c : Control) (p : Point) (d : Disk) : Prop :=
  match p with
  | .directory _ => d.liveControl = some (next c) ∧ (d.durableControl = some c ∨ d.durableControl = some (next c))
  | .done => d.liveControl = some (next c) ∧ d.durableControl = some (next c)
  | _ => d.liveControl = some c ∧ d.durableControl = some c

private theorem advance (step : Step s c p w q t) (old : Authority c p a)
    (effect : Effect c p.kind true a b) : Authority c q b := by
  cases step <;> simp_all [Authority, Effect, Point.kind]

theorem Prefix.frame (io : ControlIO.Primitives s (next c) r origin initialState R disk)
    (prims : Primitives s c origin disk stop io.media) (path : Prefix s c origin p w)
    (initial : Authority c .stat (disk origin)) : Files c (disk origin) (disk w) ∧ Authority c p (disk w) := by
  induction path with
  | start => exact ⟨.refl .., initial⟩
  | more prior step ih =>
    obtain ⟨files, effect⟩ := prims.returned _ _ _ _ prior step (prior.operand io)
    exact ⟨ih.1.trans files, advance step ih.2 effect⟩

/-- Both sides of the atomic rename may be observed at the cut. After the
rename has returned, a root barrier may preserve either durable binding. -/
def Choices (c : Control) (d : Disk) :=
  (d.liveControl = some c ∧ d.durableControl = some c) ∨
  (d.liveControl = some (next c) ∧ (d.durableControl = some c ∨ d.durableControl = some (next c)))

private theorem atCut (site : Issued s c p action k) (old : Authority c p a)
    (effect : Effect c k false a b) : Choices c b := by
  cases site <;> simp_all [Authority, Effect, Choices] <;> grind

theorem survivor (io : ControlIO.Primitives s (next c) r origin initialState R disk)
    (prims : Primitives s c origin disk stop io.media) (path : Prefix s c origin p w)
    (issued : Issued s c p action k) (cut : stop action w d)
    (initial : Authority c .stat (disk origin)) (ready : ReadyLayout c history (disk origin))
    (full : (segmentHistory c.capacity c.active history).length = c.capacity)
    (named : c.active + 1 ∈ (disk origin).liveNames ∧ c.active + 1 ∈ (disk origin).durableNames)
    (fresh : Child.Installed c.policy ((disk origin).segment (c.active + 1)) ((disk origin).cursor (c.active + 1)) []) :
    Choices c d ∧ Recoverable (historyView c history) none d ∧ Recoverable (historyView c history) none d.powerLoss := by
  obtain ⟨previous, authority⟩ := path.frame io prims initial
  obtain ⟨last, effect⟩ := prims.stopped _ _ path _ _ issued (path.operand io) _ cut
  have files := previous.trans last
  have names (i) (sel : c.selects i) :=
    And.intro ((files.names i (.inl sel)).1 (ready.layout.names i sel).1)
      ((files.names i (.inl sel)).2 (ready.layout.names i sel).2)
  have old := ready.frame names (fun i h => files.data i (.inl h)) (files.cursor _ (.inl rfl))
  have empty : Child.Installed c.policy (d.segment (c.active + 1)) (d.cursor (c.active + 1)) [] := by
    rw [files.data _ (.inr rfl), files.cursor _ (.inr rfl)]
    exact fresh
  have newReady := ready.rotate full names (fun i h => files.data i (.inl h))
    ⟨(files.names _ (.inr rfl)).1 named.1, (files.names _ (.inr rfl)).2 named.2⟩ empty
  have chosen := atCut issued authority effect
  refine ⟨chosen, ?_⟩
  suffices rec : Recoverable (historyView c history) none d from ⟨rec, rec.powerLoss⟩
  have left := old.choice (request := none) (.inl rfl)
  have right := newReady.choice (known := historyView c history) (request := none) (.inl rfl)
  rcases chosen with ⟨l, r⟩ | ⟨l, r⟩
  · exact ⟨⟨_, l, left⟩, ⟨_, r, left⟩⟩
  · exact ⟨⟨_, l, right⟩, r.elim (fun saved => ⟨_, saved, left⟩) (fun saved => ⟨_, saved, right⟩)⟩

end WalRecoverySlice.Segmented.Native.ControlCutIO
