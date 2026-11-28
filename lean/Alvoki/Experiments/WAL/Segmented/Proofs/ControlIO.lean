import Alvoki.Experiments.WAL.Segmented.Proofs.AppendIO

namespace WalRecoverySlice.Segmented.Native.ControlIO
open System Model Alvoki.NativePost
open AppendIO (At)

def stage (reports : Effects) (c : Control) : Model.M Unit := fun st =>
  namespaceChange (reports.stage st.step) (fun d persist => d.stage c persist) st

def syncStage (reports : Effects) : Model.M Unit := fun st =>
  barrier (reports.syncControl st.step) Disk.syncStage st

def rename (reports : Effects) : Model.M Unit := fun st =>
  match st.disk.staged with
  | none => .ok (.error "missing staged control") st.tick
  | some c => namespaceChange (reports.rename st.step) (fun d persist => d.rename c persist) st

def rootSync (reports : Effects) : Model.M Unit := fun st =>
  barrier (reports.root st.step) Disk.syncRoot st

/-- Setup and buffering failures stop the reviewed staging step before
rename. Only a complete staged proposal is selectable for publication. -/
def StageError (reports : Effects) (c : Control) (s : State) (R : W → State → Prop) (t : W) :=
  ∃ msg u, (stage reports c).run s = .ok (.error msg) u ∧ R t u

private theorem defer {a : IO α} {f : α → IO β} {b : Model.M γ}
    (first : IOReturns a w mid (fun t => ∃ msg u, b.run s = .ok (.error msg) u ∧ fail t u))
    (rest : ∀ x t, mid x t → At (f x) b t s ok fail) : At (a >>= f) b w s ok fail := by
  unfold IOReturns at first
  unfold At
  cases ar : a w with
  | error e t =>
    rw [ar] at first
    obtain ⟨msg, u, model, stopped⟩ := first
    simp only [Bind.bind, instMonadEIO._aux_13, EST.bind, ar, model]
    exact stopped
  | ok x t =>
    rw [ar] at first
    simpa only [At, Bind.bind, instMonadEIO._aux_13, EST.bind, ar] using rest x t first

private theorem ioTrace {a : IO α} (h : IOReturns a w ok fail) :
    IOReturns a w (fun x t => a w = .ok x t ∧ ok x t) fail := by
  unfold IOReturns at *
  split at h
  · rename_i ran; rw [ran]; exact ⟨rfl, h⟩
  · exact h

theorem trace {a : IO α} {b : Model.M β} (h : At a b w s ok fail) :
    At a b w s (fun x y t u => ok x y t u ∧ a w = .ok x t ∧ b.run s = .ok (.ok y) u) fail := by
  unfold At at *
  cases ha : a w <;> cases hb : b.run s <;> simp only [ha, hb] at h ⊢
  case ok.ok x t y u => cases y <;> first | contradiction | exact ⟨h, rfl, rfl⟩
  case error.ok x t y u => cases y <;> first | contradiction | exact h
  all_goals contradiction

/-- A witness for the sole writer that can be synced. Ownership starts
with the exclusive create and the write is of the exact encoded control. -/
inductive StagePoint
  | opened | unbuffered | written | flushed | synced | renamed

inductive WriterStage (store : Store) (c : Control) (start : W) :
    StagePoint → IO.FS.Handle → W → Prop where
  | opened : removeRegular (store.root / "CONTROL.next") start = .ok () clear →
      IO.FS.Handle.mk (store.root / "CONTROL.next") .writeNew clear = .ok h t → WriterStage store c start .opened h t
  | unbuffered : WriterStage store c start .opened h t → disableBuffering h t = .ok () v → WriterStage store c start .unbuffered h v
  | written : WriterStage store c start .unbuffered h t → h.write (ControlCodec.encode c) t = .ok () v → WriterStage store c start .written h v
  | flushed : WriterStage store c start .written h t → h.flush t = .ok () v → WriterStage store c start .flushed h v
  | synced : WriterStage store c start .flushed h t → syncHandle h t = .ok () v → WriterStage store c start .synced h v
  | renamed : WriterStage store c start .synced h t →
      IO.FS.rename (store.root / "CONTROL.next") (store.root / "CONTROL") t = .ok () v → WriterStage store c start .renamed h v

abbrev Regular (md : IO.FS.Metadata) := (md.type == .file && md.numLinks == 1) = true

/-- Local syscall reports for one invocation. Private partial bytes are
represented in the caller's physical relation. No proposal is renamed until
the actual write, flush and fsync on its own writer all returned success. -/
structure Primitives (store : Store) (c : Control) (reports : Effects)
    (start : W) (initial : State) (R : W → State → Prop) : Prop where
  stat : match (store.root / "CONTROL.next").symlinkMetadata start with
    | .ok md t => ¬ Regular md → StageError reports c initial R t
    | .error (.noFileOrDirectory ..) _ => True
    | .error _ t => StageError reports c initial R t
  unlink : ∀ md t, (store.root / "CONTROL.next").symlinkMetadata start = .ok md t → Regular md →
    IOReturns (IO.FS.removeFile (store.root / "CONTROL.next")) t (fun _ _ => True) (StageError reports c initial R)
  openWriter : ∀ t, removeRegular (store.root / "CONTROL.next") start = .ok () t →
    IOReturns (IO.FS.Handle.mk (store.root / "CONTROL.next") .writeNew) t (fun _ _ => True) (StageError reports c initial R)
  unbuffered : ∀ h t, WriterStage store c start .opened h t →
    IOReturns (disableBuffering h) t (fun _ _ => True) (StageError reports c initial R)
  write : ∀ h t, WriterStage store c start .unbuffered h t →
    IOReturns (h.write (ControlCodec.encode c)) t (fun _ _ => True) (StageError reports c initial R)
  flush : ∀ h t, WriterStage store c start .written h t →
    At h.flush (stage reports c) t initial (fun _ _ v u => R v u) R
  syncWriter : ∀ h t u, WriterStage store c start .flushed h t →
    (stage reports c).run initial = .ok (.ok ()) u → R t u →
    At (syncHandle h) (syncStage reports) t u (fun _ _ v n => R v n) R
  renameFile : ∀ h t u v, WriterStage store c start .synced h t →
    (stage reports c).run initial = .ok (.ok ()) v → (syncStage reports).run v = .ok (.ok ()) u → R t u →
    At (IO.FS.rename (store.root / "CONTROL.next") (store.root / "CONTROL")) (rename reports) t u (fun _ _ v n => R v n) R
  directory : ∀ h t u v n, WriterStage store c start .renamed h t →
    (stage reports c).run initial = .ok (.ok ()) v → (syncStage reports).run v = .ok (.ok ()) n →
    (rename reports).run n = .ok (.ok ()) u → R t u →
    At (syncHandle store.directory) (rootSync reports) t u (fun _ _ v n => R v n) R

/-- A ghost state with an absent staged proposal cannot be supplied at the
rename site, irrespective of any filesystem observations. -/
theorem proposalAtRename (stageRun : (stage reports c).run initial = .ok (.ok ()) v)
    (syncRun : (syncStage reports).run v = .ok (.ok ()) u) : u.disk.staged = some c := by
  simp only [stage, syncStage, ExceptT.run] at stageRun syncRun
  cases st : reports.stage initial.step with
  | before abort => cases abort <;> simp_all [namespaceChange, outcome, st]
  | after persist failed =>
    cases failed with
    | some e => cases e <;> simp_all [namespaceChange, outcome, st]
    | none =>
      simp [namespaceChange, outcome, st] at stageRun
      cases stageRun
      cases sy : reports.syncControl initial.tick.step with
      | before abort => cases abort <;> simp_all [barrier, outcome, sy]
      | after failure =>
        cases failure with
        | some abort => cases abort <;> simp_all [barrier, outcome, sy]
        | none => simp [barrier, outcome, sy] at syncRun; cases syncRun; rfl

private theorem cleared (p : Primitives store c reports w s R) :
    IOReturns (removeRegular (store.root / "CONTROL.next")) w (fun _ _ => True) (StageError reports c s R) := by
  let path := store.root / "CONTROL.next"
  have observed := p.stat
  change IOReturns (removeRegular path) w _ _
  unfold removeRegular metadata? IOReturns
  cases stat : path.symlinkMetadata w with
  | error e t =>
    change (store.root / "CONTROL.next").symlinkMetadata w = _ at stat
    rw [stat] at observed
    cases e <;> simp [path, tryCatchThe, MonadExceptOf.tryCatch, instMonadExceptOfEIO._aux_3,
      EST.tryCatch, Functor.map, instMonadEIO._aux_1, EST.bind, Bind.bind, instMonadEIO._aux_13, stat,
      Pure.pure, instMonadEIO._aux_5, EST.pure, throw, throwThe, MonadExceptOf.throw, instMonadExceptOfEIO._aux_1,
      EST.throw] <;> exact observed
  | ok md t =>
    change (store.root / "CONTROL.next").symlinkMetadata w = _ at stat
    rw [stat] at observed
    by_cases valid : Regular md
    · have removed := p.unlink md t stat valid
      simpa [path, tryCatchThe, MonadExceptOf.tryCatch, instMonadExceptOfEIO._aux_3,
        EST.tryCatch, Functor.map, instMonadEIO._aux_1, EST.bind, Bind.bind, instMonadEIO._aux_13,
        stat, Pure.pure, instMonadEIO._aux_5, EST.pure, regular, valid, Regular, IOReturns] using removed
    · simpa [path, tryCatchThe, MonadExceptOf.tryCatch, instMonadExceptOfEIO._aux_3,
        EST.tryCatch, Functor.map, instMonadEIO._aux_1, EST.bind, Bind.bind, instMonadEIO._aux_13,
        stat, Pure.pure, instMonadEIO._aux_5, EST.pure, regular, valid, Regular, throw, throwThe,
        MonadExceptOf.throw, instMonadExceptOfEIO._aux_1, EST.throw] using observed valid

private theorem staged (p : Primitives store c reports start initial R) :
    At (store.stageControl c) (stage reports c) start initial
      (fun h _ t u => WriterStage store c start .flushed h t ∧ R t u ∧
        (stage reports c).run initial = .ok (.ok ()) u) R := by
  unfold Store.stageControl
  apply defer (ioTrace (cleared p))
  rintro _ t ⟨clear, _⟩
  apply defer (ioTrace (p.openWriter t clear))
  rintro h u ⟨opened, _⟩
  have acquired := WriterStage.opened (c := c) clear opened
  apply defer (ioTrace (p.unbuffered h u acquired))
  rintro _ v ⟨unbuffered, _⟩
  have ready := acquired.unbuffered unbuffered
  apply defer (ioTrace (p.write h v ready))
  rintro _ x ⟨written, _⟩
  have writing := ready.written written
  have flush := p.flush h x writing
  unfold At at *
  cases actual : h.flush x with
  | error err t =>
    rw [actual] at flush
    simp only [Bind.bind, instMonadEIO._aux_13, EST.bind, actual]
    cases model : (stage reports c).run initial with
    | error => rw [model] at flush; exact flush
    | ok result u => rw [model] at flush; cases result <;> exact flush
  | ok result t =>
    cases result
    rw [actual] at flush
    simp only [Bind.bind, instMonadEIO._aux_13, EST.bind, actual, Pure.pure, instMonadEIO._aux_5, EST.pure]
    cases model : (stage reports c).run initial with
    | error => rw [model] at flush; contradiction
    | ok response u =>
      rw [model] at flush
      cases response with
      | error => contradiction
      | ok result => cases result; exact ⟨writing.flushed actual, flush, rfl⟩

/-- The native callback itself produces the reviewed publication result.
The same writer is used through its barrier; only the store's acquired
directory is used for the final root barrier. -/
theorem publish (p : Primitives store c reports start initial R)
    (held : Nat) (active : c.active ≤ ControlCodec.wordMax) (discarded : c.discarded ≤ ControlCodec.wordMax) :
    At (checked (store.callbacks.publishControl c)) (Segmented.publish (nativeControlOps store.root held reports) c)
      start initial (fun _ _ t u => R t u) R := by
  rw [store.publishControl_io c active discarded, nativeControl_run store.root held reports c active discarded]
  change At (DurableBlob.publishWith (store.stageControl c) syncHandle _ _)
    (DurableBlob.publishWith (stage reports c) (fun _ => syncStage reports) (rename reports) (rootSync reports))
    start initial _ _
  unfold DurableBlob.publishWith
  apply (staged p).bind
  rintro h _ t u ⟨flushed, frame, stageRun⟩
  apply (trace (p.syncWriter h t u flushed stageRun frame)).bind
  rintro _ _ x y ⟨frame, sync, syncRun⟩
  have synced := flushed.synced sync
  apply (trace (p.renameFile h x y u synced stageRun syncRun frame)).bind
  rintro _ _ z n ⟨frame, changed, renameRun⟩
  exact p.directory h z n u y (synced.renamed changed) stageRun syncRun renameRun frame

theorem syncRoot (store : Store) (held : Nat)
    (issued : At (syncHandle store.directory) (rootSync reports) w s ok fail) :
    At (checked store.callbacks.syncRoot) (nativeControlOps store.root held reports).syncRoot w s ok fail := by
  change At (checked (liftM (syncHandle store.directory))) (rootSync reports) w s ok fail
  have same : checked (liftM (syncHandle store.directory)) = syncHandle store.directory := by
    funext t
    have liftRun : (liftM (syncHandle store.directory) : F Unit).run =
        (do return (Except.ok (← syncHandle store.directory) : Except String Unit) : IO _) := rfl
    unfold checked
    rw [liftRun]
    cases ran : syncHandle store.directory t <;>
      simp [Bind.bind, instMonadEIO._aux_13, EST.bind, ran, Pure.pure, instMonadEIO._aux_5, EST.pure]
  rw [same]
  exact issued

end WalRecoverySlice.Segmented.Native.ControlIO
