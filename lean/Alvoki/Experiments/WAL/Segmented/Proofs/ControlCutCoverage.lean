import Alvoki.Experiments.WAL.Segmented.Proofs.ControlCutIO
import Alvoki.Experiments.WAL.Segmented.Proofs.CutSchedule

namespace WalRecoverySlice.Segmented.Native.ControlCutIO
open System Model Alvoki.NativePost AppendCut

private def leaf (stop : Stops) (a : IO α) : Observed α := ⟨a, stop a⟩

/-- The exception is the same user error produced by checked native protocol.
The pure representability check issues no system call. -/
private local instance : MonadExceptOf String Observed where
  throw e := throw (IO.userError e)
  tryCatch a f := tryCatchThe IO.Error a fun e => f e.toString

private def inspect (stop : Stops) (file : FilePath) : Observed (Option IO.FS.Metadata) :=
  ⟨metadata? file, stop file.symlinkMetadata⟩

private def clear (stop : Stops) (path : FilePath) : Observed Unit :=
  removeRegularWith (inspect stop) (fun f md => ⟨regular f md, fun _ _ => False⟩)
    (fun f => leaf stop (IO.FS.removeFile f)) path

/-- The actual generic publisher supplies every staging, rename and barrier
operand. An invalid scalar guard issues no calls. -/
def program (s : Store) (c : Control) (stop : Stops) : Observed Unit :=
  publishControlWith {
    clearStage := clear stop
    openWriter := fun f m => leaf stop (IO.FS.Handle.mk f m)
    disableBuffering := fun h => leaf stop (disableBuffering h)
    write := fun h bs => leaf stop (h.write bs)
    flush := fun h => leaf stop h.flush
    syncWriter := fun h => leaf stop (syncHandle h)
    rename := fun a b => leaf stop (IO.FS.rename a b)
    syncDirectory := fun h => leaf stop (syncHandle h)
  } s.root s.directory c

abbrev Witness (s : Store) (c : Control) (stop : Stops) (origin : W) (d : Disk) : Prop :=
  ∃ (p : Point) (t : W) (α : Type) (a : IO α) (k : OpKind),
    Prefix s c origin p t ∧ Issued s c p a k ∧ stop a t d

private abbrev SafeAt (s : Store) (c : Control) (stop : Stops) (origin : W)
    (a : Observed α) (w : W) (ok : α → W → Prop) :=
  Safe a w ok (fun _ => True) (Witness s c stop origin)

private theorem callSafe (stop : Stops) {a : IO α} (path : Prefix s c origin p w)
    (issued : Issued s c p a kind) (after : ∀ x t, a w = .ok x t → ok x t) :
    SafeAt s c stop origin (leaf stop a) w ok := by
  constructor
  · unfold IOReturns
    change (match a w with | .ok x t => ok x t | .error .. => True)
    cases ran : a w with
    | error => trivial
    | ok x t => exact after x t ran
  · exact fun d hit => ⟨_,_,_,_,_,path,issued,hit⟩

private theorem pureSafe (ok : post x w) : SafeAt s c stop origin (pure x) w post :=
  ⟨ok, fun _ h => False.elim h⟩

private theorem regularSafe (path : Prefix s c origin .unlink w) (valid : ControlIO.Regular md) :
    SafeAt s c stop origin
      (⟨regular (s.root / "CONTROL.next") md, fun _ _ => False⟩ : Observed Unit) w
      (fun _ t => Prefix s c origin .unlink t) := by
  constructor
  · simpa [IOReturns, regular, ControlIO.Regular, valid, Pure.pure, instMonadEIO._aux_5, EST.pure] using path
  · exact fun _ h => False.elim h

private theorem noFile (file : FilePath) (w : W) :
    metadata? file w =
    match file.symlinkMetadata w with
    | .ok md t => .ok (some md) t
    | .error (.noFileOrDirectory ..) t => .ok none t
    | .error e t => .error e t := by
  unfold metadata?
  simp only [tryCatchThe, MonadExceptOf.tryCatch, instMonadExceptOfEIO._aux_3, EST.tryCatch,
    Functor.map, instMonadEIO._aux_1, EST.bind, Function.comp_apply, EST.pure]
  cases file.symlinkMetadata w with
  | ok => rfl
  | error e => cases e <;> rfl

private def StatPost (s : Store) (c : Control) (origin : W) : Option IO.FS.Metadata → W → Prop
  | none, t => Prefix s c origin .openWriter t
  | some md, t => ControlIO.Regular md → Prefix s c origin .unlink t

private theorem clearSafe (s : Store) (c : Control) (stop : Stops) (origin : W) :
    SafeAt s c stop origin (clear stop (s.root / "CONTROL.next")) origin
      (fun _ t => Prefix s c origin .openWriter t) := by
  unfold clear removeRegularWith
  apply Safe.bind (mid := StatPost s c origin)
  · constructor
    · change IOReturns (metadata? _) origin _ _
      unfold IOReturns
      rw [noFile]
      cases ran : (s.root / "CONTROL.next").symlinkMetadata origin with
      | ok md t => exact fun reg => .more .start (.regular ran reg)
      | error e t =>
        cases e <;> first | trivial | exact .more .start (.missing ran)
    · exact fun d hit => ⟨_,_,_,_,_,.start,.stat,hit⟩
  · rintro (md | md) t path
    · exact pureSafe path
    · by_cases reg : ControlIO.Regular md
      · apply Safe.bind (regularSafe (path reg) reg)
        intro _ u nextPoint
        exact callSafe stop nextPoint .unlink fun _ _ ran => .more nextPoint (.cleared ran)
      · apply Safe.bind (mid := fun _ _ => False)
        · constructor
          · change IOReturns (regular _ _) _ _ _
            simp [IOReturns, regular, reg, throw, throwThe,
              MonadExceptOf.throw, instMonadExceptOfEIO._aux_1, EST.throw]
          · exact fun _ h => False.elim h
        · intro _ _ impossible; contradiction

private theorem stageSafe (s : Store) (c : Control) (stop : Stops) (origin : W) :
    SafeAt s c stop origin (program s (next c) stop) origin (fun _ t => Prefix s c origin .done t) := by
  unfold program publishControlWith DurableBlob.publishWith
  apply Safe.bind (mid := fun h t => Prefix s c origin (.syncWriter h) t)
  · dsimp only
    split
    · apply Safe.bind (clearSafe s c stop origin)
      intro _ t p
      apply Safe.bind (callSafe stop p .openWriter (fun h u ran => Prefix.more p (.opened ran)))
      intro h u q
      apply Safe.bind (callSafe stop q (.unbuffer h) (fun _ _ ran => Prefix.more q (.unbuffered ran)))
      intro _ _ r
      apply Safe.bind (callSafe stop r (.write h) (fun _ _ ran => Prefix.more r (.written ran)))
      intro _ _ v
      apply Safe.bind (callSafe stop v (.flush h) (fun _ _ ran => Prefix.more v (.flushed ran)))
      intro _ _ x
      exact pureSafe x
    · apply Safe.bind (mid := fun _ _ => False)
      · exact ⟨trivial, fun _ hit => False.elim hit⟩
      · intro _ _ impossible; contradiction
  · intro h t p
    apply Safe.bind (callSafe stop p (.syncWriter h) (fun _ _ ran => Prefix.more p (.synced ran)))
    intro _ _ q
    apply Safe.bind (callSafe stop q (.rename h) (fun _ _ ran => Prefix.more q (.renamed ran)))
    intro _ _ r
    exact callSafe stop r (.directory h) (fun _ _ ran => Prefix.more r (.settled ran))

theorem covered (hit : (program s (next c) stop).cuts w d) : Witness s c stop w d :=
  (stageSafe s c stop w).cut d hit

end WalRecoverySlice.Segmented.Native.ControlCutIO
