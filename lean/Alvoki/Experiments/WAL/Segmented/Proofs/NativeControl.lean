import Alvoki.Experiments.WAL.Segmented.Proofs.NativeReopen

namespace WalRecoverySlice.Segmented.Model

open System

/-- An exclusive create yields the staged writer. Another open of the
same inode gets a distinct open file description and has no writer barrier. -/
private inductive ControlDescription where
  | stagedWriter
  | reopened
  deriving DecidableEq

/-- The normalized staging effect records only a complete proposal. Invalid
private stage bytes cannot become CONTROL: a retry reserves and rewrites
the staging path, and a failed stage never advances to rename. -/
private def controlEffects (root : FilePath) (held : Nat) (r : Effects) :
    Native.ControlPrimitives M ControlDescription Nat where
  clearStage path :=
    if path == root / "CONTROL.next" then pure () else throw "wrong staging path"
  openWriter path mode :=
    match mode with
    | .writeNew => if path == root / "CONTROL.next" then pure .stagedWriter else throw "wrong writer path"
    | .read => if path == root / "CONTROL.next" then pure .reopened else throw "wrong reader path"
    | _ => throw "wrong writer mode"
  disableBuffering writer :=
    if writer = .stagedWriter then pure () else throw "wrong CONTROL writer"
  write writer bytes := do
    unless writer = .stagedWriter do throw "wrong CONTROL writer"
    let some c := ControlCodec.decode bytes | throw "invalid staged bytes"
    fun s => namespaceChange (r.stage s.step) (fun d p => d.stage c p) s
  flush writer :=
    if writer = .stagedWriter then pure () else throw "wrong CONTROL writer"
  syncWriter writer :=
    if writer = .stagedWriter then
      fun s => barrier (r.syncControl s.step) Disk.syncStage s
    else throw "wrong CONTROL writer"
  rename source target :=
    if source == root / "CONTROL.next" && target == root / "CONTROL" then
      fun s => match s.disk.staged with
        | none => .ok (.error "missing staged control") s.tick
        | some c => namespaceChange (r.rename s.step) (fun d p => d.rename c p) s
    else throw "wrong CONTROL rename path"
  syncDirectory directory :=
    if directory = held then fun s => barrier (r.root s.step) Disk.syncRoot s
    else throw "wrong root descriptor"

def nativeControlOps (root : FilePath) (held : Nat) (r : Effects) : Ops M :=
  { ops r with publishControl := Native.publishControlWith (controlEffects root held r) root held }

theorem nativeControl_run (root : FilePath) (held : Nat) (r : Effects) (c : Control)
    (active : c.active ≤ ControlCodec.wordMax)
    (discarded : c.discarded ≤ ControlCodec.wordMax) :
    Segmented.publish ((nativeControlOps root held r).toRootOps) c = Segmented.publish ((ops r).toRootOps) c := by
  simp [Segmented.publish, nativeControlOps, Native.publishControlWith, controlEffects, ops,
    active, discarded, ControlCodec.decode_encode c active discarded,
    DurableBlob.publishWith]
  funext s
  simp only [Bind.bind, ExceptT.bind, ExceptT.mk, EStateM.bind]
  cases namespaceChange (r.stage s.step) (fun d p => d.stage c p) s with
  | error => rfl
  | ok response _ => cases response <;> simp [ExceptT.bindCont, ExceptT.pure, ExceptT.mk, Pure.pure, EStateM.pure, EStateM.bind] <;> rfl

theorem nativeControl_cuts (root : FilePath) (held : Nat) (r : Effects) (c : Control)
    (active : c.active ≤ ControlCodec.wordMax)
    (discarded : c.discarded ≤ ControlCodec.wordMax) (before : State) :
    DiskPost (fun _ d => d = before.disk.published c) (PublishCut before.disk c)
      ((Segmented.publish ((nativeControlOps root held r).toRootOps) c).run before) := by
  rw [nativeControl_run root held r c active discarded]
  exact publish_cases r c before

/-- Publication only changes the filesystem on every outcome. -/
theorem nativeControl_framesEntry (root : FilePath) (held : Nat) (r : Effects)
    (c : Control) (active : c.active ≤ ControlCodec.wordMax)
    (discarded : c.discarded ≤ ControlCodec.wordMax) :
    FramesEntry (Segmented.publish ((nativeControlOps root held r).toRootOps) c) := by
  intro before
  rw [nativeControl_run root held r c active discarded]
  revert before
  change FramesEntry (DurableBlob.publishWith _ _ _ _ : M Unit)
  unfold DurableBlob.publishWith
  apply framesEntry_bind
  · intro state; exact namespace_framesEntry (r.stage state.step) (fun d p => d.stage c p) state
  intro _
  apply framesEntry_bind
  · intro state; exact barrier_framesEntry (r.syncControl state.step) Disk.syncStage state
  intro _
  apply framesEntry_bind
  · intro s
    dsimp only [ExceptT.run]
    cases s.disk.staged with
    | none => rfl
    | some control => exact namespace_framesEntry (r.rename s.step) (fun d p => d.rename control p) s
  · intro _ s
    exact barrier_framesEntry (r.root s.step) Disk.syncRoot s

theorem nativeControl_slot (root : FilePath) (held : Nat) (r : Effects)
    (c : Control) (active : c.active ≤ ControlCodec.wordMax)
    (discarded : c.discarded ≤ ControlCodec.wordMax) (s : State)
    (ran : (Segmented.publish ((nativeControlOps root held r).toRootOps) c).run s = .ok (.ok ()) after) :
    after.activeEntry = s.activeEntry := by
  have frame := nativeControl_framesEntry root held r c active discarded s
  rw [ran] at frame
  exact frame

theorem nativeControl_healthy (root : FilePath) (held : Nat) (c : Control) (s : State)
    (active : c.active ≤ ControlCodec.wordMax) (discarded : c.discarded ≤ ControlCodec.wordMax) :
    (Segmented.publish ((nativeControlOps root held healthy).toRootOps) c).run s =
      .ok (.ok ()) {s with disk := s.disk.published c, step := s.step + 4} := by
  rw [nativeControl_run root held healthy c active discarded]
  rfl

theorem nativeControl_rejected (root : FilePath) (held : Nat) (r : Effects) (c : Control) (s : State)
    (invalid : ¬ (c.active ≤ ControlCodec.wordMax ∧ c.discarded ≤ ControlCodec.wordMax)) :
    (Segmented.publish ((nativeControlOps root held r).toRootOps) c).run s =
      .ok (.error "segmented WAL position exhausted") s := by
  simp [Segmented.publish, nativeControlOps, Native.publishControlWith, DurableBlob.publishWith, invalid]
  rfl

private theorem nativeControl_removeRetired (root : FilePath) (held : Nat) (r : Effects)
    (first : Nat) (ids : List Nat) :
    Segmented.removeRetired ((nativeControlOps root held r).toRootOps) first ids =
      Segmented.removeRetired ((ops r).toRootOps) first ids := by
  induction ids with
  | nil => rfl
  | cons id ids ih =>
    simp only [Segmented.removeRetired, ih]
    rfl

private theorem nativeControl_collect (root : FilePath) (held : Nat) (r : Effects) (c : Control) :
    Segmented.collect ((nativeControlOps root held r).toRootOps) c = Segmented.collect ((ops r).toRootOps) c := by
  simp only [Segmented.collect, nativeControl_removeRetired]
  rfl

/-- Only the publication field changes. Collection still uses the existing
release authority and root namespace proof. -/
theorem nativeDiscard_run (root : FilePath) (held : Nat) (r : Effects)
    (session : Session) (position : Nat)
    (active : session.control.active ≤ ControlCodec.wordMax)
    (discarded : position ≤ ControlCodec.wordMax) :
    Segmented.discardThrough (nativeControlOps root held r) session position =
      Segmented.discardThrough (ops r) session position := by
  unfold Segmented.discardThrough discardControl
  split
  · rfl
  split
  · rfl
  dsimp only
  rw [nativeControl_run root held r {session.control with discarded := position} active discarded, nativeControl_collect]

/-- The reached image supports recovery on a reported error, a stopped
process, or a lost successful reply. The power-loss image is admissible too. -/
theorem nativeDiscard_recoverable (root : FilePath) (held : Nat) (r : Effects)
    (session : Session) (position : Nat) (before : State)
    (installed : Installed session before.disk)
    (active : session.control.active ≤ ControlCodec.wordMax)
    (discarded : position ≤ ControlCodec.wordMax) :
    let after := reached ((Segmented.discardThrough (nativeControlOps root held r)
      session position).run before)
    Recoverable session.view (some (.discardThrough position)) after.disk ∧
      Recoverable session.view (some (.discardThrough position)) after.disk.powerLoss := by
  rw [nativeDiscard_run root held r session position active discarded]
  have valid := discard_refines r session position before installed
  have recoverable : Recoverable session.view (some (.discardThrough position))
      (reached ((Segmented.discardThrough (ops r) session position).run before)).disk := by
    cases run : (Segmented.discardThrough (ops r) session position).run before with
    | error => rw [run] at valid; exact valid
    | ok report _ =>
      rw [run] at valid
      cases report with
      | error => exact valid
      | ok next => exact valid.1.offline (.inr valid.2)
  exact ⟨recoverable, recoverable.powerLoss⟩

theorem repeatOpenAfterNativeFailedDiscard (root : FilePath) (held : Nat) (r : Effects)
    (interruptedOpen first second : RootReports)
    (reports : Nat → Nat → SingleFile.OpenReports)
    (session : Session) (position : Nat) (before failed retried opened done : State)
    (selected repeated : Session) (installed : Installed session before.disk)
    (active : session.control.active ≤ ControlCodec.wordMax)
    (discarded : position ≤ ControlCodec.wordMax)
    (discardError : (Segmented.discardThrough (nativeControlOps root held r) session position).run before =
      .ok (.error publicationError) failed)
    (openError : (Segmented.reopen (nativeReopenOps root interruptedOpen reports)).run failed =
      .ok (.error recoveryError) retried)
    (openFirst : (Segmented.reopen (nativeReopenOps root first reports)).run retried =
      .ok (.ok selected) opened)
    (openSecond : (Segmented.reopen (nativeReopenOps root second reports)).run opened =
      .ok (.ok repeated) done) :
    PermittedView session.view (some (.discardThrough position)) selected.view ∧
      repeated.view = selected.view := by
  rw [nativeDiscard_run root held r session position active discarded] at discardError
  exact repeatOpenAfterFailedDiscard root r interruptedOpen first second reports session position
    before failed retried opened done selected repeated installed discardError openError openFirst openSecond

end WalRecoverySlice.Segmented.Model
