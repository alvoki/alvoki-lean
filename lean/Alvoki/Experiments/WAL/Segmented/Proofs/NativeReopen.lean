import Alvoki.Experiments.WAL.Segmented.Native
import Alvoki.Experiments.WAL.Segmented.Proofs.Reopen
import Alvoki.Experiments.WAL.Segmented.Proofs.ControlCodec

namespace WalRecoverySlice.Segmented.Native

open System

/-- With metadata and bytes from the bound CONTROL file, the actual native
read selects its canonical control, including the metadata size check. -/
theorem readControl_canonical (root : FilePath) (c : Control)
    (capacity : c.capacity ≤ 255) (active : c.active ≤ ControlCodec.wordMax)
    (discarded : c.discarded ≤ ControlCodec.wordMax) :
    readControlWith (m := Except String)
      (fun path => if path = root / "CONTROL" then .ok (true, (ControlCodec.encode c).size)
        else .error "unexpected metadata path")
      (fun path => if path = root / "CONTROL" then .ok (ControlCodec.encode c)
        else .error "unexpected read path") root = .ok c := by
  have fits := ControlCodec.encoded_size c capacity active discarded
  simp [readControlWith, show ¬ 80 < (ControlCodec.encode c).size from Nat.not_lt.mpr fits,
    ControlCodec.decode_encode c active discarded, Bind.bind, Pure.pure, Except.bind, Except.pure]

/-- Root acquisition opens only the protected lock name, and a denied
lock returns no owned descriptor. A missing lock can be created by open. -/
theorem acquireRoot_selects (root : FilePath) (metadata : Option Bool)
    (valid : metadata ≠ some false) (granted : Bool) :
    acquireRootWith (m := Except String)
      (fun path => if path = root / "lock" then .ok metadata else .error "unexpected metadata path")
      (fun path mode => match mode with
        | .append => if path = root / "lock" then .ok path else .error "unexpected lock path"
        | _ => .error "unexpected lock mode")
      (fun reached => if reached = root / "lock" then .ok granted else .error "unexpected lock")
      root =
    if granted then .ok (root / "lock") else .error "segmented WAL already open" := by
  cases metadata with
  | none => cases granted <;> simp [acquireRootWith, Bind.bind, Pure.pure, Except.bind, Except.pure] <;> rfl
  | some regular =>
    cases regular
    · exact (valid rfl).elim
    · cases granted <;> simp [acquireRootWith, Bind.bind, Pure.pure, Except.bind, Except.pure] <;> rfl

/-- The ready phase stores exactly the session produced by the shared
reopen protocol. The public scan uses that phase's cached view. -/
theorem scan_ready (owned : store) (session : Session) :
    scanWith (m := Except String) (.ready owned session) = .ok session.view := rfl

theorem close_ready (owned : store) (session : Session) (release : store → Except String Unit) :
    closeWith (fun _ => .ok (.ready owned session)) release = release owned := rfl

theorem close_alreadyClosed (release : store → Except String Unit) :
    closeWith (fun _ => .ok .closed) release = .ok () := rfl

/-- Once the protected namespace is checked, the actual dispatch opens the
selected path and scans exactly the handle it stores under the selected ID. -/
theorem openChild_dispatch (root : FilePath) (p : Policy) (id : Nat) (returned : child)
    (scan : child → Except String (List Bytes)) :
    openChildWith (.ok ()) (fun path =>
      if path = root / s!"segment-{id}" then .ok #["policy", "segment", "commit.0", "commit.1"]
      else .error "wrong child listing")
      (fun path => if path = (root / s!"segment-{id}") / "policy" then
        .ok (policyStamp p).utf8ByteSize else .error "wrong policy size path")
      (fun path => if path = (root / s!"segment-{id}") / "policy" then
        .ok (policyStamp p) else .error "wrong policy read path")
      (fun path => if path = root / s!"segment-{id}" then .ok returned else .error "wrong child open")
      (fun index _ => if index = id then .ok () else .error "wrong child ID")
      scan root p id = scan returned := by
  have log : (Policy.logOnly == .boundary) = false := rfl
  have marked : (Policy.boundary == .boundary) = true := rfl
  cases p <;> simp [openChildWith, segmentPath, policyStamp, Bind.bind,
    Except.bind, Array.contains, log, marked] <;> rfl

end WalRecoverySlice.Segmented.Native

namespace WalRecoverySlice.Segmented.Model
open System
open Persistence

/-- The shared phase wrapper preserves the disk proof of the existing model
schedule and ties the public scan to the exact installed session. -/
theorem reopenPhase_withChild (owned : store) (root : Effects)
    {call} {healthyCall : Prop} (childEffects : OpenChildEffects call healthyCall) (s : State)
    (prior : Recoverable known request s.disk) :
    let result := (Native.reopenPhaseWith (reopenOps root call) owned).run s
    match result with
    | .ok (.ok (.ready owner session)) after =>
      owner = owned ∧ Installed session after.disk ∧
      Contract.Step (.offline known request) (.opened session.view) (.online session.view) ∧
      Native.scanWith (m := Except String) (.ready owner session) = .ok session.view
    | .ok (.ok _) _ => False
    | .ok (.error _) after | .error _ after => Recoverable known request after.disk := by
  have physical := reopenWithChild_refines root childEffects s prior
  have phase :
      (Native.reopenPhaseWith (reopenOps root call) owned).run s =
        match (Segmented.reopen (reopenOps root call)).run s with
        | .ok (.ok session) after => .ok (.ok (.ready owned session)) after
        | .ok (.error err) after => .ok (.error err) after
        | .error token after => .error token after := by
    cases ran : (Segmented.reopen (reopenOps root call)).run s with
    | error =>
      simp [Native.reopenPhaseWith, Bind.bind, ExceptT.run, ExceptT.bind,
        ExceptT.bindCont, ExceptT.mk, EStateM.bind] at ran ⊢
      rw [ran]
    | ok response _ =>
      cases response <;>
        simp [Native.reopenPhaseWith, Bind.bind, ExceptT.run, ExceptT.bind,
          ExceptT.bindCont, ExceptT.mk, EStateM.bind] at ran ⊢ <;> rw [ran] <;> rfl
  dsimp only
  rw [phase]
  cases issued : (Segmented.reopen (reopenOps root call)).run s with
  | error => rw [issued] at physical; exact physical
  | ok response _ =>
    rw [issued] at physical
    cases response with
    | error => exact physical
    | ok session => exact ⟨rfl, physical.1, .opened physical.2, rfl⟩

/-- Embed the exact public child recovery result in a disk slot. A reported
failure or interruption still carries the reached image and preserves the
previous cursor. Root namespace and other slots are framed by `child`. -/
def nativeChildWorker (dir : System.FilePath) (policy : Policy)
    (reports : SingleFile.OpenReports) : Persistence.M Decoded := fun image =>
  match SingleFile.openExistingModel dir policy reports {image} with
  | .ok (.ok ready) after => .ok (.ok ready.recovered) after.image
  | .ok (.error err) after => .ok (.error err) after.image
  | .error token after => .error token after.image

theorem nativeChild_recoverable {id : Nat} {s : State} (dir : System.FilePath)
    (reports : SingleFile.OpenReports) (named : id ∈ s.disk.liveNames)
    (prior : Child.Recoverable policy known pending (s.disk.segment id)) :
    let result := child s id (nativeChildWorker dir policy reports) Decoded.cursor Decoded.batches
    let disk := (reached result).disk
    Child.Recoverable policy known pending (disk.segment id) ∧
    ∀ batches, returned result = some batches →
      WalRecoverySlice.Contract.Permitted known pending batches ∧
      Child.Installed policy (disk.segment id) (disk.cursor id) batches := by
  let run := nativeChildWorker dir policy reports
  have frame := child_reached named run Decoded.cursor Decoded.batches
  have observed := child_returned named run Decoded.cursor Decoded.batches
  have facts := prior.nativeOpen dir reports {image := s.disk.segment id} rfl
  dsimp only
  rw [frame, Disk.setSegment_here]
  have report : (run.run (s.disk.segment id)) =
      match SingleFile.openExistingModel dir policy reports {image := s.disk.segment id} with
      | .ok (.ok ready) after => .ok (.ok ready.recovered) after.image
      | .ok (.error err) after => .ok (.error err) after.image
      | .error token after => .error token after.image := rfl
  cases issued : SingleFile.openExistingModel dir policy reports {image := s.disk.segment id} with
  | error =>
    rw [issued] at facts report
    rw [report]
    refine ⟨facts.1, ?_⟩
    intro batches returned
    rw [observed, report] at returned
    cases returned
  | ok response after =>
    cases response with
    | error =>
      rw [issued] at facts report
      rw [report]
      refine ⟨facts.1, ?_⟩
      intro batches returned
      rw [observed, report] at returned
      cases returned
    | ok ready =>
      rw [issued] at facts report
      rw [report]
      refine ⟨facts.1, ?_⟩
      intro batches returned
      rw [observed, report] at returned
      obtain rfl := Option.some.inj returned
      obtain ⟨_, _, _, permitted, installed, _⟩ := facts.2
      rw [Disk.setCursor_here]
      exact ⟨permitted, installed⟩

/-- The public child path keeps an already settled sealed segment's exact
bytes, even if a later namespace action fails. -/
theorem nativeChild_sealed (dir : System.FilePath) (r : SingleFile.OpenReports)
    (entry : Child.Settled policy image history)
    (bounded : ∀ b ∈ history, b.length ≤ 32) (fits : history.length ≤ 255) :
    Persistence.reached ((nativeChildWorker dir policy r).run image) = image := by
  have physical := SingleFile.openExisting_worker dir policy r {image} rfl
    (entry.recoverable bounded fits).dirty (entry.recoverable bounded fits).markers
  have worker := (reopensSettledSegmentScheduled entry.ready entry.clean bounded fits r.worker r.writebacks).1
  rw [← SingleFile.recoverScheduled_eq] at worker
  dsimp only at physical
  rw [settleFiles_clean _ _ entry.clean, worker, settleFiles_clean _ _ entry.clean] at physical
  have same := physical.1.elim id id
  unfold nativeChildWorker
  cases ran : SingleFile.openExistingModel dir policy r {image} with
  | error => simpa [ExceptT.run, ran, Persistence.reached, SingleFile.postState] using same
  | ok value _ => cases value <;>
      simpa [ExceptT.run, ran, Persistence.reached, SingleFile.postState] using same

/-- A successful public child open returns the value selected from the
live child bytes. Whole-file writeback outside the worker keeps that view. -/
theorem nativeChild_selected (dir : System.FilePath) (r : SingleFile.OpenReports)
    (entry : Child.Recoverable policy known pending image)
    (selected : Child.Selects policy image batches)
    (opened : SingleFile.openExistingModel dir policy r {image} = .ok (.ok ready) after) :
    ready.recovered.batches = batches := by
  have physical := SingleFile.openExisting_worker dir policy r {image} rfl entry.dirty entry.markers
  rw [opened] at physical
  obtain ⟨marker, decoded, selected, rfl⟩ := selected
  have preserved : ReopenSelection policy (settleFiles r.beforeWorker image) marker decoded := by
    apply writebacks_keep (P := fun state => ReopenSelection policy state marker decoded) _ _ selected
    intro state file prior
    cases policy <;> cases marker <;> cases file <;> exact prior
  have exact := scheduledReopen_selected preserved r.worker r.writebacks ready.recovered
  rw [← SingleFile.recoverScheduled_eq] at exact
  exact congrArg Decoded.batches (exact physical.2)

/-- Interpret the public single-file producer at the selected segment path. -/
def nativeOpenChild (root : FilePath) (reports : Nat → Nat → SingleFile.OpenReports)
    (policy : Policy) (id : Nat) : M (List Bytes) := fun s =>
  child s id (nativeChildWorker (Native.segmentPath root id) policy (reports s.step id))
    Decoded.cursor Decoded.batches

theorem nativeOpenChild_effects (root : FilePath) (reports : Nat → Nat → SingleFile.OpenReports) :
    OpenChildEffects (nativeOpenChild root reports) False where
  frame _ _ _ named := child_frame named _ _ _
  settled {policy id s history} named entry bounded fits := by
    have frame := child_reached named
      (nativeChildWorker (Native.segmentPath root id) policy (reports s.step id))
      Decoded.cursor Decoded.batches
    have facts := nativeChild_recoverable (Native.segmentPath root id) (reports s.step id)
      named (entry.recoverable bounded fits)
    refine ⟨?_, fun batches observed => ?_⟩
    · change (reached (child s id _ Decoded.cursor Decoded.batches)).disk.segment id = _
      rw [frame, Disk.setSegment_here]
      exact nativeChild_sealed _ _ entry bounded fits
    · have permitted := (facts.2 batches observed).1
      cases permitted with
      | inl same => exact same
      | inr same => simpa using same
  dirty {policy id s known pending} named entry :=
    nativeChild_recoverable (Native.segmentPath root id) (reports s.step id) named entry
  selected {policy id s batches known pending} named entry chosen observed ack := by
    let dir := Native.segmentPath root id
    let r := reports s.step id
    change returned (child s id (nativeChildWorker dir policy r) Decoded.cursor Decoded.batches) = _ at ack
    rw [child_returned named] at ack
    cases opened : SingleFile.openExistingModel dir policy r {image := s.disk.segment id} with
    | error => simp [nativeChildWorker, ExceptT.run, opened, Persistence.acknowledged] at ack
    | ok response after =>
      cases response with
      | error => simp [nativeChildWorker, ExceptT.run, opened, Persistence.acknowledged] at ack
      | ok ready =>
        have eq : ready.recovered.batches = observed := by
          simpa [nativeChildWorker, ExceptT.run, opened, Persistence.acknowledged] using ack
        exact eq.symm.trans (nativeChild_selected dir r entry chosen opened)
  healthy _ _ impossible := impossible.elim

/-- The native child producer supplies the root recovery proof. Root namespace
operations here still use the root model. -/
theorem reopenPhase_nativeChild (owned : store) (root : FilePath) (effects : Effects)
    (reports : Nat → Nat → SingleFile.OpenReports) (s : State)
    (prior : Recoverable known request s.disk) :
    let result := (Native.reopenPhaseWith (reopenOps effects (nativeOpenChild root reports)) owned).run s
    match result with
    | .ok (.ok (.ready owner session)) after =>
      owner = owned ∧ Installed session after.disk ∧
      Contract.Step (.offline known request) (.opened session.view) (.online session.view) ∧
      Native.scanWith (m := Except String) (.ready owner session) = .ok session.view
    | .ok (.ok _) _ => False
    | .ok (.error _) after | .error _ after => Recoverable known request after.disk :=
  reopenPhase_withChild owned effects (nativeOpenChild_effects root reports) s prior

end WalRecoverySlice.Segmented.Model
