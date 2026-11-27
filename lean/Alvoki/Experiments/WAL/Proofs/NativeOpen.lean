import Alvoki.Experiments.WAL.Proofs.NativeRecovery

namespace WalRecoverySlice.SingleFile

open Persistence System

/-- The paths and modes issued by the shared open dispatcher. In particular,
the read/write and append descriptions both resolve the segment path. -/
theorem openLocations (dir : FilePath) :
    OpenTarget.location dir .lock = (dir / "lock", .append) ∧
    OpenTarget.location dir .policy = (dir / "policy", .read) ∧
    OpenTarget.location dir .reader = (dir / "segment", .readWrite) ∧
    OpenTarget.location dir .writer = (dir / "segment", .append) ∧
    OpenTarget.location dir .marker0 = (dir / "commit.0", .readWrite) ∧
    OpenTarget.location dir .marker1 = (dir / "commit.1", .readWrite) ∧
    OpenTarget.location dir .directory = (dir, .read) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Reports for the reached primitive calls. Unreached entries are immaterial.
    The lock bit counts this attempt's description, not another owner's lock. -/
structure OpenReports where
  openFault : OpenTarget → Option Abort := fun _ => none
  bufferingFault : OpenTarget → Option Abort := fun _ => none
  readFault : Option Abort := none
  lockFault : Option Abort := none
  allowLock : Bool := true
  unlockError : Bool := false
  policySync : Primitive := .after none
  directorySync : Primitive := .after none
  worker : Effects := healthyReopen
  writebacks : WritebackSchedule := {}
  beforeWorker : List WalFile := []
  afterWorker : List WalFile := []

structure OpenImage where
  image : Image
  held : Bool := false
  policyDurable : Bool := false
  namesDurable : Bool := false
  closed : Bool := false

abbrev OpenM := ExceptT String (EStateM Unit OpenImage)
abbrev OpenResult (α : Type) := EStateM.Result Unit OpenImage (Except String α)

private def finish (abort : Option Abort) (value : α) (s : OpenImage) : OpenResult α :=
  match abort with
  | none => .ok (.ok value) s
  | some .error => .ok (.error "primitive error") s
  | some .interrupted => .error () s

private def unchanged (abort : Option Abort) (value : α) : OpenM α := finish abort value

private def barrier (report : Primitive) (effect : OpenImage → OpenImage) : OpenM Unit :=
  fun s => match report with
  | .before abort => finish (some abort) () s
  | .after abort => finish abort () (effect s)

private def stampText : Policy → String
  | .boundary => "v3 boundary"
  | .logOnly => "v3 log"

private def openEffects (policy : Policy) (r : OpenReports) : OpenIO OpenM OpenTarget where
  openFile target _ _ := unchanged (r.openFault target) target
  unbuffered target := unchanged (r.bufferingFault target) ()
  readPolicy _ target := unchanged (if target = .policy then r.readFault else some .error) (stampText policy)
  tryLock target := fun s =>
    let granted := target = .lock && r.allowLock && !s.held
    match r.lockFault with
    | none => finish none granted {s with held := s.held || granted}
    | some abort => finish (some abort) false s
  unlock target := fun s =>
    if target = .lock then
      -- On return, including unlock failure, this description's last reference is dropped.
      finish (if r.unlockError then some .error else none) () {s with held := false}
    else finish (some .error) () s
  sync
    | .policy => barrier r.policySync fun s => {s with policyDurable := true}
    | .directory => barrier r.directorySync fun s => {s with namesDurable := true}
    | _ => throw "not a namespace descriptor"

def markersFor (policy : Policy) : Option (OpenTarget × OpenTarget) :=
  if policy == .boundary then some (.marker0, .marker1) else none

private def workerEffect (r : OpenReports) (policy : Policy)
    (data appender : OpenTarget) (markers : Option (OpenTarget × OpenTarget)) : OpenM Decoded :=
  if data = .reader ∧ appender = .writer ∧ markers = markersFor policy then
    fun s => match (recoverScheduled r.worker r.writebacks policy).run s.image with
      | .ok response image => .ok response {s with image}
      | .error token image => .error token {s with image}
  else throw "wrong recovery descriptions"

private def attempt (action : OpenM α) : OpenM (Except String α) :=
  fun s => match action.run s with
  | .ok result after => .ok (.ok result) after
  | .error token after => .error token after

private theorem attempt_run (action : OpenM α) (s : OpenImage) :
    (attempt action).run s = match action.run s with
      | .ok result after => .ok (.ok result) after
      | .error token after => .error token after := rfl

/-- The caller owns the expected policy and bindings of the existing segment.
    Each effect below is selected by the native schedule's reached arguments. -/
private def openAttempt (dir : FilePath) (policy : Policy) (r : OpenReports)
    (s : OpenImage) : OpenResult (Opened OpenTarget (AppendFiles OpenTarget)) :=
  match (openExistingWith (openEffects policy r) attempt throw (workerEffect r) appendFiles pure dir).run s with
  | .ok result after => .ok result after
  | .error token after => .error token {after with held := false}

private def ReadOnly (action : OpenM α) (value : α) : Prop :=
  ∀ s, ∃ abort, action.run s = finish abort value s

private theorem readOnly (abort : Option Abort) (value : α) :
    ReadOnly (unchanged abort value) value := fun _ => ⟨abort, rfl⟩

private theorem runBind (a : OpenM α) (b : α → OpenM β) (s : OpenImage) :
    (a >>= b).run s = match a.run s with
      | .ok response after => match response with
        | .ok x => (b x).run after
        | .error e => .ok (.error e) after
      | .error token after => .error token after := by
  change EStateM.bind a.run (ExceptT.bindCont b) s = _
  cases h : a.run s with
  | ok value _ => cases value <;> simp [EStateM.bind, h, ExceptT.bindCont] <;> rfl
  | error => simp [EStateM.bind, h]

private theorem run_pure (x : α) (s : OpenImage) :
    (pure x : OpenM α).run s = .ok (.ok x) s := rfl

private theorem run_throw (error : String) (s : OpenImage) :
    (throw error : OpenM α).run s = .ok (.error error) s := rfl

private theorem ReadOnly.bind {action : OpenM α} {next : α → OpenM β}
    (first : ReadOnly action value) (rest : ReadOnly (next value) final) :
    ReadOnly (action >>= next) final := by
  intro s
  obtain ⟨abort, ran⟩ := first s
  rw [runBind, ran]
  cases abort with
  | none => exact rest s
  | some abort => exact ⟨some abort, by cases abort <;> rfl⟩

private def expectedFiles (policy : Policy) : OpenFiles OpenTarget :=
  ⟨.policy, policy, .reader, .writer, markersFor policy⟩

private theorem openFiles_result (dir : FilePath) (policy : Policy) (r : OpenReports) :
    ReadOnly (openFilesWith (openEffects policy r) dir) (expectedFiles policy) := by
  simp only [openFilesWith, OpenIO.openTarget, openEffects, OpenTarget.location]
  refine ReadOnly.bind (readOnly (r.openFault .policy) OpenTarget.policy) ?_
  refine ReadOnly.bind (readOnly (r.readFault) (stampText policy)) ?_
  cases policy <;> simp only [stampText, Pure.pure, ExceptT.pure]
  all_goals first | refine ReadOnly.bind (readOnly none Policy.logOnly) ?_ |
    refine ReadOnly.bind (readOnly none Policy.boundary) ?_
  all_goals
    refine ReadOnly.bind (readOnly (r.openFault .reader) OpenTarget.reader) ?_
    refine ReadOnly.bind (readOnly (r.bufferingFault .reader) ()) ?_
    refine ReadOnly.bind (readOnly (r.openFault .writer) OpenTarget.writer) ?_
    refine ReadOnly.bind (readOnly (r.bufferingFault .writer) ()) ?_
  · exact readOnly none _
  · refine ReadOnly.bind (readOnly (r.openFault .marker0) OpenTarget.marker0) ?_
    refine ReadOnly.bind (readOnly (r.bufferingFault .marker0) ()) ?_
    refine ReadOnly.bind (readOnly (r.openFault .marker1) OpenTarget.marker1) ?_
    refine ReadOnly.bind (readOnly (r.bufferingFault .marker1) ()) ?_
    exact readOnly none _

def postState : OpenResult α → OpenImage
  | .ok _ s | .error _ s => s

private theorem settle_result (dir : FilePath) (policy : Policy) (r : OpenReports) (s : OpenImage) :
    let result := (settleWith (openEffects policy r) dir .policy).run s
    (postState result).image = s.image ∧ (postState result).held = s.held ∧
      (∀ after, result = .ok (.ok ()) after → after.policyDurable = true ∧ after.namesDurable = true) := by
  simp only [settleWith, runBind, OpenIO.openTarget, openEffects, OpenTarget.location]
  cases pol : r.policySync with
  | before abort => cases abort <;> simp_all [barrier, ExceptT.run, finish, postState]
  | after response =>
    cases response with
    | some abort => cases abort <;> simp_all [barrier, ExceptT.run, finish, postState]
    | none =>
      cases opened : r.openFault .directory with
      | some abort => cases abort <;> simp_all [barrier, ExceptT.run, unchanged, finish, postState]
      | none =>
        cases sync : r.directorySync with
        | before abort => cases abort <;> simp_all [barrier, ExceptT.run, unchanged, finish, postState]
        | after response =>
          cases response with
          | none => simp_all [barrier, ExceptT.run, unchanged, finish, postState]
          | some abort => cases abort <;> simp_all [barrier, ExceptT.run, unchanged, finish, postState]

/-- The public guarantee for an open attempt. A successful result includes the
same decoded cursor and entries that installation puts in the ready phase. -/
def OpenGuarantee (policy : Policy) (known : List Bytes) (pending : Option Bytes)
    (result : OpenResult (Opened OpenTarget (AppendFiles OpenTarget))) : Prop :=
  Dirty policy known pending (postState result).image ∧
    (policy = .logOnly → (postState result).image.MarkersSettled) ∧
    match result with
    | .ok (.ok ready) after =>
      ready.lock = .lock ∧ ready.policy = policy ∧
      ready.reader = .reader ∧ ready.writer = .writer ∧ ready.markers = markersFor policy ∧
      after.held = true ∧ after.policyDurable = true ∧ after.namesDurable = true ∧
      Contract.Permitted known pending ready.recovered.batches ∧
      ready.recovered.cursor = historyCursor ready.recovered.batches ∧
      Ready policy after.image ready.recovered.batches ∧ after.image.powerLoss = after.image ∧
      ready.phase = .active ready.lock (appendFiles ready.writer ready.reader ready.markers) ready.recovered.cursor ready.recovered.batches
    | .ok (.error _) after | .error _ after => after.held = false

private def workerProvenance (policy : Policy) (r : OpenReports) (image : Image)
    (result : OpenResult (Opened OpenTarget (AppendFiles OpenTarget))) : Prop :=
  let worker := (recoverScheduled r.worker r.writebacks policy).run image
  ((postState result).image = image ∨ (postState result).image = reached worker) ∧
    match result with
    | .ok (.ok ready) _ => acknowledged worker = some ready.recovered
    | _ => True

private theorem install_result (dir : FilePath) (r : OpenReports) (s : OpenImage)
    (held : s.held = true) (prior : Dirty policy known pending s.image)
    (markers : policy = .logOnly → s.image.MarkersSettled) :
    let result := (installWith (openEffects policy r) (workerEffect r) appendFiles dir .lock).run s
    let released := match result with
       | .ok (.ok ready) after => .ok (.ok ready) after
       | .ok (.error err) after => .ok (.error err) {after with held := false}
       | .error token after => .error token {after with held := false}
    OpenGuarantee policy known pending released ∧ workerProvenance policy r s.image released := by
  obtain ⟨abort, files⟩ := openFiles_result dir policy r s
  simp only [installWith, runBind, files, workerProvenance]
  cases abort with
  | some abort => cases abort <;> exact ⟨⟨prior, markers, rfl⟩, Or.inl rfl, trivial⟩
  | none =>
    have physical : policy = .boundary ∨ s.image.MarkersSettled := by
      cases policy with
      | boundary => exact Or.inl rfl
      | logOnly => exact Or.inr (markers rfl)
    have facts := prior.reopenScheduled r.worker r.writebacks
    rw [← recoverScheduled_eq] at facts
    dsimp only at facts
    have runWorker :
        (workerEffect r policy .reader .writer (markersFor policy)).run s =
          match (recoverScheduled r.worker r.writebacks policy).run s.image with
          | .ok value image => .ok value {s with image}
          | .error token image => .error token {s with image} := by
      simp [workerEffect, ExceptT.run]
    simp only [finish, expectedFiles, runWorker]
    generalize (recoverScheduled r.worker r.writebacks policy).run s.image = work at facts ⊢
    cases work with
    | error token image =>
      exact ⟨⟨facts.1, fun p => facts.2.1 (markers p), rfl⟩, Or.inr rfl, trivial⟩
    | ok value image =>
      cases value with
      | error err => exact ⟨⟨facts.1, fun p => facts.2.1 (markers p), rfl⟩, Or.inr rfl, trivial⟩
      | ok decoded =>
        dsimp only
        obtain ⟨choice, cursor, ready, _, _, clean⟩ := facts.2.2 decoded rfl
        have closed := clean physical
        have settled := settle_result dir policy r {s with image}
        dsimp only at settled
        cases barrierEq : (settleWith (openEffects policy r) dir .policy).run {s with image} with
        | error token after =>
          rw [barrierEq] at settled
          dsimp only
          obtain ⟨same, _, _⟩ := settled
          simp only [postState] at same
          exact ⟨⟨same ▸ facts.1, fun p => same ▸ facts.2.1 (markers p), rfl⟩, Or.inr same, trivial⟩
        | ok response after =>
          rw [barrierEq] at settled
          dsimp only
          obtain ⟨same, lockEq, barriers⟩ := settled
          simp only [postState] at same lockEq
          cases response with
          | error err =>
            exact ⟨⟨same ▸ facts.1, fun p => same ▸ facts.2.1 (markers p), rfl⟩, Or.inr same, trivial⟩
          | ok value =>
            cases value
            constructor
            · change OpenGuarantee policy known pending (.ok (.ok _) after)
              obtain ⟨stamp, names⟩ := barriers after rfl
              exact ⟨same ▸ facts.1, fun p => same ▸ facts.2.1 (markers p),
                rfl, rfl, rfl, rfl, rfl, lockEq.trans held, stamp, names, choice,
                cursor, same ▸ ready, same ▸ closed, rfl⟩
            · exact ⟨Or.inr same, rfl⟩

private theorem acquired_result (dir : FilePath) (r : OpenReports) (s : OpenImage)
    (free : s.held = false) :
    let result := (acquireWith (openEffects policy r) dir).run s
    (∀ h after, result = .ok (.ok h) after → h = .lock ∧ after = {s with held := true}) ∧
    (∀ err after, result = .ok (.error err) after → after = s) ∧
    (∀ token after, result = .error token after → after = s) := by
  simp only [acquireWith, runBind]
  cases opened : r.openFault .lock with
  | some fault => cases fault <;> simp [OpenIO.openTarget, OpenTarget.location, openEffects, unchanged, ExceptT.run, opened, finish]
  | none =>
    have gate : ((openEffects policy r).openTarget dir .lock).run s = .ok (.ok .lock) s := by
      simp [OpenIO.openTarget, OpenTarget.location, openEffects, unchanged, ExceptT.run, opened, finish]
    simp only [gate]
    cases locked : r.lockFault with
    | some fault => cases fault <;> simp [openEffects, ExceptT.run, finish, locked]
    | none =>
      have gate : ((openEffects policy r).tryLock .lock).run s =
          .ok (.ok r.allowLock) {s with held := r.allowLock} := by
        simp [openEffects, ExceptT.run, finish, locked, free]
      rw [gate]
      cases granted : r.allowLock <;> simp [run_pure, run_throw]
      cases s
      simp_all

private theorem unlock_run (r : OpenReports) (s : OpenImage) :
    ((openEffects policy r).unlock .lock).run s =
      finish (if r.unlockError then some .error else none) () {s with held := false} := rfl

/-- Public open assembles the acquired descriptions, scheduled worker and
namespace barriers. Error cleanup returns no ready phase. -/
private theorem openAttempt_refines (dir : FilePath) (policy : Policy) (r : OpenReports)
    (s : OpenImage) (free : s.held = false) (prior : Dirty policy known pending s.image)
    (markers : policy = .logOnly → s.image.MarkersSettled) :
    OpenGuarantee policy known pending (openAttempt dir policy r s) ∧
      workerProvenance policy r s.image (openAttempt dir policy r s) := by
  have acquire := acquired_result (policy := policy) dir r s free
  dsimp only at acquire
  unfold openAttempt openExistingWith
  rw [runBind]
  cases h : (acquireWith (openEffects policy r) dir).run s with
  | error token after =>
    rw [h] at acquire
    obtain rfl := acquire.2.2 token after rfl
    exact ⟨⟨prior, markers, rfl⟩, Or.inl rfl, trivial⟩
  | ok response after =>
    rw [h] at acquire
    cases response with
    | error err =>
      obtain rfl := acquire.2.1 err after rfl
      exact ⟨⟨prior, markers, free⟩, Or.inl rfl, trivial⟩
    | ok descriptor =>
      obtain ⟨rfl, rfl⟩ := acquire.1 descriptor after rfl
      have installed := install_result dir r {s with held := true} rfl prior markers
      dsimp only at installed
      have same : ∀ (state : OpenImage), (attempt
          (installWith (openEffects policy r) (workerEffect r) appendFiles dir .lock >>= pure)).run state =
          match (installWith (openEffects policy r) (workerEffect r) appendFiles dir .lock).run state with
          | .ok result after => .ok (.ok result) after
          | .error token after => .error token after := by
        intro state
        have ran : (installWith (openEffects policy r) (workerEffect r) appendFiles dir .lock >>= pure).run state =
            (installWith (openEffects policy r) (workerEffect r) appendFiles dir .lock).run state := by
          rw [runBind]
          cases (installWith (openEffects policy r) (workerEffect r) appendFiles dir .lock).run state with
          | error => rfl
          | ok value _ => cases value <;> rfl
        rw [attempt_run, ran]
        cases (installWith (openEffects policy r) (workerEffect r) appendFiles dir .lock).run state <;> rfl
      simp only [runBind, same]
      cases h : (installWith (openEffects policy r) (workerEffect r) appendFiles dir .lock).run {s with held := true} with
      | error token after =>
        rw [h] at installed
        exact installed
      | ok response after =>
        rw [h] at installed
        cases response with
        | ok ready => exact installed
        | error err =>
          cases un : r.unlockError <;>
            simpa [runBind, unlock_run, finish, un, run_throw, OpenGuarantee, workerProvenance, postState] using installed

private def settleImage (files : List WalFile) (state : OpenImage) : OpenImage :=
  {state with image := settleFiles files state.image}

private def settleResult (files : List WalFile) : OpenResult α → OpenResult α
  | .ok response after => .ok response (settleImage files after)
  | .error token after => .error token (settleImage files after)

private theorem keepDirty (files : List WalFile) (prior : Dirty policy known pending image) :
    Dirty policy known pending (settleFiles files image) :=
  writebacks_keep (fun i file h => h.writeback (file.writeback i)) files prior

private theorem keepMarkers (files : List WalFile) (prior : image.MarkersSettled) :
    (settleFiles files image).MarkersSettled :=
  writebacks_keep (fun i file h => (file.writeback i).keepsMarkersSettled h) files prior

/-- Whole-file writebacks outside the worker commute with the acquisition
and namespace primitives, which leave the live child bytes unchanged. -/
def openExistingModel (dir : FilePath) (policy : Policy) (r : OpenReports) (s : OpenImage) :
    OpenResult (Opened OpenTarget (AppendFiles OpenTarget)) :=
  settleResult r.afterWorker (openAttempt dir policy r (settleImage r.beforeWorker s))

theorem openExisting_refines (dir : FilePath) (policy : Policy) (r : OpenReports)
    (s : OpenImage) (free : s.held = false) (prior : Dirty policy known pending s.image)
    (markers : policy = .logOnly → s.image.MarkersSettled) :
    OpenGuarantee policy known pending (openExistingModel dir policy r s) := by
  have outcome := (openAttempt_refines dir policy r (settleImage r.beforeWorker s) free
    (keepDirty _ prior) (fun log => keepMarkers _ (markers log))).1
  unfold openExistingModel
  cases issued : openAttempt dir policy r (settleImage r.beforeWorker s) with
  | error token after =>
    rw [issued] at outcome
    exact ⟨keepDirty _ outcome.1, fun log => keepMarkers _ (outcome.2.1 log), outcome.2.2⟩
  | ok value after =>
    rw [issued] at outcome
    cases value with
    | error err =>
      exact ⟨keepDirty _ outcome.1, fun log => keepMarkers _ (outcome.2.1 log), outcome.2.2⟩
    | ok ready =>
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, settled, _⟩ := outcome.2.2
      have unchanged : settleImage r.afterWorker after = after := by
        unfold settleImage
        rw [settleFiles_clean _ _ settled]
      simpa only [settleResult, unchanged] using outcome

/-- Names and lock operations leave the child file image alone. A returned
child came from the exact scheduled worker selected by native open. -/
theorem openExisting_worker (dir : FilePath) (policy : Policy) (r : OpenReports)
    (s : OpenImage) (free : s.held = false) (prior : Dirty policy known pending s.image)
    (markers : policy = .logOnly → s.image.MarkersSettled) :
    let before := settleFiles r.beforeWorker s.image
    let worker := (recoverScheduled r.worker r.writebacks policy).run before
    let result := openExistingModel dir policy r s
    ((postState result).image = settleFiles r.afterWorker before ∨
      (postState result).image = settleFiles r.afterWorker (reached worker)) ∧
    match result with
    | .ok (.ok ready) _ => acknowledged worker = some ready.recovered
    | _ => True := by
  have source := (openAttempt_refines dir policy r (settleImage r.beforeWorker s) free
    (keepDirty _ prior) (fun log => keepMarkers _ (markers log))).2
  unfold openExistingModel
  cases ran : openAttempt dir policy r (settleImage r.beforeWorker s) with
  | error =>
    rw [ran] at source
    exact ⟨source.1.imp (congrArg (settleFiles r.afterWorker))
      (congrArg (settleFiles r.afterWorker)), trivial⟩
  | ok value _ =>
    rw [ran] at source
    cases value <;>
      exact ⟨source.1.imp (congrArg (settleFiles r.afterWorker))
        (congrArg (settleFiles r.afterWorker)), source.2⟩

/-- The reference-allocation primitive is interpreted by its initial content. -/
def storedPhase (ready : Opened OpenTarget (AppendFiles OpenTarget)) : Phase OpenTarget (AppendFiles OpenTarget) :=
  (storeReadyWith (m := Id) pure (pure ()) ready).1

theorem storedPhase_eq (ready : Opened OpenTarget (AppendFiles OpenTarget)) : storedPhase ready = ready.phase := rfl

theorem scan_opened (ready : Opened OpenTarget (AppendFiles OpenTarget)) (s : OpenImage)
    (installed : ready.phase = .active ready.lock (appendFiles ready.writer ready.reader ready.markers) ready.recovered.cursor ready.recovered.batches) :
    (scanWith (storedPhase ready) : OpenM _).run s = .ok (.ok ready.recovered.batches) s := by
  rw [storedPhase_eq, installed]
  rfl

private def storePhase (phase : Phase OpenTarget (AppendFiles OpenTarget)) : OpenM Unit :=
  fun state => finish none () {state with closed := match phase with | .closed => true | _ => false}

private theorem clear_run (s : OpenImage) :
    (storePhase .closed).run s = .ok (.ok ()) {s with closed := true} := rfl

def closeModel (policy : Policy) (r : OpenReports)
    (phase : Phase OpenTarget (AppendFiles OpenTarget)) (s : OpenImage) :=
  (closeWith phase storePhase (openEffects policy r).unlock).run s

/-- Closing a ready handle clears its shared phase before unlocking its
description. An alias subsequently observes the cleared phase. -/
theorem close_opened (policy : Policy) (r : OpenReports) (ready : Opened OpenTarget (AppendFiles OpenTarget))
    (lock : ready.lock = .lock) (s : OpenImage)
    (installed : ready.phase = .active ready.lock (appendFiles ready.writer ready.reader ready.markers) ready.recovered.cursor ready.recovered.batches) :
    let result := closeModel policy r (storedPhase ready) s
    let after := postState result
    after.closed = true ∧ after.held = false ∧ after.image = s.image ∧
    (scanWith (if after.closed then .closed else ready.phase) : OpenM _).run after =
      .ok (.error "WAL closed") after := by
  simp only [closeModel, storedPhase_eq, installed, closeWith, lock, runBind, clear_run, unlock_run]
  cases h : r.unlockError <;> simp_all [finish, postState] <;> rfl

/-- An uncertain append retains the original private lock in the poisoned
phase. The public close schedule still clears that phase and releases it. -/
theorem close_poisoned (policy : Policy) (r : OpenReports) (s : OpenImage) :
    let result := closeModel policy r (.poisoned .lock) s
    let after := postState result
    after.closed = true ∧ after.held = false ∧ after.image = s.image := by
  simp only [closeModel, closeWith, runBind, clear_run, unlock_run]
  cases h : r.unlockError <;> simp_all [finish, postState] <;> rfl

end WalRecoverySlice.SingleFile
