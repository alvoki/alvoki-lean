import Alvoki.Experiments.WAL.Proofs.NativeOpen
import Alvoki.Experiments.WAL.Proofs.ScheduledExecution

namespace WalRecoverySlice.SingleFile

open Persistence

/-- Interpret each reached operation at its writer or marker description. -/
private def appendEffectsIO (primitives : Ops M) : AppendIO M OpenTarget where
  appendFlushed
    | .writer => primitives.append
    | _ => fun _ => throw "not an append descriptor"
  writeFromStart
    | .marker0 => primitives.writeMarker 0
    | .marker1 => primitives.writeMarker 1
    | _ => fun _ => throw "not a marker descriptor"
  sync
    | .writer => primitives.syncData
    | .marker0 => primitives.syncMarker 0
    | .marker1 => primitives.syncMarker 1
    | _ => throw "not an append descriptor"

def appendBindings (policy : Policy) : AppendFiles OpenTarget :=
  ⟨.writer, markersFor policy⟩

/-- Reports specify byte-level effects, with the original tear and writeback
conditions. Their interpretation follows the executable descriptor routing. -/
structure AppendReports (policy : Policy) (cursor : Cursor) (batch : Bytes) where
  effects : Effects
  writebacks : WritebackSchedule := {}
  torn : Option {cut : TornAppend // cut.SameExtent batch ∧
    (policy = .logOnly → cut.Detected cursor.nextSeq)} := none

def appendWorker (files : AppendFiles OpenTarget)
    (reports : AppendReports policy cursor batch) : M Cursor :=
  let primitives := appendPrimitives reports.effects (reports.torn.map Subtype.val)
  appendBatch (scheduledOps (appendOps (appendEffectsIO primitives) files) reports.writebacks)
    policy cursor batch

theorem appendWorker_eq (reports : AppendReports policy cursor batch) :
    appendWorker (appendBindings policy) reports =
      appendBatch (scheduledOps
        (appendPrimitives reports.effects (reports.torn.map Subtype.val)) reports.writebacks)
        policy cursor batch := by
  cases policy with
  | logOnly => rfl
  | boundary =>
    let base := appendPrimitives reports.effects (reports.torn.map Subtype.val)
    let actual := appendOps (appendEffectsIO base) (appendBindings .boundary)
    change appendBatch (scheduledOps actual reports.writebacks) .boundary cursor batch = _
    have write (slot : Nat) (bound : slot < 2) : actual.writeMarker slot = base.writeMarker slot := by
      have slots : slot = 0 ∨ slot = 1 := by omega
      rcases slots with rfl | rfl <;> rfl
    have sync (slot : Nat) (bound : slot < 2) : actual.syncMarker slot = base.syncMarker slot := by
      have slots : slot = 0 ∨ slot = 1 := by omega
      rcases slots with rfl | rfl <;> rfl
    have writeSelected : actual.writeMarker (cursor.nextSeq % 2) = base.writeMarker (cursor.nextSeq % 2) :=
      write _ (by omega)
    have syncSelected : actual.syncMarker (cursor.nextSeq % 2) = base.syncMarker (cursor.nextSeq % 2) :=
      sync _ (by omega)
    have data : actual.append = base.append := rfl
    have barrier : actual.syncData = base.syncData := rfl
    change _ = appendBatch (scheduledOps base reports.writebacks) .boundary cursor batch
    simp only [appendBatch, scheduledOps, data, barrier, writeSelected, syncSelected]

abbrev AppendPhase := Phase OpenTarget (AppendFiles OpenTarget)

structure AppendImage where
  image : Image
  phase : AppendPhase

abbrev AppendM := ExceptT String (EStateM Unit AppendImage)
abbrev AppendResult := EStateM.Result Unit AppendImage (Except String Unit)

private def storeAppendPhase (phase : AppendPhase) : AppendM Unit :=
  fun s => .ok (.ok ()) {s with phase}

private def liftWorker (worker : M α) : AppendM α :=
  fun s => match worker.run s.image with
  | .ok value image => .ok value {s with image}
  | .error token image => .error token {s with image}

private def runAppend (reports : ∀ cursor, AppendReports policy cursor batch)
    (files : AppendFiles OpenTarget) (cursor : Cursor) : AppendM Cursor :=
  liftWorker (appendWorker files (reports cursor))

def appendModel (reports : ∀ cursor, AppendReports policy cursor batch) (s : AppendImage) : AppendResult :=
  (appendWith s.phase storeAppendPhase (runAppend reports) batch).run s

def appendReached : AppendResult → AppendImage
  | .ok _ after | .error _ after => after

theorem activeResult (reports : ∀ cursor, AppendReports policy cursor batch)
    (files : AppendFiles OpenTarget) (heldLock : OpenTarget) (cursor : Cursor) (known : List Bytes) (image : Image) :
    appendModel reports ⟨image, .active heldLock files cursor known⟩ =
      match (appendWorker files (reports cursor)).run image with
      | .ok (.ok next) after => .ok (.ok ()) ⟨after, .active heldLock files next (known ++ [batch])⟩
      | .ok (.error err) after => .ok (.error err) ⟨after, .poisoned heldLock⟩
      | .error token after => .error token ⟨after, .poisoned heldLock⟩ := by
  unfold appendModel appendWith runAppend
  cases h : (appendWorker files (reports cursor)).run image with
  | ok response _ =>
    simp only [ExceptT.run] at h
    cases response <;>
      simp [storeAppendPhase, liftWorker, h, Bind.bind, ExceptT.bind, ExceptT.bindCont,
        ExceptT.run, ExceptT.mk, EStateM.bind, Pure.pure, EStateM.pure]
  | error =>
    simp only [ExceptT.run] at h
    simp [storeAppendPhase, liftWorker, h, Bind.bind, ExceptT.bind, ExceptT.bindCont,
      ExceptT.run, ExceptT.mk, EStateM.bind]

/-- A successful append keeps a live phase for the same handle's bindings. -/
theorem appendModel_success_active
    (reports : ∀ cursor, AppendReports policy cursor batch) {before after : AppendImage}
    (ran : appendModel reports before = .ok (.ok ()) after) :
    ∃ heldLock files cursor history, after.phase = .active heldLock files cursor history := by
  obtain ⟨image, phase⟩ := before
  cases phase with
  | closed => cases ran
  | poisoned => cases ran
  | active heldLock files cursor history =>
    rw [activeResult] at ran
    cases work : (appendWorker files (reports cursor)).run image with
    | error => rw [work] at ran; cases ran
    | ok response reached =>
      rw [work] at ran
      cases response with
      | error => cases ran
      | ok cursor =>
        cases ran
        exact ⟨_, _, _, _, rfl⟩

theorem appendModel_error_phase (reports : ∀ cursor, AppendReports policy cursor batch)
    (ran : appendModel reports ⟨image, .active heldLock files cursor history⟩ =
      .ok (.error err) after) : after.phase = .poisoned heldLock := by
  rw [activeResult] at ran
  cases work : (appendWorker files (reports cursor)).run image with
  | error => rw [work] at ran; cases ran
  | ok response reached =>
    rw [work] at ran
    cases response with
    | ok => cases ran
    | error => cases ran; rfl

def AppendGuarantee (policy : Policy) (known : List Bytes) (batch : Bytes)
    (result : AppendResult) : Prop :=
    Dirty policy known (some batch) (appendReached result).image ∧
    (policy = .logOnly → (appendReached result).image.MarkersSettled) ∧
    match result with
    | .ok (.ok ()) after =>
      Contract.Step (.online known) (.ack batch) (.online (known ++ [batch])) ∧
      after.phase = .active .lock (appendBindings policy) (historyCursor (known ++ [batch])) (known ++ [batch]) ∧
      Ready policy after.image (known ++ [batch]) ∧ after.image.powerLoss = after.image
    | .ok (.error _) after | .error _ after =>
      Contract.Step (.online known) (.uncertain batch) (.offline known (some batch)) ∧
      after.phase = .poisoned .lock

/-- From a recovered, owned writer, the actual append schedule publishes
exactly one batch or keeps exactly that submission pending. -/
theorem append_refines (reports : ∀ cursor, AppendReports policy cursor batch)
    (entry : Ready policy image known) (clean : image.powerLoss = image)
    (bounded : ∀ b ∈ known, b.length ≤ 32) (room : known.length < 255)
    (size : batch.length ≤ 32) :
    let result := appendModel reports ⟨image, .active .lock (appendBindings policy) (historyCursor known) known⟩
    AppendGuarantee policy known batch result := by
  let input := reports (historyCursor known)
  have facts := appendPrimitive_refines input.effects input.writebacks policy image known batch
    input.torn entry clean bounded room size
  rw [← appendWorker_eq input] at facts
  dsimp only [AppendGuarantee]
  rw [activeResult]
  generalize (appendWorker (appendBindings policy) input).run image = physical at facts ⊢
  cases physical with
  | error => exact ⟨facts.1, facts.2.1, .uncertain, rfl⟩
  | ok response after =>
    cases response with
    | error => exact ⟨facts.1, facts.2.1, .uncertain, rfl⟩
    | ok next =>
      obtain ⟨rfl, ready, settled⟩ := facts.2.2 next rfl
      exact ⟨facts.1, facts.2.1, .ack, rfl, ready, settled⟩

def healthyAppendReports : AppendReports policy cursor batch where
  effects := {
    appendData := .full .old none
    dataSync := .after none
    writeMarker := .full .old none
    markerSync := fun _ => .after none
  }

theorem appendModel_healthy (policy : Policy) (image : Image) (known : List Bytes)
    (bounded : ∀ b ∈ known, b.length ≤ 32) (room : known.length < 255)
    (size : batch.length ≤ 32) :
    ∃ after, appendModel (policy := policy) (batch := batch) (fun _ => healthyAppendReports)
      ⟨image, .active .lock (appendBindings policy) (historyCursor known) known⟩ =
        .ok (.ok ()) after := by
  have seqFits : ¬255 < 1 + known.length := by omega
  have offsetFits : ¬65535 < (encodeFrames 1 known).length + (frame (1 + known.length) batch).length := by
    have bytes := encoded_history_size known 1 bounded
    rw [frame_length]
    omega
  simp only [activeResult, appendWorker_eq]
  cases policy <;>
    simp [healthyAppendReports, appendPrimitives, scheduledOps, appendBatch, ops, historyCursor,
      maxPayload, Nat.not_lt.mpr size, seqFits, offsetFits, reduceBEq, Policy.ctorIdx,
      Bind.bind, ExceptT.bind, ExceptT.run, ExceptT.mk, ExceptT.bindCont, Pure.pure,
      ExceptT.pure, EStateM.bind, EStateM.pure, withWritebacks, Write.result, Primitive.syncResult] <;>
    first | rfl | exact ⟨_, rfl⟩

/-- A lost reply after the final barrier has the same public uncertainty
as an error, while recovery still uses the exact reached image. -/
theorem AppendGuarantee.lostReply (outcome : AppendGuarantee policy known batch result) :
    Contract.Step (.online known) (.uncertain batch) (.offline known (some batch)) ∧
      Dirty policy known (some batch) (appendReached result).image :=
  ⟨.uncertain, outcome.1⟩

/-- The public open producer supplies exactly the append phase consumed by
the writer proof. No descriptor binding is supplied by the caller. -/
theorem openedAppendPhase (opened : OpenGuarantee policy prior pending (.ok (.ok ready) after)) :
    storedPhase ready = .active .lock (appendBindings policy)
      (historyCursor ready.recovered.batches) ready.recovered.batches := by
  obtain ⟨heldLock, _, _, writer, markers, _, _, _, _, cursor, _, _, installed⟩ := opened.2.2
  rw [storedPhase_eq, installed, heldLock, writer, markers, cursor]
  rfl

theorem append_rejected (reports : ∀ cursor, AppendReports policy cursor batch)
    (invalid : batch.length > 32 ∨ known.length ≥ 255) :
    appendModel reports ⟨image, .active .lock (appendBindings policy) (historyCursor known) known⟩ =
      .ok (.error "batch out of bounds") ⟨image, .poisoned .lock⟩ := by
  have guard : (batch.length > maxPayload || (historyCursor known).nextSeq == 0 ||
      (historyCursor known).nextSeq > 255) = true := by
    rcases invalid with size | room
    · simp [maxPayload, size]
    · have next : (historyCursor known).nextSeq > 255 := by simp [historyCursor]; omega
      simp [next]
  rw [activeResult, appendWorker_eq]
  simp only [appendBatch, guard, ite_true]
  rfl

theorem append_closed (reports : ∀ cursor, AppendReports policy cursor batch) (image : Image) :
    appendModel reports ⟨image, .closed⟩ = .ok (.error "WAL closed") ⟨image, .closed⟩ := rfl

theorem append_poisoned (reports : ∀ cursor, AppendReports policy cursor batch) (image : Image) :
    appendModel reports ⟨image, .poisoned .lock⟩ =
      .ok (.error "WAL poisoned; reopen required") ⟨image, .poisoned .lock⟩ := rfl

end WalRecoverySlice.SingleFile
