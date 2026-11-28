import Alvoki.Experiments.WAL.Segmented.Proofs.NativeControl
import Alvoki.Experiments.WAL.Segmented.Proofs.Append
import Alvoki.Experiments.WAL.Segmented.Proofs.Bootstrap

namespace WalRecoverySlice.Segmented.Model

abbrev ActiveAppendM := ExceptT String (EStateM Unit (State × SingleFile.AppendPhase))

/-- Interpret the native child call on the actual active image and phase.
The child keeps its phase internally. The root model retains that phase
and updates only the reached child slot. -/
private def writeActive (policy : Policy) (id : Nat)
    (reports : ∀ cursor, SingleFile.AppendReports policy cursor batch) : ActiveAppendM Unit := fun s =>
  let update (child : SingleFile.AppendImage) (cursor : Cursor) :=
    ({s.1.tick with disk := s.1.disk.setSegment id child.image cursor}, child.phase)
  match SingleFile.appendModel reports ⟨s.1.disk.segment id, s.2⟩ with
  | .ok (.ok ()) child =>
    let cursor := match child.phase with
      | .active _ _ cursor _ => cursor
      | _ => s.1.disk.cursor id
    .ok (.ok ()) (update child cursor)
  | .ok (.error err) child => .ok (.error err) (update child (s.1.disk.cursor id))
  | .error token child => .error token (update child (s.1.disk.cursor id))

/-- Check the payload actually passed by the shared schedule before using
the primitive reports for that request. -/
private def writeRequested (policy : Policy) (id : Nat)
    (reports : ∀ cursor, SingleFile.AppendReports policy cursor batch)
    (actual : Bytes) : ActiveAppendM Unit :=
  if actual = batch then writeActive policy id reports else throw "wrong append payload"

/-- Run the same public mutation schedule on the installed active reference.
The no-rotation precondition leaves preparation and publication unreachable. -/
def appendActiveModel (session : Session) (id : Nat)
    (reports : ∀ cursor, SingleFile.AppendReports session.control.policy cursor batch) :
    ActiveAppendM Session :=
  Native.appendOwnedWith (error := String) session batch (checkAppend session batch) _root_.id
    (pure (some (id, ()))) (throw "unexpected close before rotation")
    (fun _ _ => throw "unexpected rotation") (fun _ => pure ())
    (throw "unexpected root barrier") (fun _ => throw "unexpected CONTROL publication")
    (fun _ payload => writeRequested session.control.policy id reports payload) (fun _ => pure ())

theorem appendActiveModel_run (session : Session) (reports : ∀ cursor,
    SingleFile.AppendReports session.control.policy cursor batch)
    (s : State × SingleFile.AppendPhase) (room : session.activeCount ≠ session.control.capacity)
    (size : batch.length ≤ 32) (position : session.view.tail < Contract.maxPosition) :
    (appendActiveModel session session.control.active reports).run s =
      match (writeActive session.control.policy session.control.active reports).run s with
      | .ok (.ok ()) after => .ok (.ok
          ⟨session.control, session.activeCount + 1, session.view.append batch⟩) after
      | .ok (.error err) after => .ok (.error err) after
      | .error token after => .error token after := by
  unfold appendActiveModel Native.appendOwnedWith checkAppend
  simp [Nat.not_lt.mpr size, Nat.not_le.mpr position, room, writeRequested, Bind.bind, ExceptT.bind,
    ExceptT.mk, ExceptT.pure, Pure.pure]
  simp only [ExceptT.run, EStateM.bind, ExceptT.bindCont, EStateM.pure, ↓reduceIte]
  cases (writeActive session.control.policy session.control.active reports) s with
  | error => rfl
  | ok result _ => cases result <;> rfl

private def erasePhase (result : EStateM.Result Unit (State × SingleFile.AppendPhase) (Except String α)) :
    Result α :=
  match result with
  | .ok value s => .ok value s.1
  | .error token s => .error token s.1

private theorem writeActive_refines (c : Control) (history : List Bytes) (batch : Bytes)
    (s : State) (entry : ReadyLayout c history s.disk)
    (live : s.disk.liveControl = some c) (durable : s.disk.durableControl = some c)
    (room : history.length < (c.active + 1) * c.capacity) (size : batch.length ≤ 32)
    (position : (historyView c history).tail < Contract.maxPosition)
    (reports : ∀ cursor, SingleFile.AppendReports c.policy cursor batch) :
    let old := segmentHistory c.capacity c.active history
    let phase := SingleFile.Phase.active .lock (SingleFile.appendBindings c.policy)
      (Persistence.historyCursor old) old
    let run := (writeActive c.policy c.active reports).run (s, phase)
    DiskPost (fun _ disk => ReadyLayout c (history ++ [batch]) disk ∧
      disk.liveControl = some c ∧ disk.durableControl = some c)
      (Recoverable (historyView c history) (some (.append batch))) (erasePhase run) := by
  intro old phase run
  have fits : old.length < 255 := by
    dsimp only [old]
    rw [segmentHistory_active_length entry.layout.upper]
    rw [Nat.add_mul, Nat.one_mul] at room
    have := entry.layout.capacityFits
    omega
  let issued := SingleFile.appendModel reports ⟨s.disk.segment c.active, phase⟩
  have runEq : run = match issued with
      | .ok (.ok ()) result =>
        let cursor := match result.phase with
          | .active _ _ cursor _ => cursor
          | _ => s.disk.cursor c.active
        .ok (.ok ()) ({s.tick with disk := s.disk.setSegment c.active result.image cursor}, result.phase)
      | .ok (.error err) result =>
        .ok (.error err) ({s.tick with disk := s.disk.setSegment c.active result.image (s.disk.cursor c.active)}, result.phase)
      | .error token result =>
        .error token ({s.tick with disk := s.disk.setSegment c.active result.image (s.disk.cursor c.active)}, result.phase) := rfl
  have exactChild : SingleFile.AppendGuarantee c.policy old batch issued :=
    SingleFile.append_refines reports entry.active.ready entry.active.clean
      (segmentHistory_bounded entry.layout _) fits size
  apply appendActive_refinesWith c history batch s entry live durable room size position
  · rw [runEq]
    cases cut : issued with
    | error => exact ⟨_, _, rfl⟩
    | ok response after => cases response <;> exact ⟨_, _, rfl⟩
  · rw [runEq]
    cases cut : issued with
    | error token after =>
      rw [cut] at exactChild
      refine ⟨?_, fun h => by cases h⟩
      simpa [erasePhase, reached, Disk.setSegment_here, SingleFile.appendReached] using
        (Child.Recoverable.mk exactChild.1 exactChild.2.1 : Child.Recoverable c.policy old (some batch) after.image)
    | ok response after =>
      rw [cut] at exactChild
      cases response with
      | error =>
        refine ⟨?_, fun h => by cases h⟩
        simpa [erasePhase, reached, Disk.setSegment_here, SingleFile.appendReached] using
          (Child.Recoverable.mk exactChild.1 exactChild.2.1 : Child.Recoverable c.policy old (some batch) after.image)
      | ok acknowledged =>
        cases acknowledged
        obtain ⟨_, phaseEq, valid, settled⟩ := exactChild.2.2
        simp only [phaseEq, erasePhase, reached, Disk.setSegment_here, Disk.setCursor_here]
        exact ⟨⟨exactChild.1, exactChild.2.1⟩, fun _ => ⟨⟨valid, settled⟩, rfl⟩⟩

/-- Reusable authority of the current ready handle. Both append branches
consume the same phase and disk layout. -/
def AppendReady (session : Session) (state : State × SingleFile.AppendPhase) : Prop :=
  ∃ history, session = sessionOf session.control history ∧
    ReadyLayout session.control history state.1.disk ∧
    state.1.disk.liveControl = some session.control ∧ state.1.disk.durableControl = some session.control ∧
    state.2 = .active .lock (SingleFile.appendBindings session.control.policy)
      (state.1.disk.cursor session.control.active)
      (segmentHistory session.control.capacity session.control.active history)

theorem AppendReady.installed {session : Session} {state : State × SingleFile.AppendPhase}
    (ready : AppendReady session state) : Installed session state.1.disk := by
  obtain ⟨history, shape, layout, live, durable, _⟩ := ready
  exact ⟨history, shape, layout, live, durable⟩

private theorem responsePhase_fromWrite (c : Control) (history : List Bytes) (batch : Bytes)
    (s : State) (entry : ReadyLayout c history s.disk)
    (fits : (segmentHistory c.capacity c.active history).length < 255)
    (size : batch.length ≤ 32)
    (reports : ∀ cursor, SingleFile.AppendReports c.policy cursor batch)
    {phase : SingleFile.AppendPhase}
    (source : phase = .active .lock (SingleFile.appendBindings c.policy)
      (Persistence.historyCursor (segmentHistory c.capacity c.active history))
      (segmentHistory c.capacity c.active history))
    {after : State × SingleFile.AppendPhase}
    (returned : (writeActive c.policy c.active reports).run (s, phase) = .ok (.ok ()) after) :
    let suffix := segmentHistory c.capacity c.active history ++ [batch]
    after.2 = .active .lock (SingleFile.appendBindings c.policy)
      (after.1.disk.cursor c.active) suffix := by
  subst phase
  have child := SingleFile.append_refines reports entry.active.ready entry.active.clean
    (segmentHistory_bounded entry.layout _) fits size
  dsimp only at child
  simp only [writeActive, ExceptT.run] at returned
  rename_i _
  split at returned
  · rename_i target made
    rw [made] at child
    obtain ⟨_, canonical, _, _⟩ := child.2.2
    cases returned
    simp only [canonical, Disk.setCursor_here]
  · cases returned
  · cases returned

/-- A native non-rotating append supplies the L0 acknowledgement or the
recoverable image of precisely the attempted batch. -/
theorem appendActiveModel_refines (c : Control) (history : List Bytes) (batch : Bytes)
    (s : State) (entry : ReadyLayout c history s.disk)
    (live : s.disk.liveControl = some c) (durable : s.disk.durableControl = some c)
    (room : history.length < (c.active + 1) * c.capacity) (size : batch.length ≤ 32)
    (position : (historyView c history).tail < Contract.maxPosition)
    (reports : ∀ cursor, SingleFile.AppendReports c.policy cursor batch) :
    let old := segmentHistory c.capacity c.active history
    let phase := SingleFile.Phase.active .lock (SingleFile.appendBindings c.policy)
      (Persistence.historyCursor old) old
    let session := sessionOf c history
    DiskPost (fun next disk => Installed next disk ∧
      Contract.Step (.online session.view) (.ack (.append batch)) (.online next.view) ∧
      next.tailPosition = session.view.tail + 1)
      (Recoverable session.view (some (.append batch)))
      (erasePhase ((appendActiveModel session c.active reports).run (s, phase))) := by
  intro old phase session
  have spare : session.activeCount ≠ c.capacity := by
    change old.length ≠ c.capacity
    dsimp only [old]
    rw [segmentHistory_active_length entry.layout.upper]
    rw [Nat.add_mul, Nat.one_mul] at room
    have := entry.layout.lower
    omega
  have scheduled := appendActiveModel_run session reports (s, phase) spare size position
  change DiskPost _ _ (erasePhase ((appendActiveModel session session.control.active reports).run (s, phase)))
  rw [scheduled]
  have post := writeActive_refines c history batch s entry live durable room size position reports
  dsimp only at post
  change DiskPost _ _ (erasePhase (match (writeActive c.policy c.active reports).run (s, phase) with
    | .ok (.ok ()) after => .ok (.ok (⟨c, session.activeCount + 1, session.view.append batch⟩ : Session)) after
    | .ok (.error err) after => .ok (.error err) after
    | .error token after => .error token after))
  cases wrote : (writeActive c.policy c.active reports).run (s, phase) with
  | error => rw [wrote] at post; exact post
  | ok response after =>
    rw [wrote] at post
    cases response with
    | error => exact post
    | ok ack =>
      cases ack
      obtain ⟨ready, liveAfter, durableAfter⟩ := post
      have view := historyView_append entry.layout.discardedFits batch
      have suffix := segmentHistory_append batch entry.layout.lower room
      have shape : (⟨c, session.activeCount + 1, session.view.append batch⟩ : Session) =
          sessionOf c (history ++ [batch]) := by
        simp [session, sessionOf, view, suffix]
      refine ⟨⟨_, shape, ready, liveAfter, durableAfter⟩, .ack ?_, ?_⟩
      · simp [session, sessionOf, Contract.Request.apply, position]
      · change c.active * c.capacity + (old.length + 1) = (historyView c history).tail + 1
        rw [historyView_tail entry.layout.discardedFits, segmentHistory_active_length entry.layout.upper]
        have := entry.layout.lower
        omega

theorem appendActiveModel_ready (c : Control) (history : List Bytes) (batch : Bytes)
    (s : State) (entry : ReadyLayout c history s.disk)
    (live : s.disk.liveControl = some c) (durable : s.disk.durableControl = some c)
    (room : history.length < (c.active + 1) * c.capacity) (size : batch.length ≤ 32)
    (position : (historyView c history).tail < Contract.maxPosition)
    (reports : ∀ cursor, SingleFile.AppendReports c.policy cursor batch)
    (phase : SingleFile.AppendPhase)
    (source : phase = .active .lock (SingleFile.appendBindings c.policy)
      (Persistence.historyCursor (segmentHistory c.capacity c.active history))
      (segmentHistory c.capacity c.active history))
    {next : Session} {after : State × SingleFile.AppendPhase}
    (returned : (appendActiveModel (sessionOf c history) c.active reports).run (s, phase) =
      .ok (.ok next) after) :
    AppendReady next after := by
  have fits : (segmentHistory c.capacity c.active history).length < c.capacity := by
    rw [segmentHistory_active_length entry.layout.upper]
    rw [Nat.add_mul, Nat.one_mul] at room
    have := entry.layout.lower
    omega
  have spare : (sessionOf c history).activeCount ≠ (sessionOf c history).control.capacity :=
    Nat.ne_of_lt fits
  have scheduled := appendActiveModel_run (sessionOf c history) reports (s, phase) spare size position
  simp only [sessionOf] at scheduled returned
  rw [scheduled] at returned
  cases wrote : (writeActive c.policy c.active reports).run (s, phase) with
  | error => rw [wrote] at returned; cases returned
  | ok reply reached =>
    rw [wrote] at returned
    cases reply with
    | error => cases returned
    | ok unitValue =>
      cases unitValue
      cases returned
      have post := writeActive_refines c history batch s entry live durable room size position reports
      dsimp only at post
      rw [← source, wrote] at post
      obtain ⟨layout, l, r⟩ := post
      have cursor := responsePhase_fromWrite c history batch s entry
        (Nat.lt_of_lt_of_le fits entry.layout.capacityFits) size reports source wrote
      have suffix := segmentHistory_append batch entry.layout.lower room
      have view := historyView_append entry.layout.discardedFits batch
      exact ⟨history ++ [batch], by simp [sessionOf, view, suffix],
        layout, l, r, suffix.symm ▸ cursor⟩

/-- A successful non-rotating append leaves the retained child description
positioned at the new history. A failed write leaves that description poisoned. -/
theorem appendActiveModel_childPhase (c : Control) (history : List Bytes) (batch : Bytes)
    (s : State) (entry : ReadyLayout c history s.disk)
    (room : history.length < (c.active + 1) * c.capacity) (size : batch.length ≤ 32)
    (position : (historyView c history).tail < Contract.maxPosition)
    (reports : ∀ cursor, SingleFile.AppendReports c.policy cursor batch) :
    let old := segmentHistory c.capacity c.active history
    let phase := SingleFile.Phase.active .lock (SingleFile.appendBindings c.policy)
      (Persistence.historyCursor old) old
    match (appendActiveModel (sessionOf c history) c.active reports).run (s, phase) with
    | .ok (.ok _) after => after.2 =
      .active .lock (SingleFile.appendBindings c.policy)
        (Persistence.historyCursor (old ++ [batch])) (old ++ [batch])
    | .ok (.error _) after | .error _ after => after.2 = .poisoned .lock := by
  intro old phase
  have fits : old.length < 255 := by
    dsimp only [old]
    rw [segmentHistory_active_length entry.layout.upper]
    rw [Nat.add_mul, Nat.one_mul] at room
    have := entry.layout.capacityFits
    omega
  have spare : (sessionOf c history).activeCount ≠ c.capacity := by
    change old.length ≠ c.capacity
    dsimp only [old]
    rw [segmentHistory_active_length entry.layout.upper]
    rw [Nat.add_mul, Nat.one_mul] at room
    have := entry.layout.lower
    omega
  have scheduled := appendActiveModel_run (sessionOf c history) reports (s, phase) spare size position
  simp only [sessionOf] at scheduled ⊢
  rw [scheduled]
  have child := SingleFile.append_refines reports entry.active.ready entry.active.clean
    (segmentHistory_bounded entry.layout _) fits size
  dsimp only at child
  simp only [writeActive, ExceptT.run]
  change SingleFile.AppendGuarantee c.policy old batch
    (SingleFile.appendModel reports ⟨s.disk.segment c.active, phase⟩) at child
  cases issued : SingleFile.appendModel reports ⟨s.disk.segment c.active, phase⟩ with
  | error => rw [issued] at child; exact child.2.2.2
  | ok response after =>
    rw [issued] at child
    cases response with
    | error => exact child.2.2.2
    | ok ack => cases ack; exact child.2.2.2.1

theorem appendAfterNativeReopen (owned : RootBinding directory lock)
    (rootReports : RootReports) (openReports : Nat → Nat → SingleFile.OpenReports)
    (closeError : Option String) {start s : State} (prior : Recoverable known request start.disk)
    {store : ReopenedStore directory lock} {session : Session}
    (opened : (installScopedModel owned rootReports openReports closeError).run start =
      .ok (.ok (.ready store session)) s)
    (room : session.activeCount < session.control.capacity)
    (size : batch.length ≤ 32) (position : session.view.tail < Contract.maxPosition)
    (reports : ∀ cursor, SingleFile.AppendReports session.control.policy cursor batch) :
    let result := (appendActiveModel session store.activeId reports).run
      (s, SingleFile.storedPhase store.activeChild)
    DiskPost (fun next disk => Installed next disk ∧
      Contract.Step (.online session.view) (.ack (.append batch)) (.online next.view) ∧
      next.tailPosition = session.view.tail + 1)
      (Recoverable session.view (some (.append batch))) (erasePhase result) ∧
    match result with
    | .ok (.ok _) after =>
      let next := store.activeChild.recovered.batches ++ [batch]
      after.2 = .active .lock (SingleFile.appendBindings session.control.policy)
        (Persistence.historyCursor next) next
    | .ok (.error _) after | .error _ after => after.2 = .poisoned .lock := by
  obtain ⟨history, shape, entry, live, durable, _, idEq, phaseEq, batchesEq⟩ :=
    installScopedModel_appendPhase owned rootReports openReports closeError prior opened
  have fits : history.length < (session.control.active + 1) * session.control.capacity := by
    have length := segmentHistory_active_length entry.layout.upper
    have count := congrArg Session.activeCount shape
    change session.activeCount =
      (segmentHistory session.control.capacity session.control.active history).length at count
    rw [length] at count
    have lower := entry.layout.lower
    have upper := entry.layout.upper
    rw [Nat.add_mul, Nat.one_mul] at upper ⊢
    omega
  have exactView := congrArg Session.view shape
  change session.view = historyView session.control history at exactView
  have post := appendActiveModel_refines session.control history batch s entry live durable
    fits size (exactView ▸ position) reports
  have phase := appendActiveModel_childPhase session.control history batch s entry fits size
    (exactView ▸ position) reports
  dsimp only at post phase ⊢
  rw [idEq] at batchesEq
  rw [phaseEq, idEq, entry.active.position, batchesEq]
  cases session with
  | mk control count view =>
    simp only [sessionOf, Session.mk.injEq, true_and] at shape
    obtain ⟨rfl, rfl⟩ := shape
    exact ⟨post, phase⟩

/-- Position exhaustion and oversize checks run before any child or
namespace action, so the original history remains recoverable. -/
theorem appendActiveModel_rejected (session : Session) (id : Nat)
    (reports : ∀ cursor, SingleFile.AppendReports session.control.policy cursor batch)
    (s : State × SingleFile.AppendPhase)
    (rejected : batch.length > 32 ∨ session.view.tail ≥ Contract.maxPosition) :
    (appendActiveModel session id reports).run s =
      .ok (.error (if batch.length > 32 then "batch out of bounds" else
        "segmented WAL position exhausted")) s := by
  by_cases size : batch.length > 32
  · simp only [appendActiveModel, Native.appendOwnedWith, checkAppend, size, ↓reduceIte]
    rfl
  · have exhausted := rejected.resolve_left size
    simp only [appendActiveModel, Native.appendOwnedWith, checkAppend, size, exhausted, ↓reduceIte]
    rfl

/-- Retain the outer phase alongside the reached child and disk. Phase
writes are reference operations and have no disk effects. -/
private abbrev PublicAppendM :=
  ExceptT String (EStateM Unit ((State × SingleFile.AppendPhase) × Native.Phase Nat))

def publicAppendActiveModel
    (action : Nat → Session → ActiveAppendM Session) : PublicAppendM Session :=
  Native.updateWith (error := String) _root_.id
    (fun s => .ok (.ok s.2) s)
    (fun phase s => .ok (.ok ()) (s.1, phase))
    (fun id session s =>
      match (action id session).run s.1 with
      | .ok response after => .ok response (after, s.2)
      | .error token after => .error token (after, s.2))

theorem publicAppendActiveModel_run (action : Nat → Session → ActiveAppendM Session)
    (id : Nat) (session : Session) (s : State × SingleFile.AppendPhase) :
    (publicAppendActiveModel action).run (s, .ready id session) =
      match (action id session).run s with
      | .ok (.ok next) after => .ok (.ok next) (after, .ready id next)
      | .ok (.error err) after => .ok (.error err) (after, .poisoned id)
      | .error token after => .error token (after, .poisoned id) := by
  unfold publicAppendActiveModel Native.updateWith
  simp only [Bind.bind, ExceptT.bind, ExceptT.run, ExceptT.mk, EStateM.bind, ExceptT.bindCont]
  cases (action id session) s with
  | error => rfl
  | ok response _ => cases response <;> rfl

/-- The public non-rotating append returns the acknowledged session in the
ready phase; an unsuccessful write preserves its reached disk in the
poisoned phase for the recovery producer. -/
theorem publicAppendAfterReopen (owned : RootBinding directory lock)
    (rootReports : RootReports) (openReports : Nat → Nat → SingleFile.OpenReports)
    (closeError : Option String) {start s : State} (prior : Recoverable known request start.disk)
    {store : ReopenedStore directory lock} {session : Session}
    (opened : (installScopedModel owned rootReports openReports closeError).run start =
      .ok (.ok (.ready store session)) s)
    (room : session.activeCount < session.control.capacity)
    (size : batch.length ≤ 32) (position : session.view.tail < Contract.maxPosition)
    (reports : ∀ policy cursor, SingleFile.AppendReports policy cursor batch) :
    let action := fun id (current : Session) =>
      appendActiveModel current id (reports current.control.policy)
    match (publicAppendActiveModel action).run
        ((s, SingleFile.storedPhase store.activeChild), .ready store.activeId session) with
    | .ok (.ok next) (after, phase) =>
      phase = .ready store.activeId next ∧ Installed next after.1.disk ∧
      Contract.Step (.online session.view) (.ack (.append batch)) (.online next.view) ∧
      next.tailPosition = session.view.tail + 1 ∧
      let nextHistory := store.activeChild.recovered.batches ++ [batch]
      after.2 = .active .lock (SingleFile.appendBindings session.control.policy)
        (Persistence.historyCursor nextHistory) nextHistory
    | .ok (.error _) (after, phase) | .error _ (after, phase) =>
      phase = .poisoned store.activeId ∧
      Recoverable session.view (some (.append batch)) after.1.disk ∧
      after.2 = .poisoned .lock := by
  dsimp only
  rw [publicAppendActiveModel_run]
  have result := appendAfterNativeReopen owned rootReports openReports closeError prior opened
    room size position (reports session.control.policy)
  dsimp only at result
  cases ran : (appendActiveModel session store.activeId (reports session.control.policy)).run
      (s, SingleFile.storedPhase store.activeChild) with
  | error => rw [ran] at result; exact ⟨rfl, result.1, result.2⟩
  | ok response after =>
    rw [ran] at result
    cases response with
    | error => exact ⟨rfl, result.1, result.2⟩
    | ok => exact ⟨rfl, result.1.1, result.1.2.1, result.1.2.2, result.2⟩

/-- A pending append's exact reached disk is a valid input to the existing
reopen producer. A failed attempt preserves both choices, and the first
successful open pins its selection for another open. -/
theorem repeatOpenAfterAppend (root : System.FilePath) (failedFirst first second : RootReports)
    (reports : Nat → Nat → SingleFile.OpenReports) {s failed opened done : State}
    {firstSession secondSession : Session}
    (pending : Recoverable known (some (.append batch)) s.disk)
    (fail : (Segmented.reopen (nativeReopenOps root failedFirst reports)).run s =
      .ok (.error err) failed)
    (openFirst : (Segmented.reopen (nativeReopenOps root first reports)).run failed =
      .ok (.ok firstSession) opened)
    (openSecond : (Segmented.reopen (nativeReopenOps root second reports)).run opened =
      .ok (.ok secondSession) done) :
    PermittedView known (some (.append batch)) firstSession.view ∧
      secondSession.view = firstSession.view := by
  have retry := reopen_nativeRoot root failedFirst reports s pending
  rw [fail] at retry
  have chosen := reopen_nativeRoot root first reports failed retry
  rw [openFirst] at chosen
  have pinned := chosen.1.offline (request := none) (.inl rfl)
  have again := reopen_nativeRoot root second reports opened pinned
  rw [openSecond] at again
  exact ⟨chosen.2, again.2.elim id (fun impossible => by cases impossible)⟩

/-- A lost acknowledgement leaves the installed result as the surviving
choice, and power loss may be applied to the exact reached disk. -/
theorem appendLostAck {before next : Session} {disk : Disk} {batch : Bytes}
    (installed : Installed next disk)
    (ack : Contract.Step (.online before.view) (.ack (.append batch)) (.online next.view)) :
    Recoverable before.view (some (.append batch)) disk ∧
      Recoverable before.view (some (.append batch)) disk.powerLoss := by
  cases ack with
  | ack applied =>
    have stopped := installed.offline (request := some (.append batch)) (.inr applied)
    exact ⟨stopped, stopped.powerLoss⟩

/-- The public open producer handles both reported failure and process stop
on the exact reached image. It pins a successful choice for later opens. -/
theorem publicAppendRecovery (owned : RootBinding directory lock)
    (interrupted first second : RootReports)
    (reports : Nat → Nat → SingleFile.OpenReports) (childError rootError : Option String)
    {start failed returned final : State} {original : Contract.View} {batch : Bytes}
    (pending : Recoverable original (some (.append batch)) start.disk)
    {firstStore secondStore : ReopenedStore directory lock} {firstSession secondSession : Session}
    (failedOpen : match (publicOpenModel (.ok owned) interrupted reports childError rootError).run (start, false) with
      | .ok (.error _) after | .error _ after => after.1 = failed
      | .ok (.ok _) _ => False)
    (opened : (publicOpenModel (.ok owned) first reports childError rootError).run (failed, false) =
      .ok (.ok (.ready firstStore firstSession, ())) (returned, true))
    (reopened : (publicOpenModel (.ok owned) second reports childError rootError).run (returned, false) =
      .ok (.ok (.ready secondStore secondSession, ())) (final, true)) :
    PermittedView original (some (.append batch)) firstSession.view ∧
      secondSession.view = firstSession.view := by
  have failedPost := publicOpenModel_refines (.ok owned) interrupted reports childError rootError start pending
  have retry : Recoverable original (some (.append batch)) failed.disk := by
    cases ran : (publicOpenModel (.ok owned) interrupted reports childError rootError).run (start, false) with
    | error token after =>
      rw [ran] at failedPost failedOpen
      exact failedOpen ▸ failedPost.2
    | ok response after =>
      rw [ran] at failedPost failedOpen
      cases response with
      | ok => exact False.elim failedOpen
      | error => exact failedOpen ▸ failedPost.2.1
  have chosen := publicOpenModel_refines (.ok owned) first reports childError rootError failed retry
  rw [opened] at chosen
  have pinned := chosen.2.2.2.1.offline (request := none) (.inl rfl)
  have again := publicOpenModel_refines (.ok owned) second reports childError rootError returned pinned
  rw [reopened] at again
  exact ⟨chosen.2.2.2.2.1, again.2.2.2.2.1.elim id (fun impossible => by cases impossible)⟩

/-- Collect the exact durable writes made by the native initialization
schedule, including the marker that selects the empty boundary history. -/
theorem initializeChild_writes (dir : System.FilePath) (policy : Policy) :
    let write (path : System.FilePath) (bytes : ByteArray) : StateM (List (System.FilePath × ByteArray)) Unit :=
      modify (· ++ [(path, bytes)])
    ((SingleFile.initializeFilesWith write dir policy).run []).2 =
      [(dir / "policy", (Native.policyStamp policy).toUTF8), (dir / "segment", ByteArray.empty)] ++
      (if policy == .boundary then
        [(dir / "commit.0", ⟨(encodeMarker 0 0).toArray⟩), (dir / "commit.1", ByteArray.empty)]
      else []) := by
  cases policy <;> rfl

/-- The position bound used by L0 also bounds the selected CONTROL fields. -/
theorem installed_controlRepresentable {session : Session} {s : State}
    (installed : Installed session s.disk) (bound : session.view.tail ≤ Contract.maxPosition) :
    session.control.capacity ≤ 255 ∧ session.control.active ≤ ControlCodec.wordMax ∧
      session.control.discarded ≤ ControlCodec.wordMax := by
  obtain ⟨history, shape, entry, _, _⟩ := installed
  have view := congrArg Session.view shape
  change session.view = historyView session.control history at view
  rw [view, historyView_tail entry.layout.discardedFits] at bound
  have active := Nat.le_trans
    (Nat.le_mul_of_pos_right session.control.active entry.layout.capacityPositive) entry.layout.lower
  exact ⟨entry.layout.capacityFits, Nat.le_trans active bound,
    Nat.le_trans entry.layout.discardedFits bound⟩

/-- A permitted rotating append has room to publish the successor ID. -/
theorem successor_controlRepresentable {session : Session} {s : State}
    (installed : Installed session s.disk) (bound : session.view.tail < Contract.maxPosition) :
    (successor session).active ≤ ControlCodec.wordMax ∧
      (successor session).discarded ≤ ControlCodec.wordMax := by
  obtain ⟨history, shape, entry, _, _⟩ := installed
  have view := congrArg Session.view shape
  change session.view = historyView session.control history at view
  rw [view, historyView_tail entry.layout.discardedFits] at bound
  have active := Nat.le_trans
    (Nat.le_mul_of_pos_right session.control.active entry.layout.capacityPositive) entry.layout.lower
  exact ⟨Nat.succ_le_of_lt (Nat.lt_of_le_of_lt active bound),
    Nat.le_trans entry.layout.discardedFits (Nat.le_of_lt bound)⟩

theorem nativeControl_bootstrap (root : System.FilePath) (held : Nat) (r : Effects)
    (policy : Policy) (capacity : Nat) :
    Segmented.create (nativeControlOps root held r) policy capacity =
      Segmented.create (ops r) policy capacity := by
  unfold Segmented.create
  split
  · rfl
  · dsimp only
    rw [nativeControl_run root held r ⟨policy, capacity, 0, 0⟩ (Nat.zero_le _) (Nat.zero_le _)]
    rfl

/-- The existing rotation cuts consume the native CONTROL producer.
Preparation remains the disk namespace action in this interpretation. -/
theorem nativeControl_rotate (root : System.FilePath) (held : Nat) (r : Effects)
    (session : Session) (s : State) (installed : Installed session s.disk)
    (room : session.view.tail < Contract.maxPosition) :
    rotateIfFull (nativeControlOps root held r) session = rotateIfFull (ops r) session := by
  have fits := successor_controlRepresentable installed room
  by_cases full : session.activeCount = session.control.capacity
  · simp only [rotateIfFull, full, ↓reduceIte]
    have ran := nativeControl_run root held r (successor session) fits.1 fits.2
    simp only [successor] at ran
    rw [ran]
    rfl
  · simp [rotateIfFull, full]

/-- Any rotation cut before the child write preserves the old view.
Even a published successor with zero batches has a ready layout and
exactly the previous absolute tail. -/
theorem nativeRotation_beforeAppend (root : System.FilePath) (held : Nat) (reports : Effects)
    (c : Control) (history : List Bytes) (batch : Bytes) (s : State)
    (entry : ReadyLayout c history s.disk) (live : s.disk.liveControl = some c)
    (durable : s.disk.durableControl = some c)
    (fits : (historyView c history).tail < Contract.maxPosition) :
    DiskPost (fun pair disk =>
      Installed ⟨pair.1, pair.2, historyView c history⟩ disk ∧
      Recoverable (historyView c history) none disk)
      (Recoverable (historyView c history) (some (.append batch)))
      ((rotateIfFull (nativeControlOps root held reports) (sessionOf c history)).run s) := by
  have installed : Installed (sessionOf c history) s.disk := ⟨history, rfl, entry, live, durable⟩
  rw [nativeControl_rotate root held reports _ s installed fits]
  have post := rotateIfFull_refines reports c history batch s entry live durable
  cases ran : (rotateIfFull (ops reports) (sessionOf c history)).run s with
  | error => rw [ran] at post; exact post
  | ok response after =>
    rw [ran] at post
    cases response with
    | error => exact post
    | ok pair =>
      obtain ⟨layout, named, synced, count, view, _⟩ := post
      have next : Installed ⟨pair.1, pair.2, historyView c history⟩ after.disk :=
        ⟨history, by simp [sessionOf, count, view], layout, named, synced⟩
      exact ⟨next, next.offline (request := none) (.inl rfl)⟩

/-- The installed active phase of a newly created child has the empty
history on a settled image, with the descriptions expected by append. -/
theorem nativeCreatedChild (dir : System.FilePath) (policy : Policy)
    (reports : SingleFile.CreateReports) (linux : System.Platform.isWindows = false)
    (created : SingleFile.createModel dir policy reports = .ok (.ok ready) after) :
    after.image = Persistence.freshImage ∧ after.namesDurable = true ∧ after.held = true ∧
      SingleFile.storedPhase ready = .active .lock (SingleFile.appendBindings policy)
        (Persistence.historyCursor []) [] := by
  obtain ⟨opened, source⟩ := SingleFile.createModel_opened dir policy reports linux created
  have phase := SingleFile.openedAppendPhase opened
  obtain ⟨_, _, _, _, _, lock, _, names, permitted, _, _, _, _⟩ := opened.2.2
  have empty : ready.recovered.batches = [] := by
    exact permitted.elim id id
  rw [empty] at phase
  refine ⟨source.elim id ?_, names, lock, phase⟩
  intro worker
  have fixed := (reopensSettledSegmentScheduled (Persistence.fresh_ready policy) rfl
    (by simp) (by simp) reports.opening.worker reports.opening.writebacks).1
  rw [← SingleFile.recoverScheduled_eq] at fixed
  exact worker.trans fixed

/-- The real successor preparation schedule uses the existing checked removal
interpreter, then creates the selected directory and initializes its child. -/
def prepareNativeChild (root : System.FilePath) (removal : RootReports)
    (mkdir : Nat → NamespaceEffect) (create : SingleFile.CreateReports)
    (policy : Policy) (id : Nat) : M SingleFile.AppendPhase :=
  let path := Native.segmentPath root id
  Native.prepareChildWith (nativeReopenOps root removal (fun _ _ => {})).removeSegment
    (fun observed s =>
      if observed == path then namespaceChange (mkdir s.step) (fun d p => d.prepare id p) s
      else .ok (.error "wrong successor directory") s)
    (fun observed selected s =>
      if observed == path then
        let update (after : SingleFile.OpenImage) : State :=
          {s with disk := s.disk.setSegment id after.image {}}
        match SingleFile.createModel observed selected create with
        | .ok (.ok ready) after => .ok (.ok (SingleFile.storedPhase ready)) (update after)
        | .ok (.error err) after => .ok (.error err) (update after)
        | .error token after => .error token (update after)
      else .ok (.error "wrong child create path") s)
    root policy id

/-- A returned successor came from create at the exact path passed to mkdir.
Partial initialization cannot produce a phase with append authority. -/
theorem prepareNativeChild_authority (root : System.FilePath) (removal : RootReports)
    (mkdir : Nat → NamespaceEffect) (create : SingleFile.CreateReports) (policy : Policy) (id : Nat)
    (linux : System.Platform.isWindows = false) {s t : State} {phase : SingleFile.AppendPhase}
    (ran : (prepareNativeChild root removal mkdir create policy id).run s = .ok (.ok phase) t) :
    t.disk.segment id = Persistence.freshImage ∧ t.disk.cursor id = {} ∧
      phase = .active .lock (SingleFile.appendBindings policy) (Persistence.historyCursor []) [] := by
  simp only [prepareNativeChild, Native.prepareChildWith, Bind.bind, ExceptT.bind,
    ExceptT.run, ExceptT.mk, EStateM.bind] at ran
  cases removed : (nativeReopenOps root removal (fun _ _ => {})).removeSegment id s with
  | error => rw [removed] at ran; cases ran
  | ok response removedAt =>
    rw [removed] at ran
    cases response with
    | error => cases ran
    | ok done =>
      cases done
      simp only [ExceptT.bindCont, BEq.rfl, ↓reduceIte, EStateM.bind] at ran
      cases made : namespaceChange (mkdir removedAt.step) (fun d p => d.prepare id p) removedAt with
      | error => rw [made] at ran; cases ran
      | ok response madeAt =>
        rw [made] at ran
        cases response with
        | error => cases ran
        | ok done =>
          cases done
          cases opened : SingleFile.createModel (Native.segmentPath root id) policy create with
          | error => rw [opened] at ran; cases ran
          | ok response after =>
            rw [opened] at ran
            cases response with
            | error => cases ran
            | ok ready =>
              cases ran
              obtain ⟨image, _, _, binding⟩ := nativeCreatedChild _ _ _ linux opened
              exact ⟨(Disk.setSegment_here ..).trans image, Disk.setCursor_here .., binding⟩

private theorem prepareFrame {session : Session} {d t : Disk}
    (installed : Installed session d) (id : Nat) (away : session.control.active < id)
    (live : t.liveControl = d.liveControl) (durable : t.durableControl = d.durableControl)
    (names : ∀ i, i ≠ id →
      (i ∈ t.liveNames ↔ i ∈ d.liveNames) ∧ (i ∈ t.durableNames ↔ i ∈ d.durableNames))
    (images : ∀ i, i ≠ id → t.segment i = d.segment i)
    (cursor : t.cursor session.control.active = d.cursor session.control.active) :
    Installed session t := by
  obtain ⟨history, shape, layout, oldLive, oldDurable⟩ := installed
  refine ⟨history, shape, layout.frame ?_ ?_ cursor, live.trans oldLive, durable.trans oldDurable⟩
  · intro i selected
    have different : i ≠ id := by have := selected.2; omega
    obtain ⟨l, r⟩ := layout.layout.names i selected
    exact ⟨(names i different).1.mpr l, (names i different).2.mpr r⟩
  · intro i selected
    have different : i ≠ id := by have := selected.2; omega
    exact images i different

/-- Unpublished successor preparation can replace the private successor
artifact at any cut. It leaves the selected layout and old CONTROL ready. -/
theorem prepareNativeChild_frames (root : System.FilePath) (removal : RootReports)
    (mkdir : Nat → NamespaceEffect) (create : SingleFile.CreateReports)
    (id : Nat) (session : Session) (s : State) (initial : Installed session s.disk)
    (away : session.control.active < id) :
    DiskPost (fun _ d => Installed session d ∧ id ∈ d.liveNames)
      (Installed session) ((prepareNativeChild root removal mkdir create session.control.policy id).run s) := by
  let callbacks := nativeReopenOps root removal (fun _ _ => {})
  have removalFacts := (nativeRootEffects root removal (fun _ _ => {})).collection.remove id s
  have removedReady (persist : Bool) : Installed session (s.disk.remove id persist) := by
    refine prepareFrame (t := s.disk.remove id persist) initial id away rfl rfl ?_ ?_ ?_
    · intro i other
      cases persist <;> simp [Disk.remove, other]
    · intro _ _; rfl
    · rfl
  have afterMkdir (d : Disk) (previous : Installed session d) (persist : Bool) :
      Installed session (d.prepare id persist) := by
    refine prepareFrame (t := d.prepare id persist) previous id away rfl rfl ?_ ?_ ?_
    · intro i other
      cases persist <;> simp [Disk.prepare, Disk.setSegment, other]
    · intro i other
      exact Disk.setSegment_other d Persistence.freshImage {} other
    · simp [Disk.prepare, Disk.setSegment, Nat.ne_of_lt away]
  have afterWrite (d : Disk) (previous : Installed session d) (image : DataImage) :
      Installed session (d.setSegment id image {}) := by
    refine prepareFrame (t := d.setSegment id image {}) previous id away rfl rfl ?_ ?_ ?_
    · intro _ _; exact ⟨Iff.rfl, Iff.rfl⟩
    · intro _ other; exact Disk.setSegment_other _ _ _ other
    · simp [Disk.setSegment, Nat.ne_of_lt away]
  unfold prepareNativeChild Native.prepareChildWith
  apply bindPost (P := fun _ d => Installed session d)
  · change DiskPost _ _ ((callbacks.removeSegment id).run s)
    cases ran : (callbacks.removeSegment id).run s with
    | error =>
      change DiskPost _ _ ((callbacks.removeSegment id).run s) at removalFacts
      rw [ran] at removalFacts
      rcases removalFacts with same | ⟨persist, same⟩
      · simp only [DiskPost, same]; exact initial
      · simp only [DiskPost, same]; exact removedReady persist
    | ok response t =>
      change DiskPost _ _ ((callbacks.removeSegment id).run s) at removalFacts
      rw [ran] at removalFacts
      cases response with
      | error =>
        rcases removalFacts with same | ⟨persist, same⟩
        · simp only [DiskPost, same]; exact initial
        · simp only [DiskPost, same]; exact removedReady persist
      | ok _ =>
        obtain ⟨persist, same⟩ := removalFacts
        simp only [DiskPost, same]; exact removedReady persist
  intro _ mid ready
  dsimp only
  apply bindPost (P := fun _ d => Installed session d ∧ id ∈ d.liveNames)
  · change DiskPost _ _ (if Native.segmentPath root id == Native.segmentPath root id then _
      else .ok (.error "wrong successor directory") mid)
    simp only [BEq.rfl, ↓reduceIte]
    apply namespacePost
    · exact ready
    · exact afterMkdir mid.disk ready
    · intro persist
      exact ⟨afterMkdir mid.disk ready persist, List.Mem.head _⟩
  intro _ made ⟨valid, named⟩
  simp only [BEq.rfl, ↓reduceIte, ExceptT.run]
  cases SingleFile.createModel (Native.segmentPath root id) session.control.policy create with
  | error => exact afterWrite made.disk valid _
  | ok response _ =>
    cases response with
    | error => exact afterWrite made.disk valid _
    | ok _ => exact ⟨afterWrite made.disk valid _, named⟩

/-- Publication starts after the successor name has been settled. Reuse
the same cuts for the empty successor and for all reported CONTROL errors. -/
theorem publishPreparedChild (root : System.FilePath) (held : Nat) (reports : Effects)
    (c : Control) (history : List Bytes) (s : State)
    (layout : ReadyLayout c history s.disk)
    (live : s.disk.liveControl = some c) (durable : s.disk.durableControl = some c)
    (full : (segmentHistory c.capacity c.active history).length = c.capacity)
    (room : (historyView c history).tail < Contract.maxPosition)
    (named : c.active + 1 ∈ s.disk.liveNames ∧ c.active + 1 ∈ s.disk.durableNames)
    (empty : Child.Installed c.policy (s.disk.segment (c.active + 1)) (s.disk.cursor (c.active + 1)) []) :
    let next := {c with active := c.active + 1}
    DiskPost (fun _ d => Installed (sessionOf next history) d ∧
      (sessionOf next history).view = historyView c history ∧ ReadyLayout next history d)
      (Recoverable (historyView c history) none)
      ((Segmented.publish (nativeControlOps root held reports) next).run s) := by
  intro next
  have old : Installed (sessionOf c history) s.disk := ⟨history, rfl, layout, live, durable⟩
  have fits := successor_controlRepresentable old room
  have cuts := nativeControl_cuts root held reports next fits.1 fits.2 s
  have keepNames {d : Disk} (cut : PublishCut s.disk next d) (id : Nat)
      (old : id ∈ s.disk.liveNames ∧ id ∈ s.disk.durableNames) :
      id ∈ d.liveNames ∧ id ∈ d.durableNames := by
    obtain ⟨_, _, visible, saved, _⟩ := cut.frames
    exact ⟨visible.symm ▸ old.1, saved.elim (·.symm ▸ old.2) (·.symm ▸ old.1)⟩
  have keepOld {d : Disk} (cut : PublishCut s.disk next d) : ReadyLayout c history d :=
    layout.frame (fun id selected => keepNames cut id (layout.layout.names id selected))
      (fun id _ => congrFun cut.frames.1 id) (congrFun cut.frames.2.1 c.active)
  have keepNew {d : Disk} (cut : PublishCut s.disk next d) : ReadyLayout next history d := by
    have child : Child.Installed c.policy (d.segment (c.active + 1)) (d.cursor (c.active + 1)) [] := by
      rw [cut.frames.1, cut.frames.2.1]
      exact empty
    exact layout.rotate full (fun id selected => keepNames cut id (layout.layout.names id selected))
      (fun id _ => congrFun cut.frames.1 id) (keepNames cut _ named) child
  have stopped {d : Disk} (cut : PublishCut s.disk next d) :
      Recoverable (historyView c history) none d := by
    have oldView := (keepOld cut).choice (request := none) (.inl rfl)
    have nextView := (keepNew cut).choice (known := historyView c history) (request := none) (.inl rfl)
    rcases cut.frames.2.2.2.2 with ⟨l, r⟩ | ⟨l, r⟩
    · exact ⟨⟨c, l.trans live, oldView⟩, ⟨c, r.trans durable, oldView⟩⟩
    · exact ⟨⟨next, l, nextView⟩, r.elim
        (fun saved => ⟨c, saved.trans durable, oldView⟩) (fun saved => ⟨next, saved, nextView⟩)⟩
  cases ran : (Segmented.publish (nativeControlOps root held reports) next).run s with
  | error => rw [ran] at cuts; exact stopped cuts
  | ok response after =>
    rw [ran] at cuts
    cases response with
    | error => exact stopped cuts
    | ok _ =>
      change after.disk = s.disk.published next at cuts
      have frame : PublishCut s.disk next after.disk := cuts ▸ .settled
      have finalLive : after.disk.liveControl = some next := by rw [cuts]; rfl
      have finalDurable : after.disk.durableControl = some next := by rw [cuts]; rfl
      exact ⟨⟨history, rfl, keepNew frame, finalLive, finalDurable⟩, rfl, keepNew frame⟩

private def liftRootAction (action : M α) : ActiveAppendM α := fun s =>
  match action.run s.1 with
  | .ok response after => .ok response (after, s.2)
  | .error token after => .error token (after, s.2)

private def closeActive (id : Nat) (policy : Policy) (reports : SingleFile.OpenReports) :
    ActiveAppendM Unit := fun s =>
  match SingleFile.closeModel policy reports s.2 {image := s.1.disk.segment id, held := true} with
  | .ok response _ => .ok response ({s.1 with activeEntry := none}, .closed)
  | .error token _ => .error token ({s.1 with activeEntry := none}, .closed)

private def acquireSuccessor (root : System.FilePath) (removal : RootReports)
    (reports : Effects) (create : SingleFile.CreateReports) (policy : Policy)
    (id : Nat) : ActiveAppendM Nat := fun s =>
  match (prepareNativeChild root removal (fun step => reports.prepare step id) create policy id).run s.1 with
  | .ok (.ok phase) after => .ok (.ok id) (after, phase)
  | .ok (.error err) after => .ok (.error err) (after, s.2)
  | .error token after => .error token (after, .closed)

private def storeActiveEntry (entry : Nat × Nat) : ActiveAppendM Unit := fun s =>
  .ok (.ok ()) ({s.1 with activeEntry := some entry.1}, s.2)

private def registerSuccessor (expected : Nat) (entry : Nat × Nat) : ActiveAppendM Unit :=
  if entry = (expected, expected) then storeActiveEntry entry else throw "wrong successor registration"

private def readActiveEntry : ActiveAppendM (Option (Nat × Nat)) := fun s =>
  .ok (.ok (s.1.activeEntry.map fun id => (id, id))) s

/-- One interpreted append schedule for the current or successor child.
The successor is returned by preparation and later transferred to the
store by the shared executable scope. -/
def nativeAppendModel (root : System.FilePath) (held : Nat) (removal : RootReports)
    (effects : Effects) (create : SingleFile.CreateReports) (close : SingleFile.OpenReports)
    (session : Session) (id : Nat)
    (reports : ∀ cursor, SingleFile.AppendReports session.control.policy cursor batch) :
    ActiveAppendM Session :=
  Native.appendOwnedWith (error := String) session batch (checkAppend session batch) _root_.id
    readActiveEntry (closeActive id session.control.policy close)
    (acquireSuccessor root removal effects create)
    (fun id => closeActive id session.control.policy close)
    (liftRootAction (nativeControlOps root held effects).syncRoot)
    (fun control => liftRootAction (Segmented.publish (nativeControlOps root held effects) control))
    (fun next payload => writeRequested session.control.policy next reports payload)
    (registerSuccessor (successor session).active)

theorem nativeAppendModel_active (root : System.FilePath) (held : Nat) (removal : RootReports)
    (effects : Effects) (create : SingleFile.CreateReports) (close : SingleFile.OpenReports)
    (session : Session) (reports : ∀ cursor, SingleFile.AppendReports session.control.policy cursor batch)
    (room : session.activeCount ≠ session.control.capacity)
    (state : State × SingleFile.AppendPhase)
    (registered : state.1.activeEntry = some session.control.active) :
    (nativeAppendModel root held removal effects create close session session.control.active reports).run state =
      (appendActiveModel session session.control.active reports).run state := by
  simp only [nativeAppendModel, appendActiveModel, Native.appendOwnedWith, room, ↓reduceIte]
  -- At this branch the guard is read-only. Its continuation reads exactly
  -- the entry written by bootstrap, recovery or the previous rotation.
  by_cases size : batch.length > 32
  · simp only [checkAppend, size, ↓reduceIte]; rfl
  · by_cases exhausted : session.view.tail ≥ Contract.maxPosition
    · simp only [checkAppend, size, exhausted, ↓reduceIte]; rfl
    · simp [checkAppend, size, exhausted, readActiveEntry, registered, Bind.bind, ExceptT.bind,
        ExceptT.run, ExceptT.mk, EStateM.bind, ExceptT.bindCont, Pure.pure, ExceptT.pure, EStateM.pure]

private def resumeSuccessor (root : System.FilePath) (held : Nat) (effects : Effects)
    (session : Session)
    (reports : ∀ cursor, SingleFile.AppendReports session.control.policy cursor batch)
    (id : Nat) : ActiveAppendM Session := do
  liftRootAction (nativeControlOps root held effects).syncRoot
  liftRootAction (Segmented.publish (nativeControlOps root held effects) (successor session))
  writeActive session.control.policy id reports
  registerSuccessor (successor session).active ((successor session).active, id)
  pure ⟨successor session, 1, session.view.append batch⟩

private theorem nativeAppendModel_rotation_run (root : System.FilePath) (held : Nat)
    (removal : RootReports) (effects : Effects) (create : SingleFile.CreateReports)
    (close : SingleFile.OpenReports) (session : Session)
    (reports : ∀ cursor, SingleFile.AppendReports session.control.policy cursor batch)
    (s : State × SingleFile.AppendPhase)
    (full : session.activeCount = session.control.capacity)
    (size : batch.length ≤ 32) (room : session.view.tail < Contract.maxPosition) :
    (nativeAppendModel root held removal effects create close session session.control.active reports).run s =
      ((closeActive session.control.active session.control.policy close) >>= fun _ =>
        Native.withActiveChild (error := String)
          (acquireSuccessor root removal effects create session.control.policy (successor session).active)
          (fun id => closeActive id session.control.policy close)
          (resumeSuccessor root held effects session reports)).run s := by
  simp [nativeAppendModel, Native.appendOwnedWith, writeRequested, successor, checkAppend,
    full, Nat.not_lt.mpr size, Nat.not_le.mpr room, Bind.bind, ExceptT.bind,
    ExceptT.mk, ExceptT.pure, Pure.pure]
  rfl

/-- Close never changes the namespace or bytes, including when the
unlock callback reports an error after releasing its description. -/
private theorem closeActive_frames (id : Nat) (policy : Policy) (reports : SingleFile.OpenReports)
    (s : State × SingleFile.AppendPhase) :
    ∃ response, (closeActive id policy reports).run s = .ok response ({s.1 with activeEntry := none}, .closed) := by
  obtain ⟨response, after, ran, _⟩ := SingleFile.closeModel_frames policy reports s.2
    {image := s.1.disk.segment id, held := true}
  simp only [closeActive, ExceptT.run]
  rw [ran]
  exact ⟨response, rfl⟩

/-- The root barrier jointly settles both CONTROL and the new child name.
Before and after a fault, every previously selected binding survives. -/
theorem settlePreparedChild (root : System.FilePath) (held : Nat) (reports : Effects)
    (session : Session) (s : State) (entry : Installed session s.disk)
    (named : session.control.active + 1 ∈ s.disk.liveNames) :
    DiskPost (fun _ d => Installed session d ∧
      session.control.active + 1 ∈ d.liveNames ∧ session.control.active + 1 ∈ d.durableNames ∧
      d.segment = s.disk.segment ∧ d.cursor = s.disk.cursor)
      (Installed session)
      ((nativeControlOps root held reports).syncRoot.run s) := by
  obtain ⟨history, shape, layout, live, durable⟩ := entry
  have settled : Installed session s.disk.syncRoot := by
    refine ⟨history, shape, layout.frame ?_ (fun _ _ => rfl) rfl, live, live⟩
    intro id selected
    have old := (layout.layout.names id selected).1
    exact ⟨old, old⟩
  change DiskPost _ _ (barrier (reports.root s.step) Disk.syncRoot s)
  apply barrierPost
  · exact ⟨history, shape, layout, live, durable⟩
  · exact settled
  · exact ⟨settled, named, named, rfl, rfl⟩

/-- A healthy prepared child carries the same phase on which the single-file
writer proof starts. CONTROL publication cannot change the child image. -/
theorem readyAfterPublishingSuccessor (root : System.FilePath) (held : Nat) (effects : Effects)
    (removal : RootReports) (create : SingleFile.CreateReports) (session : Session)
    (start prepared settled after : State) (phase : SingleFile.AppendPhase)
    (initial : Installed session start.disk)
    (full : session.activeCount = session.control.capacity)
    (room : session.view.tail < Contract.maxPosition)
    (linux : System.Platform.isWindows = false)
    (created : (prepareNativeChild root removal (fun step => effects.prepare step (successor session).active)
      create session.control.policy (successor session).active).run start = .ok (.ok phase) prepared)
    (synced : ((nativeControlOps root held effects).syncRoot).run prepared = .ok (.ok ()) settled)
    (published : (Segmented.publish (nativeControlOps root held effects) (successor session)).run settled =
      .ok (.ok ()) after) :
    (∃ next : Session, next.control = successor session ∧ next.activeCount = 0 ∧
      next.view = session.view ∧ Installed next after.disk) ∧
      phase = .active .lock (SingleFile.appendBindings session.control.policy)
        (Persistence.historyCursor []) [] := by
  have preparedPost := prepareNativeChild_frames root removal (fun step => effects.prepare step (successor session).active) create (successor session).active session start initial
    (Nat.lt_succ_self _)
  rw [created] at preparedPost
  have ⟨image, cursor, authority⟩ := prepareNativeChild_authority root removal (fun step => effects.prepare step (successor session).active) create _ _ linux created
  have barrier := settlePreparedChild root held effects session prepared preparedPost.1 preparedPost.2
  rw [synced] at barrier
  obtain ⟨⟨history, shape, layout, live, durable⟩, named, saved, files, cursors⟩ := barrier
  have fullChild := congrArg Session.activeCount shape
  change session.activeCount =
      (segmentHistory session.control.capacity session.control.active history).length at fullChild
  rw [full] at fullChild
  have visible := congrArg Session.view shape
  change session.view = historyView session.control history at visible
  have empty : Child.Installed session.control.policy
      (settled.disk.segment (session.control.active + 1)) (settled.disk.cursor (session.control.active + 1)) [] := by
    rw [files, cursors]
    change prepared.disk.segment (session.control.active + 1) = _ at image
    change prepared.disk.cursor (session.control.active + 1) = _ at cursor
    rw [image, cursor]
    exact Child.Installed.fresh _
  have successorReady := publishPreparedChild root held effects session.control history settled
    layout live durable fullChild.symm (visible ▸ room) ⟨named, saved⟩ empty
  dsimp only at successorReady
  change DiskPost _ _ ((Segmented.publish (nativeControlOps root held effects) (successor session)).run settled)
    at successorReady
  rw [published] at successorReady
  have count : (sessionOf (successor session) history).activeCount = 0 := by
    change (segmentHistory session.control.capacity (session.control.active + 1) history).length = 0
    rw [segmentHistory_next_empty layout.layout.upper]
    rfl
  exact ⟨⟨sessionOf (successor session) history, rfl, count, successorReady.2.1.trans visible.symm,
    successorReady.1⟩, authority⟩

private theorem noAppend_pending {disk : Disk} {known : Contract.View} {batch : Bytes}
    (ready : Recoverable known none disk) : Recoverable known (some (.append batch)) disk := by
  obtain ⟨⟨c, l, h, p, readable, permits⟩, ⟨d, r, h', p', saved, permits'⟩⟩ := ready
  refine ⟨⟨c, l, h, p, readable, ?_⟩, ⟨d, r, h', p', saved, ?_⟩⟩
  · intro history permission
    exact .inl ((permits history permission).elim id (fun impossible => by cases impossible))
  · intro history permission
    exact .inl ((permits' history permission).elim id (fun impossible => by cases impossible))

private def appendAfterPublish (session : Session) (phase : SingleFile.AppendPhase)
    (reports : ∀ cursor, SingleFile.AppendReports session.control.policy cursor batch) : M Session :=
  fun s =>
    match (writeActive session.control.policy (successor session).active reports).run (s, phase) with
    | .ok (.ok ()) after => .ok (.ok ⟨successor session, 1, session.view.append batch⟩) {after.1 with activeEntry := some (successor session).active}
    | .ok (.error err) after => .ok (.error err) after.1
    | .error token after => .error token after.1

private theorem resumeSuccessor_disk (root : System.FilePath) (held : Nat) (effects : Effects)
    (session : Session) (reports : ∀ cursor, SingleFile.AppendReports session.control.policy cursor batch)
    (prepared : State × SingleFile.AppendPhase) :
    erasePhase ((resumeSuccessor root held effects session reports (successor session).active).run prepared) =
      ((nativeControlOps root held effects).syncRoot >>= fun _ =>
        Segmented.publish (nativeControlOps root held effects) (successor session) >>= fun _ =>
          appendAfterPublish session prepared.2 reports).run prepared.1 := by
  simp only [resumeSuccessor, liftRootAction, Bind.bind, ExceptT.bind, ExceptT.run,
    ExceptT.mk, EStateM.bind, ExceptT.bindCont, Pure.pure, ExceptT.pure]
  cases (nativeControlOps root held effects).syncRoot prepared.1 with
  | error => rfl
  | ok response settled =>
    cases response with
    | error => rfl
    | ok _ =>
      simp only [liftRootAction, ExceptT.run, EStateM.bind, ExceptT.bindCont]
      cases Segmented.publish (nativeControlOps root held effects) (successor session) settled with
      | error => rfl
      | ok response published =>
        cases response with
        | error => rfl
        | ok _ =>
          simp only [appendAfterPublish, registerSuccessor, ExceptT.run, EStateM.bind, ExceptT.bindCont, ↓reduceIte]
          cases writeActive session.control.policy (successor session).active reports (published, prepared.2) with
          | error => rfl
          | ok response _ => cases response <;> rfl

private abbrev AppendDiskPost (session : Session) (batch : Bytes) (run : Result Session) :=
  DiskPost (fun next disk => Installed next disk ∧
    Contract.Step (.online session.view) (.ack (.append batch)) (.online next.view) ∧
    next.tailPosition = session.view.tail + 1)
    (Recoverable session.view (some (.append batch))) run

private theorem resumeSuccessor_refines (root : System.FilePath) (held : Nat) (effects : Effects)
    (session : Session) (reports : ∀ cursor, SingleFile.AppendReports session.control.policy cursor batch)
    (prepared : State × SingleFile.AppendPhase)
    (valid : Installed session prepared.1.disk) (named : (successor session).active ∈ prepared.1.disk.liveNames)
    (empty : prepared.1.disk.segment (successor session).active = Persistence.freshImage)
    (cursor : prepared.1.disk.cursor (successor session).active = {})
    (authority : prepared.2 = .active .lock (SingleFile.appendBindings session.control.policy)
      (Persistence.historyCursor []) [])
    (full : session.activeCount = session.control.capacity)
    (size : batch.length ≤ 32) (position : session.view.tail < Contract.maxPosition) :
    AppendDiskPost session batch
      (erasePhase ((resumeSuccessor root held effects session reports (successor session).active).run prepared)) := by
  rw [resumeSuccessor_disk]
  have rootPost := settlePreparedChild root held effects session prepared.1 valid named
  apply bindPost (P := fun _ d => Installed session d ∧
    session.control.active + 1 ∈ d.liveNames ∧ session.control.active + 1 ∈ d.durableNames ∧
    d.segment = prepared.1.disk.segment ∧ d.cursor = prepared.1.disk.cursor)
  · cases ran : (nativeControlOps root held effects).syncRoot.run prepared.1 with
    | error => rw [ran] at rootPost; exact rootPost.offline (.inl rfl)
    | ok response after =>
      rw [ran] at rootPost
      cases response with
      | error => exact rootPost.offline (.inl rfl)
      | ok _ => exact rootPost
  intro _ settled post
  obtain ⟨⟨history, shape, layout, live, durable⟩, named, saved, files, cursors⟩ := post
  have view := congrArg Session.view shape
  change session.view = historyView session.control history at view
  have count := congrArg Session.activeCount shape
  change session.activeCount = (segmentHistory session.control.capacity session.control.active history).length at count
  rw [full] at count
  have fresh : Child.Installed session.control.policy
      (settled.disk.segment (session.control.active + 1)) (settled.disk.cursor (session.control.active + 1)) [] := by
    rw [files, cursors]
    change prepared.1.disk.segment (session.control.active + 1) = _ at empty
    change prepared.1.disk.cursor (session.control.active + 1) = _ at cursor
    rw [empty, cursor]
    exact Child.Installed.fresh _
  let next := successor session
  have publish := publishPreparedChild root held effects session.control history settled
    layout live durable count.symm (view ▸ position) ⟨named, saved⟩ fresh
  dsimp only at publish
  change DiskPost (fun _ d => Installed (sessionOf next history) d ∧
    (sessionOf next history).view = historyView session.control history ∧ ReadyLayout next history d)
    (Recoverable (historyView session.control history) none)
    ((Segmented.publish (nativeControlOps root held effects) next).run settled) at publish
  apply bindPost (P := fun _ d => Installed (sessionOf next history) d ∧
    (sessionOf next history).view = historyView session.control history ∧ ReadyLayout next history d)
  · change DiskPost _ _ ((Segmented.publish (nativeControlOps root held effects) next).run settled)
    cases ran : (Segmented.publish (nativeControlOps root held effects) next).run settled with
    | error => rw [ran] at publish; exact noAppend_pending (view.symm ▸ publish)
    | ok response after =>
      rw [ran] at publish
      cases response with
      | error => exact noAppend_pending (view.symm ▸ publish)
      | ok _ => exact publish
  intro _ published ⟨installed, newView, entry⟩
  obtain ⟨_, _, _, afterLive, afterDurable⟩ := installed
  have nextEmpty : segmentHistory next.capacity next.active history = [] := by
    change segmentHistory session.control.capacity (session.control.active + 1) history = []
    rw [segmentHistory_next_empty layout.layout.upper]
  have countZero : (sessionOf next history).activeCount = 0 := by
    change (segmentHistory next.capacity next.active history).length = 0
    rw [nextEmpty]
    rfl
  have appendRoom : history.length < (next.active + 1) * next.capacity := by
    have upper := layout.layout.upper
    have positive := layout.layout.capacityPositive
    change history.length < (session.control.active + 1 + 1) * session.control.capacity
    rw [Nat.add_mul, Nat.one_mul]
    omega
  have nextPos : (historyView next history).tail < Contract.maxPosition := view ▸ position
  have post := appendActiveModel_refines next history batch published entry afterLive afterDurable
    appendRoom size nextPos reports
  dsimp only at post
  let phase : SingleFile.AppendPhase :=
    .active .lock (SingleFile.appendBindings next.policy) (Persistence.historyCursor []) []
  have phaseEq : (.active .lock (SingleFile.appendBindings next.policy)
      (Persistence.historyCursor (segmentHistory next.capacity next.active history))
      (segmentHistory next.capacity next.active history) : SingleFile.AppendPhase) = phase := by
    rw [nextEmpty]
  rw [phaseEq] at post
  have spare : (sessionOf next history).activeCount ≠ (sessionOf next history).control.capacity := by
    rw [countZero]
    exact Nat.ne_of_lt entry.layout.capacityPositive
  have exactRun := appendActiveModel_run (sessionOf next history) reports (published, phase) spare size nextPos
  change DiskPost _ _ (erasePhase ((appendActiveModel (sessionOf next history) (sessionOf next history).control.active reports).run
    (published, phase))) at post
  rw [exactRun] at post
  have visible : (sessionOf next history).view = session.view := newView.trans view.symm
  rw [countZero, visible] at post
  change AppendDiskPost session batch ((appendAfterPublish session prepared.2 reports).run published)
  rw [authority]
  unfold appendAfterPublish
  change AppendDiskPost _ _ (match (writeActive session.control.policy (successor session).active reports).run
      (published, phase) with
    | .ok (.ok ()) after => .ok (.ok ⟨successor session, 1, session.view.append batch⟩) {after.1 with activeEntry := some (successor session).active}
    | .ok (.error err) after => .ok (.error err) after.1
    | .error token after => .error token after.1)
  change AppendDiskPost session batch (erasePhase (match
      (writeActive session.control.policy (successor session).active reports).run (published, phase) with
    | .ok (.ok ()) after => .ok (.ok (⟨successor session, 1, session.view.append batch⟩ : Session)) after
    | .ok (.error err) after => .ok (.error err) after
    | .error token after => .error token after)) at post
  simp only [ExceptT.run] at post ⊢
  cases wrote : writeActive session.control.policy (successor session).active reports (published, phase) with
  | error => rw [wrote] at post; exact post
  | ok response _ => rw [wrote] at post; cases response <;> exact post

private theorem appendActiveModel_reusable (session : Session) (state : State × SingleFile.AppendPhase)
    (ready : AppendReady session state) (noRotation : session.activeCount ≠ session.control.capacity)
    (size : batch.length ≤ 32) (position : session.view.tail < Contract.maxPosition)
    (reports : ∀ cursor, SingleFile.AppendReports session.control.policy cursor batch)
    (returned : (appendActiveModel session session.control.active reports).run state = .ok (.ok next) after) :
    AppendReady next after := by
  obtain ⟨history, shape, entry, live, durable, phase⟩ := ready
  have count := congrArg Session.activeCount shape
  change session.activeCount = (segmentHistory session.control.capacity session.control.active history).length at count
  rw [segmentHistory_active_length entry.layout.upper] at count
  have room : history.length < (session.control.active + 1) * session.control.capacity := by
    have lower := entry.layout.lower
    have upper := entry.layout.upper
    rw [Nat.add_mul, Nat.one_mul] at upper ⊢
    omega
  have visible := congrArg Session.view shape
  change session.view = historyView session.control history at visible
  have source : state.2 = .active .lock (SingleFile.appendBindings session.control.policy)
      (Persistence.historyCursor (segmentHistory session.control.capacity session.control.active history))
      (segmentHistory session.control.capacity session.control.active history) := by
    rw [phase, entry.active.position]
  cases session with
  | mk control count view =>
    simp only [sessionOf, Session.mk.injEq, true_and] at shape
    obtain ⟨rfl, rfl⟩ := shape
    exact appendActiveModel_ready control history batch state.1 entry live durable room size position
      reports state.2 source returned

private theorem freshAppendReady (session : Session) (s : State)
    (entry : Installed session s.disk) (empty : session.activeCount = 0) :
    AppendReady session (s, .active .lock (SingleFile.appendBindings session.control.policy)
      (Persistence.historyCursor []) []) := by
  obtain ⟨history, shape, layout, live, durable⟩ := entry
  have length := congrArg Session.activeCount shape
  change session.activeCount = (segmentHistory session.control.capacity session.control.active history).length at length
  rw [empty] at length
  have noBatches : segmentHistory session.control.capacity session.control.active history = [] :=
    List.length_eq_zero_iff.mp length.symm
  exact ⟨history, shape, layout, live, durable, by rw [layout.active.position, noBatches]⟩

private theorem resumeSuccessor_ready (root : System.FilePath) (held : Nat)
    (removal : RootReports) (effects : Effects) (create : SingleFile.CreateReports)
    (session : Session) (start : State)
    (initial : Installed session start.disk) (full : session.activeCount = session.control.capacity)
    (size : batch.length ≤ 32) (position : session.view.tail < Contract.maxPosition)
    (linux : System.Platform.isWindows = false)
    (reports : ∀ cursor, SingleFile.AppendReports session.control.policy cursor batch)
    {prepared : State × SingleFile.AppendPhase}
    (created : (prepareNativeChild root removal (fun step => effects.prepare step (successor session).active)
        create session.control.policy (successor session).active).run start =
      .ok (.ok prepared.2) prepared.1)
    (returned : (resumeSuccessor root held effects session reports (successor session).active).run prepared =
      .ok (.ok next) after) :
    AppendReady next after ∧ after.1.activeEntry = some next.control.active := by
  simp only [resumeSuccessor, liftRootAction, Bind.bind, ExceptT.bind, ExceptT.run,
    ExceptT.mk, EStateM.bind, ExceptT.bindCont, Pure.pure, ExceptT.pure] at returned
  cases synced : (nativeControlOps root held effects).syncRoot prepared.1 with
  | error => rw [synced] at returned; cases returned
  | ok report settled =>
    rw [synced] at returned
    cases report with
    | error => cases returned
    | ok done =>
      cases done
      simp only [liftRootAction, ExceptT.run, EStateM.bind, ExceptT.bindCont] at returned
      cases published : Segmented.publish (nativeControlOps root held effects) (successor session) settled with
      | error => rw [published] at returned; cases returned
      | ok report named =>
        rw [published] at returned
        cases report with
        | error => cases returned
        | ok done =>
          cases done
          obtain ⟨⟨successorSession, control, zero, view, installed⟩, phase⟩ :=
            readyAfterPublishingSuccessor root held effects removal create session start prepared.1 settled named
              prepared.2 initial full position linux created synced published
          have authority := freshAppendReady successorSession named installed zero
          have positive : 0 < successorSession.control.capacity := by
            obtain ⟨_, _, layout, _, _⟩ := installed
            exact layout.layout.capacityPositive
          cases successorSession with
          | mk controlValue countValue viewValue =>
            change controlValue = successor session at control
            change countValue = 0 at zero
            change viewValue = session.view at view
            subst controlValue countValue viewValue
            let fresh : Session := ⟨successor session, 0, session.view⟩
            have spare : fresh.activeCount ≠ fresh.control.capacity := Nat.ne_of_lt positive
            have ready : AppendReady fresh (named, prepared.2) := by
              rw [phase]
              exact authority
            simp only [ExceptT.bindCont, EStateM.bind, registerSuccessor, ↓reduceIte, Pure.pure] at returned
            cases ran : writeActive session.control.policy (successor session).active reports (named, prepared.2) with
            | error => rw [ran] at returned; cases returned
            | ok response actual =>
              rw [ran] at returned
              cases response with
              | error => cases returned
              | ok ack =>
                cases ack
                simp only [ExceptT.bindCont, EStateM.bind, storeActiveEntry, EStateM.pure] at returned
                cases returned
                let next : Session := ⟨successor session, 1, session.view.append batch⟩
                have wrote : (appendActiveModel fresh fresh.control.active reports).run (named, prepared.2) =
                    .ok (.ok next) actual := by
                  rw [appendActiveModel_run fresh reports _ spare size position]
                  change (match writeActive session.control.policy (successor session).active reports (named, prepared.2) with
                    | .ok (.ok ()) after => EStateM.Result.ok (Except.ok next) after
                    | .ok (.error err) after => EStateM.Result.ok (Except.error err) after
                    | .error token after => EStateM.Result.error token after) = _
                  rw [ran]
                obtain ⟨history, shape, layout, live, durable, current⟩ :=
                  appendActiveModel_reusable fresh (named, prepared.2) ready spare size position reports wrote
                exact ⟨⟨history, shape, layout, live, durable, current⟩, rfl⟩

private def returnedAuthority :
    EStateM.Result Unit (State × SingleFile.AppendPhase) (Except String Session) → Prop
  | .ok (.ok next) after => AppendReady next after ∧ after.1.activeEntry = some next.control.active
  | _ => True

/-- The rotating native schedule preserves the old recoverable view until
the successor write takes over. A failed cleanup keeps the same reached disk. -/
theorem nativeAppendModel_rotation_refines (root : System.FilePath) (held : Nat)
    (removal : RootReports) (effects : Effects) (create : SingleFile.CreateReports)
    (close : SingleFile.OpenReports) (session : Session)
    (reports : ∀ cursor, SingleFile.AppendReports session.control.policy cursor batch)
    (s : State × SingleFile.AppendPhase) (installed : Installed session s.1.disk)
    (full : session.activeCount = session.control.capacity)
    (size : batch.length ≤ 32) (room : session.view.tail < Contract.maxPosition)
    (linux : System.Platform.isWindows = false) :
    let result := (nativeAppendModel root held removal effects create close session session.control.active reports).run s
    AppendDiskPost session batch (erasePhase result) ∧ returnedAuthority result := by
  dsimp only
  rw [nativeAppendModel_rotation_run root held removal effects create close session reports s full size room]
  let oldClose := closeActive session.control.active session.control.policy close
  let acquire := acquireSuccessor root removal effects create session.control.policy (successor session).active
  let release := fun id => closeActive id session.control.policy close
  let resume := resumeSuccessor root held effects session reports
  obtain ⟨response, closed⟩ := closeActive_frames session.control.active session.control.policy close s
  let whole := (oldClose >>= fun _ => Native.withActiveChild (error := String) acquire release resume).run s
  change AppendDiskPost _ _ (erasePhase whole) ∧ returnedAuthority whole
  unfold whole
  have prior : Recoverable session.view (some (.append batch)) s.1.disk :=
    installed.offline (.inl rfl)
  simp only [Bind.bind, ExceptT.bind, ExceptT.run, ExceptT.mk, EStateM.bind]
  change oldClose s = _ at closed
  rw [closed]
  let cleared := {s.1 with activeEntry := none}
  cases response with
  | error => exact ⟨prior, trivial⟩
  | ok closedValue =>
    cases closedValue
    let rotated := (Native.withActiveChild (error := String) (ExceptT.mk acquire.run) release resume).run (cleared, .closed)
    change AppendDiskPost _ _ (erasePhase rotated) ∧ returnedAuthority rotated
    unfold rotated
    rw [Native.withActiveChild_reached]
    let prepare := prepareNativeChild root removal (fun step => effects.prepare step (successor session).active)
      create session.control.policy (successor session).active
    have prep := prepareNativeChild_frames root removal (fun step => effects.prepare step (successor session).active)
      create (successor session).active session cleared installed (Nat.lt_succ_self _)
    change DiskPost _ _ (prepare.run cleared) at prep
    simp only [acquire, acquireSuccessor, ExceptT.run] at prep ⊢
    change DiskPost _ _ (prepare cleared) at prep
    cases ready : prepare cleared with
    | error =>
      simp only [prepare] at ready prep
      rw [ready] at prep
      try rw [ready]
      exact ⟨prep.offline (.inl rfl), trivial⟩
    | ok reply atPrepare =>
      simp only [prepare] at ready prep
      rw [ready] at prep
      try rw [ready]
      cases reply with
      | error => exact ⟨prep.offline (.inl rfl), trivial⟩
      | ok phase =>
        have ⟨image, cursor, authority⟩ := prepareNativeChild_authority root removal
          (fun step => effects.prepare step (successor session).active)
          create session.control.policy (successor session).active linux ready
        have continued := resumeSuccessor_refines root held effects session reports (atPrepare, phase)
          prep.1 prep.2 image cursor authority full size room
        change AppendDiskPost _ _ (erasePhase ((resume (successor session).active).run (atPrepare, phase))) at continued
        dsimp only
        simp only [ExceptT.run] at continued
        cases ran : resume (successor session).active (atPrepare, phase) with
        | error => rw [ran] at continued; exact ⟨continued, trivial⟩
        | ok reply atWrite =>
          rw [ran] at continued
          cases reply with
          | ok next =>
            have readyAfter := resumeSuccessor_ready root held removal effects create session cleared installed
              full size room linux reports (prepared := (atPrepare, phase)) ready ran
            exact ⟨continued, readyAfter⟩
          | error err =>
            obtain ⟨reported, released⟩ := closeActive_frames (successor session).active session.control.policy close atWrite
            change release (successor session).active atWrite = _ at released
            try dsimp only
            rw [released]
            cases reported with
            | error => exact ⟨continued, trivial⟩
            | ok unitValue => cases unitValue; exact ⟨continued, trivial⟩

/-- Disk postcondition for both branches of the shared executable schedule. -/
theorem nativeAppendModel_refines (root : System.FilePath) (held : Nat)
    (removal : RootReports) (effects : Effects) (create : SingleFile.CreateReports)
    (close : SingleFile.OpenReports) (session : Session)
    (reports : ∀ cursor, SingleFile.AppendReports session.control.policy cursor batch)
    (state : State × SingleFile.AppendPhase) (ready : AppendReady session state)
    (registered : state.1.activeEntry = some session.control.active)
    (size : batch.length ≤ 32) (position : session.view.tail < Contract.maxPosition)
    (linux : System.Platform.isWindows = false) :
    AppendDiskPost session batch (erasePhase
      ((nativeAppendModel root held removal effects create close session session.control.active reports).run state)) := by
  obtain ⟨history, shape, entry, live, durable, phase⟩ := ready
  by_cases full : session.activeCount = session.control.capacity
  · exact nativeAppendModel_rotation_refines root held removal effects create close session reports state
      ⟨history, shape, entry, live, durable⟩ full size position linux |>.1
  rw [nativeAppendModel_active root held removal effects create close session reports full state registered]
  have count := congrArg Session.activeCount shape
  change session.activeCount = (segmentHistory session.control.capacity session.control.active history).length at count
  rw [segmentHistory_active_length entry.layout.upper] at count
  have room : history.length < (session.control.active + 1) * session.control.capacity := by
    have lower := entry.layout.lower
    have upper := entry.layout.upper
    rw [Nat.add_mul, Nat.one_mul] at upper ⊢
    omega
  have visible := congrArg Session.view shape
  change session.view = historyView session.control history at visible
  have post := appendActiveModel_refines session.control history batch state.1 entry live durable
    room size (visible ▸ position) reports
  have same : state =
      (state.1, .active .lock (SingleFile.appendBindings session.control.policy)
        (Persistence.historyCursor (segmentHistory session.control.capacity session.control.active history))
        (segmentHistory session.control.capacity session.control.active history)) := by
    refine Prod.ext ?_ ?_
    · rfl
    · rw [phase, entry.active.position]
  rw [same]
  dsimp only at post
  cases session with
  | mk control count view =>
    simp only [sessionOf, Session.mk.injEq, true_and] at shape
    obtain ⟨rfl, rfl⟩ := shape
    exact post

theorem nativeAppendModel_ready (root : System.FilePath) (held : Nat)
    (removal : RootReports) (effects : Effects) (create : SingleFile.CreateReports)
    (close : SingleFile.OpenReports) (session : Session)
    (reports : ∀ cursor, SingleFile.AppendReports session.control.policy cursor batch)
    (state : State × SingleFile.AppendPhase) (ready : AppendReady session state)
    (registered : state.1.activeEntry = some session.control.active)
    (size : batch.length ≤ 32) (position : session.view.tail < Contract.maxPosition)
    (linux : System.Platform.isWindows = false)
    (returned : (nativeAppendModel root held removal effects create close session session.control.active reports).run state =
      .ok (.ok next) after) :
    AppendReady next after ∧ after.1.activeEntry = some next.control.active := by
  by_cases full : session.activeCount = session.control.capacity
  · have installed : Installed session state.1.disk := by
      obtain ⟨history, shape, entry, live, durable, _⟩ := ready
      exact ⟨history, shape, entry, live, durable⟩
    have post := nativeAppendModel_rotation_refines root held removal effects create close session reports state
      installed full size position linux
    dsimp only at post
    rw [returned] at post
    exact post.2
  rw [nativeAppendModel_active root held removal effects create close session reports full state registered] at returned
  refine ⟨appendActiveModel_reusable session state ready full size position reports returned, ?_⟩
  have run := appendActiveModel_run session reports state full size position
  rw [run] at returned
  cases ran : (writeActive session.control.policy session.control.active reports).run state with
  | error => rw [ran] at returned; cases returned
  | ok reply reached =>
    rw [ran] at returned
    cases reply with
    | error => cases returned
    | ok everything =>
      cases everything
      cases returned
      simp only [writeActive, ExceptT.run] at ran
      split at ran <;> cases ran
      exact registered

theorem appendChoice_tailBound {known view : Contract.View} {request : Option Contract.Request}
    (appending : request = none ∨ ∃ batch, request = some (.append batch))
    (bounded : known.tail ≤ Contract.maxPosition) (choice : PermittedView known request view) :
    view.tail ≤ Contract.maxPosition := by
  rcases choice with rfl | changed
  · exact bounded
  rcases appending with rfl | ⟨batch, rfl⟩
  · cases changed
  simp only [Option.bind_some, Contract.Request.apply] at changed
  split at changed
  · have same := Option.some.inj changed
    rw [← same]
    simp only [Contract.View.tail, Contract.View.append, List.length_append, List.length_cons, List.length_nil] at *
    omega
  · cases changed

/-- The same public contract covers both append paths. Success supplies
the ready phase and reusable authority at the actual reached disk. Error
and process stop expose the recoverable image with the one pending batch. -/
theorem publicNativeAppend_refines (root : System.FilePath) (held : Nat)
    (removal : RootReports) (effects : Effects) (create : SingleFile.CreateReports)
    (close : SingleFile.OpenReports) (session : Session)
    (reports : ∀ policy cursor, SingleFile.AppendReports policy cursor batch)
    (state : State × SingleFile.AppendPhase) (ready : AppendReady session state)
    (registered : state.1.activeEntry = some session.control.active)
    (size : batch.length ≤ 32) (position : session.view.tail < Contract.maxPosition)
    (linux : System.Platform.isWindows = false) :
    let action := fun (_ : Nat) (current : Session) =>
      nativeAppendModel root held removal effects create close current current.control.active (reports current.control.policy)
    match (publicAppendActiveModel action).run (state, .ready held session) with
    | .ok (.ok next) (after, phase) =>
      phase = .ready held next ∧ AppendReady next after ∧
      after.1.activeEntry = some next.control.active ∧ Contract.Step (.online session.view) (.ack (.append batch)) (.online next.view) ∧
      next.tailPosition = session.view.tail + 1 ∧ next.view.tail ≤ Contract.maxPosition
    | .ok (.error _) (after, phase) | .error _ (after, phase) =>
      phase = .poisoned held ∧
      Recoverable session.view (some (.append batch)) after.1.disk := by
  dsimp only
  rw [publicAppendActiveModel_run]
  let action := nativeAppendModel root held removal effects create close session session.control.active
    (reports session.control.policy)
  have post := nativeAppendModel_refines root held removal effects create close session
    (reports session.control.policy) state ready registered size position linux
  change AppendDiskPost _ _ (erasePhase (action.run state)) at post
  cases ran : action.run state with
  | error => rw [ran] at post; exact ⟨rfl, post⟩
  | ok response after =>
    rw [ran] at post
    cases response with
    | error => exact ⟨rfl, post⟩
    | ok next =>
      obtain ⟨_, ack, absolute⟩ := post
      have bounded : next.view.tail ≤ Contract.maxPosition := by
        cases ack with
        | ack applied =>
          exact appendChoice_tailBound (.inr ⟨batch, rfl⟩)
            (Nat.le_of_lt position) (.inr applied)
      obtain ⟨nextReady, nextEntry⟩ := nativeAppendModel_ready root held removal effects create close session
        (reports session.control.policy) state ready registered size position linux ran
      exact ⟨rfl, nextReady, nextEntry, ack, absolute, bounded⟩

/-- Reject an invalid request before releasing, preparing, or writing a
child. The old disk and child remain unchanged even if the public root
phase is conservatively poisoned. -/
theorem nativeAppendModel_rejected (root : System.FilePath) (held : Nat)
    (removal : RootReports) (effects : Effects) (create : SingleFile.CreateReports)
    (close : SingleFile.OpenReports) (session : Session) (id : Nat)
    (reports : ∀ cursor, SingleFile.AppendReports session.control.policy cursor batch)
    (state : State × SingleFile.AppendPhase)
    (invalid : batch.length > 32 ∨ session.view.tail ≥ Contract.maxPosition) :
    (nativeAppendModel root held removal effects create close session id reports).run state =
      .ok (.error (if batch.length > 32 then "batch out of bounds" else
        "segmented WAL position exhausted")) state := by
  by_cases size : batch.length > 32
  · simp only [nativeAppendModel, Native.appendOwnedWith, checkAppend, size, ↓reduceIte]
    rfl
  · have exhausted := invalid.resolve_left size
    simp only [nativeAppendModel, Native.appendOwnedWith, checkAppend, size, exhausted, ↓reduceIte]
    rfl

/-- Recovery needs representability of the surviving authority. The
admissible bounded history supplies it without a caller's CONTROL premise. -/
theorem appendRecovery_representable {disk : Disk} {known : Contract.View} {request : Option Contract.Request}
    (prior : Recoverable known request disk) (appending : request = none ∨ ∃ batch, request = some (.append batch))
    (bounded : known.tail ≤ Contract.maxPosition) :
    ∀ c, disk.liveControl = some c →
      c.capacity ≤ 255 ∧ c.active ≤ ControlCodec.wordMax ∧ c.discarded ≤ ControlCodec.wordMax := by
  obtain ⟨⟨live, found, history, pending, readable, allowed⟩, _⟩ := prior
  intro c selected
  have same : live = c := Option.some.inj (found.symm.trans selected)
  subst c
  have tail := appendChoice_tailBound appending bounded (allowed history (.inl rfl))
  rw [historyView_tail readable.layout.discardedFits] at tail
  have active := Nat.le_trans
    (Nat.le_mul_of_pos_right live.active readable.layout.capacityPositive) readable.layout.lower
  exact ⟨readable.layout.capacityFits, Nat.le_trans active tail,
    Nat.le_trans readable.layout.discardedFits tail⟩

/-- The public open's exact stored phase can start the shared append proof. -/
theorem reopensWithAppendAuthority (owned : RootBinding directory lock) (root : RootReports)
    (reports : Nat → Nat → SingleFile.OpenReports) (childError rootError : Option String)
    {start after : State} (prior : Recoverable known request start.disk)
    {store : ReopenedStore directory lock} {session : Session}
    (opened : (publicOpenModel (.ok owned) root reports childError rootError).run (start, false) =
      .ok (.ok (.ready store session, ())) (after, true)) :
    store.activeId = session.control.active ∧
      AppendReady session ({after with activeEntry := some store.activeId}, SingleFile.storedPhase store.activeChild) := by
  rw [publicOpenModel_run] at opened
  dsimp only at opened
  have success : (installScopedModel owned root reports childError).run start =
      .ok (.ok (.ready store session)) after := by
    cases ran : (installScopedModel owned root reports childError).run start with
    | error => rw [ran] at opened; cases opened
    | ok response reached =>
      rw [ran] at opened
      cases response with
      | error => cases opened
      | ok phase => cases opened; rfl
  obtain ⟨history, shape, layout, live, durable, _, index, phase, _⟩ :=
    installScopedModel_appendPhase owned root reports childError prior success
  rw [index] at phase
  exact ⟨index, ⟨history, shape, layout, live, durable, phase⟩⟩

private theorem writeActive_healthy (policy : Policy) (id : Nat) (s : State × SingleFile.AppendPhase)
    (history : List Bytes) (bounded : ∀ b ∈ history, b.length ≤ 32) (room : history.length < 255)
    (size : batch.length ≤ 32) (phase : s.2 = .active .lock (SingleFile.appendBindings policy)
      (Persistence.historyCursor history) history) :
    ∃ after, (writeActive policy id (batch := batch) (fun _ => SingleFile.healthyAppendReports (batch := batch))).run s =
      .ok (.ok ()) after := by
  obtain ⟨after, wrote⟩ := SingleFile.appendModel_healthy policy (s.1.disk.segment id) history bounded room size
  simp only [writeActive, ExceptT.run, phase, wrote]
  exact ⟨_, rfl⟩

theorem prepareNativeChild_healthy (root : System.FilePath) (removal : RootReports)
    (healthy : HealthyRoot removal) (policy : Policy) (id : Nat) (s : State)
    (linux : System.Platform.isWindows = false) :
    ∃ phase after, (prepareNativeChild root removal (fun _ => .after false none) {} policy id).run s =
      .ok (.ok phase) after := by
  obtain ⟨removed, cleared⟩ := nativeRemove_healthy root removal (fun _ _ => {}) healthy id s
  obtain ⟨opened, created, installed⟩ := SingleFile.createModel_healthy (Native.segmentPath root id) policy linux
  simp only [prepareNativeChild, Native.prepareChildWith, Bind.bind, ExceptT.bind,
    ExceptT.run, ExceptT.mk, EStateM.bind] at cleared ⊢
  rw [cleared]
  simp only [ExceptT.bindCont, BEq.rfl, ↓reduceIte, EStateM.bind, namespaceChange, outcome, installed]
  exact ⟨_, _, rfl⟩

/-- Healthy primitive effects produce an acknowledgement whether or not a
successor has to be prepared and published. -/
theorem nativeAppendModel_healthy (root : System.FilePath) (held : Nat) (removal : RootReports)
    (removes : HealthyRoot removal) (session : Session) (state : State × SingleFile.AppendPhase)
    (ready : AppendReady session state) (registered : state.1.activeEntry = some session.control.active)
    (size : batch.length ≤ 32)
    (position : session.view.tail < Contract.maxPosition) (linux : System.Platform.isWindows = false) :
    ∃ next after,
      (nativeAppendModel root held removal healthy {} {} session session.control.active
        (batch := batch) (fun _ => SingleFile.healthyAppendReports (batch := batch))).run state = .ok (.ok next) after := by
  obtain ⟨history, shape, entry, live, durable, phase⟩ := ready
  let childHistory := segmentHistory session.control.capacity session.control.active history
  have canonical : state.2 = .active .lock (SingleFile.appendBindings session.control.policy)
      (Persistence.historyCursor childHistory) childHistory := by
    rw [phase, entry.active.position]
  by_cases full : session.activeCount = session.control.capacity
  · rw [nativeAppendModel_rotation_run root held removal healthy {} {} session _ state full size position]
    let cleared := {state.1 with activeEntry := none}
    have closed : (closeActive session.control.active session.control.policy {}).run state =
      .ok (.ok ()) (cleared, .closed) := by
      simp only [closeActive, ExceptT.run, canonical]
      rfl
    let id := (successor session).active
    obtain ⟨phase, prepared, created⟩ := prepareNativeChild_healthy root removal removes
      session.control.policy id cleared linux
    have acquired : (acquireSuccessor root removal healthy {} session.control.policy id).run
        (cleared, .closed) = .ok (.ok id) (prepared, phase) := by
      simp only [acquireSuccessor, healthy, ExceptT.run] at created ⊢
      rw [created]
    have own := (prepareNativeChild_authority root removal (fun _ => .after false none) {} session.control.policy id linux created).2.2
    let settled : State := {prepared.tick with disk := prepared.disk.syncRoot}
    have synced : ((nativeControlOps root held healthy).syncRoot).run prepared = .ok (.ok ()) settled := rfl
    have fits := successor_controlRepresentable
      (show Installed session state.1.disk from ⟨history, shape, entry, live, durable⟩) position
    have published := nativeControl_healthy root held (successor session) settled fits.1 fits.2
    let afterPublication : State := {settled with disk := settled.disk.published (successor session), step := settled.step + 4}
    change (Segmented.publish (nativeControlOps root held healthy) (successor session)).run settled =
      .ok (.ok ()) afterPublication at published
    obtain ⟨wrote, wroteOK⟩ := writeActive_healthy session.control.policy id (afterPublication, phase) []
      (by simp) (by decide) size own
    let stored := ({wrote.1 with activeEntry := some id}, wrote.2)
    have resumeOK : (resumeSuccessor root held healthy session (fun _ => SingleFile.healthyAppendReports (batch := batch)) id).run
        (prepared, phase) = .ok (.ok ⟨successor session, 1, session.view.append batch⟩) stored := by
      simp only [resumeSuccessor, liftRootAction, ExceptT.run, Bind.bind, ExceptT.bind,
        ExceptT.mk, EStateM.bind, ExceptT.bindCont] at synced published wroteOK ⊢
      rw [synced]
      simp only [liftRootAction, ExceptT.run, EStateM.bind, ExceptT.bindCont]
      rw [published]
      simp only [EStateM.bind, ExceptT.bindCont]
      rw [wroteOK]
      simp only [registerSuccessor, ↓reduceIte, id]
      rfl
    refine ⟨⟨successor session, 1, session.view.append batch⟩, stored, ?_⟩
    simp only [Bind.bind, ExceptT.bind, ExceptT.run, ExceptT.mk, EStateM.bind] at closed ⊢
    rw [closed]
    change (Native.withActiveChild (error := String)
      (ExceptT.mk (acquireSuccessor root removal healthy {} session.control.policy id).run)
      (fun child => closeActive child session.control.policy {})
      (resumeSuccessor root held healthy session (fun _ => SingleFile.healthyAppendReports (batch := batch)))).run
      (cleared, .closed) = _
    rw [Native.withActiveChild_reached]
    simp only [ExceptT.run] at acquired resumeOK ⊢
    rw [acquired]
    dsimp only
    rw [resumeOK]
  · rw [nativeAppendModel_active root held removal healthy {} {} session _ full state registered]
    have count := congrArg Session.activeCount shape
    change session.activeCount = childHistory.length at count
    have limit : childHistory.length ≤ session.control.capacity := by
      dsimp only [childHistory]
      rw [segmentHistory_active_length entry.layout.upper]
      have upper := entry.layout.upper
      rw [Nat.add_mul, Nat.one_mul] at upper
      omega
    have room : childHistory.length < 255 := by
      have := entry.layout.capacityFits
      omega
    obtain ⟨after, wrote⟩ := writeActive_healthy session.control.policy session.control.active state
      childHistory (segmentHistory_bounded entry.layout _) room size canonical
    rw [appendActiveModel_run _ _ _ full size position, wrote]
    exact ⟨_, _, rfl⟩

private theorem prepareNativeChild_initial (root : System.FilePath) (removal : RootReports)
    (mkdir : Nat → NamespaceEffect) (create : SingleFile.CreateReports) (policy : Policy) (id : Nat)
    (linux : System.Platform.isWindows = false) {s t : State} {phase : SingleFile.AppendPhase}
    (initial : s.disk = {}) (ran : (prepareNativeChild root removal mkdir create policy id).run s =
        .ok (.ok phase) t) :
    ∃ persist, t.disk = ({} : Disk).prepare id persist := by
  have removedPost := (nativeRootEffects root removal (fun _ _ => {})).collection.remove id s
  simp only [prepareNativeChild, Native.prepareChildWith, Bind.bind, ExceptT.bind,
    ExceptT.run, ExceptT.mk, EStateM.bind] at ran
  cases removed : (nativeReopenOps root removal (fun _ _ => {})).removeSegment id s with
  | error => rw [removed] at ran; cases ran
  | ok response removedAt =>
    rw [removed] at ran
    cases response with
    | error => cases ran
    | ok done =>
      cases done
      simp only [ExceptT.run] at removedPost
      rw [removed] at removedPost
      obtain ⟨persistOld, gone⟩ := removedPost
      have vacant : removedAt.disk = {} := by
        rw [gone, initial]
        cases persistOld <;> rfl
      simp only [ExceptT.bindCont, BEq.rfl, ↓reduceIte, EStateM.bind] at ran
      have mkdirPost : DiskPost (fun _ d => ∃ persist, d = removedAt.disk.prepare id persist)
          (fun _ => True) (namespaceChange (mkdir removedAt.step) (fun d p => d.prepare id p) removedAt) := by
        apply namespacePost
        · trivial
        · intro; trivial
        · intro persist; exact ⟨persist, rfl⟩
      cases made : namespaceChange (mkdir removedAt.step) (fun d p => d.prepare id p) removedAt with
      | error => rw [made] at ran; cases ran
      | ok response madeAt =>
        rw [made] at ran mkdirPost
        cases response with
        | error => cases ran
        | ok done =>
          cases done
          obtain ⟨persist, readyDir⟩ := mkdirPost
          cases opened : SingleFile.createModel (Native.segmentPath root id) policy create with
          | error => rw [opened] at ran; cases ran
          | ok response after =>
            rw [opened] at ran
            cases response with
            | error => cases ran
            | ok ready =>
              cases ran
              have child := (nativeCreatedChild _ _ _ linux opened).1
              refine ⟨persist, ?_⟩
              dsimp only
              rw [readyDir, vacant, child]
              simp [Disk.prepare, Disk.setSegment]

def nativeBootstrapModel (root : System.FilePath) (held : Nat) (removal : RootReports)
    (effects : Effects) (create : SingleFile.CreateReports) (policy : Policy)
    (capacity : Nat) : ActiveAppendM Session :=
  let ops := nativeControlOps root held effects
  Segmented.create {
    prepareSegment := fun policy id => Native.registerPreparedWith
      (acquireSuccessor root removal effects create policy id) (registerSuccessor id) id
    syncRoot := liftRootAction ops.syncRoot
    publishControl := fun c => liftRootAction (Segmented.publish ops c)
    readControl := liftRootAction ops.readControl
    openSegment := fun policy id => liftRootAction (ops.openSegment policy id)
    appendSegment := fun policy id batch => liftRootAction (ops.appendSegment policy id batch)
    listSegments := liftRootAction ops.listSegments
    removeSegment := fun id => liftRootAction (ops.removeSegment id)
  } policy capacity

theorem nativeBootstrap_ready (root : System.FilePath) (held : Nat) (removal : RootReports)
    (effects : Effects) (create : SingleFile.CreateReports) (policy : Policy)
    (capacity : Nat) (linux : System.Platform.isWindows = false)
    (returned : (nativeBootstrapModel root held removal effects create policy capacity).run
      ({}, .closed) = .ok (.ok session) after) :
    AppendReady session after ∧ after.1.activeEntry = some session.control.active ∧ session.view.tail = 0 := by
  by_cases zero : capacity = 0
  · simp only [nativeBootstrapModel, Segmented.create, zero, decide_true, Bool.true_or, ↓reduceIte] at returned
    cases returned
  by_cases large : capacity > 255
  · simp only [nativeBootstrapModel, Segmented.create, large, decide_true, Bool.or_true, ↓reduceIte] at returned
    cases returned
  let c := initialControl policy capacity
  let make := prepareNativeChild root removal (fun step => effects.prepare step 0) create policy 0
  let start : State := {}
  have good : 0 < capacity := Nat.pos_of_ne_zero zero
  have bound : capacity ≤ 255 := Nat.le_of_not_gt large
  simp only [nativeBootstrapModel, Segmented.create, Native.registerPreparedWith, zero, large, decide_false, Bool.false_or,
    Bool.false_eq_true, ↓reduceIte, Bind.bind, ExceptT.bind, ExceptT.run, ExceptT.mk, EStateM.bind] at returned
  simp only [acquireSuccessor, ExceptT.run] at returned
  cases made : make start with
  | error => simp only [make, start] at made; rw [made] at returned; cases returned
  | ok response prepared =>
    have exactMade := made
    simp only [make, start] at made
    rw [made] at returned
    cases response with
    | error => cases returned
    | ok phase =>
      have ⟨persist, preparedDisk⟩ := prepareNativeChild_initial root removal (fun step => effects.prepare step 0)
        create policy 0 linux rfl exactMade
      have authority := (prepareNativeChild_authority root removal (fun step => effects.prepare step 0)
        create policy 0 linux exactMade).2.2
      let registered := {prepared with activeEntry := some 0}
      simp only [ExceptT.bindCont, EStateM.bind, registerSuccessor, storeActiveEntry, ↓reduceIte,
        liftRootAction, ExceptT.run] at returned
      have synced := barrierPost (effects.root registered.step) Disk.syncRoot registered
        (P := fun _ d => d = registered.disk.syncRoot) (F := fun _ => True) trivial trivial rfl
      cases barrierRan : (nativeControlOps root held effects).syncRoot registered with
      | error => rw [barrierRan] at returned; cases returned
      | ok response settled =>
        rw [barrierRan] at returned
        cases response with
        | error => cases returned
        | ok done =>
          cases done
          change DiskPost _ _ ((nativeControlOps root held effects).syncRoot registered) at synced
          rw [barrierRan] at synced
          change settled.disk = prepared.disk.syncRoot at synced
          simp only [Segmented.publish, ExceptT.bindCont, EStateM.bind, liftRootAction, ExceptT.run] at returned
          have publication := nativeControl_cuts root held effects c (Nat.zero_le _) (Nat.zero_le _) settled
          simp only [ExceptT.run, c, initialControl] at publication
          cases published : Segmented.publish (nativeControlOps root held effects) ⟨policy, capacity, 0, 0⟩ settled with
          | error => simp only [Segmented.publish] at published; rw [published] at returned; cases returned
          | ok response disk =>
            simp only [Segmented.publish] at published publication
            rw [published] at returned publication
            cases response with
            | error => cases returned
            | ok unitValue =>
              cases unitValue
              cases returned
              change disk.disk = settled.disk.published c at publication
              have same : disk.disk = ((({} : Disk).prepare 0 false).syncRoot).published c := by
                rw [publication, synced, preparedDisk]
                cases persist <;> rfl
              have baseline := create_returns_ready healthy policy good bound
              have healthyRun : (Segmented.create (ops healthy) policy capacity).run {} =
                  .ok (.ok ⟨c, 0, ⟨0, []⟩⟩)
                    ⟨((( {} : Disk).prepare 0 false).syncRoot).published c, 6, none⟩ := by
                simp only [Segmented.create, zero, large, decide_false, Bool.false_or, Bool.false_eq_true,
                  ↓reduceIte]
                rfl
              dsimp only at baseline
              rw [healthyRun] at baseline
              obtain ⟨shape, live, durable, layout⟩ := baseline
              rw [← same] at live durable layout
              refine ⟨⟨[], shape, layout, live, durable, ?_⟩, ?_, rfl⟩
              · have cursor : disk.disk.cursor 0 = Persistence.historyCursor [] := by
                  simpa only [initialControl, segmentHistory, List.drop_nil, List.take_nil] using layout.active.position
                simp only [authority, cursor, segmentHistory, List.drop_nil, List.take_nil]
              · have barrierEntry : settled.activeEntry = some 0 := by
                  change barrier (effects.root registered.step) Disk.syncRoot registered = _ at barrierRan
                  cases cut : effects.root registered.step with
                  | before fault => rw [cut] at barrierRan; cases fault <;> cases barrierRan
                  | after fault =>
                    rw [cut] at barrierRan
                    cases fault with
                    | none => cases barrierRan; rfl
                    | some stop => cases stop <;> cases barrierRan
                exact (nativeControl_slot root held effects c (Nat.zero_le _) (Nat.zero_le _) settled
                  (by simpa only [Segmented.publish, initialControl, c, ExceptT.run] using published)).trans barrierEntry

/-- Bootstrap's publication producer supplies the absolute-position bound
on every returned session. Child preparation is still the namespace
action of `ops` at this boundary. -/
theorem nativeControl_bootstrap_ready (root : System.FilePath) (held : Nat) (r : Effects)
    (policy : Policy) {capacity : Nat} (positive : 0 < capacity) (fits : capacity ≤ 255) :
    DiskPost (fun session disk => Installed session disk ∧ session.view.tail = 0)
      (fun _ => True) ((Segmented.create (nativeControlOps root held r) policy capacity).run {}) := by
  rw [nativeControl_bootstrap]
  have post := create_returns_ready r policy positive fits
  dsimp only at post
  cases ran : (Segmented.create (ops r) policy capacity).run {} with
  | error => trivial
  | ok response after =>
    rw [ran] at post
    cases response with
    | error => trivial
    | ok session =>
      obtain ⟨shape, live, durable, layout⟩ := post
      subst session
      exact ⟨⟨[], rfl, layout, live, durable⟩, rfl⟩

end WalRecoverySlice.Segmented.Model
