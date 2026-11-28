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

/-- Run the same public mutation schedule on the installed active reference.
The no-rotation precondition leaves preparation and publication unreachable. -/
def appendActiveModel (session : Session) (id : Nat)
    (reports : ∀ cursor, SingleFile.AppendReports session.control.policy cursor batch) :
    ActiveAppendM Session :=
  Native.appendOwnedWith (error := String) session batch (checkAppend session batch) _root_.id
    (pure (some (id, ()))) (throw "unexpected close before rotation")
    (fun _ _ => throw "unexpected rotation") (fun _ => pure ())
    (throw "unexpected root barrier") (fun _ => throw "unexpected CONTROL publication")
    (fun _ _ => writeActive session.control.policy id reports) (fun _ => pure ())

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
  simp [Nat.not_lt.mpr size, Nat.not_le.mpr position, room, Bind.bind, ExceptT.bind,
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
      (Recoverable session.view (some (.append batch))) (erasePhase result) := by
  obtain ⟨history, shape, entry, live, durable, _, idEq, phaseEq⟩ :=
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
  dsimp only at post ⊢
  rw [phaseEq, idEq, entry.active.position]
  cases session with
  | mk control count view =>
    simp only [sessionOf, Session.mk.injEq, true_and] at shape
    obtain ⟨rfl, rfl⟩ := shape
    exact post

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
      next.tailPosition = session.view.tail + 1
    | .ok (.error _) (after, phase) | .error _ (after, phase) =>
      phase = .poisoned store.activeId ∧
      Recoverable session.view (some (.append batch)) after.1.disk := by
  dsimp only
  rw [publicAppendActiveModel_run]
  have result := appendAfterNativeReopen owned rootReports openReports closeError prior opened
    room size position (reports session.control.policy)
  dsimp only at result
  cases ran : (appendActiveModel session store.activeId (reports session.control.policy)).run
      (s, SingleFile.storedPhase store.activeChild) with
  | error => rw [ran] at result; exact ⟨rfl, result⟩
  | ok response after =>
    rw [ran] at result
    cases response <;> exact ⟨rfl, result⟩

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

end WalRecoverySlice.Segmented.Model
