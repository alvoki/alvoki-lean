import Alvoki.Experiments.WAL.Segmented.Proofs.Model
import Alvoki.Experiments.WAL.Segmented.Proofs.Layout
import Alvoki.Experiments.WAL.Proofs.DirtyAppend

/-! The file obligations of each selectable control record. -/

namespace WalRecoverySlice.Segmented

open Model (Disk State)
open Persistence (Ready Dirty historyCursor)

def Control.selects (control : Control) (id : Nat) : Prop :=
  control.firstNeeded ≤ id ∧ id ≤ control.active

theorem Control.selectsActive (control : Control) : control.selects control.active :=
  ⟨Nat.min_le_left .., Nat.le_refl _⟩

def historyView (control : Control) (history : List Bytes) : Contract.View :=
  ⟨control.discarded, history.drop control.discarded⟩

def sessionOf (control : Control) (history : List Bytes) : Session :=
  ⟨control, (segmentHistory control.capacity control.active history).length, historyView control history⟩

theorem historyView_tail {control : Control} {history : List Bytes}
    (covered : control.discarded ≤ history.length) : (historyView control history).tail = history.length := by
  simp [historyView, Contract.View.tail, List.length_drop]
  omega

/-- The selected closed segments contain their entire batch interval. The
active file is refined separately so the same layout survives an uncertain
append. Every ID authorized by this record must exist in both namespaces. -/
structure Layout (control : Control) (history : List Bytes) (disk : Disk) : Prop where
  capacityPositive : 0 < control.capacity
  capacityFits : control.capacity ≤ 255
  lower : control.active * control.capacity ≤ history.length
  upper : history.length ≤ (control.active + 1) * control.capacity
  discardedFits : control.discarded ≤ history.length
  bounded : ∀ p ∈ history, p.length ≤ 32
  names : ∀ id, control.selects id → id ∈ disk.liveNames ∧ id ∈ disk.durableNames
  sealed : ∀ id, control.selects id → id < control.active →
    Ready control.policy (disk.segment id) (segmentHistory control.capacity id history) ∧
      (disk.segment id).powerLoss = disk.segment id

structure ReadyLayout (control : Control) (history : List Bytes) (disk : Disk) : Prop where
  layout : Layout control history disk
  active : Ready control.policy (disk.segment control.active) (segmentHistory control.capacity control.active history)
  clean : (disk.segment control.active).powerLoss = disk.segment control.active
  cursor : disk.cursor control.active = historyCursor (segmentHistory control.capacity control.active history)

/-- A returned table has the exact canonical client view and an active
cursor ready for another append. Its control and needed names are durable. -/
def Installed (session : Session) (disk : Disk) : Prop :=
  ∃ history, session = sessionOf session.control history ∧
    ReadyLayout session.control history disk ∧
    disk.liveControl = some session.control ∧ disk.durableControl = some session.control

structure Readable (control : Control) (history : List Bytes) (pending : Option Bytes) (disk : Disk) : Prop where
  layout : Layout control history disk
  room : pending.isSome → history.length < (control.active + 1) * control.capacity
  active : Dirty control.policy (segmentHistory control.capacity control.active history) pending (disk.segment control.active)
  logMarkers : control.policy = .logOnly → (disk.segment control.active).MarkersSettled

def PermittedView (known : Contract.View) (request : Option Contract.Request) (observed : Contract.View) : Prop :=
  observed = known ∨ request.bind (fun req => req.apply known) = some observed

/-- Each possible authority supplies its own physical observations. A
directory barrier before repair deliberately selects the visible one. -/
def RecoveryChoice (known : Contract.View) (request : Option Contract.Request) (control : Control)
    (disk : Disk) : Prop :=
  ∃ history pending, Readable control history pending disk ∧
    ∀ retained, WalRecoverySlice.Contract.Permitted history pending retained →
      PermittedView known request (historyView control retained)

structure Recoverable (known : Contract.View) (request : Option Contract.Request) (disk : Disk) : Prop where
  live : ∃ control, disk.liveControl = some control ∧ RecoveryChoice known request control disk
  durable : ∃ control, disk.durableControl = some control ∧ RecoveryChoice known request control disk

theorem segmentHistory_bounded {control history disk} (layout : Layout control history disk) (id : Nat) :
    ∀ p ∈ segmentHistory control.capacity id history, p.length ≤ 32 := by
  intro p member
  exact layout.bounded p (List.mem_of_mem_drop (List.mem_of_mem_take member))

theorem segmentHistory_fits (capacity id : Nat) (history : List Bytes) :
    (segmentHistory capacity id history).length ≤ capacity := by
  simp only [segmentHistory, List.length_take]
  exact Nat.min_le_left ..

theorem Layout.frame {control history before after} (layout : Layout control history before)
    (names : ∀ id, control.selects id → id ∈ after.liveNames ∧ id ∈ after.durableNames)
    (files : ∀ id, control.selects id → id < control.active → after.segment id = before.segment id) :
    Layout control history after := by
  refine ⟨layout.capacityPositive, layout.capacityFits, layout.lower, layout.upper,
    layout.discardedFits, layout.bounded, names, ?_⟩
  intro id selected sealed
  rw [files id selected sealed]
  exact layout.sealed id selected sealed

theorem ReadyLayout.frame {control history before after} (ready : ReadyLayout control history before)
    (names : ∀ id, control.selects id → id ∈ after.liveNames ∧ id ∈ after.durableNames)
    (files : ∀ id, control.selects id → after.segment id = before.segment id)
    (cursor : after.cursor control.active = before.cursor control.active) :
    ReadyLayout control history after := by
  have active := files control.active control.selectsActive
  exact ⟨ready.layout.frame names (fun id chosen _ => files id chosen),
    active.symm ▸ ready.active, active.symm ▸ ready.clean, cursor.trans ready.cursor⟩

theorem Readable.frame {control history pending before after} (readable : Readable control history pending before)
    (names : ∀ id, control.selects id → id ∈ after.liveNames ∧ id ∈ after.durableNames)
    (files : ∀ id, control.selects id → after.segment id = before.segment id) :
    Readable control history pending after := by
  have active := files control.active control.selectsActive
  exact ⟨readable.layout.frame names (fun id chosen _ => files id chosen), readable.room,
    active.symm ▸ readable.active, fun branch => active.symm ▸ readable.logMarkers branch⟩

theorem ReadyLayout.readable {control history disk} (ready : ReadyLayout control history disk) :
    Readable control history none disk := by
  refine ⟨ready.layout, by simp, ?_, ?_⟩
  · exact Persistence.ready_dirty control.policy _ _ ready.active ready.clean
      (segmentHistory_bounded ready.layout control.active)
      (Nat.le_trans (segmentHistory_fits _ _ _) ready.layout.capacityFits)
  · intro _
    rw [← ready.clean]
    exact ⟨rfl, rfl⟩

theorem Readable.powerLoss {control history pending disk} (readable : Readable control history pending disk) :
    Readable control history pending disk.powerLoss := by
  refine ⟨readable.layout.frame (fun id chosen => ⟨(readable.layout.names id chosen).2,
    (readable.layout.names id chosen).2⟩) (fun id chosen sealed => (readable.layout.sealed id chosen sealed).2),
    readable.room, readable.active.powerLoss, fun _ => ⟨rfl, rfl⟩⟩

theorem Recoverable.powerLoss {known request disk} (recoverable : Recoverable known request disk) :
    Recoverable known request disk.powerLoss := by
  obtain ⟨control, found, history, pending, layout, permits⟩ := recoverable.durable
  exact ⟨⟨control, found, history, pending, layout.powerLoss, permits⟩,
    ⟨control, found, history, pending, layout.powerLoss, permits⟩⟩

theorem RecoveryChoice.frame {known request control before after} (choice : RecoveryChoice known request control before)
    (names : ∀ id, control.selects id → id ∈ after.liveNames ∧ id ∈ after.durableNames)
    (files : ∀ id, control.selects id → after.segment id = before.segment id) :
    RecoveryChoice known request control after := by
  obtain ⟨history, pending, layout, permits⟩ := choice
  exact ⟨history, pending, layout.frame names files, permits⟩

theorem ReadyLayout.choice {control history disk} (ready : ReadyLayout control history disk)
    {known request} (permitted : PermittedView known request (historyView control history)) :
    RecoveryChoice known request control disk := by
  refine ⟨history, none, ready.readable, ?_⟩
  intro selected allowed
  have same : selected = history := by simpa [WalRecoverySlice.Contract.Permitted] using allowed
  exact same.symm ▸ permitted

theorem Installed.offline {session disk known request} (installed : Installed session disk)
    (allowed : PermittedView known request session.view) : Recoverable known request disk := by
  obtain ⟨history, shaped, ready, live, durable⟩ := installed
  have view : session.view = historyView session.control history := congrArg Session.view shaped
  rw [view] at allowed
  exact ⟨⟨session.control, live, ready.choice allowed⟩, ⟨session.control, durable, ready.choice allowed⟩⟩

/-- Raising the release frontier hides a prefix but cannot introduce a
newly named segment. The contents of all remaining segments stay the same. -/
theorem ReadyLayout.release {control history disk} (ready : ReadyLayout control history disk)
    {next : Nat} (advance : control.discarded ≤ next) (valid : next ≤ history.length) :
    ReadyLayout {control with discarded := next} history disk := by
  let updated := {control with discarded := next}
  have first : control.firstNeeded ≤ updated.firstNeeded := by
    unfold Control.firstNeeded
    exact Nat.le_min.mpr ⟨Nat.min_le_left .., Nat.le_trans (Nat.min_le_right ..) (Nat.div_le_div_right advance)⟩
  have restrict {id : Nat} (selected : updated.selects id) : control.selects id :=
    ⟨Nat.le_trans first selected.1, selected.2⟩
  refine ⟨⟨ready.layout.capacityPositive, ready.layout.capacityFits, ready.layout.lower, ready.layout.upper,
    valid, ready.layout.bounded, fun id selected => ready.layout.names id (restrict selected), ?_⟩,
    ready.active, ready.clean, ready.cursor⟩
  intro id selected sealed
  exact ready.layout.sealed id (restrict selected) sealed

theorem historyView_release {control : Control} {history : List Bytes}
    {next : Nat} (advance : control.discarded ≤ next) :
    historyView {control with discarded := next} history =
      (historyView control history).discardThrough next := by
  simp only [historyView, Contract.View.discardThrough, Nat.max_eq_left advance, List.drop_drop]
  congr 2
  omega

theorem Layout.extend {control history disk} (layout : Layout control history disk)
    (p : Bytes) (bounded : p.length ≤ 32) (room : history.length < (control.active + 1) * control.capacity) :
    Layout control (history ++ [p]) disk := by
  refine ⟨layout.capacityPositive, layout.capacityFits, ?_, ?_, ?_, ?_, layout.names, ?_⟩
  · simp [List.length_append]; have := layout.lower; omega
  · simp [List.length_append]; omega
  · simp [List.length_append]; have := layout.discardedFits; omega
  · intro q member
    rcases List.mem_append.mp member with member | member
    · exact layout.bounded q member
    · simpa only [List.mem_singleton.mp member] using bounded
  · intro id chosen sealed
    have through : (id + 1) * control.capacity ≤ history.length :=
      Nat.le_trans (Nat.mul_le_mul_right _ (by omega)) layout.lower
    rw [segmentHistory_before_append p through]
    exact layout.sealed id chosen sealed

theorem historyView_append {control : Control} {history : List Bytes}
    (fits : control.discarded ≤ history.length) (p : Bytes) :
    historyView control (history ++ [p]) = (historyView control history).append p := by
  simp [historyView, Contract.View.append, List.drop_append_of_le_length fits]

theorem ReadyLayout.rotate {control history before after} (ready : ReadyLayout control history before)
    (full : (segmentHistory control.capacity control.active history).length = control.capacity)
    (names : ∀ id, control.selects id → id ∈ after.liveNames ∧ id ∈ after.durableNames)
    (files : ∀ id, control.selects id → after.segment id = before.segment id)
    (nextNamed : control.active + 1 ∈ after.liveNames ∧ control.active + 1 ∈ after.durableNames)
    (empty : after.segment (control.active + 1) = Persistence.freshImage)
    (cursor : after.cursor (control.active + 1) = {}) :
    ReadyLayout {control with active := control.active + 1} history after := by
  let next := {control with active := control.active + 1}
  have atTail : (control.active + 1) * control.capacity = history.length := by
    rw [segmentHistory_active_length ready.layout.upper] at full
    rw [Nat.add_mul, Nat.one_mul]
    have := ready.layout.lower
    omega
  have first : control.firstNeeded ≤ next.firstNeeded := by
    unfold Control.firstNeeded
    exact Nat.le_min.mpr ⟨Nat.le_trans (Nat.min_le_left ..) (by simp [next]), Nat.min_le_right ..⟩
  have prior {id : Nat} (chosen : next.selects id) (sealed : id < next.active) : control.selects id :=
    ⟨Nat.le_trans first chosen.1, by dsimp [next] at sealed; omega⟩
  refine ⟨⟨ready.layout.capacityPositive, ready.layout.capacityFits, Nat.le_of_eq atTail, ?_,
      ready.layout.discardedFits, ready.layout.bounded, ?_, ?_⟩, ?_, ?_, ?_⟩
  · rw [← atTail]
    exact Nat.mul_le_mul_right _ (by dsimp [next]; omega)
  · intro id chosen
    by_cases atNew : id = next.active
    · exact atNew.symm ▸ nextNamed
    · have below : id < next.active := Nat.lt_of_le_of_ne chosen.2 atNew
      exact names id (prior chosen below)
  · intro id chosen sealed
    have old := prior chosen sealed
    rw [files id old]
    by_cases active : id = control.active
    · subst id
      exact ⟨ready.active, ready.clean⟩
    · exact ready.layout.sealed id old (Nat.lt_of_le_of_ne old.2 active)
  · change Ready control.policy (after.segment (control.active + 1)) (segmentHistory control.capacity (control.active + 1) history)
    rw [empty, segmentHistory_next_empty ready.layout.upper]
    exact Persistence.fresh_ready _
  · rw [show next.active = control.active + 1 from rfl, empty]
    rfl
  · change after.cursor (control.active + 1) = historyCursor (segmentHistory control.capacity (control.active + 1) history)
    rw [cursor, segmentHistory_next_empty ready.layout.upper]
    rfl

end WalRecoverySlice.Segmented
