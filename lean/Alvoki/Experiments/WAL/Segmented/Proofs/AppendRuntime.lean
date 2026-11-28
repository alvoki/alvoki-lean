import Alvoki.Experiments.WAL.Segmented.Proofs.AppendRotationIO

namespace WalRecoverySlice.Segmented.Native.AppendIO
open Alvoki.NativePost (W IOReturns)
open Model (Disk AppendReady)

def sourceState (disk : W → Disk) (w : W) (reg : Registration) (phase : SingleFile.AppendPhase) : Work :=
  (⟨disk w, 0, some reg.session.control.active⟩, phase)

def inputContext (mem : ChildMemory disk) (heap : PhaseMemory) (Q : W → Prop)
    (cell : IO.Ref (Phase Store)) (reg : Registration) : Context disk :=
  ⟨mem, heap, cell, reg.store, reg.session, Q⟩

theorem SelectedDisk.ofWritebacks (writes : Writebacks model actual) : SelectedDisk model actual :=
  ⟨actual, writes, rfl, rfl, fun _ _ => ⟨fun _ _ => ⟨id,id,rfl⟩,rfl⟩⟩

/-- The native heap, caller footprint and physical disk on one memory
primitive. A child binding is preserved only from a world where it is live. -/
structure MemoryEdge {disk : W → Disk} (mem : ChildMemory disk) (Q : W → Prop) (before after : W) : Prop where
  frame : Q before → Q after
  writes : Writebacks (disk before) (disk after)
  live : ∀ {dir id p h} (a : ChildAuthority mem dir id p h) {phase}, a.Live before phase → a.Live after phase

theorem MemoryEdge.trans {mem : ChildMemory disk} (a : MemoryEdge mem Q s t) (b : MemoryEdge mem Q t u) :
    MemoryEdge mem Q s u := ⟨fun h => b.frame (a.frame h), a.writes.trans b.writes, fun {_ _ _ _} key {_} live => b.live key (a.live key live)⟩

def installedWorld (cell : IO.Ref (Phase Store)) (store : Store) (session : Session) (t : W) :=
  ((cell.set (.ready store session) : BaseIO Unit) t).state

/-- The only memory boundaries outside the segmented worker. File, root and
child obligations occur inside LocalInPlace and LocalRotation. -/
structure Memory (mem : ChildMemory disk) (heap : PhaseMemory) (Q : W → Prop) (reg : Registration)
    (cell : IO.Ref (Phase Store)) (mutex : Std.BaseMutex) (w : W) where
  lock : MemoryEdge mem Q w (mutex.lock w).state
  read : MemoryEdge mem Q (mutex.lock w).state ((cell.get : BaseIO _) (mutex.lock w).state).state
  poison : MemoryEdge mem Q ((cell.get : BaseIO _) (mutex.lock w).state).state (issuedWorld cell mutex reg.store w)
  slotSet : ∀ slot t phase, heap.separate cell reg.store.active → heap.holds reg.store.active slot t →
    heap.holds reg.store.active slot ((cell.set phase : BaseIO _) t).state
  install : ∀ next t, Q t → heap.holds cell (.poisoned reg.store) t →
    MemoryEdge mem Q t (installedWorld cell reg.store next t)
  unlock : ∀ t phase, Q t → heap.holds cell phase t → MemoryEdge mem Q t (mutex.unlock t).state

theorem Memory.entry {mem : ChildMemory disk} (m : Memory mem heap Q reg cell mutex w) :
    MemoryEdge mem Q w (issuedWorld cell mutex reg.store w) := (m.lock.trans m.read).trans m.poison

structure LocalIO (mem : ChildMemory disk) (heap : PhaseMemory) (Q : W → Prop) (wal : Handle)
    (reg : Registration) (batch : Bytes) (w : W) where
  cell : IO.Ref (Phase Store)
  mutex : Std.BaseMutex
  parts : wal.Parts cell mutex
  memory : Memory mem heap Q reg cell mutex w
  reports : Reports batch
  inside : ∀ phase, let c := inputContext mem heap Q cell reg
    let begin := issuedWorld cell mutex reg.store w
    let s := sourceState disk w reg phase
    reg.session.activeCount ≠ reg.session.control.capacity →
    c.ReadyFile (some (reg.session.control.active,reg.child)) reg.session.control.active reg.child begin s →
    LocalInPlace c reports reg.child begin s
  rotate : ∀ phase, let c := inputContext mem heap Q cell reg
    let begin := issuedWorld cell mutex reg.store w
    let s := sourceState disk w reg phase
    reg.session.activeCount = reg.session.control.capacity →
    c.ReadyFile (some (reg.session.control.active,reg.child)) reg.session.control.active reg.child begin s →
    LocalRotation c reports reg.child begin s

def Succeeded (mem : ChildMemory disk) (heap : PhaseMemory) (Q : W → Prop) (wal : Handle)
    (reg : Registration) (batch : Bytes) (pos : Nat) (w : W) : Prop :=
  ∃ next : Registration, next.store = reg.store ∧ next.session = nextSession reg.session batch ∧
    Active mem heap wal next w ∧ Q w ∧
    Contract.Step (.online reg.session.view) (.ack (.append batch)) (.online next.session.view) ∧
    pos = next.session.tailPosition ∧ pos = reg.session.view.tail + 1

def Failed (disk : W → Disk) (heap : PhaseMemory) (Q : W → Prop) (wal : Handle)
    (reg : Registration) (batch : Bytes) (w : W) : Prop :=
  Q w ∧ Recoverable reg.session.view (some (.append batch)) (disk w) ∧ ∃ slot, Custody heap wal reg.store slot w

private theorem LocalIO.begin {mem : ChildMemory disk} (op : LocalIO mem heap Q wal reg batch w)
    (entry : Active mem heap wal reg w) (framed : Q w) :
    let c := inputContext mem heap Q op.cell reg
    let begin := issuedWorld op.cell op.mutex reg.store w
    ∃ phase, AppendReady reg.session (sourceState disk w reg phase) ∧
      c.ReadyFile (some (reg.session.control.active,reg.child)) reg.session.control.active reg.child
        begin (sourceState disk w reg phase) := by
  obtain ⟨_,registered,a,phase,live,ready⟩ := entry
  obtain ⟨sep,outer,slot⟩ := registered
  have aligned : heap.separate op.cell reg.store.active := op.parts.1 ▸ sep
  have base : (inputContext mem heap Q op.cell reg).Base (some (reg.session.control.active,reg.child))
      (issuedWorld op.cell op.mutex reg.store w) (disk w) :=
    ⟨op.memory.entry.frame framed,.ofWritebacks op.memory.entry.writes,heap.set _ _ _,
      op.memory.slotSet _ _ _ aligned (heap.readFrame op.cell (heap.lock op.mutex slot))⟩
  obtain ⟨hist, shape, layout, left, right, eq⟩ := ready
  exact ⟨phase,⟨hist, shape, layout, left, right, eq⟩,
    base,⟨a,op.memory.entry.live a live⟩,_,_,eq,rfl⟩

theorem LocalIO.append {mem : ChildMemory disk} (op : LocalIO mem heap Q wal reg batch w)
    (entry : Active mem heap wal reg w) (framed : Q w) (size : batch.length ≤ 32)
    (room : reg.session.view.tail < Contract.maxPosition) (linux : System.Platform.isWindows = false) :
    IOReturns (Native.append wal batch) w (Succeeded mem heap Q wal reg batch) (Failed disk heap Q wal reg batch) := by
  obtain ⟨phase,ready,typed⟩ := op.begin entry framed
  obtain ⟨root, held, _⟩ := entry
  let c := inputContext mem heap Q op.cell reg
  let s := sourceState disk w reg phase
  let begin := issuedWorld op.cell op.mutex reg.store w
  have parts := op.parts
  obtain ⟨separate, owns, slot⟩ := held
  have regFacts : heap.separate op.cell reg.store.active ∧ heap.holds op.cell (.ready reg.store reg.session) w := by
    rw [← parts.1]
    exact ⟨separate,owns⟩
  let memIO := op.memory
  have get := heap.read (heap.lock op.mutex regFacts.2)
  have base := typed.1
  have installed := ready.installed
  have bounds := Model.successor_controlRepresentable installed room
  have body := append_admitted op.reports reg.store reg.session op.parts w s get.1 ready rfl size room linux
    (c.Done batch) c.Failed (fun ne => (op.inside phase ne typed).assemble base rfl ne)
    (fun eq => (op.rotate phase eq typed).assemble typed bounds.1 bounds.2 eq linux)
  unfold IOReturns at *
  cases actual : Native.append wal batch w with
  | ok pos endWorld =>
    rw [actual] at body
    obtain ⟨next,t,u,rfl,⟨child,base,auth,bound⟩,nextEq,reusable,slotAt,ack,posEq,absolute⟩ := body
    let reg' : Registration := ⟨next,reg.store,child⟩
    let readyAt := installedWorld op.cell reg.store next t
    obtain ⟨q,physical,poison,stored⟩ := base
    have set := memIO.install next t q poison
    have fresh := heap.set op.cell (.ready reg.store next) t
    have unlocked := memIO.unlock readyAt _ (set.frame q) fresh
    let finish := readyWorld op.cell op.mutex reg.store next t
    have edges := set.trans unlocked
    have sameId : (nextSession reg.session batch).control.active = next.control.active := nextEq ▸ rfl
    have sameP : reg.session.control.policy = next.control.policy := by
      rw [nextEq]; unfold nextSession; split <;> rfl
    have registered : heap.Registered wal reg' finish := by
      refine ⟨separate, ?_, ?_⟩
      · rw [parts.1]
        exact heap.unlock _ fresh
      · change heap.holds reg.store.active (some (next.control.active,child)) finish
        rw [← sameId]
        exact heap.unlock _ (memIO.slotSet _ t _ regFacts.1 stored)
    have finalReady := (SelectedDisk.ofWritebacks edges.writes).appendReady (physical.appendReady reusable)
    have typedChild : ∃ b : ChildAuthority mem (segmentPath reg.store.root next.control.active)
        next.control.active next.control.policy child, b.Live finish u.2 := by
      rw [← sameId, ← sameP]
      exact ⟨auth, edges.live auth bound⟩
    obtain ⟨b, alive⟩ := typedChild
    exact ⟨reg',rfl,nextEq,⟨root,registered,b,u.2,alive,finalReady⟩,edges.frame q,ack,posEq,absolute⟩
  | error e endWorld =>
    rw [actual] at body
    obtain ⟨t,u,rfl,⟨slot,⟨q,physical,poison,stored⟩,locks⟩,_,recover⟩ := body
    have edge := memIO.unlock t _ q poison
    exact ⟨edge.frame q, edge.writes.recoverable (physical.recoverable recover),
      slot,root,locks,op.cell,op.mutex,op.parts,regFacts.1,.inl (heap.unlock _ poison),heap.unlock _ stored⟩

/-- An admission guard can reject the payload or absolute position before
either child path starts. Close then consumes the original active child. -/
theorem LocalIO.rejected {mem : ChildMemory disk} (op : LocalIO mem heap Q wal reg batch w)
    (entry : Active mem heap wal reg w) (framed : Q w)
    (invalid : batch.length > 32 ∨ reg.session.view.tail ≥ Contract.maxPosition) :
    ∃ err t, Native.append wal batch w = .error err t ∧ Q t ∧
      Recoverable reg.session.view (some (.append batch)) (disk t) ∧
      Custody heap wal reg.store (some (reg.session.control.active,reg.child)) t := by
  obtain ⟨root,registered,a,phase,live,ready⟩ := entry
  obtain ⟨sep,outer,slot⟩ := registered
  have aligned : heap.separate op.cell reg.store.active ∧ heap.holds op.cell (.ready reg.store reg.session) w := by
    rw [← op.parts.1]; exact ⟨sep,outer⟩
  let begin := issuedWorld op.cell op.mutex reg.store w
  have read := heap.read (heap.lock op.mutex aligned.2)
  obtain ⟨e,ran⟩ := append_rejected op.parts reg.store reg.session w batch read.1 invalid
  have poison : heap.holds op.cell (.poisoned reg.store) begin := heap.set _ _ _
  have child : heap.holds reg.store.active (some (reg.session.control.active,reg.child)) begin :=
    op.memory.slotSet _ _ _ aligned.1 (heap.readFrame op.cell (heap.lock op.mutex slot))
  have edges := op.memory.entry.trans (op.memory.unlock begin _ (op.memory.entry.frame framed) poison)
  have prior : Recoverable reg.session.view (some (.append batch)) (disk w) := ready.installed.offline (.inl rfl)
  exact ⟨_,_,ran,edges.frame framed,edges.writes.recoverable prior,root,⟨a.fd,a.source.openedChild⟩,
    op.cell,op.mutex,op.parts,aligned.1,.inl (heap.unlock _ poison),heap.unlock _ child⟩

theorem LocalIO.run {mem : ChildMemory disk} (op : LocalIO mem heap Q wal reg batch w)
    (entry : Active mem heap wal reg w) (framed : Q w) (linux : System.Platform.isWindows = false) :
    IOReturns (Native.append wal batch) w (Succeeded mem heap Q wal reg batch) (Failed disk heap Q wal reg batch) := by
  by_cases size : batch.length ≤ 32
  · by_cases room : reg.session.view.tail < Contract.maxPosition
    · exact op.append entry framed size room linux
    · obtain ⟨e,t,ran,q,d,held⟩ := op.rejected entry framed (.inr (Nat.le_of_not_gt room))
      unfold IOReturns; rw [ran]; exact ⟨q,d,_,held⟩
  · obtain ⟨e,t,ran,q,d,held⟩ := op.rejected entry framed (.inl (Nat.lt_of_not_ge size))
    unfold IOReturns; rw [ran]; exact ⟨q,d,_,held⟩

def healthyReports (batch : Bytes) (directory : Nat) (removal : Model.RootReports) : Reports batch :=
  ⟨directory, removal, Model.healthy, {}, {}, fun _ _ => SingleFile.healthyAppendReports⟩

/-- Healthy local primitive reports force an actual success on both
branches. The returned registration carries the ready descriptor for a
second operation, even when the client subsequently loses the reply. -/
theorem LocalIO.healthy {mem : ChildMemory disk} (op : LocalIO mem heap Q wal reg batch w)
    (entry : Active mem heap wal reg w) (framed : Q w) (size : batch.length ≤ 32)
    (room : reg.session.view.tail < Contract.maxPosition) (linux : System.Platform.isWindows = false)
    (healthy : op.reports = healthyReports batch directory removal) (removes : Model.HealthyRoot removal) :
    ∃ pos t, Native.append wal batch w = .ok pos t ∧ Succeeded mem heap Q wal reg batch pos t := by
  obtain ⟨phase,ready,file⟩ := op.begin entry framed
  have bounds := Model.successor_controlRepresentable ready.installed room
  let s := sourceState disk w reg phase
  have body := appendSession op.reports reg.store reg.session size room
    (fun ne => (op.inside phase ne file).assemble file.1 rfl ne)
    (fun eq => (op.rotate phase eq file).assemble file bounds.1 bounds.2 eq linux)
  obtain ⟨next,u,ran⟩ := Model.nativeAppendModel_healthy reg.store.root directory removal removes reg.session
    s ready rfl size room linux (batch := batch)
  have success : (op.reports.action reg.store reg.session).run s = .ok (.ok next) u := by
    rw [healthy]; exact ran
  unfold At at body
  rw [success] at body
  have read := heap.read (heap.lock op.mutex (op.parts.1 ▸ entry.2.1.2.1))
  have output := op.append entry framed size room linux
  unfold IOReturns at output
  rw [append_ready_run op.parts batch w read.1] at output ⊢
  dsimp only
  cases real : reg.store.appendSession reg.session batch (issuedWorld op.cell op.mutex reg.store w) with
  | error => rw [real] at body; contradiction
  | ok x t =>
    change reg.store.appendSession reg.session batch _ = .ok x t at real
    rw [show ((op.cell.set (.poisoned reg.store) : BaseIO _)
      ((op.cell.get : BaseIO _) (op.mutex.lock w).state).state).state = issuedWorld op.cell op.mutex reg.store w from rfl]
    rw [real]
    dsimp only at output
    rw [show ((op.cell.set (.poisoned reg.store) : BaseIO _) ((op.cell.get : BaseIO _) (op.mutex.lock w).state).state).state = issuedWorld op.cell op.mutex reg.store w from rfl] at output
    rw [real] at output
    exact ⟨_,_,rfl,output⟩

end WalRecoverySlice.Segmented.Native.AppendIO
