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

theorem LocalIO.append {mem : ChildMemory disk} (op : LocalIO mem heap Q wal reg batch w)
    (entry : Active mem heap wal reg w) (framed : Q w) (size : batch.length ≤ 32)
    (room : reg.session.view.tail < Contract.maxPosition) (linux : System.Platform.isWindows = false) :
    IOReturns (Native.append wal batch) w (Succeeded mem heap Q wal reg batch) (Failed disk heap Q wal reg batch) := by
  obtain ⟨root, held, a, phase, live, ready⟩ := entry
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
  have base : c.Base (some (reg.session.control.active,reg.child)) begin s.1.disk :=
    ⟨memIO.entry.frame framed, .ofWritebacks memIO.entry.writes, heap.set _ _ _,
      memIO.slotSet _ _ _ regFacts.1 (heap.readFrame op.cell (heap.lock op.mutex slot))⟩
  have typed : c.ReadyFile (some (reg.session.control.active,reg.child)) reg.session.control.active reg.child begin s := by
    obtain ⟨hist, shape, layout, left, right, eq⟩ := ready
    exact ⟨base, ⟨a, memIO.entry.live a live⟩, _, _, eq, rfl⟩
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

end WalRecoverySlice.Segmented.Native.AppendIO
