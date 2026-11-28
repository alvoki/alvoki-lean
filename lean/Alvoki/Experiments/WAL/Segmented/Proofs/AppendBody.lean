import Alvoki.Experiments.WAL.Segmented.Proofs.AppendIngress
import Alvoki.Experiments.WAL.Segmented.Proofs.PublicAppendIO
import Alvoki.Experiments.WAL.Segmented.Proofs.AppendSlotIO
import Alvoki.Experiments.WAL.Segmented.Proofs.SuccessorIO

namespace WalRecoverySlice.Segmented.Native.AppendIO
open Alvoki.NativePost (W)
open Model (Disk State AppendReady successor)
variable {id : Nat}

/-- The state owned while the outer WAL phase is poisoned. The concrete
slot is retained on the in-place path and empty during successor creation. -/
structure Context (disk : W → Disk) where
  mem : ChildMemory disk
  heap : PhaseMemory
  cell : IO.Ref (Phase Store)
  store : Store
  session : Session
  frame : W → Prop

def Context.Base (c : Context disk) (slot : Option (Nat × SingleFile.Handle)) (w : W) (d : Disk) : Prop :=
  c.frame w ∧ SelectedDisk d (disk w) ∧ c.heap.holds c.cell (.poisoned c.store) w ∧
    c.heap.holds c.store.active slot w

def Context.Bound (c : Context disk) (id : Nat) (h : SingleFile.Handle) (w : W) (phase : SingleFile.AppendPhase) : Prop :=
  ∃ a : ChildAuthority c.mem (segmentPath c.store.root id) id c.session.control.policy h, a.Live w phase

def Context.Failed (c : Context disk) (w : W) (s : Work) : Prop :=
  ∃ slot, c.Base slot w s.1.disk ∧ SlotLocks c.store slot

def Context.Done (c : Context disk) (batch : Bytes) (w : W) (s : Work) : Prop :=
  let id := (nextSession c.session batch).control.active
  ∃ h, c.Base (some (id,h)) w s.1.disk ∧ c.Bound id h w s.2

def Matches (p : Policy) (id : Nat) (s : Work) : Prop :=
  ∃ pos bs, s.2 = .active .lock (SingleFile.appendBindings p) pos bs ∧ s.1.disk.cursor id = pos

def Context.ReadyFile (c : Context disk) (slot : Option (Nat × SingleFile.Handle)) (id : Nat)
    (h : SingleFile.Handle) (w : W) (s : Work) : Prop :=
  c.Base slot w s.1.disk ∧ c.Bound id h w s.2 ∧ Matches c.session.control.policy id s

theorem Context.base_empty (c : Context disk) (s : Work) (held : c.Base none w s.1.disk) : c.Failed w s :=
  ⟨none, held, trivial⟩

theorem Context.base_owned (c : Context disk) (s : Work) (held : c.Base (some (id,h)) w s.1.disk)
    (child : c.Bound id h w s.2) : c.Failed w s := by
  obtain ⟨a, _⟩ := child
  exact ⟨_, held, a.fd, a.source.openedChild⟩

structure WriteSteps (c : Context disk) (slot : Option (Nat × SingleFile.Handle)) (id : Nat)
    (h : SingleFile.Handle) (r : Reports batch) (w : W) (s : Work) where
  steps : ∀ (a : ChildAuthority c.mem (segmentPath c.store.root id) id c.session.control.policy h) pos bs,
    a.Live w s.2 → s.2 = .active .lock (SingleFile.appendBindings c.session.control.policy) pos bs →
    s.1.disk.cursor id = pos →
    SingleFile.ConcreteAppend.Steps (a.Link (c.Base slot) s.1) c.session.control.policy pos batch
      (r.append c.session.control.policy pos) bs (s.1.disk.segment id) a.ref a.fd a.files a.mutex w

theorem WriteSteps.run {r : Reports batch} (localIO : WriteSteps c slot id h r w s)
    (owned : c.ReadyFile slot id h w s) (key : Model.AppendChild) (same : key.segment = id) :
    At (SingleFile.append h batch) (Model.writeAs c.session (r.append c.session.control.policy) key key batch) w s
      (fun _ _ t u => c.Base slot t u.1.disk ∧ c.Bound id h t u.2)
      (fun t u => c.Base slot t u.1.disk ∧ c.Bound id h t u.2) := by
  obtain ⟨base, ⟨a, live⟩, pos, bs, phase, cursor⟩ := owned
  have steps := localIO.steps a pos bs live phase cursor
  cases s with
  | mk st old =>
    dsimp only at phase
    subst old
    exact (a.writeAs key same _ steps live cursor base).map
      (fun _ _ _ _ out => ⟨out.2, a, out.1⟩) (fun _ _ out => ⟨out.2, a, out.1⟩)

/-- All four owned resources are transported across the one reached slot get. -/
structure LocalInPlace (c : Context disk) (r : Reports batch) (h : SingleFile.Handle) (w : W) (s : Work) where
  readFrame : c.ReadyFile (some (c.session.control.active, h)) c.session.control.active h
    ((c.store.active.get : BaseIO _) w).state s
  write : WriteSteps c (some (c.session.control.active,h)) c.session.control.active h r
    ((c.store.active.get : BaseIO _) w).state s

def LocalInPlace.assemble {r : Reports batch} (io : LocalInPlace c r h w s)
    (base : c.Base (some (c.session.control.active,h)) w s.1.disk)
    (registered : s.1.activeEntry = some c.session.control.active)
    (inside : c.session.activeCount ≠ c.session.control.capacity) :
    InPlace c.store c.session r w s (c.Done batch) c.Failed := by
  let u := ((c.store.active.get : BaseIO _) w).state
  refine ⟨fun child t st => child = h ∧ t = u ∧ st = s, ?_, ?_⟩
  · have slot := slot_get (bad := fun _ _ => False) c.store s w (c.heap.read base.2.2.2).1 registered (P := fun t st => t = u ∧ st = s) ⟨rfl,rfl⟩
    exact slot.map (fun _ _ _ _ x => ⟨h, x.1, x.2.1, rfl, x.2.2⟩) (fun _ _ x => False.elim x)
  · rintro _ _ _ ⟨rfl, rfl, rfl⟩
    exact (io.write.run io.readFrame (.stored _) rfl).map (fun _ _ _ _ x => by
      unfold Context.Done
      simp only [nextSession, inside, ↓reduceIte]
      exact ⟨_,x⟩) (fun _ st x => c.base_owned st x.1 x.2)

end WalRecoverySlice.Segmented.Native.AppendIO
