import Alvoki.Experiments.WAL.Segmented.Native

/-! A finite, first-order model of owned runtime roles. The production
installation schedules run here over an explicit heap and checked accesses.
Identifiers for children and mutexes describe model resources. -/
namespace L0Audit.OwnedRoleModel

open WalRecoverySlice.Segmented (Session)
open WalRecoverySlice.Segmented.Native (Phase installPhaseWith installReopenedWith)

inductive Role where
  | active | phase | mutex
  deriving DecidableEq

structure Key where
  slot : Nat
  epoch : Nat
  role : Role
  deriving DecidableEq

inductive Value where
  | active (child : Option (Nat × Nat))
  | phase (state : Phase Key)
  | mutex (locked : Bool)

def Value.role : Value → Role
  | .active _ => .active
  | .phase _ => .phase
  | .mutex _ => .mutex

structure Cell where
  epoch : Nat
  contents : Option Value

abbrev Heap := List Cell

def Owns (h : Heap) (k : Key) (v : Value) : Prop :=
  h[k.slot]? = some ⟨k.epoch,some v⟩ ∧ v.role = k.role

def read (h : Heap) (k : Key) : Option Value := do
  let cell ← h[k.slot]?
  let v ← cell.contents
  if cell.epoch = k.epoch ∧ v.role = k.role then some v else none

def write (h : Heap) (k : Key) (v : Value) : Option Heap := do
  let _ ← read h k
  if v.role = k.role then some (h.set k.slot ⟨k.epoch,some v⟩) else none

def release (h : Heap) (k : Key) : Option Heap := do
  let _ ← read h k
  return h.set k.slot ⟨k.epoch,none⟩

/-- An allocation is issued at a reserved empty address. Reuse changes the epoch. -/
def allocate (h : Heap) (n : Nat) (v : Value) : Option (Key × Heap) := do
  let c ← h[n]?
  match c.contents with
  | some _ => none
  | none => return (⟨n,c.epoch+1,v.role⟩, h.set n ⟨c.epoch+1,some v⟩)

abbrev Separate (left right : Key) := left.slot ≠ right.slot

private theorem held_read (held : Owns h k v) : read h k = some v := by
  simp [read, held.1, held.2]

private theorem bound {h : Heap} (atSlot : h[n]? = some c) : n < h.length := by
  by_cases present : n < h.length
  · exact present
  · rw [List.getElem?_eq_none (by omega)] at atSlot
    contradiction

private theorem frame (held : Owns h k v) (apart : n ≠ k.slot) (c : Cell) :
    Owns (h.set n c) k v := by
  exact ⟨(List.getElem?_set_ne (by omega)).trans held.1, held.2⟩

/-- Laws are indexed by one issued key and its pre-state. Each mutating
law supplies ownership in its own reached heap and frames only other slots. -/
structure Contract (H : Type) (owns : H → Key → Value → Prop)
    (get : H → Key → Option Value) (set : H → Key → Value → Option H)
    (drop : H → Key → Option H) (alloc : H → Nat → Value → Option (Key × H))
    (free : H → Nat → Nat → Prop) : Prop where
  observe : ∀ {h k v}, owns h k v → get h k = some v
  modify : ∀ {h k old} (v : Value), owns h k old → v.role = k.role →
    ∃ t, set h k v = some t ∧ owns t k v ∧ ∀ j x, Separate k j → owns h j x → owns t j x
  dispose : ∀ {h k v}, owns h k v → ∃ t, drop h k = some t ∧ free t k.slot k.epoch ∧ get t k = none ∧
    ∀ j x, Separate k j → owns h j x → owns t j x
  acquire : ∀ {h n epoch} (v : Value), free h n epoch →
    ∃ t, alloc h n v = some (⟨n,epoch+1,v.role⟩,t) ∧ owns t ⟨n,epoch+1,v.role⟩ v ∧
      ∀ j x, n ≠ j.slot → owns h j x → owns t j x

def Free (h : Heap) (n epoch : Nat) := h[n]? = some ⟨epoch,none⟩

theorem realized : Contract Heap Owns read write release allocate Free := by
  refine ⟨fun held => held_read held,?_,?_,?_⟩
  · intro h k old v held role
    have present := bound held.1
    refine ⟨h.set k.slot ⟨k.epoch,some v⟩,by simp [write,held_read held,role],⟨?_,role⟩,fun j x apart other => frame other apart _⟩
    simp [present]
  · intro h k v held
    have present := bound held.1
    refine ⟨h.set k.slot ⟨k.epoch,none⟩,by simp [release,held_read held],?_,?_,fun j x apart other => frame other apart _⟩
    · simp [Free,present]
    · simp [read,present]
  · intro h n epoch v free
    have present := bound free
    unfold Free at free
    refine ⟨h.set n ⟨epoch+1,some v⟩,by simp [allocate,free],⟨?_,rfl⟩,fun j x apart other => frame other apart _⟩
    simp [present]

/-- Run the production phase-installation and reopened-child schedules.
The recovered child is supplied as input. Installing it writes the owned
active slot before allocating the phase cell that points back to that slot. -/
abbrev M := EStateM Unit Heap

private def assign (k : Key) (v : Value) : M Unit := fun h =>
  match write h k v with | some t => .ok () t | none => .error () h

private def newKey (n : Nat) (v : Value) : M Key := fun h =>
  match allocate h n v with | some (k,t) => .ok k t | none => .error () h

def install (slot : Key) (session : Session) (child : Nat) : M (Key × Key) :=
  installPhaseWith (error := Unit)
    (installReopenedWith (pure (session,child)) (fun selected => do
      assign slot (.active selected)
      return slot))
    (fun ph => newKey 1 (.phase ph)) (newKey 2 (.mutex false)) (assign slot (.active none))

private def emptyCell : Cell := ⟨0,none⟩
private def slot : Key := ⟨0,1,.active⟩
private def ph : Key := ⟨1,1,.phase⟩
private def mutex : Key := ⟨2,1,.mutex⟩
private def session : Session := ⟨⟨.logOnly,1,0,0⟩,0,⟨0,[]⟩⟩

/-- From an actual allocation and install, poison the phase, then change
the child while keeping the poisoned phase. Every read is authorized by
the ownership produced for that same heap. -/
theorem reached :
    ∃ h t u v, allocate [emptyCell,emptyCell,emptyCell] 0 (.active none) = some (slot,h) ∧
      install slot session 7 h = .ok (ph,mutex) t ∧
      read t ph = some (.phase (.ready slot session)) ∧ read t slot = some (.active (some (0,7))) ∧
      write t ph (.phase (.poisoned slot)) = some u ∧ read u slot = some (.active (some (0,7))) ∧
      write u slot (.active (some (1,8))) = some v ∧ read v ph = some (.phase (.poisoned slot)) ∧
      read v slot = some (.active (some (1,8))) ∧ read v mutex = some (.mutex false) := by
  let h : Heap := [⟨1,some (.active none)⟩,emptyCell,emptyCell]
  let t : Heap := [⟨1,some (.active (some (0,7)))⟩,⟨1,some (.phase (.ready slot session))⟩,⟨1,some (.mutex false)⟩]
  have p : Owns t ph (.phase (.ready slot session)) := ⟨rfl,rfl⟩
  have s : Owns t slot (.active (some (0,7))) := ⟨rfl,rfl⟩
  have m : Owns t mutex (.mutex false) := ⟨rfl,rfl⟩
  obtain ⟨u,modified,pu,kept⟩ := realized.modify (.phase (.poisoned slot)) p rfl
  have su := kept _ _ (by decide : Separate ph slot) s
  have mu := kept _ _ (by decide : Separate ph mutex) m
  obtain ⟨v,changed,sv,framed⟩ := realized.modify (.active (some (1,8))) su rfl
  exact ⟨h,t,u,v,rfl,rfl,realized.observe p,realized.observe s,modified,realized.observe su,changed,
    realized.observe (framed _ _ (by decide : Separate slot ph) pu),realized.observe sv,
    realized.observe (framed _ _ (by decide : Separate slot mutex) mu)⟩

/-- With no address for the mutex, the second allocation reports failure.
The real installation error path empties the active slot at that reached
heap. The model retains the allocated phase cell after the failed construction. -/
theorem mutexFailure : ∃ h t,
    allocate [emptyCell,emptyCell] 0 (.active none) = some (slot,h) ∧
    install slot session 7 h = .error () t ∧ read t slot = some (.active none) ∧
    read t ph = some (.phase (.ready slot session)) :=
  ⟨[⟨1,some (.active none)⟩,emptyCell],
    [⟨1,some (.active none)⟩,⟨1,some (.phase (.ready slot session))⟩],rfl,rfl,rfl,rfl⟩

/-- A second acquisition at the same address and role rejects the old key
even when the new contents equal the old contents. -/
theorem reuse : ∃ h empty fresh, allocate [emptyCell] 0 (.active none) = some (slot,h) ∧
    release h slot = some empty ∧ allocate empty 0 (.active none) = some (⟨0,2,.active⟩,fresh) ∧
    read fresh slot = none ∧ write fresh slot (.active (some (3,5))) = none ∧
    read fresh ⟨0,2,.active⟩ = some (.active none) :=
  ⟨[⟨1,some (.active none)⟩],[⟨1,none⟩],[⟨2,some (.active none)⟩],rfl,rfl,rfl,rfl,rfl,rfl⟩

end L0Audit.OwnedRoleModel
