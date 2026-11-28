import Alvoki.Experiments.WAL.Segmented.Native

/-! A finite, first-order model of owned runtime roles. The production
installation schedules run here over an explicit heap and checked accesses.
Child and mutex keys identify model resources. -/
namespace L0Audit.OwnedRoleModel

open WalRecoverySlice.Segmented (Session)
open WalRecoverySlice.Segmented.Native (Phase installPhaseWith installReopenedWith)

inductive Role where
  | active | phase | mutex | child
  deriving DecidableEq

structure Key where
  slot : Nat
  epoch : Nat
  role : Role
  deriving DecidableEq

inductive Value where
  | active (child : Option (Nat × Key))
  | phase (state : Phase Key)
  | mutex (locked : Bool)
  | child (log : List WalRecoverySlice.Bytes)

def Value.role : Value → Role
  | .active _ => .active
  | .phase _ => .phase
  | .mutex _ => .mutex
  | .child .. => .child

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

def installAt (phaseAddress mutexAddress : Nat) (slot : Key) (session : Session) (child : Key) : M (Key × Key) :=
  installPhaseWith (error := Unit)
    (installReopenedWith (pure (session,child)) (fun selected => do
      assign slot (.active selected)
      return slot))
    (fun ph => newKey phaseAddress (.phase ph)) (newKey mutexAddress (.mutex false)) (assign slot (.active none))

def install := installAt 1 2

private def oldChild : Key := ⟨4,1,.child⟩
private def newChild : Key := ⟨5,1,.child⟩
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
      install slot session oldChild h = .ok (ph,mutex) t ∧
      read t ph = some (.phase (.ready slot session)) ∧ read t slot = some (.active (some (0,oldChild))) ∧
      write t ph (.phase (.poisoned slot)) = some u ∧ read u slot = some (.active (some (0,oldChild))) ∧
      write u slot (.active (some (1,newChild))) = some v ∧ read v ph = some (.phase (.poisoned slot)) ∧
      read v slot = some (.active (some (1,newChild))) ∧ read v mutex = some (.mutex false) := by
  let h : Heap := [⟨1,some (.active none)⟩,emptyCell,emptyCell]
  let t : Heap := [⟨1,some (.active (some (0,oldChild)))⟩,⟨1,some (.phase (.ready slot session))⟩,⟨1,some (.mutex false)⟩]
  have p : Owns t ph (.phase (.ready slot session)) := ⟨rfl,rfl⟩
  have s : Owns t slot (.active (some (0,oldChild))) := ⟨rfl,rfl⟩
  have m : Owns t mutex (.mutex false) := ⟨rfl,rfl⟩
  obtain ⟨u,modified,pu,kept⟩ := realized.modify (.phase (.poisoned slot)) p rfl
  have su := kept _ _ (by decide : Separate ph slot) s
  have mu := kept _ _ (by decide : Separate ph mutex) m
  obtain ⟨v,changed,sv,framed⟩ := realized.modify (.active (some (1,newChild))) su rfl
  exact ⟨h,t,u,v,rfl,rfl,realized.observe p,realized.observe s,modified,realized.observe su,changed,
    realized.observe (framed _ _ (by decide : Separate slot ph) pu),realized.observe sv,
    realized.observe (framed _ _ (by decide : Separate slot mutex) mu)⟩

/-- With no address for the mutex, the second allocation reports failure.
The real installation error path empties the active slot at that reached
heap. The model retains the allocated phase cell after the failed construction. -/
theorem mutexFailure : ∃ h t,
    allocate [emptyCell,emptyCell] 0 (.active none) = some (slot,h) ∧
    install slot session oldChild h = .error () t ∧ read t slot = some (.active none) ∧
    read t ph = some (.phase (.ready slot session)) :=
  ⟨[⟨1,some (.active none)⟩,emptyCell],
    [⟨1,some (.active none)⟩,⟨1,some (.phase (.ready slot session))⟩],rfl,rfl,rfl,rfl⟩

/-- A second acquisition at the same address and role rejects the old key
even when the new contents equal the old contents. -/
theorem reuse : ∃ h empty fresh, allocate [emptyCell] 0 (.active none) = some (slot,h) ∧
    release h slot = some empty ∧ allocate empty 0 (.active none) = some (⟨0,2,.active⟩,fresh) ∧
    read fresh slot = none ∧ write fresh slot (.active (some (3,newChild))) = none ∧
    read fresh ⟨0,2,.active⟩ = some (.active none) :=
  ⟨[⟨1,some (.active none)⟩],[⟨1,none⟩],[⟨2,some (.active none)⟩],rfl,rfl,rfl,rfl,rfl,rfl⟩

private def fetch (key : Key) : M Value := fun h =>
  match read h key with | some v => .ok v h | none => .error () h

private def relinquish (key : Key) : M Unit := fun h =>
  match release h key with | some t => .ok () t | none => .error () h

private def check (s : Session) (batch : WalRecoverySlice.Bytes) : M Unit :=
  match WalRecoverySlice.Segmented.checkAppend (m := Except String) s batch with
  | .ok () => pure ()
  | .error _ => throw ()

/-- Run the production update and in-place append schedules. The issued
child action checks its own live key and the exact key delivered from the
installed slot before it writes the batch. Rotation lies outside this fixture. -/
def appendUsing (handle : Key × Key) (candidate : Key) (batch : WalRecoverySlice.Bytes) : M Session := do
  let .mutex false ← fetch handle.2 | throw ()
  WalRecoverySlice.Segmented.Native.updateWith (fun _ => ())
    (do
      let .phase phase ← fetch handle.1 | throw ()
      return phase)
    (fun phase => assign handle.1 (.phase phase)) fun active s =>
      WalRecoverySlice.Segmented.Native.appendOwnedWith (error := Unit) s batch (check s batch) (fun _ => ())
        (do
          let .active child ← fetch active | throw ()
          return child)
        (throw ()) (fun _ _ => throw ()) (fun _ => throw ()) (throw ()) (fun _ => throw ())
        (fun selected b => do
          unless candidate = selected do throw ()
          let .child log ← fetch selected | throw ()
          assign selected (.child (log ++ [b])))
        (fun child => assign active (.active child))

private def retried : Key × Key := (⟨3,1,.phase⟩,⟨2,2,.mutex⟩)

private def reserve : M (Key × Key × Key × Key) := do
  let active ← newKey 0 (.active none)
  let blocker ← newKey 2 (.mutex true)
  let first ← newKey 4 (.child [])
  let second ← newKey 5 (.child [])
  return (active,blocker,first,second)

private def retry (active blocker recovered : Key) : M (Key × Key) := do
  relinquish blocker
  installAt 3 2 active session recovered

private def openWithRetry (active blocker first second : Key) : M (Key × Key) :=
  try install active session first catch _ => retry active blocker second

/-- The mutex address is occupied during the first install. Its cleanup
empties the active slot. On the reached failure heap the other owner
releases the mutex address, and the second install can reuse it at epoch
two. Both candidate child keys remain live. Only the one chosen by this
install can consume its ready phase and append the supplied batch. -/
theorem retryHandoff :
    let batch : WalRecoverySlice.Bytes := [42]
    ∃ reserved failed ready committed rejected,
      reserve (List.replicate 6 emptyCell) = .ok (slot,mutex,oldChild,newChild) reserved ∧
      install slot session oldChild reserved = .error () failed ∧
      read failed slot = some (.active none) ∧ read failed mutex = some (.mutex true) ∧
      retry slot mutex newChild failed = .ok retried ready ∧ read ready mutex = none ∧
      read ready retried.1 = some (.phase (.ready slot session)) ∧
      read ready slot = some (.active (some (session.control.active,newChild))) ∧
      read ready oldChild = some (.child []) ∧ read ready newChild = some (.child []) ∧
      appendUsing retried oldChild batch ready = .error () rejected ∧
      read rejected retried.1 = some (.phase (.poisoned slot)) ∧
      read rejected oldChild = some (.child []) ∧ read rejected newChild = some (.child []) ∧
      let next : Session := ⟨session.control,1,session.view.append batch⟩
      (openWithRetry slot mutex oldChild newChild >>= fun handle => appendUsing handle newChild batch) reserved = .ok next committed ∧
      read committed retried.1 = some (.phase (.ready slot next)) ∧
      read committed newChild = some (.child [batch]) ∧ read committed oldChild = some (.child []) := by
  intro batch
  exact ⟨_,_,_,_,_,rfl, rfl,rfl,rfl, rfl,rfl,rfl,rfl,rfl,rfl,
    rfl,rfl,rfl,rfl, rfl,rfl,rfl,rfl⟩

/-- A deliberately faulty write returns the requested value at its own
slot and clears an unrelated cell. -/
def clobberWrite (h : Heap) (k : Key) (v : Value) : Option Heap := do
  let t ← write h k v
  return if k.slot = 0 then t.set 1 ⟨0,none⟩ else t

theorem clobberKeepsTarget (held : Owns h k old) (v : Value) (role : v.role = k.role) :
    ∃ t, clobberWrite h k v = some t ∧ Owns t k v := by
  obtain ⟨middle,written,target,_⟩ := realized.modify v held role
  by_cases zero : k.slot = 0
  · exact ⟨_, by simp [clobberWrite,written,zero], frame target (by omega : 1 ≠ k.slot) ⟨0,none⟩⟩
  · exact ⟨middle,by simp [clobberWrite,written,zero],target⟩

theorem clobberRejected : ¬ Contract Heap Owns read clobberWrite release allocate Free := by
  intro contract
  let h : Heap := [⟨1,some (.active none)⟩,⟨1,some (.phase .closed)⟩]
  let t : Heap := [⟨1,some (.active (some (0,oldChild)))⟩,⟨0,none⟩]
  have target : Owns h slot (.active none) := ⟨rfl,rfl⟩
  have sibling : Owns h ph (.phase .closed) := ⟨rfl,rfl⟩
  have actual : clobberWrite h slot (.active (some (0,oldChild))) = some t := rfl
  obtain ⟨after,returned,_,kept⟩ := contract.modify (.active (some (0,oldChild))) target rfl
  rw [actual] at returned
  cases Option.some.inj returned
  have observed := contract.observe (kept _ _ (by decide : Separate slot ph) sibling)
  change none = some (.phase .closed : Value) at observed
  contradiction

end L0Audit.OwnedRoleModel
