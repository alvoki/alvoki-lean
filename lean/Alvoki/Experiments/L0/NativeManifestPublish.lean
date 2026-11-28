import Alvoki.Experiments.L0.NativeManifest

namespace ExperimentalL0.NativeManifestPublish
open System DurableBlob L0Manifest

abbrev W := NativeManifest.World
abbrev Stop := {α : Type} → IO α → W → W → Prop

inductive Point
  | openWriter | write (h : IO.FS.Handle) | flush (h : IO.FS.Handle) | sync (h : IO.FS.Handle)
  | rename (h : IO.FS.Handle) | openDirectory (h : IO.FS.Handle) | barrier (h directory : IO.FS.Handle)

def Point.Result : Point → Type
  | .openWriter | .openDirectory _ => IO.FS.Handle
  | _ => Unit

def action (dir : FilePath) (bytes : ByteArray) : (p : Point) → IO p.Result
  | .openWriter => IO.FS.Handle.mk (dir / "BLOB.next") .write
  | .write h => h.write bytes
  | .flush h => h.flush
  | .sync h => DurableBlob.syncHandle h
  | .rename _ => IO.FS.rename (dir / "BLOB.next") (dir / "BLOB")
  | .openDirectory _ => IO.FS.Handle.mk dir .read
  | .barrier _ fd => DurableBlob.syncHandle fd

def advance : (p : Point) → p.Result → Option Point
  | .openWriter, h => some (.write h)
  | .write h, _ => some (.flush h)
  | .flush h, _ => some (.sync h)
  | .sync h, _ => some (.rename h)
  | .rename h, _ => some (.openDirectory h)
  | .openDirectory h, fd => some (.barrier h fd)
  | .barrier .., _ => none

def Point.rank : Point → Nat
  | .openWriter => 7 | .write _ => 6 | .flush _ => 5 | .sync _ => 4
  | .rename _ => 3 | .openDirectory _ => 2 | .barrier .. => 1

private theorem smaller (eq : advance p result = some q) : q.rank < p.rank := by
  cases p <;> simp [advance] at eq <;> subst q <;> simp [Point.rank]

def remaining (dir : FilePath) (bytes : ByteArray) (p : Point) : IO Unit := do
  let x ← action dir bytes p
  match _eq : advance p x with
  | none => return ()
  | some q => remaining dir bytes q
termination_by p.rank
decreasing_by exact smaller _eq

inductive Prefix (dir : FilePath) (bytes : ByteArray) (start : W) : Point → W → Prop where
  | initial : Prefix dir bytes start .openWriter start
  | next : Prefix dir bytes start p w → action dir bytes p w = .ok x t → advance p x = some q →
      Prefix dir bytes start q t

/-- Erasure follows the actual buffered writer and separately opened
directory descriptor of the DurableBlob Linux adapter. -/
theorem concrete (dir : FilePath) (bytes : ByteArray) :
    (native dir).publish bytes = remaining dir bytes .openWriter := by
  funext w
  change (DurableBlob.publishWith (do
    let h ← IO.FS.Handle.mk (dir / "BLOB.next") .write
    h.write bytes
    h.flush
    return h) DurableBlob.syncHandle (IO.FS.rename (dir / "BLOB.next") (dir / "BLOB"))
    (do DurableBlob.syncHandle (← IO.FS.Handle.mk dir .read)) : IO Unit) w = _
  simp only [remaining, advance, action, DurableBlob.publishWith, Bind.bind, instMonadEIO._aux_13,
    EST.bind, Pure.pure, instMonadEIO._aux_5, EST.pure]
  cases op : IO.FS.Handle.mk (dir / "BLOB.next") .write w <;> simp_all only
  rename_i h t
  cases written : h.write bytes t <;> simp_all only
  rename_i a
  cases flushed : h.flush a <;> simp_all only
  rename_i b
  cases synced : DurableBlob.syncHandle h b <;> simp_all only
  rename_i z
  cases renamed : IO.FS.rename (dir / "BLOB.next") (dir / "BLOB") z <;> simp_all only
  rename_i u
  cases opened : IO.FS.Handle.mk dir .read u <;> simp_all only
  rename_i fd v
  cases settled : DurableBlob.syncHandle fd v <;> rfl

theorem Prefix.continuation (pc : Prefix dir bytes start p w) :
    (native dir).publish bytes start = remaining dir bytes p w := by
  induction pc with
  | initial => rw [concrete]
  | next _ ran after ih =>
    rw [ih, remaining]
    simp only [Bind.bind, instMonadEIO._aux_13, EST.bind, ran]
    rename_i previous _ _ _ _ _
    cases previous <;> simp_all [advance]

/-- The runtime relates the open file description and its resolved
pathname to the same inode. The stream includes buffered bytes, while
live and durable observe the inode independently. -/
structure Media (inode : Type) where
  path : FilePath → W → Option inode
  descriptor : IO.FS.Handle → W → Option inode
  stream : IO.FS.Handle → W → ByteArray
  live : IO.FS.Handle → W → ByteArray
  durable : IO.FS.Handle → W → ByteArray

def Media.Bound (m : Media inode) (h : IO.FS.Handle) (path : FilePath) (w : W) :=
  ∃ i, m.descriptor h w = some i ∧ m.path path w = some i

/-- Opening the reserved staging name with .write truncates that inode.
If present, it must resolve away from the initialized active inode. -/
def Media.Private (m : Media inode) (dir : FilePath) (w : W) :=
  ∃ active, m.path (dir / "BLOB") w = some active ∧ m.path (dir / "BLOB.next") w ≠ some active

def Media.Synced (m : Media inode) (h : IO.FS.Handle) (path : FilePath) (bytes : ByteArray) (w : W) :=
  m.Bound h path w ∧ m.live h w = bytes ∧ m.durable h w = bytes

def Operand (m : Media inode) (dir : FilePath) (bytes : ByteArray) (w : W) : Point → Prop
  | .openWriter => m.Private dir w
  | .write h => m.Bound h (dir / "BLOB.next") w
  | .flush h => m.Bound h (dir / "BLOB.next") w ∧ m.stream h w = bytes
  | .sync h => m.Bound h (dir / "BLOB.next") w ∧ m.live h w = bytes
  | .rename h => m.Synced h (dir / "BLOB.next") bytes w
  | .openDirectory h => m.Synced h (dir / "BLOB") bytes w
  | .barrier h fd => m.Synced h (dir / "BLOB") bytes w ∧ m.Bound fd dir w

/-- Between barriers the filesystem can settle a name in the background.
The survivors are nonempty and can only narrow. -/
def Keeps (before after : Image) := after.active = before.active ∧ after.survivors ≠ [] ∧
  ∀ bytes ∈ after.survivors, bytes ∈ before.survivors

def Effect (m : Media inode) (p : Point) (completed : Bool) (w : W) (before after : Image) : Prop :=
  match p with
  | .rename h => (completed = false ∧ Keeps before after) ∨
      (after.active = m.durable h w ∧ after.survivors ≠ [] ∧
        ∀ bytes ∈ after.survivors, bytes = m.durable h w ∨ bytes ∈ before.survivors)
  | .barrier .. => (completed = false ∧ Keeps before after) ∨ after.Stable before.active
  | _ => Keeps before after

def NextOperand (m : Media inode) (dir : FilePath) (bytes : ByteArray) (p : Point) (x : p.Result) (t : W) :=
  match advance p x with
  | some q => Operand m dir bytes t q
  | none => True

structure Primitives (dir : FilePath) (bytes : ByteArray) (start : W) (P : W → Prop)
    (image : W → Image) (stop : Stop) (m : Media inode) : Prop where
  returned : ∀ p w, Prefix dir bytes start p w → P w → Operand m dir bytes w p →
    match action dir bytes p w with
    | .ok x t => P t ∧ Effect m p true w (image w) (image t) ∧ NextOperand m dir bytes p x t
    | .error _ t => P t ∧ Effect m p false w (image w) (image t)
  interrupted : ∀ p w, Prefix dir bytes start p w → P w → Operand m dir bytes w p →
    ∀ observed, stop (action dir bytes p) w observed → P observed ∧ Effect m p false w (image w) (image observed)

/-- Until rename, only the old manifest can be recovered. After a returned
rename, the live name is new and a loss of power may still restore the old
binding. A successful directory barrier settles the new name. -/
def Before (p : Point) (old proposed : ByteArray) (img : Image) :=
  match p with
  | .openDirectory _ | .barrier .. => img.active = proposed ∧ img.Admits old (some proposed)
  | _ => img.Admits old none

def Window (p : Point) (old proposed : ByteArray) (img : Image) :=
  match p with
  | .rename _ => img.Admits old (some proposed)
  | _ => Before p old proposed img

private theorem ofStable {img : Image} (h : img.Stable old) : img.Admits old pending := by
  obtain ⟨live, durable⟩ := h
  simp [Image.Admits, live, durable, Permitted]

private theorem widen {img : Image} (h : img.Admits old none) : img.Admits old (some proposed) := by
  simpa [Image.Admits, Permitted] using
    And.intro (Or.inl (by simpa [Permitted] using h.1) : img.active = old ∨ proposed = img.active)
      (fun b member => (Or.inl (by simpa [Permitted] using h.2 b member) : b = old ∨ proposed = b))

theorem Window.admits (range : Window p old proposed img) : img.Admits old (some proposed) := by
  cases p <;> first | exact range | exact range.2 | exact widen range

private theorem Keeps.admits (keep : Keeps before after) (h : before.Admits old pending) : after.Admits old pending :=
  ⟨keep.1 ▸ h.1, fun b mem => h.2 b (keep.2.2 b mem)⟩

private theorem renamed {a b : Image} {m : Media inode} (synced : m.Synced h path new w) (prior : a.Admits old none)
    (active : b.active = m.durable h w) (survivors : ∀ z ∈ b.survivors, z = m.durable h w ∨ z ∈ a.survivors) :
    b.active = new ∧ b.Admits old (some new) := by
  have live := active.trans synced.2.2
  refine ⟨live, Or.inr (congrArg some live.symm), ?_⟩
  intro z member
  rcases survivors _ member with same | earlier
  · exact Or.inr (congrArg some (same.trans synced.2.2).symm)
  · exact (widen prior).2 z earlier

private theorem continued (prior : Before p old bytes a) (operand : Operand m dir bytes w p)
    (eff : Effect m p true w a b) (go : advance p x = some q) : Before q old bytes b := by
  cases p <;> simp only [advance, Option.some.injEq, reduceCtorEq] at go <;> first | contradiction | subst q
  all_goals try exact Keeps.admits eff prior
  all_goals try exact ⟨(show Keeps _ _ from eff).1.trans prior.1, Keeps.admits eff prior.2⟩
  rcases eff with ⟨wrong,_⟩ | ⟨active,_,survivors⟩
  · contradiction
  · exact renamed operand prior active survivors

private theorem stopped (prior : Before p old bytes a) (operand : Operand m dir bytes w p)
    (eff : Effect m p false w a b) : Window p old bytes b := by
  cases p <;> try exact Keeps.admits eff prior
  all_goals try exact ⟨(show Keeps _ _ from eff).1.trans prior.1, Keeps.admits eff prior.2⟩
  case rename =>
    rcases eff with ⟨_,kept⟩ | ⟨active,_,survivors⟩
    · exact widen (kept.admits prior)
    · exact (renamed operand prior active survivors).2
  case barrier =>
    rcases eff with ⟨_,kept⟩ | stable
    · exact ⟨kept.1.trans prior.1, kept.admits prior.2⟩
    · have h : b.Stable bytes := prior.1 ▸ stable
      refine ⟨h.1, Or.inr (congrArg some h.1.symm), ?_⟩
      intro value mem
      have same : value = bytes := by simpa [h.2] using mem
      exact Or.inr (congrArg some same.symm)

theorem Prefix.state (pc : Prefix dir bytes start p w) (ops : Primitives dir bytes start P image stop m)
    (startFrame : P start) (reserved : m.Private dir start) (valid : (image start).Stable old) :
    P w ∧ Operand m dir bytes w p ∧ Before p old bytes (image w) := by
  induction pc with
  | initial => exact ⟨startFrame, reserved, ofStable valid⟩
  | next prior ran go ih =>
    have receipt := ops.returned _ _ prior ih.1 ih.2.1
    rw [ran] at receipt
    obtain ⟨kept,eff,body⟩ := receipt
    unfold NextOperand at body
    rw [go] at body
    exact ⟨kept,body,continued ih.2.2 ih.2.1 eff go⟩

theorem interrupted (ops : Primitives dir bytes start P image stop m) (startFrame : P start)
    (reserved : m.Private dir start) (valid : (image start).Stable old)
    (pc : Prefix dir bytes start p w) (cut : stop (action dir bytes p) w observed) :
    P observed ∧ Window p old bytes (image observed) := by
  obtain ⟨pre, operand, saved⟩ := pc.state ops startFrame reserved valid
  obtain ⟨post, effect⟩ := ops.interrupted _ _ pc pre operand _ cut
  exact ⟨post, stopped saved operand effect⟩

private theorem execute (ops : Primitives dir bytes start P image stop m) (pc : Prefix dir bytes start p w)
    (pre : P w) (operand : Operand m dir bytes w p) (entry : Before p old bytes (image w)) :
    match remaining dir bytes p w with
    | .ok _ t => P t ∧ (image t).Stable bytes
    | .error _ t => P t ∧ (image t).Admits old (some bytes) := by
  have receipt := ops.returned _ _ pc pre operand
  cases ran : action dir bytes p w with
  | error err t =>
    rw [ran] at receipt
    rw [remaining]
    simpa only [Bind.bind, instMonadEIO._aux_13, EST.bind, ran] using
      And.intro receipt.1 (stopped entry operand receipt.2).admits
  | ok x t =>
    rw [ran] at receipt
    obtain ⟨frame, eff, body⟩ := receipt
    have result : remaining dir bytes p w = (match advance p x with
        | none => (pure () : IO Unit) | some q => remaining dir bytes q) t := by
      rw [remaining]
      simp only [Bind.bind, instMonadEIO._aux_13, EST.bind, ran]
      cases p <;> rfl
    rw [result]
    cases go : advance p x with
    | none =>
      cases p <;> simp only [advance, reduceCtorEq] at go
      rcases eff with ⟨wrong,_⟩ | stable
      · contradiction
      · exact ⟨frame,entry.1 ▸ stable⟩
    | some q =>
      unfold NextOperand at body
      rw [go] at body
      exact execute ops (.next pc ran go) frame body (continued entry operand eff go)
termination_by p.rank
decreasing_by exact smaller go

theorem bytes (ops : Primitives dir proposed w P image stop m) (start : P w)
    (reserved : m.Private dir w) (oldStable : (image w).Stable old) :
    match (native dir).publish proposed w with
    | .ok _ t => P t ∧ (image t).Stable proposed
    | .error _ t => P t ∧ (image t).Admits old (some proposed) := by
  rw [concrete]
  exact execute ops .initial start reserved (ofStable oldStable)

theorem publish (ops : Primitives dir (encode proposal) w P image stop m) (start : P w)
    (reserved : m.Private dir w) (oldStable : (image w).Stable (encode old)) (valid : proposal.Valid) :
    match ((NativeManifest.backend dir).publish proposal).run w with
    | .ok (.ok ()) t => P t ∧ (image t).Stable (encode proposal)
    | .ok (.error _) t | .error _ t => P t ∧ (image t).Admits (encode old) (some (encode proposal)) := by
  have run := bytes ops start reserved oldStable
  simp only [NativeManifest.backend, L0Manifest.backend, valid, ↓reduceIte]
  change (match (ExceptT.lift ((native dir).publish (encode proposal)) : ExceptT String IO Unit).run w with
    | .ok (.ok ()) t => _
    | .ok (.error _) t | .error _ t => _)
  simp only [ExceptT.lift, ExceptT.run, ExceptT.mk, Functor.map, instMonadEIO._aux_1, EST.bind]
  cases ran : (native dir).publish (encode proposal) w <;> rw [ran] at run <;> exact run

/-- Healthy positive reports concern the individual call at its exact
issued input, including the writer and directory descriptors. -/
def Healthy (dir : FilePath) (bytes : ByteArray) (origin : W) (P : W → Prop) (m : Media inode) :=
  ∀ p w, Prefix dir bytes origin p w → P w → Operand m dir bytes w p →
    ∃ x t, action dir bytes p w = .ok x t

private theorem completes {bytes : ByteArray} (ops : Primitives dir bytes origin P image stop m) (healthy : Healthy dir bytes origin P m)
    (pc : Prefix dir bytes origin p w) (pre : P w) (arg : Operand m dir bytes w p) :
    ∃ t, remaining dir bytes p w = .ok () t := by
  obtain ⟨x,t,ran⟩ := healthy _ _ pc pre arg
  have receipt := ops.returned _ _ pc pre arg
  rw [ran] at receipt
  have result : remaining dir bytes p w = (match advance p x with
      | none => (pure () : IO Unit) | some q => remaining dir bytes q) t := by
    rw [remaining]
    simp only [Bind.bind, instMonadEIO._aux_13, EST.bind, ran]
    cases p <;> rfl
  rw [result]
  cases go : advance p x with
  | none => exact ⟨t,rfl⟩
  | some q =>
    have body := receipt.2.2
    unfold NextOperand at body
    rw [go] at body
    exact completes ops healthy (.next pc ran go) receipt.1 body
termination_by p.rank
decreasing_by exact smaller go

theorem healthyPublish (ops : Primitives dir (encode proposal) w P image stop m)
    (healthy : Healthy dir (encode proposal) w P m) (start : P w) (reserved : m.Private dir w)
    (source : (image w).Stable (encode old)) (valid : proposal.Valid) :
    ∃ t, ((NativeManifest.backend dir).publish proposal).run w = .ok (.ok ()) t ∧ P t ∧
      (image t).Stable (encode proposal) := by
  obtain ⟨t,ran⟩ := completes ops healthy .initial start reserved
  rw [← concrete] at ran
  have result := bytes ops start reserved source
  rw [ran] at result
  refine ⟨t,?_,result⟩
  simp only [NativeManifest.backend, L0Manifest.backend, valid, ↓reduceIte]
  change (ExceptT.lift ((native dir).publish (encode proposal)) : ExceptT String IO Unit).run w = _
  simp [ExceptT.lift, ExceptT.run, ExceptT.mk, Functor.map, instMonadEIO._aux_1, EST.bind, ran]
  rfl

private theorem select {actual : ByteArray} (h : Permitted (encode old) (some (encode proposal)) actual)
    (oldValid : old.Valid) (newValid : proposal.Valid) :
    ∃ selected, (selected = old ∨ selected = proposal) ∧ selected.Valid ∧
      actual = encode selected ∧ decode actual = some selected := by
  rcases h with same | changed
  · exact ⟨old, .inl rfl, oldValid, same, same ▸ decode_encode oldValid⟩
  · have eq := (Option.some.inj changed).symm
    exact ⟨proposal, .inr rfl, newValid, eq, eq ▸ decode_encode newValid⟩

theorem liveSelected {current : Image} (h : current.Admits (encode old) (some (encode proposal)))
    (oldValid : old.Valid) (newValid : proposal.Valid) :
    ∃ selected, (selected = old ∨ selected = proposal) ∧ selected.Valid ∧
      current.active = encode selected ∧ decode current.active = some selected :=
  select h.1 oldValid newValid

/-- The booted active value is selected by the actual surviving name.
The witness is ready for NativeManifest.reopen and recoverAt. -/
theorem restartSelected {observed current : Image} (h : observed.Admits (encode old) (some (encode proposal)))
    (booted : current.active ∈ observed.survivors) (oldValid : old.Valid) (newValid : proposal.Valid) :
    ∃ selected, (selected = old ∨ selected = proposal) ∧ selected.Valid ∧
      current.active = encode selected ∧ decode current.active = some selected :=
  select (h.2 current.active booted) oldValid newValid

/-- Consume the booted selection in the real typed manifest read and
directory barrier. Failure retains this boot's bytes for a retry. -/
theorem reopenRestored (ops : NativeManifest.Primitives dir P image) (pre : P w)
    {observed : Image} (cut : observed.Admits (encode old) (some (encode proposal)))
    (booted : (image w).active ∈ observed.survivors) (oldValid : old.Valid) (newValid : proposal.Valid) :
    ∃ selected, (selected = old ∨ selected = proposal) ∧ selected.Valid ∧ (image w).active = encode selected ∧
      match (NativeManifest.backend dir).reopen.run w with
      | .ok (.ok value) t => value = selected ∧ P t ∧ image t = (image w).barrier ∧ (image t).Stable (encode value)
      | .ok (.error _) t | .error _ t => P t ∧ (image t = image w ∨ image t = (image w).barrier) := by
  obtain ⟨selected, choice, valid, projection, _⟩ := restartSelected cut booted oldValid newValid
  exact ⟨selected, choice, valid, projection, NativeManifest.reopen ops pre projection valid⟩

end ExperimentalL0.NativeManifestPublish
