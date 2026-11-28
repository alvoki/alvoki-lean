import Alvoki.Experiments.L0.DurableCatalog
import Alvoki.Experiments.L0.Refinement

namespace ExperimentalL0.NativeTableReads
open ImmutableSSTable

/-- Interpret one native read. The returned world is installed on every
outcome, including an outer IO failure. -/
def call (world : σ → Void IO.RealWorld) (advance : σ → Void IO.RealWorld → σ)
    (action : ExceptT String IO α) : StorageM σ α := fun s =>
  match action.run (world s) with
  | .ok (.ok value) after => .ok value (advance s after)
  | .ok (.error error) after => .error error (advance s after)
  | .error error after => .error (toString error) (advance s after)

/-- Healthy stat and acquire reports on the protected table name, with
bounded exact reads for the chosen immutable inode. -/
def HealthySource (ns : TableNamespace σ) (s : σ) (id : UInt64)
    (world : Void IO.RealWorld) : Prop :=
  ∃ (handle : IO.FS.Handle) (inodeAt : IO.FS.Handle → Option ns.inode)
    (checked entered : Void IO.RealWorld) (metadata : IO.FS.Metadata),
    (nativeTableStat (tablePath ns.directory id)).run world = .ok (.ok metadata) checked ∧
    isTableFile metadata = true ∧
    IO.FS.Handle.mk (tablePath ns.directory id) .read checked = .ok handle entered ∧
    inodeAt handle = ns.names s (tablePath ns.directory id) ∧
    ∀ identity bytes, inodeAt handle = some identity → ns.contents s identity = some bytes →
      nativeReadPrimitives.ReadsExactly handle bytes

/-- Both table callbacks evaluate the native scope once. The carrier
update accounts only for the reached IO world. -/
structure Interpretation (ops : Tables (StorageM σ)) (selected : σ → Selected)
    (ns : TableNamespace σ) where
  world : σ → Void IO.RealWorld
  advance : σ → Void IO.RealWorld → σ
  checkSchedule : ∀ id, ops.check id =
    call world advance (nativeTableAt ns.directory id (fun _ => pure ()))
  lookupSchedule : ∀ id key, ops.lookup id key =
    call world advance (nativeTableAt ns.directory id (·.lookup key))
  readFrame : ∀ s reached, selected (advance s reached) = selected s ∧
    ns.Keeps s (advance s reached) (selected s).tables
  lookupPrimitives : ∀ s id key value reached,
    (nativeTableAt ns.directory id (·.lookup key)).run (world s) = .ok (.ok value) reached →
    HealthySource ns s id (world s)

/-- On the product carrier, read steps preserve the durable table namespace
and selected image by construction. -/
theorem productFrame (ns : TableNamespace σ) (selected : σ → Selected)
    (s : Void IO.RealWorld × σ) (reached : Void IO.RealWorld) :
    (selected ∘ Prod.snd) (reached, s.2) = (selected ∘ Prod.snd) s ∧
      ns.storage.Keeps s (reached, s.2) (selected s.2).tables :=
  ⟨rfl, fun _ _ _ _ _ name content => ⟨name, content⟩⟩

def productTables (ns : TableNamespace σ)
    (create : Rows → StorageM (Void IO.RealWorld × σ) UInt64) :
    Tables (StorageM (Void IO.RealWorld × σ)) where
  create
  check id := call Prod.fst (fun s reached => (reached, s.2))
    (nativeTableAt ns.directory id (fun _ => pure ()))
  lookup id key := call Prod.fst (fun s reached => (reached, s.2))
    (nativeTableAt ns.directory id (·.lookup key))

def product (ns : TableNamespace σ) (selected : σ → Selected)
    (create : Rows → StorageM (Void IO.RealWorld × σ) UInt64)
    (primitives : ∀ (s : Void IO.RealWorld × σ) id key value reached,
      (nativeTableAt ns.directory id (·.lookup key)).run s.1 = .ok (.ok value) reached →
      HealthySource ns.storage s id s.1) :
    Interpretation (productTables ns create) (selected ∘ Prod.snd) ns.storage where
  world := Prod.fst
  advance s reached := (reached, s.2)
  checkSchedule _ := rfl
  lookupSchedule _ _ := rfl
  readFrame := productFrame ns selected
  lookupPrimitives := primitives

variable {σ : Type} {ops : Tables (StorageM σ)} {selected : σ → Selected} {ns : TableNamespace σ}

theorem Interpretation.checkEffect (i : Interpretation ops selected ns) (s : σ) (id : UInt64) :
    match ops.check id s with
    | .ok _ after | .error _ after => selected after = selected s := by
  rw [i.checkSchedule]
  cases ran : (nativeTableAt ns.directory id (fun _ => pure ())).run (i.world s) with
  | error error reached => simpa [call, ran] using (i.readFrame s reached).1
  | ok result reached =>
    cases result <;> simpa [call, ran] using (i.readFrame s reached).1

theorem Interpretation.checkHealthy {id : UInt64} (i : Interpretation ops selected ns)
    (bound : ns.Bound s id rows) (healthy : HealthySource ns s id (i.world s)) :
    ∃ after, ops.check id s = .ok () after ∧
      ns.Keeps s after (selected s).tables := by
  obtain ⟨handle, inodeAt, _, entered, _, stat, regular, acquired, picked, reads⟩ := healthy
  have ran := ns.scopedCheck bound handle stat regular acquired inodeAt picked reads
  exact ⟨i.advance s entered, by simp [i.checkSchedule, call, ran], (i.readFrame s entered).2⟩

theorem Interpretation.lookupEffect (i : Interpretation ops selected ns)
    (catalog : ns.Represents s (selected s).tables) (id key : UInt64)
    (bound : (selected s).tables id = some rows) :
    match ops.lookup id key s with
    | .ok result after => result = lookupRows rows key ∧ selected after = selected s ∧
        ns.Represents after (selected after).tables
    | .error _ after => selected after = selected s ∧ ns.Represents after (selected after).tables := by
  rw [i.lookupSchedule]
  cases ran : (nativeTableAt ns.directory id (·.lookup key)).run (i.world s) with
  | error error reached =>
    obtain ⟨frame, keeps⟩ := i.readFrame s reached
    have kept : ns.Represents (i.advance s reached) (selected (i.advance s reached)).tables :=
      frame.symm ▸ catalog.frame keeps
    simpa [call, ran] using And.intro frame kept
  | ok response reached =>
    obtain ⟨frame, keeps⟩ := i.readFrame s reached
    have kept : ns.Represents (i.advance s reached) (selected (i.advance s reached)).tables :=
      frame.symm ▸ catalog.frame keeps
    cases response with
    | error error => simpa [call, ran] using And.intro frame kept
    | ok value =>
      obtain ⟨handle, inodeAt, _, _, _, stat, regular, acquired, picked, reads⟩ :=
        i.lookupPrimitives s id key value reached ran
      have result := ns.scopedLookup (catalog id rows bound) handle key stat regular acquired inodeAt picked reads
      have same := Except.ok.inj (EST.Out.ok.inj (ran.symm.trans result)).1
      simpa [call, ran] using And.intro same (And.intro frame kept)

/-- Get needs only the reached lookup effects and the durable catalog. -/
theorem Interpretation.get {components : Components (StorageM σ)}
    (reads : Interpretation components.tables selected ns)
    (catalog : ns.Represents s (selected s).tables)
    (prior : Installed session (selected s) history) (key : UInt64) :
    match ExperimentalL0.get components session key s with
    | .ok value after => value = denote history key ∧ selected after = selected s ∧
        ns.Represents after (selected after).tables
    | .error _ after => selected after = selected s ∧ ns.Represents after (selected after).tables :=
  get_refines_from (fun s => ns.Represents s (selected s).tables)
    (fun _ id key _ ready binding => reads.lookupEffect ready id key binding)
    s catalog session prior key

end ExperimentalL0.NativeTableReads
