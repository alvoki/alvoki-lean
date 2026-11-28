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

/-- A descriptor acquired from the protected name, with the caller's
read guarantee for its bound bytes. -/
def AcquiredSource (guarantee : IO.FS.Handle → ByteArray → Prop)
    (ns : TableNamespace σ) (s : σ) (id : UInt64)
    (world : Void IO.RealWorld) : Prop :=
  ∃ (handle : IO.FS.Handle) (inodeAt : IO.FS.Handle → Option ns.inode)
    (checked entered : Void IO.RealWorld) (metadata : IO.FS.Metadata),
    (nativeTableStat (tablePath ns.directory id)).run world = .ok (.ok metadata) checked ∧
    isTableFile metadata = true ∧
    IO.FS.Handle.mk (tablePath ns.directory id) .read checked = .ok handle entered ∧
    inodeAt handle = ns.names s (tablePath ns.directory id) ∧
    ∀ identity bytes, inodeAt handle = some identity → ns.contents s identity = some bytes →
      guarantee handle bytes

abbrev HealthySource {σ : Type} := AcquiredSource (σ := σ) nativeReadPrimitives.ReadsExactly
/-- The healthy-recovery interpreter evaluates the native table check. -/
structure Interpretation (ops : Tables (StorageM σ)) (selected : σ → Selected)
    (ns : TableNamespace σ) where
  world : σ → Void IO.RealWorld
  advance : σ → Void IO.RealWorld → σ
  checkSchedule : ∀ id, ops.check id =
    call world advance (nativeTableAt ns.directory id (fun _ => pure ()))
  readFrame : ∀ s reached, selected (advance s reached) = selected s ∧
    ns.Keeps s (advance s reached) (selected s).tables

/-- On the product carrier, read steps preserve the durable table namespace
and selected image by construction. -/
theorem productFrame (ns : TableNamespace σ) (selected : σ → Selected)
    (s : Void IO.RealWorld × σ) (reached : Void IO.RealWorld) :
    (selected ∘ Prod.snd) (reached, s.2) = (selected ∘ Prod.snd) s ∧
      ns.storage.Keeps s (reached, s.2) (selected s.2).tables :=
  ⟨rfl, fun _ _ _ _ _ name content => ⟨name, content⟩⟩

/-- Interpret the recovery check on the old storage carrier. Read callbacks
on public handles are verified through NativeRead. -/
def product (ns : TableNamespace σ) (selected : σ → Selected)
    (ops : Tables (StorageM (Void IO.RealWorld × σ)))
    (schedule : ∀ id, ops.check id = call Prod.fst (fun s reached => (reached, s.2))
      (nativeTableAt ns.directory id (fun _ => pure ()))) :
    Interpretation ops (selected ∘ Prod.snd) ns.storage where
  world := Prod.fst
  advance s reached := (reached, s.2)
  checkSchedule := schedule
  readFrame := productFrame ns selected

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

end ExperimentalL0.NativeTableReads
