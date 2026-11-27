import Alvoki.Experiments.WAL.Segmented.Protocol
import Alvoki.Experiments.WAL.Proofs.Client
import Alvoki.Experiments.WAL.Writeback

/-! File observations used to interpret the shared segmented WAL protocol. -/

namespace WalRecoverySlice.Segmented.Model

open WalRecoverySlice
abbrev DataImage := Persistence.Image
abbrev Abort := Persistence.Abort
abbrev Primitive := Persistence.Primitive

/-- Segment identity is independent of its current name. Retired objects can
remain in the mathematical map after unlink, but cannot be opened by name. -/
structure Disk where
  liveControl : Option Control := none
  durableControl : Option Control := none
  staged : Option Control := none
  stagedDurable : Option Control := none
  liveNames : List Nat := []
  durableNames : List Nat := []
  segment : Nat → DataImage := fun _ => Persistence.freshImage
  cursor : Nat → Cursor := fun _ => {}

def Disk.powerLoss (disk : Disk) : Disk :=
  { disk with
    liveControl := disk.durableControl
    staged := disk.stagedDurable
    liveNames := disk.durableNames
    segment := fun id => (disk.segment id).powerLoss
    cursor := fun _ => {} }

def Disk.setSegment (disk : Disk) (id : Nat) (image : DataImage) (cursor : Cursor) : Disk :=
  { disk with segment := fun i => if i = id then image else disk.segment i
              cursor := fun i => if i = id then cursor else disk.cursor i }

/-- Settle one file of an existing child image without changing its name or cursor. -/
def Disk.writeback (disk : Disk) (id : Nat) (file : Persistence.WalFile) : Disk :=
  { disk with segment := fun i => if i = id then file.settle (disk.segment i) else disk.segment i }

def Disk.syncRoot (disk : Disk) : Disk :=
  { disk with durableControl := disk.liveControl, durableNames := disk.liveNames }

def Disk.prepare (disk : Disk) (id : Nat) (persist : Bool) : Disk :=
  let name := fun names : List Nat => id :: names.filter (· != id)
  { (disk.setSegment id Persistence.freshImage {}) with
    liveNames := name disk.liveNames
    durableNames := if persist then name disk.durableNames else disk.durableNames }

def Disk.remove (disk : Disk) (id : Nat) (persist : Bool) : Disk :=
  { disk with
    liveNames := disk.liveNames.filter (· != id)
    durableNames := if persist then disk.durableNames.filter (· != id) else disk.durableNames }

def Disk.stage (disk : Disk) (control : Control) (persist : Bool) : Disk :=
  { disk with staged := some control,
              stagedDurable := if persist then some control else disk.stagedDurable }

def Disk.syncStage (disk : Disk) : Disk :=
  { disk with stagedDurable := disk.staged }

def Disk.rename (disk : Disk) (control : Control) (persist : Bool) : Disk :=
  { disk with liveControl := some control, staged := none,
              durableControl := if persist then some control else disk.durableControl }

/-- A namespace mutation can report a failure after becoming visible, with
its durable effect independently present or absent until a directory sync. -/
inductive NamespaceEffect where
  | before (abort : Abort)
  | after (persist : Bool) (failure : Option Abort)

/-- Choices are indexed by the actual sequence of invoked callbacks.
Each child runs the single-file primitives and has its own interleaved
writeback schedule. A selected tear replaces the ordinary append primitive. -/
structure Effects where
  prepare : Nat → Nat → NamespaceEffect := fun _ _ => .after false none
  root : Nat → Primitive := fun _ => .after none
  stage : Nat → NamespaceEffect := fun _ => .after false none
  syncControl : Nat → Primitive := fun _ => .after none
  rename : Nat → NamespaceEffect := fun _ => .after false none
  controlRead : Nat → Option Abort := fun _ => none
  listing : Nat → Option Abort := fun _ => none
  openSegment : Nat → Nat → Persistence.Effects := fun _ _ => Persistence.healthyReopen
  appendSegment : Nat → Nat → Persistence.Effects := fun _ _ =>
    { appendData := .full .old none, dataSync := .after none,
      writeMarker := .full .old none, markerSync := fun _ => .after none }
  reopenWritebacks : Nat → Nat → Persistence.WritebackSchedule := fun _ _ => {}
  appendWritebacks : Nat → Nat → Persistence.WritebackSchedule := fun _ _ => {}
  tornAppend : Nat → Nat → (policy : Policy) → (cursor : Cursor) → (payload : Bytes) →
    Option {cut : Persistence.TornAppend //
      cut.SameExtent payload ∧ (policy = .logOnly → cut.Detected cursor.nextSeq)} := fun _ _ _ _ _ => none
  remove : Nat → Nat → NamespaceEffect := fun _ _ => .after false none

def healthy : Effects := {}

def openChild (effects : Effects) (clock id : Nat) (policy : Policy) : Persistence.M Decoded :=
  WalRecoverySlice.reopen
    (Persistence.scheduledOps (Persistence.ops (effects.openSegment clock id)) (effects.reopenWritebacks clock id))
    policy

def Effects.appendRun (effects : Effects) (clock id : Nat) (policy : Policy) (cursor : Cursor)
    (payload : Bytes) : Persistence.M Cursor :=
  let cut := (effects.tornAppend clock id policy cursor payload).map Subtype.val
  let plain := Persistence.appendPrimitives (effects.appendSegment clock id) cut
  appendBatch (Persistence.scheduledOps plain (effects.appendWritebacks clock id)) policy cursor payload

structure State where
  disk : Disk := {}
  step : Nat := 0

abbrev M := ExceptT String (EStateM Unit State)
abbrev Result (α : Type) := EStateM.Result Unit State (Except String α)

def reached {α : Type} : Result α → State
  | .ok _ reached | .error _ reached => reached

def returned {α : Type} : Result α → Option α
  | .ok (.ok value) _ => some value
  | _ => none

def State.tick (state : State) : State := {state with step := state.step + 1}

def outcome {α : Type} (failed : Option Abort) (value : α) (state : State) : Result α :=
  match failed with
  | none => .ok (.ok value) state
  | some .error => .ok (.error "primitive I/O error") state
  | some .interrupted => .error () state

def namespaceChange (effect : NamespaceEffect) (change : Disk → Bool → Disk) (state : State) : Result Unit :=
  match effect with
  | .before fault => outcome (some fault) () state.tick
  | .after persist failed => outcome failed () {state.tick with disk := change state.disk persist}

def barrier (effect : Primitive) (change : Disk → Disk) (state : State) : Result Unit :=
  match effect with
  | .before fault => outcome (some fault) () state.tick
  | .after failed => outcome failed () {state.tick with disk := change state.disk}

def read (failed : Option Abort) (value : Except String α) (state : State) : Result α :=
  match failed with
  | none => .ok value state.tick
  | some .error => .ok (.error "primitive I/O error") state.tick
  | some .interrupted => .error () state.tick

/-- Every child callback addresses a currently named segment, runs the same
single-file action, and retains its reached bytes on success, EIO, or stop. -/
def child (state : State) (id : Nat) (run : Persistence.M α) (nextCursor : α → Cursor) (result : α → β) :
    Result β :=
  if id ∈ state.disk.liveNames then
    let disk := state.disk
    match run.run (disk.segment id) with
    | .ok (.ok value) image =>
      .ok (.ok (result value)) {state.tick with disk := disk.setSegment id image (nextCursor value)}
    | .ok (.error error) image =>
      .ok (.error error) {state.tick with disk := disk.setSegment id image (disk.cursor id)}
    | .error _ image =>
      .error () {state.tick with disk := disk.setSegment id image (disk.cursor id)}
  else
    .ok (.error "missing segment") state.tick

def ops (effects : Effects) : Segmented.Ops M where
  prepareSegment _ id := fun state =>
    namespaceChange (effects.prepare state.step id) (fun disk persist => disk.prepare id persist) state
  syncRoot := fun state => barrier (effects.root state.step) Disk.syncRoot state
  stageControl value := fun state =>
    namespaceChange (effects.stage state.step) (fun disk persist => disk.stage value persist) state
  syncControl := fun state => barrier (effects.syncControl state.step) Disk.syncStage state
  renameControl := fun state => match state.disk.staged with
    | none => .ok (.error "missing staged control") state.tick
    | some value =>
      namespaceChange (effects.rename state.step) (fun disk persist => disk.rename value persist) state
  readControl := fun state =>
    read (effects.controlRead state.step)
      (match state.disk.liveControl with | some control => .ok control | none => .error "missing control") state
  openSegment policy id := fun state =>
    child state id (openChild effects state.step id policy) Decoded.cursor Decoded.batches
  appendSegment policy id payload := fun state =>
    child state id (effects.appendRun state.step id policy
      (state.disk.cursor id) payload) (fun cursor => cursor) (fun _ => ())
  listSegments := fun state => read (effects.listing state.step) (.ok state.disk.liveNames) state
  removeSegment id := fun state =>
    namespaceChange (effects.remove state.step id) (fun disk persist => disk.remove id persist) state

end WalRecoverySlice.Segmented.Model
