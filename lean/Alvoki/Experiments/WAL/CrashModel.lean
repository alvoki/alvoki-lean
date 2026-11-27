import Alvoki.Experiments.WAL.Recovery

/-! Primitive filesystem outcomes for the single-segment experiment. -/

namespace WalRecoverySlice.Persistence

structure FileImage where
  live : Bytes
  durable : Bytes
  deriving DecidableEq

structure Image where
  data : FileImage
  slot0 : FileImage
  slot1 : FileImage

def Image.marker (image : Image) (slot : Nat) : FileImage :=
  if slot = 0 then image.slot0 else image.slot1

def Image.withMarker (image : Image) (slot : Nat) (file : FileImage) : Image :=
  if slot = 0 then { image with slot0 := file } else { image with slot1 := file }

def FileImage.powerLoss (image : FileImage) : FileImage :=
  { image with live := image.durable }

def Image.powerLoss (image : Image) : Image :=
  ⟨image.data.powerLoss, image.slot0.powerLoss, image.slot1.powerLoss⟩

inductive WalFile where
  | data
  | slot0
  | slot1
  deriving DecidableEq

/-- Background settlement of one entire file's current visible contents and length. -/
def WalFile.settle (file : WalFile) (image : Image) : Image :=
  match file with
  | .data => { image with data.durable := image.data.live }
  | .slot0 => { image with slot0.durable := image.slot0.live }
  | .slot1 => { image with slot1.durable := image.slot1.live }

/-- A background step settles one file's complete visible contents and
length independently of the other files. No visible bytes or client response
change. In particular, a completed live truncate can become durable. -/
inductive Writeback : Image → Image → Prop where
  | data (before : Image) : Writeback before (WalFile.data.settle before)
  | slot0 (before : Image) : Writeback before (WalFile.slot0.settle before)
  | slot1 (before : Image) : Writeback before (WalFile.slot1.settle before)

inductive Abort where
  | error
  | interrupted

abbrev M := ExceptT String (EStateM Unit Image)

def Abort.result {α : Type} (abort : Abort) (after : Image) : EStateM.Result Unit Image (Except String α) :=
  match abort with
  | .error => .ok (.error "primitive I/O error") after
  | .interrupted => .error () after

/-- Choices for persistence before a successful sync. A prefix denotes a short
physical write. A torn marker may also retain a full-length checksum-invalid image. -/
inductive Written where
  | old
  | short (length : Nat)
  | complete

def Written.bytes (written : Written) (write : Bytes → Bytes → Bytes) (old requested : Bytes) : Bytes :=
  match written with
  | .old => old
  | .short count => write old (requested.take count)
  | .complete => write old requested

/-- A successful write has full visible bytes. An ambiguous result can have no
effect, short visible bytes, or a complete visible write. Durability is independent. -/
inductive Write where
  | before (abort : Abort)
  | torn (visible : Nat) (durable : Written) (abort : Abort)
  | full (durable : Written) (abort : Option Abort)

def Write.result (outcome : Write) (write : Bytes → Bytes → Bytes) (requested : Bytes)
    (image : Image) (file : FileImage) (replace : FileImage → Image) :
    EStateM.Result Unit Image (Except String Unit) :=
  match outcome with
  | .before abort => abort.result image
  | .torn count persisted abort =>
    abort.result (replace ⟨write file.live (requested.take count), persisted.bytes write file.durable requested⟩)
  | .full persisted none =>
    .ok (.ok ()) (replace ⟨write file.live requested, persisted.bytes write file.durable requested⟩)
  | .full persisted (some abort) =>
    abort.result (replace ⟨write file.live requested, persisted.bytes write file.durable requested⟩)

inductive Primitive where
  | before (abort : Abort)
  | after (abort : Option Abort)

def Primitive.syncResult (outcome : Primitive) (image : Image) (file : FileImage) (replace : FileImage → Image) :
    EStateM.Result Unit Image (Except String Unit) :=
  match outcome with
  | .before abort => abort.result image
  | .after none => .ok (.ok ()) (replace { file with durable := file.live })
  | .after (some abort) => abort.result (replace { file with durable := file.live })

/-- A full-length torn slot can contain arbitrary fields whose stored hash fails validation.
This admits, in particular, the new prefix plus old suffix of an in-place overwrite. -/
structure DamagedMarker where
  magic : UInt8
  format : UInt8
  generation : UInt8
  sequence : UInt8
  high : UInt8
  low : UInt8
  check : Bytes
  checkLength : check.length = 8
  damaged : check ≠ checksumBytes [magic, format, generation, sequence, high, low]

def DamagedMarker.bytes (m : DamagedMarker) : Bytes :=
  [m.magic, m.format, m.generation, m.sequence, m.high, m.low] ++ m.check

def markerFragment (residue : Option DamagedMarker) (_old fragment : Bytes) : Bytes :=
  if fragment.length = markerSize then fragment else (residue.map DamagedMarker.bytes).getD fragment

structure Effects where
  appendData : Write
  dataSync : Primitive
  writeMarker : Write
  markerSync : Nat → Primitive
  tornSlot : Option DamagedMarker := none
  truncate : Primitive := .after none
  readDataError : Bool := false
  readMarkerError : Option Nat := none

/-- The same executable schedules can be run against independent primitive effects.
An outer interruption has a reached image and no API response. -/
def ops (effects : Effects) : Ops M where
  append bytes := fun image =>
    effects.appendData.result List.append bytes image image.data (fun file => { image with data := file })
  syncData := fun image =>
    effects.dataSync.syncResult image image.data (fun file => { image with data := file })
  writeMarker slot bytes := fun image =>
    effects.writeMarker.result (markerFragment effects.tornSlot) bytes image (image.marker slot) (image.withMarker slot)
  syncMarker slot := fun image =>
    (effects.markerSync slot).syncResult image (image.marker slot) (image.withMarker slot)
  readData := fun image =>
    .ok (if effects.readDataError then .error "data read error" else .ok image.data.live) image
  readMarker slot := fun image =>
    .ok (if effects.readMarkerError == some slot then .error "marker read error" else .ok (image.marker slot).live) image
  truncate count := fun image =>
    match effects.truncate with
    | .before abort => abort.result image
    | .after abort =>
      let repaired := { image with data.live := image.data.live.take count }
      match abort with
      | none => .ok (.ok ()) repaired
      | some fault => fault.result repaired

/-- Physical residue of an append that stopped before the data barrier.
A torn frame retains the four header bytes and their eight-byte checksum. -/
inductive DataResidue where
  | prefix (count : Nat)
  | torn (observed trailer : Bytes)

def DataResidue.bytes (residue : DataResidue) (requested : Bytes) : Bytes :=
  match residue with
  | .prefix n => requested.take n
  | .torn observed trailer => requested.take 12 ++ observed ++ trailer

def DataResidue.SameExtent (residue : DataResidue) (submitted : Bytes) : Prop :=
  match residue with
  | .prefix _ => True
  | .torn observed trailer => observed.length = submitted.length ∧ trailer.length = 8

/-- Log-only recovery needs a checksum mismatch to identify a full-width
corrupt frame. Boundary recovery ignores any suffix beyond its intact marker. -/
def DataResidue.Detected (residue : DataResidue) (seq : Nat) : Prop :=
  match residue with
  | .prefix _ => True
  | .torn observed trailer =>
    trailer ≠ checksumBytes ([42, 1, seq.toUInt8, observed.length.toUInt8] ++ observed)

structure TornAppend where
  live : DataResidue
  durable : DataResidue
  abort : Abort

def TornAppend.SameExtent (cut : TornAppend) (submitted : Bytes) : Prop :=
  cut.live.SameExtent submitted ∧ cut.durable.SameExtent submitted

def TornAppend.Detected (cut : TornAppend) (seq : Nat) : Prop :=
  cut.live.Detected seq ∧ cut.durable.Detected seq

def TornAppend.after (cut : TornAppend) (s : Image) (requested : Bytes) : Image :=
  { s with data := ⟨s.data.live ++ cut.live.bytes requested, s.data.durable ++ cut.durable.bytes requested⟩ }

def TornAppend.ops (cut : TornAppend) : Ops M :=
  let callbacks := Persistence.ops {
    appendData := .full .old none, dataSync := .after none,
    writeMarker := .full .old none, markerSync := fun _ => .after none }
  { callbacks with append := fun requested s => cut.abort.result (cut.after s requested) }

/-- Primitive effects used by append, with a torn first write when reported. -/
def appendPrimitives (effects : Effects) (cut : Option TornAppend) : Ops M :=
  match cut with
  | none => ops effects
  | some residue => residue.ops

abbrev Result (α : Type) := EStateM.Result Unit Image (Except String α)

def reached {α : Type} : Result α → Image
  | .ok _ image | .error _ image => image

def acknowledged {α : Type} : Result α → Option α
  | .ok (.ok value) _ => some value
  | _ => none

/-- A clean append entry obtained by a successful append or successful repair.
The live and durable data both end at the cursor. -/
def AtEnd (image : Image) (cursor : Cursor) (prior : Bytes) : Prop :=
  image.data = ⟨prior, prior⟩ ∧ cursor.endPos = prior.length

end WalRecoverySlice.Persistence
