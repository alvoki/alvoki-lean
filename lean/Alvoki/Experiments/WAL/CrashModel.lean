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

inductive Abort where
  | error
  | interrupted

abbrev M := ExceptT String (EStateM Unit Image)

def Abort.result (abort : Abort) (after : Image) : EStateM.Result Unit Image (Except String Unit) :=
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

/-- A full-length torn slot can contain arbitrary fields whose check byte fails.
This admits, in particular, the new prefix plus old suffix of an in-place overwrite. -/
structure DamagedMarker where
  magic : UInt8
  format : UInt8
  generation : UInt8
  sequence : UInt8
  high : UInt8
  low : UInt8
  check : UInt8
  damaged : check ≠ (checksum [magic, format, generation, sequence, high, low]).toUInt8

def DamagedMarker.bytes (m : DamagedMarker) : Bytes :=
  [m.magic, m.format, m.generation, m.sequence, m.high, m.low, m.check]

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
