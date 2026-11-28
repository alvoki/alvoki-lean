import Alvoki.Experiments.L0.Basic

namespace ExperimentalL0.Model
open WalRecoverySlice.Segmented

/-- Names are list indices. Existing tables never change, including orphaned
tables left by a failed flush. The WAL view is the retained byte history. -/
structure Image where
  view : Contract.View := ⟨0, []⟩
  version : L0Manifest.Version := L0Manifest.Version.empty
  catalog : List Rows := []

inductive Outcome where
  | ok
  | beforeEffect
  | afterEffect
  deriving DecidableEq

structure Faults where
  append : Outcome := .ok
  create : Outcome := .ok
  publish : Outcome := .ok
  openManifest : Bool := true
  openWal : Bool := true

abbrev M := EStateM String Image

def effect (outcome : Outcome) (update : Image → Image) (value : Image → α) : M α :=
  fun image => match outcome with
    | .ok => .ok (value image) (update image)
    | .beforeEffect => .error "interrupted before effect" image
    | .afterEffect => .error "interrupted after effect" (update image)

def Image.append (image : Image) (batch : Contract.Batch) : Image :=
  {image with view := image.view.append batch}

def Image.store (image : Image) (rows : Rows) : Image :=
  {image with catalog := image.catalog ++ [rows]}

def Image.select (image : Image) (version : L0Manifest.Version) : Image :=
  {image with version := version}

def tableOps (outcome : Outcome) : Tables M where
  create rows := fun image =>
    if image.catalog.length < UInt64.size then
      effect outcome (·.store rows) (fun s => s.catalog.length.toUInt64) image
    else .error "table IDs exhausted" image
  check id := fun image =>
    if id.toNat < image.catalog.length then .ok () image else .error "missing table" image
  lookup id key := fun image =>
    match image.catalog[id.toNat]? with
    | some rows => .ok (lookupRows rows key) image
    | none => .error "missing table" image

/-- An interrupted primitive leaves a selected image, either the prior image
or its completed effect. Offline recovery only reads that selection. At the
component boundary the same choices represent power loss and lost replies. -/
def components (faults : Faults := {}) : Components M where
  append batch := effect faults.append (·.append batch) (fun _ => ())
  scan := fun image => .ok image.view image
  reopenWal := fun image =>
    if faults.openWal then .ok image.view image else .error "WAL reopen failed" image
  manifest := {
    publish := fun version => effect faults.publish (·.select version) (fun _ => ())
    reopen := fun image =>
      if faults.openManifest then .ok image.version image else .error "open failed" image
  }
  tables := tableOps faults.create

end ExperimentalL0.Model
