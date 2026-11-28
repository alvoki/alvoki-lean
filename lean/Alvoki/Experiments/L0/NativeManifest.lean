import Alvoki.Experiments.DurableBlob.FileRead
import Alvoki.Experiments.Manifest.Proofs
import Alvoki.Experiments.DurableBlob.Proofs

namespace ExperimentalL0.NativeManifest
open System DurableBlob L0Manifest

abbrev World := FileRead.World

structure Primitives (dir : FilePath) (owned : World → Prop) (image : World → Image) where
  file : FileRead.Primitives (dir / "BLOB") owned image Image.active
  directory : IO.FS.Handle → World → Prop
  openDirectory : ∀ w, owned w → FileRead.Effect owned image (IO.FS.Handle.mk dir .read)
    (fun _ h after => directory h after) w
  sync : ∀ h w, owned w → directory h w →
    match syncHandle h w with
    | .ok _ t => owned t ∧ image t = (image w).barrier
    | .error _ t => owned t ∧ (image t = image w ∨ image t = (image w).barrier)

/-- This backend is definitionally the manifest field assembled by the L0
native callback. Native IO errors and typed decode errors remain distinct. -/
def backend (dir : FilePath) : Backend (ExceptT String IO) Version :=
  let raw := DurableBlob.native dir
  L0Manifest.backend id {
    publish := fun bytes => liftM (raw.publish bytes)
    reopen := liftM raw.reopen }

theorem reopenBytes (p : Primitives dir P image) (start : P w) :
    match (DurableBlob.native dir).reopen w with
    | .ok value t => P t ∧ value = (image w).active ∧ image t = (image w).barrier
    | .error _ t => P t ∧ (image t = image w ∨ image t = (image w).barrier) := by
  rw [native_reopen_schedule]
  simp only [Bind.bind, instMonadEIO._aux_13, EST.bind]
  have read := FileRead.readBinFile p.file start
  unfold FileRead.Effect at read
  cases byteRun : IO.FS.readBinFile (dir / "BLOB") w with
  | error e t =>
    rw [byteRun] at read
    exact ⟨read.1, Or.inl read.2⟩
  | ok bytes t =>
    rw [byteRun] at read
    have opened := p.openDirectory t read.1
    unfold FileRead.Effect at opened
    dsimp only
    cases dirRun : IO.FS.Handle.mk dir .read t with
    | error e u =>
      rw [dirRun] at opened
      exact ⟨opened.1, Or.inl (opened.2.trans read.2.1)⟩
    | ok h u =>
      rw [dirRun] at opened
      have synced := p.sync h u opened.1 opened.2.2
      have same := opened.2.1.trans read.2.1
      dsimp only
      cases syncRun : syncHandle h u with
      | error e v =>
        rw [syncRun, same] at synced
        exact synced
      | ok _ v =>
        rw [syncRun, same] at synced
        exact ⟨synced.1, read.2.2, synced.2⟩

/-- Exact observed response from the byte backend. A filesystem error is
preserved in the outer channel. Malformed live bytes become a typed error
after the directory was synced. -/
theorem decodeReached (dir : FilePath) (w : World) :
    (backend dir).reopen.run w =
      match (DurableBlob.native dir).reopen w with
      | .error e t => .error e t
      | .ok bytes t =>
        match L0Manifest.decode bytes with
        | some v => .ok (.ok v) t
        | none => .ok (.error "invalid L0 manifest") t := by
  unfold backend L0Manifest.backend
  rw [ExceptT.run_bind]
  simp only [Bind.bind, instMonadEIO._aux_13, EST.bind]
  have liftRun : (liftM ((DurableBlob.native dir).reopen) : ExceptT String IO ByteArray).run w =
      match (DurableBlob.native dir).reopen w with
      | .ok bytes t => .ok (.ok bytes) t
      | .error e t => .error e t := by
    show (ExceptT.lift ((DurableBlob.native dir).reopen)).run w = _
    simp only [ExceptT.lift, ExceptT.run, ExceptT.mk, Functor.map, instMonadEIO._aux_1, EST.bind]
    cases (DurableBlob.native dir).reopen w <;> rfl
  rw [liftRun]
  cases ran : (DurableBlob.native dir).reopen w with
  | error => rfl
  | ok bytes t =>
    dsimp only
    cases L0Manifest.decode bytes <;> rfl

/-- Selected manifest from the actual native read, including a barrier
that took effect despite a reported error. -/
theorem reopen (p : Primitives dir P image) (start : P w)
    (selected : (image w).active = L0Manifest.encode version) (valid : version.Valid) :
    match (backend dir).reopen.run w with
    | .ok (.ok v) t => v = version ∧ P t ∧ image t = (image w).barrier ∧
        (image t).Stable (L0Manifest.encode v)
    | .ok (.error _) t | .error _ t => P t ∧
        (image t = image w ∨ image t = (image w).barrier) := by
  have observed := reopenBytes p start
  rw [decodeReached]
  cases ran : (DurableBlob.native dir).reopen w with
  | error e t => simpa only [ran] using observed
  | ok bytes t =>
    rw [ran] at observed
    simp only [observed.2.1.trans selected, decode_encode valid]
    refine ⟨trivial, observed.1, observed.2.2, ?_⟩
    rw [observed.2.2]
    exact ⟨selected, congrArg List.singleton selected⟩

/-- A reported directory sync is the last native effect of manifest
reopen. Healthy completion and reported sync failure consume the same
acquired handle and reached world. -/
theorem reopen_atSync (p : Primitives dir P image) (start : P w)
    (selected : (image w).active = L0Manifest.encode version) (valid : version.Valid)
    (metadata : (dir / "BLOB").metadata w = .ok md checked)
    (openBlob : IO.FS.Handle.mk (dir / "BLOB") .read checked = .ok file entered)
    (initial : (if md.byteSize.toUSize > 0 then file.read md.byteSize.toUSize
      else pure (ByteArray.emptyWithCapacity 0) : IO ByteArray) entered = .ok acc filled)
    (eof : file.readBinToEndInto acc filled = .ok bytes afterRead)
    (openDirectory : IO.FS.Handle.mk dir .read afterRead = .ok directory acquired) :
    (backend dir).reopen.run w =
      match syncHandle directory acquired with
      | .error e t => .error e t
      | .ok _ t => .ok (.ok version) t := by
  have readRun := (FileRead.readBinFile_atEOF metadata openBlob initial).trans eof
  have safe := FileRead.readBinFile p.file start
  unfold FileRead.Effect at safe
  rw [readRun] at safe
  rw [decodeReached, native_reopen_schedule]
  simp only [Bind.bind, instMonadEIO._aux_13, EST.bind, readRun, openDirectory]
  cases syncHandle directory acquired with
  | error => rfl
  | ok _ t =>
    change (match L0Manifest.decode bytes with
      | some v => EST.Out.ok (Except.ok v : Except String Version) t
      | none => .ok (.error "invalid L0 manifest") t) = _
    rw [safe.2.2.trans selected, decode_encode valid]

end ExperimentalL0.NativeManifest
