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
  unfold backend L0Manifest.backend
  rw [ExceptT.run_bind]
  simp only [Bind.bind, instMonadEIO._aux_13, EST.bind]
  cases ran : (DurableBlob.native dir).reopen w with
  | error e t =>
    rw [ran] at observed
    have lifted : (liftM ((DurableBlob.native dir).reopen) : ExceptT String IO ByteArray).run w = .error e t := by
      show (ExceptT.lift ((DurableBlob.native dir).reopen)).run w = _
      simp [ExceptT.lift, ExceptT.run, ExceptT.mk, Functor.map, instMonadEIO._aux_1, EST.bind, ran]
    rw [lifted]
    exact observed
  | ok bytes t =>
    rw [ran] at observed
    have lifted : (liftM ((DurableBlob.native dir).reopen) : ExceptT String IO ByteArray).run w = .ok (.ok bytes) t := by
      show (ExceptT.lift ((DurableBlob.native dir).reopen)).run w = _
      simp [ExceptT.lift, ExceptT.run, ExceptT.mk, Functor.map, instMonadEIO._aux_1, EST.bind, ran]
      rfl
    simp only [lifted, observed.2.1.trans selected, decode_encode valid]
    refine ⟨rfl, observed.1, observed.2.2, ?_⟩
    rw [observed.2.2]
    exact ⟨selected, congrArg List.singleton selected⟩

end ExperimentalL0.NativeManifest
