import Alvoki.Experiments.WAL.CrashModel

namespace WalRecoverySlice.Persistence

theorem WalFile.writeback (file : WalFile) (before : Image) : Writeback before (file.settle before) := by
  cases file <;> constructor

def settleFiles (files : List WalFile) (image : Image) : Image :=
  files.foldl (fun current file => file.settle current) image

theorem WalFile.settle_clean (file : WalFile) (b : Image) (h : b.powerLoss = b) :
    file.settle b = b := by
  obtain ⟨⟨dl, dd⟩, ⟨al, ad⟩, ⟨bl, bd⟩⟩ := b
  simp [Image.powerLoss, FileImage.powerLoss] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  cases file <;> rfl

theorem settleFiles_clean (files : List WalFile) (b : Image) (h : b.powerLoss = b) :
    settleFiles files b = b := by
  induction files with
  | nil => rfl
  | cons file rest ih =>
    change settleFiles rest (file.settle b) = b
    rw [file.settle_clean b h, ih]

/-- Perform only the selected background writebacks before the reached callback. -/
def withWritebacks (files : List WalFile) (action : M α) : M α :=
  fun image => action (settleFiles files image)

/-- Each reached callback can be preceded by a finite sequence of whole-file
writebacks. Marker callbacks choose the sequence for the actual slot. -/
structure WritebackSchedule where
  appendData : List WalFile := []
  dataSync : List WalFile := []
  writeMarker : Nat → List WalFile := fun _ => []
  markerSync : Nat → List WalFile := fun _ => []
  markerRead : Nat → List WalFile := fun _ => []
  dataRead : List WalFile := []
  truncate : List WalFile := []

def scheduledOps (plain : Ops M) (s : WritebackSchedule) : Ops M where
  append bytes := withWritebacks s.appendData (plain.append bytes)
  syncData := withWritebacks s.dataSync plain.syncData
  writeMarker slot bytes := withWritebacks (s.writeMarker slot) (plain.writeMarker slot bytes)
  syncMarker slot := withWritebacks (s.markerSync slot) (plain.syncMarker slot)
  readMarker slot := withWritebacks (s.markerRead slot) (plain.readMarker slot)
  readData := withWritebacks s.dataRead plain.readData
  truncate size := withWritebacks s.truncate (plain.truncate size)

end WalRecoverySlice.Persistence
