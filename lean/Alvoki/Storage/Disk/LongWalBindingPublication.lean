import Alvoki.Storage.Disk.LongWalStagedCustody

namespace Alvoki.Storage.WalSegmentRepair

open System DiskSession SyncHandleRouting
open WAL.Boundary (WalInodeImage)

/-- The long route settles the marker and suffix names before running the
four replacement steps. An error in those earlier steps skips replacement. -/
theorem finishBoundedMarkedOpen_long {m : Type → Type} [Monad m] [LawfulMonad m] [MonadExceptOf IO.Error m]
    (directory : DiskDirectory) (plan : Plan) (physicalSize : Nat)
    (remove : FilePath → m (Except IO.Error Unit)) (write : FilePath → ByteArray → m Unit)
    (sync : Array FilePath → m Unit) (rename : FilePath → FilePath → m Unit)
    (valid : plan.valid = true) (size : plan.keeperBytes.size = plan.keeperSize)
    (long : plan.keeperSize < physicalSize) :
    let run := performPaths directory plan remove throw write sync rename
    finishBoundedMarkedOpen directory plan physicalSize remove write sync rename = (do
      sync #[directory.path]
      (plan.newer.map Step.unlink ++ [Step.syncPruned]).forM run
      run (.replace .writeStaged)
      run (.replace .syncStaged)
      run (.replace .renameStaged)
      run (.replace .syncDirectory)
      pure ()) := by
  intro run
  have unequal : (physicalSize == plan.keeperSize) = false := by
    simpa using (Nat.ne_of_gt long)
  simp only [finishBoundedMarkedOpen, valid, size, beq_self_eq_true, decide_eq_true (Nat.le_of_lt long),
    Bool.and_true, Bool.false_eq_true, ite_true, ite_false, pure_bind, unequal, Bool.and_false,
    decide_eq_true long, runRepairPlan, steps, List.forM_eq_forM, List.forM_append,
    List.map_cons, List.map_nil, Publication.steps, List.forM_cons, List.forM_nil, bind_assoc, run]

private abbrev RepairState := Cache (DescriptorInventory × DescriptorSlot × Nat) × WalInodeImage

/-- Rename changes bindings and retains the synced bytes. The replacement
is added to the old binding alternatives until the directory is synced. -/
def bindReplacement (image : WalInodeImage) (inode : Nat) : WalInodeImage :=
  { image with active := inode, crashBindings := inode :: image.crashBindings }

private theorem synced_bindReplacement (image : WalInodeImage) (inode : Nat) {bytes : ByteArray}
    (visible : image.visible inode = bytes) :
    bindReplacement (image.completeFileSync inode) inode = image.renameSynced inode bytes := by
  simp only [bindReplacement, WalInodeImage.completeFileSync, WalInodeImage.reportFileSync, WalInodeImage.renameSynced]
  have contents : image.visible = fun object => if object = inode then bytes else image.visible object := by
    funext object
    by_cases same : object = inode
    · simpa only [same, ite_true] using visible
    · simp only [ite_eq_right same]
  rw [visible, ← contents]

private def replacementResult (staged renamed directory : EStateM.Result IO.Error RepairState Unit) :
    EStateM.Result IO.Error RepairState Unit :=
  match staged with
  | .error cause after => .error cause after
  | .ok () _ =>
    match renamed with
    | .error cause after => .error cause after
    | .ok () _ => directory

/-- Given the reached long-keeper barriers and individual native operation
reports, the actual finisher only publishes a replacement whose staged inode
has the selected bytes. A staged write/sync error skips rename. A rename
error retains the binding effect it reports and skips the final directory
barrier. The barrier's exact result retains the old binding choices before
its effect and settles the synced replacement after its effect. -/
theorem finishBoundedMarkedOpen_long_publication
    (directory : DiskDirectory) (plan : Plan) (physicalSize : Nat)
    (valid : plan.valid = true) (size : plan.keeperBytes.size = plan.keeperSize)
    (long : plan.keeperSize < physicalSize)
    (remove : FilePath → EStateM IO.Error RepairState (Except IO.Error Unit))
    (write : FilePath → ByteArray → EStateM IO.Error RepairState Unit)
    (openRead : FilePath → EStateM IO.Error WalInodeImage (DescriptorInventory × DescriptorSlot × Nat))
    (fsync : (DescriptorInventory × DescriptorSlot × Nat) → EStateM IO.Error WalInodeImage Unit)
    (rename : FilePath → FilePath → EStateM IO.Error RepairState Unit)
    (initial : RepairState) (beforeStage written : WalInodeImage)
    (cache : Cache (DescriptorInventory × DescriptorSlot × Nat))
    (directoryInventory : DescriptorInventory) (directorySlot : DescriptorSlot) (offset : Nat)
    (hasDirectory : cache.directory = some (directoryInventory, directorySlot, offset))
    (drops : List LockReferenceDrop)
    (renameBindings directoryBindings : FilePath → Option Nat)
    (inode : Nat) (visible : written.visible inode = plan.keeperBytes) :
    let path := directory.file .stagedWal
    let keeper := directory.file (.walSegment plan.keeper)
    let chosen := cache.consume path
    let retained := (directoryInventory, directorySlot, offset)
    let synced := written.completeFileSync inode
    let published := written.renameSynced inode plan.keeperBytes
    let grouped := SyncPathGroup.run (sync directory.path openRead fsync)
    let run := performPaths directory plan remove throw write grouped rename
    let earlier := (do
      grouped #[directory.path]
      (plan.newer.map Step.unlink ++ [Step.syncPruned]).forM run : EStateM IO.Error RepairState Unit) initial
    let staged := (run (.replace .writeStaged) >>= fun _ => run (.replace .syncStaged)) (cache, beforeStage)
    let renamed := rename path keeper (chosen, synced)
    let directorySync := SyncPathGroup.run (m := EStateM IO.Error RepairState)
      (fun _ (_, files) => withCache chosen (fsync retained files)) #[directory.path] (chosen, published)
    let finish := finishBoundedMarkedOpen directory plan physicalSize remove write grouped rename initial
    earlier = .ok () (cache, beforeStage) →
    ((∃ cause after, staged = .error cause after) ∨
      ∃ effective, FsyncResult (chosen, written) (chosen, synced) effective staged) →
    (staged = .ok () (chosen, synced) → renameBindings path = some inode) →
    (∀ {source}, renameBindings path = some source → match renamed with
      | .ok () after => after = (chosen, bindReplacement synced source)
      | .error _ after => after = (chosen, synced) ∨ after = (chosen, bindReplacement synced source)) →
    ∀ {effective : Bool},
    (staged = .ok () (chosen, synced) → renamed = .ok () (chosen, published) →
      directorySlot.reference ∈ (directoryInventory.afterDrops drops).references directorySlot.description ∧
      directoryBindings directory.path = some (directoryInventory.inode directorySlot.description) ∧
      FsyncResult published published.settleBinding effective (fsync retained published)) →
      finish = replacementResult staged renamed directorySync ∧
      (∀ {cause after}, staged = .ok () (chosen, synced) → renamed = .error cause after →
        finish = .error cause after ∧ (after = (chosen, synced) ∨ after = (chosen, published))) ∧
      (staged = .ok () (chosen, synced) → renamed = .ok () (chosen, published) →
        (∃ observed : FsyncObservation (fun handle => handle.2.1.description)
            (fun handle => handle.1.inode handle.2.1.description) retained published
            (fun _ (image : WalInodeImage) => image.settleBinding) (fsync retained published),
          observed.issuer = directorySlot.reference ∧ observed.effective = effective ∧
            directoryBindings directory.path = some observed.effectInode) ∧
        FsyncResult (chosen, published) (chosen, published.settleBinding) effective finish) ∧
      (∀ directoryImage : DirectoryPublication.Image,
        (published.settleBinding.project directoryImage).wal.active = some plan.keeperBytes ∧
        (published.settleBinding.project directoryImage).wal.crashImages = [some plan.keeperBytes]) := by
  intro path keeper chosen retained synced published grouped run earlier staged renamed directorySync finish
    barriers stageEffect renameSource renameEffect effective directoryEffect
  have binds : bindReplacement synced inode = published := synced_bindReplacement written inode visible
  have stagedSuccess {after : RepairState} (ok : staged = .ok () after) : after = (chosen, synced) := by
    rcases stageEffect with ⟨cause, before, failed⟩ | ⟨_, syncedReport⟩
    · rw [ok] at failed
      cases failed
    · rw [ok] at syncedReport
      cases syncedReport
      rfl
  have runs : finish = replacementResult staged renamed directorySync := by
    rw [show finish = _ from congrFun (finishBoundedMarkedOpen_long directory plan physicalSize
      remove write grouped rename valid size long) initial]
    have discardUnit (action : EStateM IO.Error RepairState Unit) : (action >>= fun _ => pure ()) = action := by
      funext state
      cases returned : action state with
      | error => simp [Bind.bind, EStateM.bind, returned]
      | ok result => cases result; simp [Bind.bind, EStateM.bind, Pure.pure, EStateM.pure, returned]
    have nextStep (action : EStateM IO.Error RepairState Unit)
        (next : Unit → EStateM IO.Error RepairState Unit) (before : RepairState) :
        (action >>= next) before = match action before with
        | .ok value after => next value after
        | .error cause after => .error cause after := by
      cases returned : action before <;> simp [Bind.bind, EStateM.bind, returned]
    have reassociate : (do
        grouped #[directory.path]
        (plan.newer.map Step.unlink ++ [Step.syncPruned]).forM run
        run (.replace .writeStaged)
        run (.replace .syncStaged)
        run (.replace .renameStaged)
        run (.replace .syncDirectory)
        pure () : EStateM IO.Error RepairState Unit) = (do
        (do
          grouped #[directory.path]
          (plan.newer.map Step.unlink ++ [Step.syncPruned]).forM run)
        (run (.replace .writeStaged) >>= fun _ => run (.replace .syncStaged))
        run (.replace .renameStaged)
        run (.replace .syncDirectory) : EStateM IO.Error RepairState Unit) := by
      simp only [bind_assoc, discardUnit]
    rw [reassociate, nextStep]
    change (match earlier with
      | .ok _ after =>
        (((run (.replace .writeStaged) >>= fun _ => run (.replace .syncStaged)) >>= fun _ =>
          run (.replace .renameStaged) >>= fun _ => run (.replace .syncDirectory)) after)
      | .error cause after => EStateM.Result.error cause after) = _
    rw [barriers]
    simp only
    rw [nextStep]
    change (match staged with
      | .ok _ after =>
        ((run (.replace .renameStaged) >>= fun _ => run (.replace .syncDirectory)) after)
      | .error cause after => EStateM.Result.error cause after) = _
    cases stageReport : staged with
    | error cause after => rfl
    | ok value after =>
      cases value
      have exactStage := stagedSuccess stageReport
      subst after
      simp only [replacementResult]
      rw [nextStep]
      change (match renamed with
        | .ok _ after => grouped #[directory.path] after
        | .error cause after => EStateM.Result.error cause after) = _
      cases renameReport : renamed with
      | error cause after => rfl
      | ok value after =>
        cases value
        have reached := renameEffect (renameSource stageReport)
        rw [renameReport, binds] at reached
        subst after
        simp only
        have routed : sync directory.path openRead fsync directory.path (chosen, published) =
            withCache chosen (fsync retained published) := by
          simp [sync, Cache.resolve, chosen, Cache.consume, hasDirectory, retained]
        rw [show grouped = SyncPathGroup.run (sync directory.path openRead fsync) from rfl,
          SyncPathGroup.run_single, routed]
        exact (SyncPathGroup.run_single
          (fun _ (entered : RepairState) => withCache chosen (fsync retained entered.2))
          directory.path (chosen, published)).symm
  refine ⟨runs, ?_, ?_, ?_⟩
  · intro cause after stageOK renameError
    have reached := renameEffect (renameSource stageOK)
    rw [renameError, binds] at reached
    exact ⟨by simp [runs, stageOK, renameError, replacementResult], reached⟩
  · intro stageOK renameOK
    obtain ⟨issuing, directoryBound, reported⟩ := directoryEffect stageOK renameOK
    let observed := FsyncObservation.ofInventory directoryInventory drops
      (fun handle => handle.2.1.description) (fun handle => handle.1.inode handle.2.1.description)
      retained directorySlot.reference issuing rfl published
      (fun _ (image : WalInodeImage) => image.settleBinding) (effective := effective) reported
    refine ⟨⟨observed, rfl, rfl, directoryBound⟩, ?_⟩
    rw [runs, stageOK, renameOK]
    simp only [replacementResult, directorySync]
    rw [SyncPathGroup.run_single
      (fun _ (entered : RepairState) => withCache chosen (fsync retained entered.2))
        directory.path (chosen, published)]
    generalize fsync retained published = returned at reported ⊢
    cases reported <;> constructor
  · intro directoryImage
    simp [published, WalInodeImage.project, WalInodeImage.settleBinding, WalInodeImage.renameSynced]

end Alvoki.Storage.WalSegmentRepair
