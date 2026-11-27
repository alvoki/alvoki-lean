import Alvoki.Storage.Disk.Proofs.Collection.RunFileInventory

namespace Alvoki.Storage.CheckpointPublication

abbrev RunAddress := UInt64 × Nat

/-- Remove one exact address from a run map. -/
def RunFiles.eraseName (files : RunFiles) (name : RunAddress) : RunFiles :=
  fun generation index => if (generation, index) = name then none else files generation index

/-- A namespace image records actual visible regular run bindings and each
admitted crash run map. Every present name refers to immutable, previously
synced file bytes. Here `none` means the name is absent in that image. -/
structure RunUnlinkImage where
  visible : RunFiles
  crashImages : List RunFiles

def RunUnlinkImage.settled (files : RunFiles) : RunUnlinkImage := ⟨files, [files]⟩

/-- A completed unlink removes the visible name. Before the directory sync,
power loss can preserve either the prior binding or its removal. Applying
this step to an already absent name is safe for a retry. -/
def RunUnlinkImage.unlink (image : RunUnlinkImage) (name : RunAddress) : RunUnlinkImage :=
  ⟨image.visible.eraseName name, image.crashImages.map (·.eraseName name) ++ image.crashImages⟩

/-- The directory barrier settles names. Run contents are already synced. -/
def RunUnlinkImage.syncDirectory (image : RunUnlinkImage) : RunUnlinkImage := .settled image.visible

theorem RunUnlinkImage.unlink_crashImages {image : RunUnlinkImage} {name : RunAddress} {files : RunFiles} :
    files ∈ (image.unlink name).crashImages ↔ files ∈ image.crashImages ∨
      ∃ prior ∈ image.crashImages, prior.eraseName name = files := by
  simp only [unlink, List.mem_append, List.mem_map]
  exact or_comm

/-- The checkpoint model's map guarantees only bindings that agree with the
visible map in every crash image. Absence in that guarantee map alone carries
no claim about actual presence. -/
def RunUnlinkImage.guaranteed (image : RunUnlinkImage) : RunFiles := fun generation index =>
  let visible := image.visible generation index
  if image.crashImages.all (fun files => decide (files generation index = visible)) then visible else none

def RunUnlinkImage.project (image : RunUnlinkImage) (manifest : Publication.Image) : Image :=
  ⟨manifest, image.guaranteed⟩

/-- A run name is durably absent when it is gone both live and in every
admitted crash outcome. -/
def RunUnlinkImage.DurablyAbsent (image : RunUnlinkImage) (name : RunAddress) : Prop :=
  image.visible name.1 name.2 = none ∧ ∀ files ∈ image.crashImages, files name.1 name.2 = none

/-- Removing a known durable name immediately hides it from live reads.
The original directory binding can survive until the directory sync. -/
theorem RunUnlinkImage.unlink_beforeSync {files : RunFiles} {name : RunAddress} {bytes : ByteArray}
    (present : files name.1 name.2 = some bytes) :
    let after := (settled files).unlink name
    after.visible name.1 name.2 = none ∧ ¬ after.DurablyAbsent name := by
  refine ⟨?_, ?_⟩
  · obtain ⟨generation, index⟩ := name
    simp [unlink, settled, RunFiles.eraseName]
  · intro absent
    have old : files ∈ ((settled files).unlink name).crashImages :=
      unlink_crashImages.mpr (.inl List.mem_cons_self)
    have missing := absent.2 _ old
    rw [present] at missing
    contradiction

private theorem RunUnlinkImage.guaranteed_of_same {image : RunUnlinkImage}
    {generation : UInt64} {index : Nat} {binding : Option ByteArray}
    (visible : image.visible generation index = binding)
    (durable : ∀ files ∈ image.crashImages, files generation index = binding) :
    image.guaranteed generation index = binding := by
  have exactChoice : image.crashImages.all (fun files => decide (files generation index = binding)) = true :=
    List.all_eq_true.mpr (fun files chosen => decide_eq_true (durable files chosen))
  simp [guaranteed, visible, exactChoice]

theorem RunUnlinkImage.project_settled (files : RunFiles) (manifest : Publication.Image) :
    (settled files).project manifest = ⟨manifest, files⟩ := by
  have exactRuns : (settled files).guaranteed = files := by
    funext generation index
    apply guaranteed_of_same rfl
    intro candidate chosen
    obtain rfl := List.mem_singleton.mp chosen
    rfl
  simp [project, exactRuns]

/-- A reported failure can leave the operation's preceding state or its
completed effect. Repeated crash choices and later attempts can act only
on the approved addresses. The surrounding manifest stays fixed. -/
inductive RunUnlinkRetry (approved : List RunAddress) : RunUnlinkImage → RunUnlinkImage → Prop where
  | start (initial : RunUnlinkImage) : RunUnlinkRetry approved initial initial
  | unlink (prior : RunUnlinkRetry approved initial before) (chosen : name ∈ approved) :
      RunUnlinkRetry approved initial (before.unlink name)
  | sync (prior : RunUnlinkRetry approved initial before) :
      RunUnlinkRetry approved initial before.syncDirectory
  | crash (prior : RunUnlinkRetry approved initial before) (survives : files ∈ before.crashImages) :
      RunUnlinkRetry approved initial (.settled files)

/-- Once a name is durably absent, later unlink, sync and crash steps
within this collection lineage cannot restore it. -/
theorem RunUnlinkRetry.keepsAbsent {approved : List RunAddress} {initial after : RunUnlinkImage}
    (retry : RunUnlinkRetry approved initial after) {name : RunAddress} (absent : initial.DurablyAbsent name) :
    after.DurablyAbsent name := by
  induction retry with
  | start => exact absent
  | @unlink before removed _ _ prior =>
    refine ⟨?_, ?_⟩
    · simp [RunUnlinkImage.unlink, RunFiles.eraseName, prior.1]
    · intro files survives
      rcases RunUnlinkImage.unlink_crashImages.mp survives with unchanged | ⟨earlier, earlierSurvives, rfl⟩
      · exact prior.2 _ unchanged
      · simp [RunFiles.eraseName, prior.2 _ earlierSurvives]
  | sync _ prior =>
    refine ⟨prior.1, ?_⟩
    intro files survives
    obtain rfl := List.mem_singleton.mp survives
    exact prior.1
  | crash _ survives prior =>
    refine ⟨prior.2 _ survives, ?_⟩
    intro files chosen
    obtain rfl := List.mem_singleton.mp chosen
    exact prior.2 _ survives

/-- A known binding at an unapproved address survives any retry, even when
unrelated bindings in the starting namespace are still unsettled. -/
theorem RunUnlinkRetry.keepsKnown {approved : List RunAddress} {initial after : RunUnlinkImage}
    (retry : RunUnlinkRetry approved initial after) {name : RunAddress} {bytes : ByteArray}
    (known : initial.guaranteed name.1 name.2 = some bytes) (unapproved : name ∉ approved) :
    after.guaranteed name.1 name.2 = some bytes := by
  have bindings : after.visible name.1 name.2 = some bytes ∧
      ∀ files ∈ after.crashImages, files name.1 name.2 = some bytes := by
    induction retry with
    | start =>
      unfold RunUnlinkImage.guaranteed at known
      dsimp only at known
      split at known
      · rename_i agreement
        refine ⟨known, ?_⟩
        intro files survives
        exact (of_decide_eq_true (List.all_eq_true.mp agreement files survives)).trans known
      · contradiction
    | @unlink before removed _ chosen prior =>
      have different : (name.1, name.2) ≠ removed := by
        change name ≠ removed
        exact fun same => unapproved (same.symm ▸ chosen)
      refine ⟨?_, ?_⟩
      · simpa [RunUnlinkImage.unlink, RunFiles.eraseName, different] using prior.1
      · intro files survives
        rcases RunUnlinkImage.unlink_crashImages.mp survives with unchanged | ⟨earlier, survived, rfl⟩
        · exact prior.2 _ unchanged
        · simpa [RunFiles.eraseName, different] using prior.2 _ survived
    | sync _ prior =>
      refine ⟨prior.1, ?_⟩
      intro files survives
      obtain rfl := List.mem_singleton.mp survives
      exact prior.1
    | crash _ survives prior =>
      refine ⟨prior.2 _ survives, ?_⟩
      intro files chosen
      obtain rfl := List.mem_singleton.mp chosen
      exact prior.2 _ survives
  exact RunUnlinkImage.guaranteed_of_same bindings.1 bindings.2

private def RunFiles.RemovesOnly (files base : RunFiles) (approved : List RunAddress) : Prop :=
  ∀ name : RunAddress, files name.1 name.2 = base name.1 name.2 ∨
    (name ∈ approved ∧ files name.1 name.2 = none)

private theorem RunFiles.RemovesOnly.eraseName {files base : RunFiles} {approved : List RunAddress}
    (only : files.RemovesOnly base approved) {name : RunAddress} (chosen : name ∈ approved) :
    (files.eraseName name).RemovesOnly base approved := by
  intro address
  obtain ⟨generation, index⟩ := address
  by_cases same : (generation, index) = name
  · exact Or.inr ⟨same.symm ▸ chosen, by simp [RunFiles.eraseName, same]⟩
  · simpa [RunFiles.eraseName, same] using only (generation, index)

private theorem RunUnlinkRetry.effects {approved : List RunAddress} {files : RunFiles} {after : RunUnlinkImage}
    (retry : RunUnlinkRetry approved (.settled files) after) :
    after.visible.RemovesOnly files approved ∧ ∀ candidate ∈ after.crashImages, candidate.RemovesOnly files approved := by
  induction retry with
  | start =>
    refine ⟨fun _ => Or.inl rfl, ?_⟩
    intro candidate chosen
    obtain rfl := List.mem_singleton.mp chosen
    exact fun _ => Or.inl rfl
  | @unlink before name _ chosen prior =>
    refine ⟨prior.1.eraseName chosen, ?_⟩
    intro candidate survives
    rcases RunUnlinkImage.unlink_crashImages.mp survives with unchanged | ⟨earlier, survived, rfl⟩
    · exact prior.2 _ unchanged
    · exact (prior.2 _ survived).eraseName chosen
  | sync _ prior =>
    refine ⟨prior.1, ?_⟩
    intro candidate chosen
    obtain rfl := List.mem_singleton.mp chosen
    exact prior.1
  | crash _ survives prior =>
    refine ⟨prior.2 _ survives, ?_⟩
    intro candidate chosen
    obtain rfl := List.mem_singleton.mp chosen
    exact prior.2 _ survives

/-- The live map and every crash outcome agree on the original binding at an
unapproved address, so it remains guaranteed. -/
theorem RunUnlinkRetry.keepsUnapproved {approved : List RunAddress} {files : RunFiles}
    {after : RunUnlinkImage} (retry : RunUnlinkRetry approved (.settled files) after)
    {name : RunAddress} (unapproved : name ∉ approved) :
    after.guaranteed name.1 name.2 = files name.1 name.2 := by
  obtain ⟨visible, durable⟩ := retry.effects
  apply RunUnlinkImage.guaranteed_of_same ((visible name).resolve_right (fun cut => unapproved cut.1))
  intro candidate survives
  exact (durable candidate survives name).resolve_right (fun cut => unapproved cut.1)

/-- Starting from a settled run map, every retry state projects to an allowed
loss of guarantees. Only approved, individually collectable addresses can
lose their guaranteed bindings. The checkpoint manifest is unchanged. -/
theorem RunUnlinkRetry.projectsDeletion {approved : List RunAddress} {files : RunFiles}
    {after : RunUnlinkImage} (retry : RunUnlinkRetry approved (.settled files) after)
    (manifest : Publication.Image) (held : UInt64 → Prop)
    (eligible : ∀ address ∈ approved, (⟨manifest, files⟩ : Image).Collectable held address.1) :
    RunDeletion held ⟨manifest, files⟩ (after.project manifest) := by
  have visible := retry.effects.1
  refine ⟨rfl, ?_⟩
  intro generation index
  by_cases selected : (generation, index) ∈ approved
  · have guarantee : after.guaranteed generation index = after.visible generation index ∨
        after.guaranteed generation index = none := by
      unfold RunUnlinkImage.guaranteed
      dsimp only
      split
      · exact Or.inl rfl
      · exact Or.inr rfl
    rcases guarantee with witnessed | unknown
    · rcases visible (generation, index) with same | ⟨_, removed⟩
      · exact Or.inl (witnessed.trans same)
      · exact Or.inr ⟨eligible _ selected, witnessed.trans removed⟩
    · exact Or.inr ⟨eligible _ selected, unknown⟩
  · exact Or.inl (retry.keepsUnapproved selected)

/-- All selected requests complete, then the directory sync settles every
name. The barrier also applies to an empty list because a retry can see an
earlier unlink before its removal is durable. -/
def RunUnlinkImage.finishPass (start : RunUnlinkImage) (selected : List RunAddress) : RunUnlinkImage :=
  (selected.foldl RunUnlinkImage.unlink start).syncDirectory

private theorem foldl_unlink_visible (start : RunUnlinkImage) (selected : List RunAddress)
    (name : RunAddress) :
    (selected.foldl RunUnlinkImage.unlink start).visible name.1 name.2 =
      if name ∈ selected then none else start.visible name.1 name.2 := by
  induction selected generalizing start with
  | nil => simp
  | cons head rest later =>
    rw [List.foldl_cons, later]
    obtain ⟨generation, index⟩ := name
    by_cases remains : (generation, index) ∈ rest <;>
      simp [remains, List.mem_cons, RunUnlinkImage.unlink, RunFiles.eraseName]

private theorem RunUnlinkRetry.foldl_unlink {approved : List RunAddress} {initial before : RunUnlinkImage}
    (retry : RunUnlinkRetry approved initial before) (steps : List RunAddress)
    (chosen : ∀ name ∈ steps, name ∈ approved) :
    RunUnlinkRetry approved initial (steps.foldl RunUnlinkImage.unlink before) := by
  induction steps generalizing before with
  | nil => exact retry
  | cons name rest later =>
    exact later (.unlink retry (chosen name List.mem_cons_self))
      (fun candidate member => chosen candidate (List.mem_cons_of_mem _ member))

theorem RunUnlinkRetry.finishPass {selected : List RunAddress} {initial before : RunUnlinkImage}
    (retry : RunUnlinkRetry selected initial before) :
    RunUnlinkRetry selected initial (before.finishPass selected) :=
  .sync (retry.foldl_unlink selected (fun _ member => member))

/-- The successful finite pass removes each selected name durably and leaves
all unselected visible bindings unchanged in the settled image. -/
theorem RunUnlinkImage.finishPass_binding (start : RunUnlinkImage) (selected : List RunAddress) (name : RunAddress) :
    let after := start.finishPass selected
    let binding := if name ∈ selected then none else start.visible name.1 name.2
    after.visible name.1 name.2 = binding ∧
      ∀ files ∈ after.crashImages, files name.1 name.2 = binding := by
  have exactBinding := foldl_unlink_visible start selected name
  refine ⟨exactBinding, ?_⟩
  intro files survives
  obtain rfl := List.mem_singleton.mp survives
  exact exactBinding

theorem RunUnlinkImage.finishPass_absent {start : RunUnlinkImage} {selected : List RunAddress} {name : RunAddress}
    (chosen : name ∈ selected) : (start.finishPass selected).DurablyAbsent name := by
  simpa only [ite_eq_left chosen, DurablyAbsent] using start.finishPass_binding selected name

/-- A settled pass removes exactly the chosen live names and also makes
the absence of every already hidden name durable. -/
theorem RunUnlinkImage.finishPass_absent_iff (start : RunUnlinkImage) (selected : List RunAddress)
    (name : RunAddress) :
    (start.finishPass selected).DurablyAbsent name ↔ name ∈ selected ∨ start.visible name.1 name.2 = none := by
  obtain ⟨visible, crash⟩ := start.finishPass_binding selected name
  by_cases chosen : name ∈ selected
  · simp [chosen, finishPass_absent chosen]
  · rw [or_iff_right chosen]
    simp only [chosen, ↓reduceIte] at visible crash
    exact ⟨fun absent => visible.symm.trans absent.1,
      fun absent => ⟨visible.trans absent, fun files survived => (crash files survived).trans absent⟩⟩

end Alvoki.Storage.CheckpointPublication

namespace Alvoki.Storage
open System CheckpointPublication

/-- A retry over the selected locked inventory preserves the checkpoint's
run guarantees, with the same manifest and WAL as before the pass. -/
theorem LockedRunInventory.unlinkRetry_projects {dir : DiskDirectory} {regularAt : FilePath → Prop}
    (inventory : LockedRunInventory dir regularAt) {files : RunFiles} {after : RunUnlinkImage}
    {manifest : Publication.Image} {current : Option UInt64} {held : UInt64 → Bool}
    (settled : manifest.crashImages = [manifest.active])
    (observed : runCollectionGeneration manifest.active = .ok current)
    (retry : RunUnlinkRetry (selectRunFiles dir current held inventory.kindAt inventory.names)
      (.settled files) after) :
    RunDeletion (fun generation => held generation = true) ⟨manifest, files⟩ (after.project manifest) := by
  apply retry.projectsDeletion manifest (fun generation => held generation = true)
  rintro ⟨generation, index⟩ member
  obtain ⟨_, _, _, _, _, eligible⟩ := inventory.sound (image := ⟨manifest, files⟩) settled observed member
  exact eligible

/-- If listing and lstat succeed for each visible eligible regular run,
a healthy pass removes all of those names in the durable image. -/
theorem LockedRunInventory.finishUnlinkPass_complete {dir : DiskDirectory} {regularAt : FilePath → Prop}
    (inventory : LockedRunInventory dir regularAt) {start : RunUnlinkImage}
    {manifest : Publication.Image} {current : Option UInt64} {held : UInt64 → Bool}
    (settled : manifest.crashImages = [manifest.active])
    (observed : runCollectionGeneration manifest.active = .ok current)
    (complete : ∀ generation index bytes, start.visible generation index = some bytes →
      (start.project manifest).Collectable (fun gen => held gen = true) generation →
      renderRunFileName generation index ∈ inventory.names ∧
      inventory.kindAt (dir.file (.run generation index)) = .ok .file) :
    ∀ generation index, (start.project manifest).Collectable (fun gen => held gen = true) generation →
      (start.finishPass (selectRunFiles dir current held inventory.kindAt inventory.names)).DurablyAbsent
        (generation, index) := by
  intro generation index eligible
  cases live : start.visible generation index with
  | none =>
    simpa [RunUnlinkImage.DurablyAbsent, live] using start.finishPass_binding
      (selectRunFiles dir current held inventory.kindAt inventory.names) (generation, index)
  | some bytes =>
    obtain ⟨listed, regular⟩ := complete generation index bytes live eligible
    exact RunUnlinkImage.finishPass_absent (inventory.complete settled observed eligible listed regular)

/-- All indices of a current or independently held run generation keep their
old bindings through successful collection. -/
theorem LockedRunInventory.finishUnlinkPass_keepsProtected {dir : DiskDirectory} {regularAt : FilePath → Prop}
    (inventory : LockedRunInventory dir regularAt) {start : RunUnlinkImage}
    {current : Option UInt64} {held : UInt64 → Bool} {generation : UInt64} {index : Nat}
    (excluded : current = some generation ∨ held generation = true) :
    let after := start.finishPass (selectRunFiles dir current held inventory.kindAt inventory.names)
    after.visible generation index = start.visible generation index ∧
      ∀ files ∈ after.crashImages, files generation index = start.visible generation index := by
  have unselected := not_mem_selectRunFiles_of_protected (dir := dir) (kindAt := inventory.kindAt)
    (names := inventory.names) (index := index) excluded
  simpa only [ite_eq_right unselected] using start.finishPass_binding
    (selectRunFiles dir current held inventory.kindAt inventory.names) (generation, index)

end Alvoki.Storage
