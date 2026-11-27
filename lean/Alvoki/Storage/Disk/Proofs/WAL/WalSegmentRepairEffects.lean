import Alvoki.Storage.Disk.Proofs.WAL.RetainedWalBoundary
import Alvoki.Storage.Disk.WalSegmentCollection
import Alvoki.Storage.Disk.WalSegmentRepairIO

namespace Alvoki.Storage.WalSegmentRepair

/-- The selected pair and checked prefix at the keeper's canonical start.
The checked read plan supplies these values from the locked directory. -/
structure Target where
  pair : DirectoryPublication.Bindings
  range : MarkedWalRange
  decoded : pair.walRange = some range
  first : Nat
  firstCovered : first ≤ range.through
  trimmed : ByteArray
  trimmedSize : trimmed.size = (range.through - first) * WAL.frameSize

def Target.Accepts (target : Target) (binding : Option ByteArray) : Prop :=
  ∃ unchecked, binding = some (target.trimmed ++ unchecked)

theorem Target.acceptsTrimmed (target : Target) : target.Accepts (some target.trimmed) :=
  ⟨ByteArray.empty, by simp⟩

theorem Target.selectKeeper (target : Target) {marker : ByteArray} {count : UInt64} {keeper : ByteArray}
    (visible : target.pair.walBoundary = some marker) (decoded : WAL.Boundary.decode marker = .ok count)
    (valid : target.Accepts (some keeper)) :
    WAL.Boundary.selectRetained target.first count keeper = .ok target.trimmed := by
  obtain ⟨_, _, saved, length, savedVisible, savedDecoded, absolute⟩ :=
    DirectoryPublication.Bindings.walRange_accounting target.decoded
  have same := Option.some.inj (savedVisible.symm.trans visible)
  subst saved
  have same := Except.ok.inj (savedDecoded.symm.trans decoded)
  subst length
  have covered : target.first * WAL.frameSize ≤ count.toNat := by
    rw [absolute]
    exact Nat.mul_le_mul_right _ target.firstCovered
  have relative : count.toNat - target.first * WAL.frameSize = target.trimmed.size := by
    rw [absolute, ← Nat.sub_mul, target.trimmedSize]
  unfold WAL.Boundary.selectRetained
  rw [ite_eq_right (Nat.not_lt.mpr covered)]
  change WAL.Boundary.select (count.toNat - target.first * WAL.frameSize).toUInt64 keeper = _
  rw [relative]
  have fits : target.trimmed.size < UInt64.size := by
    rw [← relative]
    exact Nat.lt_of_le_of_lt (Nat.sub_le ..) count.toNat_lt_size
  obtain ⟨unchecked, exactKeeper⟩ := valid
  have bytes := Option.some.inj exactKeeper
  rw [bytes]
  have aligned : target.trimmed.size % WAL.frameSize = 0 := by simp [target.trimmedSize]
  have enough : ¬ (target.trimmed ++ unchecked).size < target.trimmed.size := by simp [ByteArray.size_append]
  unfold WAL.Boundary.select
  simp only [UInt64.toNat_ofNat_of_lt' fits, aligned, bne_self_eq_false, Bool.false_eq_true, ite_false, enough]
  split
  · rename_i sameSize
    have empty : unchecked = ByteArray.empty := ByteArray.size_eq_zero_iff.mp (by rw [ByteArray.size_append] at sameSize; omega)
    simp [empty]
  · rw [ByteArray.extract_append_eq_left rfl]

/-- Only later name presence matters. A crash may retain any subset of
unsynced removals. Contents at these names remain outside the marked read. -/
structure LaterNames where
  visible : List Nat
  crashImages : List (List Nat)

def LaterNames.settled (names : List Nat) : LaterNames := ⟨names, [names]⟩

private def dropName (first : Nat) (names : List Nat) : List Nat := names.filter fun name => decide (name ≠ first)

def LaterNames.unlink (names : LaterNames) (first : Nat) : LaterNames :=
  ⟨dropName first names.visible, names.crashImages.map (dropName first) ++ names.crashImages⟩

def LaterNames.syncDirectory (names : LaterNames) : LaterNames := .settled names.visible

def LaterNames.Beyond (names : LaterNames) (through : Nat) : Prop :=
  ∀ visible ∈ names.visible :: names.crashImages, ∀ first ∈ visible, through < first

def LaterNames.DurablyEmpty (names : LaterNames) : Prop :=
  names.visible = [] ∧ names.crashImages = [[]]

private theorem LaterNames.Beyond.unlink {names : LaterNames} {through : Nat}
    (bound : names.Beyond through) (first : Nat) : (names.unlink first).Beyond through := by
  intro visible chosen addr listed
  change visible ∈ dropName first names.visible ::
    (names.crashImages.map (dropName first) ++ names.crashImages) at chosen
  rcases List.mem_cons.mp chosen with rfl | survives
  · exact bound _ (List.mem_cons_self ..) _ (List.mem_filter.mp listed).1
  rcases List.mem_append.mp survives with applied | old
  · obtain ⟨before, present, rfl⟩ := List.mem_map.mp applied
    exact bound _ (List.mem_cons_of_mem _ present) _ (List.mem_filter.mp listed).1
  · exact bound _ (List.mem_cons_of_mem _ old) _ listed

private theorem LaterNames.Beyond.syncDirectory {names : LaterNames} {through : Nat}
    (bound : names.Beyond through) : names.syncDirectory.Beyond through := by
  intro visible chosen
  have selected : visible = names.visible := by simp [LaterNames.syncDirectory, LaterNames.settled] at chosen; exact chosen
  subst visible
  exact bound _ (List.mem_cons_self ..)

private theorem LaterNames.Beyond.crash {names : LaterNames} {through : Nat}
    (bound : names.Beyond through) {saved : List Nat} (survives : saved ∈ names.crashImages) :
    (LaterNames.settled saved).Beyond through := by
  intro visible chosen
  have selected : visible = saved := by simpa [LaterNames.settled] using chosen
  subst visible
  exact bound _ (List.mem_cons_of_mem _ survives)

/-- Kept sealed bytes are immutable. Keeper contents have their own
publication state, and later names only track presence. This deliberately
keeps old keeper possibilities through a directory-only barrier. -/
structure FileImage where
  directory : DirectoryPublication.Image
  kept : Nat → Option ByteArray
  keeper : Publication.Image
  later : LaterNames

def FileImage.syncDirectory (image : FileImage) : FileImage :=
  { image with directory := image.directory.syncDirectory, later := image.later.syncDirectory }

def FileImage.unlinkLater (image : FileImage) (first : Nat) : FileImage :=
  { image with later := image.later.unlink first }

def FileImage.syncKeeper (image : FileImage) : FileImage :=
  { image with keeper.crashImages := [image.keeper.active] }

def FileImage.withScratch (image : FileImage) (staged : Option (ByteArray × Bool)) : FileImage :=
  { image with keeper.staged := staged }

def FileImage.replacementCut (image : FileImage) (target : Target) (cut : Nat) : Option FileImage :=
  (image.keeper.execute target.trimmed (Publication.steps.take cut)).map fun keeper =>
    { (if Publication.steps.length ≤ cut then image.syncDirectory else image) with keeper }

def FileImage.crash (image : FileImage) (pair : DirectoryPublication.Bindings)
    (keeper : Option ByteArray) (later : List Nat) : FileImage :=
  ⟨.settled pair, image.kept, .settled keeper, .settled later⟩

structure FileImage.Valid (image : FileImage) (target : Target) : Prop where
  selected : image.directory.active = target.pair
  settled : image.directory.crashImages = [target.pair]
  keeper : image.keeper.Valid target.Accepts
  later : image.later.Beyond target.range.through

/-- The actual first directory barrier is what rules out earlier metadata
alternatives. Before it reports success, callers can recover a different
admitted pair from an unmodified crash image. -/
theorem FileImage.valid_afterSync {image : FileImage} {target : Target}
    (selected : image.directory.active = target.pair)
    (keeper : image.keeper.Valid target.Accepts) (later : image.later.Beyond target.range.through) :
    image.syncDirectory.Valid target :=
  ⟨selected, congrArg (fun pair => [pair]) selected, keeper, later.syncDirectory⟩

theorem FileImage.Valid.allMarkersAtMost {image : FileImage} {target : Target} (valid : image.Valid target)
    {pair : DirectoryPublication.Bindings} (chosen : pair ∈ image.directory.active :: image.directory.crashImages) :
    ∃ range, pair.walRange = some range ∧ range.through ≤ target.range.through := by
  have exactPair : pair = target.pair := by simpa [List.mem_cons, valid.selected, valid.settled] using chosen
  subst pair
  exact ⟨target.range, target.decoded, Nat.le_refl _⟩

/-- A destructive repair trace starts at the successful metadata barrier.
Each prefix may be followed by a crash and another attempt. Replacing an
interior keeper requires durable absence of all later names. -/
inductive EffectTrace (target : Target) (initial : FileImage) : FileImage → Prop where
  | authorized : EffectTrace target initial initial.syncDirectory
  | unlink (prior : EffectTrace target initial before) (later : target.range.through < first) :
      EffectTrace target initial (before.unlinkLater first)
  | syncPruned (prior : EffectTrace target initial before) : EffectTrace target initial before.syncDirectory
  | replace (prior : EffectTrace target initial before) (gone : before.later.DurablyEmpty)
      (ran : before.replacementCut target cut = some after) : EffectTrace target initial after
  | aligned (prior : EffectTrace target initial before) (gone : before.later.DurablyEmpty)
      (exactRead : before.keeper.active = some target.trimmed) :
      EffectTrace target initial before.syncKeeper
  | scratch (prior : EffectTrace target initial before) :
      EffectTrace target initial (before.withScratch staged)
  | crash (prior : EffectTrace target initial before)
      (metadataSurvives : pair ∈ before.directory.crashImages)
      (keeperSurvives : bytes ∈ before.keeper.crashImages) (laterSurvive : names ∈ before.later.crashImages) :
      EffectTrace target initial (before.crash pair bytes names)

private theorem FileImage.Valid.replace {before after : FileImage} {target : Target} {cut : Nat}
    (valid : before.Valid target) (ran : before.replacementCut target cut = some after) : after.Valid target := by
  unfold FileImage.replacementCut at ran
  obtain ⟨keeper, applies, rfl⟩ := Option.map_eq_some_iff.mp ran
  have accepted := Publication.Image.execute_cut_valid valid.keeper target.acceptsTrimmed cut applies
  by_cases complete : Publication.steps.length ≤ cut
  · have settled := FileImage.valid_afterSync valid.selected valid.keeper valid.later
    simpa only [ite_eq_left complete] using
      (show { before.syncDirectory with keeper := keeper }.Valid target from
        ⟨settled.selected, settled.settled, accepted, settled.later⟩)
  · simpa only [ite_eq_right complete] using
      (show { before with keeper := keeper }.Valid target from ⟨valid.selected, valid.settled, accepted, valid.later⟩)

theorem EffectTrace.valid {target : Target} {initial after : FileImage} (trace : EffectTrace target initial after)
    (selected : initial.directory.active = target.pair)
    (keeper : initial.keeper.Valid target.Accepts) (later : initial.later.Beyond target.range.through) :
    after.Valid target := by
  induction trace with
  | authorized => exact FileImage.valid_afterSync selected keeper later
  | unlink _ first prior => exact ⟨prior.selected, prior.settled, prior.keeper, prior.later.unlink _⟩
  | syncPruned _ prior => exact FileImage.valid_afterSync prior.selected prior.keeper prior.later
  | replace _ gone ran prior => exact prior.replace ran
  | aligned _ _ _ prior =>
    refine ⟨prior.selected, prior.settled, ⟨by simp [FileImage.syncKeeper], prior.keeper.activeValid, ?_⟩, prior.later⟩
    intro candidate survives
    exact (List.mem_singleton.mp survives).symm ▸ prior.keeper.activeValid
  | scratch _ prior =>
    exact ⟨prior.selected, prior.settled,
      ⟨prior.keeper.hasCrashImage, prior.keeper.activeValid, prior.keeper.crashValid⟩, prior.later⟩
  | crash _ metadataSurvives keeperSurvives laterSurvive prior =>
    have exactPair := List.mem_singleton.mp (prior.settled ▸ metadataSurvives)
    exact ⟨exactPair, congrArg (fun pair => [pair]) exactPair,
      Publication.Image.settled_valid (prior.keeper.crashValid _ keeperSurvives), prior.later.crash laterSurvive⟩

theorem EffectTrace.keepsSealed {target : Target} {initial after : FileImage} (trace : EffectTrace target initial after) :
    after.kept = initial.kept := by
  induction trace with
  | authorized => rfl
  | unlink _ _ prior | syncPruned _ prior | aligned _ _ _ prior | scratch _ prior | crash _ _ _ _ prior => exact prior
  | replace _ _ ran prior =>
    unfold FileImage.replacementCut at ran
    obtain ⟨keeper, _, rfl⟩ := Option.map_eq_some_iff.mp ran
    split <;> exact prior

/-- Each current or crash-surviving keeper still supplies the exact checked
prefix. Every surviving later address is beyond the selected marker and is
used only as a name to prune. -/
theorem EffectTrace.recoveryInputs {target : Target} {initial after : FileImage}
    (trace : EffectTrace target initial after) (selected : initial.directory.active = target.pair)
    (keeper : initial.keeper.Valid target.Accepts) (later : initial.later.Beyond target.range.through)
    {chosen : Option ByteArray} (available : chosen ∈ after.keeper.active :: after.keeper.crashImages) :
    after.directory.crashImages = [target.pair] ∧ after.kept = initial.kept ∧
      target.Accepts chosen ∧ after.later.Beyond target.range.through := by
  have valid := trace.valid selected keeper later
  refine ⟨valid.settled, trace.keepsSealed, ?_, valid.later⟩
  rcases List.mem_cons.mp available with rfl | survives
  · exact valid.keeper.activeValid
  · exact valid.keeper.crashValid _ survives

/-- Reopening after a modeled crash still selects the original keeper
prefix from the same marker, with every preceding sealed byte unchanged. -/
theorem EffectTrace.selectKeeper {target : Target} {initial after : FileImage}
    (trace : EffectTrace target initial after) (selected : initial.directory.active = target.pair)
    (keeper : initial.keeper.Valid target.Accepts) (later : initial.later.Beyond target.range.through)
    {marker : ByteArray} {count : UInt64} {bytes : ByteArray}
    (markerRead : after.directory.active.walBoundary = some marker)
    (decoded : WAL.Boundary.decode marker = .ok count)
    (keeperRead : after.keeper.active = some bytes) :
    WAL.Boundary.selectRetained target.first count bytes = .ok target.trimmed ∧ after.kept = initial.kept := by
  have valid := trace.valid selected keeper later
  have accepted := keeperRead ▸ valid.keeper.activeValid
  rw [valid.selected] at markerRead
  exact ⟨target.selectKeeper markerRead decoded accepted, trace.keepsSealed⟩

/-- Exact preparation reports from the held lock. The visible list includes
every currently present later name. The keeper prefix and immutable earlier
reads come from checked marker-limited open. -/
structure Prepared (image : FileImage) (target : Target) (plan : Plan) : Prop where
  pair : image.directory.active = target.pair
  keeperPrefix : image.keeper.Valid target.Accepts
  newer : image.later.Beyond target.range.through
  through : plan.through = target.range.through
  start : plan.keeper = target.first
  names : plan.newer = image.later.visible
  keeperRead : image.keeper.active = some plan.keeperBytes

private theorem Prepared.readPrefix {image : FileImage} {target : Target} {plan : Plan}
    (prepared : Prepared image target plan) : ∃ extra, plan.keeperBytes = target.trimmed ++ extra := by
  obtain ⟨extra, exactRead⟩ := prepared.keeperPrefix.activeValid
  exact ⟨extra, Option.some.inj (prepared.keeperRead.symm.trans exactRead)⟩

theorem Prepared.valid {image : FileImage} {target : Target} {plan : Plan}
    (prepared : Prepared image target plan) : plan.valid = true := by
  obtain ⟨extra, raw⟩ := prepared.readPrefix
  apply (Plan.valid_iff _).mpr
  refine ⟨by rw [prepared.through, prepared.start]; exact target.firstCovered, ?_, ?_⟩
  · simp [Plan.keeperSize, prepared.through, prepared.start, ← target.trimmedSize, raw, ByteArray.size_append]
  · intro first listed
    rw [prepared.through]
    exact prepared.newer _ (List.mem_cons_self ..) _ (prepared.names ▸ listed)

theorem Prepared.replacementBytes {image : FileImage} {target : Target} {plan : Plan}
    (prepared : Prepared image target plan) : plan.keeperBytes.extract 0 plan.keeperSize = target.trimmed := by
  obtain ⟨extra, raw⟩ := prepared.readPrefix
  rw [Plan.keeperSize, prepared.through, prepared.start, ← target.trimmedSize, raw]
  exact ByteArray.extract_append_eq_left rfl

theorem Prepared.aligned {image : FileImage} {target : Target} {plan : Plan}
    (prepared : Prepared image target plan) (sameLength : ¬ plan.keeperSize < plan.keeperBytes.size) :
    image.keeper.active = some target.trimmed := by
  obtain ⟨extra, raw⟩ := prepared.readPrefix
  have size : extra.size = 0 := by
    rw [Plan.keeperSize, prepared.through, prepared.start, ← target.trimmedSize,
      raw, ByteArray.size_append] at sameLength
    omega
  rw [prepared.keeperRead, raw, ByteArray.size_eq_zero_iff.mp size, ByteArray.append_empty]

/-- An authorized retry has an admissible plan from the current visible
file image. Native calls to obtain these exact reports may still fail. -/
theorem EffectTrace.retryPlan {initial after : FileImage} {target : Target} {plan : Plan}
    (trace : EffectTrace target initial after) (prepared : Prepared initial target plan) :
    ∃ next, Prepared after target next := by
  have valid := trace.valid prepared.pair prepared.keeperPrefix prepared.newer
  obtain ⟨unchecked, bytes⟩ := valid.keeper.activeValid
  exact ⟨⟨target.range.through, target.first, after.later.visible, target.trimmed ++ unchecked⟩,
    ⟨valid.selected, valid.keeper, valid.later, rfl, rfl, rfl, bytes⟩⟩

/-- An acknowledged repair has the selected pair, exact keeper bytes and
no later names in its visible or crash-surviving inventory. -/
structure FileImage.Ready (image : FileImage) (target : Target) : Prop where
  selected : image.directory.active = target.pair
  settled : image.directory.crashImages = [target.pair]
  keeper : image.keeper.active = some target.trimmed
  keeperDurable : image.keeper.crashImages = [some target.trimmed]
  pruned : image.later.DurablyEmpty

/-- Syncing the retained keeper makes its current contents durable.
Selection and suffix removal are established at the directory barrier. -/
theorem FileImage.readyAfterKeeperSync {image : FileImage} {target : Target}
    (selected : image.directory.active = target.pair)
    (settled : image.directory.crashImages = [target.pair])
    (bytes : image.keeper.active = some target.trimmed) (pruned : image.later.DurablyEmpty) :
    image.syncKeeper.Ready target :=
  ⟨selected, settled, bytes, congrArg (fun payload => [payload]) bytes, pruned⟩

def FileImage.effect (image : FileImage) (target : Target) : Step → Option FileImage
  | .unlink first => some (image.unlinkLater first)
  | .syncPruned => some image.syncDirectory
  | .replace action => (image.keeper.step target.trimmed action).map fun keeper =>
      { (if action = .syncDirectory then image.syncDirectory else image) with keeper }
  | .syncKeeper => some image.syncKeeper

private theorem replacedPrefix (image : FileImage) (target : Target) (cut : Nat) :
    ((Publication.steps.take cut).map Step.replace).foldlM (fun state action => state.effect target action) image =
      image.replacementCut target cut := by
  rcases cut with _ | _ | _ | _ | cut
  · rfl
  · rfl
  · rfl
  · rfl
  · have complete : Publication.steps.length ≤ cut + 1 + 1 + 1 + 1 := by simp [Publication.steps]
    simp only [FileImage.replacementCut, List.take_of_length_le complete, ite_eq_left complete]
    rfl

private theorem unlinks_execute (image : FileImage) (target : Target) (addresses : List Nat) :
    (addresses.map Step.unlink).foldlM (fun state action => state.effect target action) image =
      some (addresses.foldl FileImage.unlinkLater image) := by
  induction addresses generalizing image with
  | nil => rfl
  | cons first rest ih => exact ih (image.unlinkLater first)

/-- A sequence of unlinks confined to later WAL addresses preserves the
selected repair prefix at every reached removal. -/
theorem EffectTrace.unlinks {target : Target} {initial before : FileImage}
    (trace : EffectTrace target initial before) (addresses : List Nat)
    (allowed : ∀ first ∈ addresses, target.range.through < first) :
    EffectTrace target initial (addresses.foldl FileImage.unlinkLater before) := by
  induction addresses generalizing before with
  | nil => exact trace
  | cons first rest ih =>
    exact ih (.unlink trace (allowed first (List.mem_cons_self ..)))
      (fun offset mem => allowed offset (List.mem_cons_of_mem _ mem))

private theorem visibleUnlinks (before : FileImage) (addresses : List Nat) (first : Nat) :
    first ∈ (addresses.foldl FileImage.unlinkLater before).later.visible ↔
      first ∈ before.later.visible ∧ first ∉ addresses := by
  induction addresses generalizing before with
  | nil => simp
  | cons name rest ih =>
    rw [List.foldl_cons, ih]
    simp [FileImage.unlinkLater, LaterNames.unlink, dropName, List.mem_filter, List.mem_cons, and_assoc]

private theorem completedPrune {before : FileImage} {addresses : List Nat}
    (complete : ∀ first ∈ before.later.visible, first ∈ addresses) :
    (addresses.foldl FileImage.unlinkLater before).syncDirectory.later.DurablyEmpty := by
  have absent : (addresses.foldl FileImage.unlinkLater before).later.visible = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro first remains
    obtain ⟨prior, kept⟩ := (visibleUnlinks before addresses first).mp remains
    exact kept (complete first prior)
  simp [FileImage.syncDirectory, LaterNames.syncDirectory, LaterNames.settled, LaterNames.DurablyEmpty, absent]

private theorem keptDuringUnlinks (before : FileImage) (addresses : List Nat) :
    (addresses.foldl FileImage.unlinkLater before).keeper = before.keeper := by
  induction addresses generalizing before with
  | nil => rfl
  | cons first rest ih => exact ih (before.unlinkLater first)

private theorem Prepared.mayUnlink {image : FileImage} {target : Target} {plan : Plan}
    (prepared : Prepared image target plan) {first : Nat} (listed : first ∈ plan.newer) :
    target.range.through < first :=
  prepared.newer _ (List.mem_cons_self ..) _ (prepared.names ▸ listed)

private def keeperActions (plan : Plan) : List Step :=
  if decide (plan.keeperSize < plan.keeperBytes.size) then Publication.steps.map Step.replace else [Step.syncKeeper]

private theorem repairSteps (plan : Plan) :
    steps plan.newer (decide (plan.keeperSize < plan.keeperBytes.size)) =
      plan.newer.map Step.unlink ++ Step.syncPruned :: keeperActions plan := by
  simp [steps, keeperActions, List.append_assoc]

private theorem cutPreservesTrace {initial after : FileImage} {target : Target} {plan : Plan} {cut : Nat}
    (prepared : Prepared initial target plan)
    (applied : ((steps plan.newer (decide (plan.keeperSize < plan.keeperBytes.size))).take cut).foldlM
      (fun state action => state.effect target action) initial.syncDirectory = some after) :
    EffectTrace target initial after := by
  rw [repairSteps, List.take_append, List.foldlM_append, ← List.map_take, unlinks_execute, List.length_map] at applied
  let pruned := (plan.newer.take cut).foldl FileImage.unlinkLater initial.syncDirectory
  change ((Step.syncPruned :: keeperActions plan).take (cut - plan.newer.length)).foldlM
    (fun state action => state.effect target action) pruned = some after at applied
  have prunedTrace : EffectTrace target initial pruned :=
    EffectTrace.authorized.unlinks _ (fun _ mem => prepared.mayUnlink (List.mem_of_mem_take mem))
  cases remaining : cut - plan.newer.length with
  | zero =>
    rw [remaining] at applied
    exact Option.some.inj applied ▸ prunedTrace
  | succ count =>
    have complete : plan.newer.length ≤ cut := by omega
    have all : plan.newer.take cut = plan.newer := List.take_of_length_le complete
    have gone : pruned.syncDirectory.later.DurablyEmpty := by
      unfold pruned
      rw [all]
      exact completedPrune (fun first present => prepared.names.symm ▸ present)
    have settled := prunedTrace.syncPruned
    have exactKeeper : pruned.syncDirectory.keeper = initial.keeper := by
      exact keptDuringUnlinks _ _
    rw [remaining] at applied
    change ((keeperActions plan).take count).foldlM (fun state action => state.effect target action)
      pruned.syncDirectory = some after at applied
    by_cases needs : plan.keeperSize < plan.keeperBytes.size
    · simp only [keeperActions, decide_eq_true needs, ite_true, ← List.map_take, replacedPrefix] at applied
      exact settled.replace gone applied
    · have aligned : pruned.syncDirectory.keeper.active = some target.trimmed := by
        rw [exactKeeper]
        exact prepared.aligned needs
      cases count with
      | zero => cases applied; exact settled
      | succ count =>
        have entire : [Step.syncKeeper].length ≤ count + 1 := by simp
        simp only [keeperActions, decide_eq_false needs, Bool.false_eq_true, ite_false,
          List.take_of_length_le entire, List.foldlM_cons, List.foldlM_nil, FileImage.effect, Bind.bind, Option.bind] at applied
        cases applied
        exact settled.aligned gone aligned

/-- Continuing an authorized trace can settle the same metadata again,
including retries that observe no remaining later names. -/
theorem EffectTrace.trans {target : Target} {initial middle after : FileImage}
    (earlier : EffectTrace target initial middle) (retry : EffectTrace target middle after) :
    EffectTrace target initial after := by
  induction retry with
  | authorized => exact earlier.syncPruned
  | unlink _ later prior => exact prior.unlink later
  | syncPruned _ prior => exact prior.syncPruned
  | replace _ gone ran prior => exact prior.replace gone ran
  | aligned _ gone exactRead prior => exact prior.aligned gone exactRead
  | scratch _ prior => exact prior.scratch
  | crash _ metadataSurvives keeperSurvives laterSurvive prior =>
    exact prior.crash metadataSurvives keeperSurvives laterSurvive

def Plan.actions (plan : Plan) : List Step :=
  steps plan.newer (decide (plan.keeperSize < plan.keeperBytes.size))

private theorem completeExecution {initial : FileImage} {target : Target} {plan : Plan}
    (prepared : Prepared initial target plan) :
    ∃ after, plan.actions.foldlM (fun state action => state.effect target action) initial.syncDirectory = some after ∧
      after.Ready target := by
  let pruned := (plan.newer.foldl FileImage.unlinkLater initial.syncDirectory).syncDirectory
  have gone : pruned.later.DurablyEmpty :=
    completedPrune (fun _ present => prepared.names.symm ▸ present)
  have sameDirectory : (plan.newer.foldl FileImage.unlinkLater initial.syncDirectory).directory =
      initial.syncDirectory.directory := by
    have unchanged (before : FileImage) (names : List Nat) :
        (names.foldl FileImage.unlinkLater before).directory = before.directory := by
      induction names generalizing before with
      | nil => rfl
      | cons first rest ih => exact ih (before.unlinkLater first)
    exact unchanged _ _
  have visible : pruned.directory.active = target.pair := by
    change (plan.newer.foldl FileImage.unlinkLater initial.syncDirectory).directory.active = target.pair
    rw [sameDirectory]
    exact prepared.pair
  have durable : pruned.directory.crashImages = [target.pair] := congrArg (fun pair => [pair]) visible
  have execute : plan.actions.foldlM (fun state action => state.effect target action) initial.syncDirectory =
      (keeperActions plan).foldlM (fun state action => state.effect target action) pruned := by
    rw [Plan.actions, repairSteps, List.foldlM_append, unlinks_execute]
    rfl
  rw [execute]
  by_cases needs : plan.keeperSize < plan.keeperBytes.size
  · let after := { pruned.syncDirectory with keeper := Publication.Image.settled (some target.trimmed) }
    have complete := replacedPrefix pruned target Publication.steps.length
    rw [List.take_length, FileImage.replacementCut, List.take_length,
      ite_eq_left (Nat.le_refl _), Publication.successful_replace] at complete
    have prunedAgain : after.later.DurablyEmpty := ⟨gone.1, congrArg (fun names => [names]) gone.1⟩
    refine ⟨after, ?_, ⟨visible, durable, rfl, rfl, prunedAgain⟩⟩
    simpa [keeperActions, needs, after] using complete
  · have sameKeeper : pruned.keeper = initial.keeper := keptDuringUnlinks _ _
    have aligned : pruned.keeper.active = some target.trimmed := by
      rw [sameKeeper]
      exact prepared.aligned needs
    refine ⟨pruned.syncKeeper, ?_, ⟨visible, durable, aligned, congrArg (fun bytes => [bytes]) aligned, gone⟩⟩
    simp [keeperActions, needs, List.foldlM_cons, FileImage.effect]

/-- The first directory callback may stop before settling the selected
metadata, or report an error after it settles. Preparation already
validated the visible marker and did no destructive work. -/
def MetadataReport (initial : FileImage) (sync : EStateM e FileImage Unit) : Prop :=
  match sync initial with
  | .ok _ after => after = initial.syncDirectory
  | .error _ after => after = initial ∨ after = initial.syncDirectory

/-- The action is next after an executed prefix of this exact plan. -/
def ReachesAction (target : Target) (initial : FileImage) (actions : List Step)
    (action : Step) (before : FileImage) : Prop :=
  ∃ prior rest, actions = prior ++ action :: rest ∧
    prior.foldlM (fun state step => state.effect target step) initial = some before

private theorem ReachesAction.head (target : Target) (initial : FileImage) (action : Step) (rest : List Step) :
    ReachesAction target initial (action :: rest) action initial :=
  ⟨[], rest, rfl, rfl⟩

private theorem ReachesAction.cons {target : Target} {initial next before : FileImage} {first action : Step}
    {actions : List Step} (effect : initial.effect target first = some next)
    (reached : ReachesAction target next actions action before) :
    ReachesAction target initial (first :: actions) action before := by
  obtain ⟨prior, rest, schedule, executed⟩ := reached
  refine ⟨first :: prior, rest, congrArg (List.cons first) schedule, ?_⟩
  simpa only [List.foldlM_cons, effect, Bind.bind, Option.bind] using executed

/-- Exact primitive callback contract for the shared path dispatcher.
An error may report either public effect and leave arbitrary scratch.
A retry never resumes at a later replacement step using these bytes. -/
def EffectReports (target : Target) (initial : FileImage) (actions : List Step)
    (perform : Step → EStateM e FileImage Unit) : Prop :=
  ∀ action before, ReachesAction target initial actions action before → match perform action before with
    | .ok _ after => before.effect target action = some after
    | .error _ after => ∃ publicResult,
        (publicResult = before ∨ before.effect target action = some publicResult) ∧
        after = publicResult.withScratch after.keeper.staged

private theorem observedPrefix {initial : FileImage} {target : Target}
    {perform : Step → EStateM e FileImage Unit} (actions : List Step)
    (reports : EffectReports target initial actions perform) :
    match (actions.forM perform) initial with
    | .ok _ after => actions.foldlM (fun state action => state.effect target action) initial = some after
    | .error _ after => ∃ cut publicResult,
        (actions.take cut).foldlM (fun state action => state.effect target action) initial = some publicResult ∧
        after = publicResult.withScratch after.keeper.staged := by
  induction actions generalizing initial with
  | nil => rfl
  | cons action rest ih =>
    have report := reports action initial (ReachesAction.head _ _ _ _)
    change (match EStateM.bind (perform action) (fun _ => rest.forM perform) initial with
      | .ok _ after => (action :: rest).foldlM (fun state action => state.effect target action) initial = some after
      | .error _ after => ∃ cut publicResult,
          ((action :: rest).take cut).foldlM (fun state action => state.effect target action) initial = some publicResult ∧
          after = publicResult.withScratch after.keeper.staged)
    unfold EStateM.bind
    cases ran : perform action initial with
    | error _ after =>
      rw [ran] at report
      obtain ⟨publicResult, effect, scratch⟩ := report
      rcases effect with rfl | applied
      · exact ⟨0, publicResult, rfl, scratch⟩
      · exact ⟨1, publicResult, by simp [List.foldlM_cons, applied], scratch⟩
    | ok _ next =>
      rw [ran] at report
      have follow := ih (initial := next) (fun action before reached => reports action before (reached.cons report))
      change (match (rest.forM perform) next with
        | .ok _ after => (action :: rest).foldlM (fun state action => state.effect target action) initial = some after
        | .error _ after => ∃ cut publicResult,
            ((action :: rest).take cut).foldlM (fun state action => state.effect target action) initial = some publicResult ∧
            after = publicResult.withScratch after.keeper.staged)
      cases continued : (rest.forM perform) next with
      | ok _ after =>
        rw [continued] at follow
        change (action :: rest).foldlM (fun state action => state.effect target action) initial = some after
        simp only [List.foldlM_cons, report, Bind.bind, Option.bind]
        exact follow
      | error _ after =>
        rw [continued] at follow
        obtain ⟨cut, publicResult, applied, scratch⟩ := follow
        refine ⟨cut + 1, publicResult, ?_, scratch⟩
        simpa only [List.take_succ_cons, List.foldlM_cons, report, Bind.bind, Option.bind] using applied

/-- Interpretation of the native schedule after read-only preparation.
The static preparation guard is discharged by `Prepared.valid`. -/
def FileImage.runObserved (initial : FileImage) (plan : Plan)
    (settleMetadata : EStateM e FileImage Unit) (perform : Step → EStateM e FileImage Unit) :
    EStateM.Result e FileImage Unit :=
  (settleMetadata >>= fun _ => plan.actions.forM perform) initial

/-- Every report from the shared repair schedule preserves recovery from the
selected pair after authority settles. An earlier failure leaves the image
untouched. Successful reports also establish the durable append-ready image. -/
theorem runObserved_safe {initial : FileImage} {target : Target} {plan : Plan}
    (prepared : Prepared initial target plan) {settleMetadata : EStateM e FileImage Unit}
    {perform : Step → EStateM e FileImage Unit}
    (metadataReport : MetadataReport initial settleMetadata)
    (reports : EffectReports target initial.syncDirectory plan.actions perform) :
    match initial.runObserved plan settleMetadata perform with
    | .ok _ after => EffectTrace target initial after ∧ after.Ready target
    | .error _ after => after = initial ∨ EffectTrace target initial after := by
  have metadata := metadataReport
  unfold MetadataReport at metadata
  unfold FileImage.runObserved
  change (match EStateM.bind settleMetadata (fun _ => plan.actions.forM perform) initial with
    | .ok _ after => EffectTrace target initial after ∧ after.Ready target
    | .error _ after => after = initial ∨ EffectTrace target initial after)
  unfold EStateM.bind
  cases barrier : settleMetadata initial with
  | error err after =>
    rw [barrier] at metadata
    rcases metadata with rfl | rfl
    · exact .inl rfl
    · exact .inr .authorized
  | ok _ settled =>
    rw [barrier] at metadata
    subst settled
    have outcome := observedPrefix plan.actions reports
    change (match (plan.actions.forM perform) initial.syncDirectory with
      | .ok _ after => EffectTrace target initial after ∧ after.Ready target
      | .error _ after => after = initial ∨ EffectTrace target initial after)
    cases ran : (plan.actions.forM perform) initial.syncDirectory with
    | ok _ after =>
      rw [ran] at outcome
      obtain ⟨expected, complete, ready⟩ := completeExecution prepared
      have exactImage := Option.some.inj (complete.symm.trans outcome)
      have applied := outcome
      rw [← List.take_length (l := plan.actions)] at applied
      exact ⟨cutPreservesTrace prepared applied, exactImage ▸ ready⟩
    | error _ after =>
      rw [ran] at outcome
      obtain ⟨cut, publicResult, applied, scratch⟩ := outcome
      exact .inr (scratch ▸ (cutPreservesTrace prepared applied).scratch)

private theorem successfulReports {target : Target} {perform : Step → EStateM e FileImage Unit}
    {actions : List Step} {initial after : FileImage}
    (executed : actions.foldlM (fun state action => state.effect target action) initial = some after)
    (healthy : ∀ action before next, ReachesAction target initial actions action before →
      before.effect target action = some next → perform action before = .ok () next) :
    (actions.forM perform) initial = .ok () after := by
  induction actions generalizing initial with
  | nil =>
    cases executed
    rfl
  | cons action rest ih =>
    rw [List.foldlM_cons] at executed
    cases effect : initial.effect target action with
    | none => simp [effect] at executed
    | some next =>
      change EStateM.bind (perform action) (fun _ => rest.forM perform) initial = _
      unfold EStateM.bind
      rw [healthy action _ _ (ReachesAction.head _ _ _ _) effect]
      exact ih (by simpa only [effect, Bind.bind, Option.bind] using executed)
        (fun action before after reached => healthy action before after (reached.cons effect))

/-- A fresh retry can finish when its selected reads and every required
callback succeed. The completion follows from the actual shared order,
including both barriers when there are no remaining names to unlink. -/
theorem runObserved_completes {initial : FileImage} {target : Target} {plan : Plan}
    (prepared : Prepared initial target plan) {settleMetadata : EStateM e FileImage Unit}
    {perform : Step → EStateM e FileImage Unit}
    (settles : settleMetadata initial = .ok () initial.syncDirectory)
    (healthy : ∀ action before next, ReachesAction target initial.syncDirectory plan.actions action before →
      before.effect target action = some next → perform action before = .ok () next) :
    ∃ after, initial.runObserved plan settleMetadata perform = .ok () after ∧
      after.Ready target ∧ EffectTrace target initial after := by
  obtain ⟨after, complete, ready⟩ := completeExecution prepared
  have trace := complete
  rw [← List.take_length (l := plan.actions)] at trace
  refine ⟨after, ?_, ready, cutPreservesTrace (cut := plan.actions.length) prepared
    trace⟩
  change EStateM.bind settleMetadata (fun _ => plan.actions.forM perform) initial = _
  unfold EStateM.bind
  rw [settles]
  exact successfulReports complete healthy

/-- The executable path dispatcher projects to the exact observed effect
sequence when preparation returns a checked plan without changing files. -/
theorem runAt_observed {initial : FileImage} {target : Target} {plan : Plan}
    (prepared : Prepared initial target plan) (dir : DiskDirectory)
    (prepare : EStateM IO.Error FileImage Plan) (preparedRead : prepare initial = .ok plan initial)
    (removeFile : System.FilePath → EStateM IO.Error FileImage (Except IO.Error Unit))
    (write : System.FilePath → ByteArray → EStateM IO.Error FileImage Unit)
    (sync : Array System.FilePath → EStateM IO.Error FileImage Unit)
    (rename : System.FilePath → System.FilePath → EStateM IO.Error FileImage Unit) :
    runAt dir prepare removeFile write sync rename initial =
      initial.runObserved plan (sync #[dir.path]) (performPaths dir plan removeFile throw write sync rename) := by
  unfold runAt
  change EStateM.bind prepare (fun plan => if plan.valid then _ else _) initial = _
  unfold EStateM.bind
  rw [preparedRead]
  simp only [prepared.valid, ite_true]
  rfl

/-- Safety of the executable repair dispatcher under the checked read and
primitive file-effect contracts for its canonical path callbacks. -/
theorem runAt_safe {initial : FileImage} {target : Target} {plan : Plan}
    (prepared : Prepared initial target plan) (dir : DiskDirectory)
    (prepare : EStateM IO.Error FileImage Plan) (preparedRead : prepare initial = .ok plan initial)
    (removeFile : System.FilePath → EStateM IO.Error FileImage (Except IO.Error Unit))
    (write : System.FilePath → ByteArray → EStateM IO.Error FileImage Unit)
    (sync : Array System.FilePath → EStateM IO.Error FileImage Unit)
    (rename : System.FilePath → System.FilePath → EStateM IO.Error FileImage Unit)
    (metadataReport : MetadataReport initial (sync #[dir.path]))
    (reports : EffectReports target initial.syncDirectory plan.actions
      (performPaths dir plan removeFile throw write sync rename)) :
    match runAt dir prepare removeFile write sync rename initial with
    | .ok _ after => EffectTrace target initial after ∧ after.Ready target
    | .error _ after => after = initial ∨ EffectTrace target initial after := by
  rw [runAt_observed prepared dir prepare preparedRead removeFile write sync rename]
  have safety := runObserved_safe prepared metadataReport reports
  cases ran : initial.runObserved plan (sync #[dir.path]) (performPaths dir plan removeFile throw write sync rename) <;>
    simpa only [ran] using safety

end Alvoki.Storage.WalSegmentRepair
