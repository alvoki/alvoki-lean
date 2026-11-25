import Alvoki.Storage.Disk.RunRetentionCollection
import Alvoki.Storage.Disk.WalSegmentCollectionSpace
import Alvoki.Storage.Disk.WalSegmentCollectionNames

namespace Alvoki.Storage.DiskSession

open CheckpointPublication WalSegmentRepair
open Compaction.Model (retentionRowBound)
open WAL (frameSize)

private theorem namedRunTotal_filter (files : RunFiles) (catalog : List RunAddress)
    (keep : RunAddress → Bool) :
    files.namedRunTotal ByteArray.size catalog =
      files.namedRunTotal ByteArray.size (catalog.filter keep) +
        files.namedRunTotal ByteArray.size (catalog.filter fun address => !keep address) := by
  induction catalog with
  | nil => rfl
  | cons address rest ih =>
    cases chosen : keep address <;>
      simp [RunFiles.namedRunTotal, chosen] at ih ⊢ <;> omega

private theorem namedRunTotal_agrees {left right : RunFiles} {catalog : List RunAddress}
    (same : ∀ address ∈ catalog, left address.1 address.2 = right address.1 address.2) :
    left.namedRunTotal ByteArray.size catalog = right.namedRunTotal ByteArray.size catalog := by
  unfold RunFiles.namedRunTotal
  congr 1
  apply List.map_inj_left.mpr
  intro address member
  obtain ⟨generation, index⟩ := address
  change ((left generation index).map ByteArray.size).getD 0 = ((right generation index).map ByteArray.size).getD 0
  rw [show left generation index = right generation index from same (generation, index) member]

private theorem namedRunTotal_empty (catalog : List RunAddress) :
    RunFiles.namedRunTotal (fun _ _ => none) ByteArray.size catalog = 0 := by
  induction catalog with
  | nil => rfl
  | cons address rest ih => simpa [RunFiles.namedRunTotal] using ih

/-- Account for the whole checked run-name catalog after a healthy collection.
The selected addresses are known present. The only added bytes in the total
come from the initial values at unselected addresses that the policy keeps. -/
theorem SegmentedRunCollectionReports.finishedNamedBytes {directory descriptor state runs}
    (reports : SegmentedRunCollectionReports directory state runs)
    (ready : state.RetainedReady directory descriptor)
    (unique : reports.inventory.names.Nodup)
    (complete : ∀ generation index bytes, runs.visible generation index = some bytes →
      renderRunFileName generation index ∈ reports.inventory.names)
    {count : Nat}
    (known : ∀ index < count, ∃ bytes, runs.visible state.installed.generation index = some bytes)
    (regular : ∀ generation index bytes, runs.visible generation index = some bytes →
      generation < state.installed.generation → generation ∉ reports.held →
      reports.inventory.kindAt (directory.file (.run generation index)) = .ok .file) :
    let catalog := reports.inventory.names.filterMap parseRunFileName
    let selected := (List.range count).map fun index => (state.installed.generation, index)
    let extra := catalog.filter fun address =>
      !selected.contains address && retainRunGeneration state.installed.generation reports.held address.1
    let collected := runs.finishPass reports.selected
    catalog.Nodup ∧
    (∀ generation index bytes, collected.visible generation index = some bytes → (generation, index) ∈ catalog) ∧
    collected.visible.namedRunTotal ByteArray.size catalog =
      collected.visible.namedRunTotal ByteArray.size selected + runs.visible.namedRunTotal ByteArray.size extra := by
  intro catalog selected extra collected
  have catalogUnique : catalog.Nodup := by
    apply unique.filterMap parseRunFileName
    intro left right different address parsed next other same
    obtain ⟨generation, index⟩ := address
    subst next
    exact different ((parseRunFileName_eq_some_iff.mp parsed).trans (parseRunFileName_eq_some_iff.mp other).symm)
  have initialCatalog generation index bytes (present : runs.visible generation index = some bytes) :
      (generation, index) ∈ catalog :=
    List.mem_filterMap.mpr ⟨_, complete generation index bytes present, parseRunFileName_render ..⟩
  have selectedUnique : selected.Nodup :=
    List.Pairwise.map _ (fun _ _ different same => different (congrArg Prod.snd same)) List.nodup_range
  have selectedSubset : selected ⊆ catalog := by
    intro address member
    obtain ⟨index, within, rfl⟩ := List.mem_map.mp member
    obtain ⟨bytes, present⟩ := known index (List.mem_range.mp within)
    exact initialCatalog _ _ bytes present
  have partition :
      (catalog.filter selected.contains).Perm selected := by
    apply (List.perm_ext_iff_of_nodup (catalogUnique.filter _) selectedUnique).mpr
    intro address
    simp only [List.mem_filter, List.contains_iff_mem]
    exact ⟨And.right, fun member => ⟨selectedSubset member, member⟩⟩
  have retained generation index
      (keep : retainRunGeneration state.installed.generation reports.held generation = true) :
      collected.visible generation index = runs.visible generation index := by
    have unselected : (generation, index) ∉ reports.selected := by
      intro chosen
      obtain ⟨_, older, unheld, _⟩ := (reports.selected_eligible ready).mp chosen
      exact Bool.noConfusion ((retainRunGeneration_false_iff.mpr ⟨older, unheld⟩).symm.trans keep)
    simp [(runs.finishPass_binding reports.selected (generation, index)).1, unselected, collected]
  have removed generation index
      (drop : retainRunGeneration state.installed.generation reports.held generation = false) :
      collected.visible generation index = none := by
    obtain ⟨older, unheld⟩ := retainRunGeneration_false_iff.mp drop
    cases present : runs.visible generation index with
    | none =>
      simp [(runs.finishPass_binding reports.selected (generation, index)).1, present, collected]
    | some bytes =>
      have chosen : (generation, index) ∈ reports.selected := (reports.selected_eligible ready).mpr
        ⟨complete generation index bytes present, older, unheld, regular generation index bytes present older unheld⟩
      simp [(runs.finishPass_binding reports.selected (generation, index)).1, chosen, collected]
  let rest := catalog.filter fun address => !selected.contains address
  let keep := fun address : RunAddress => retainRunGeneration state.installed.generation reports.held address.1
  have extraEq : rest.filter keep = extra := by simp [rest, keep, extra, List.filter_filter, Bool.and_comm]
  have keptSum : collected.visible.namedRunTotal ByteArray.size (rest.filter keep) =
      runs.visible.namedRunTotal ByteArray.size extra := by
    rw [← extraEq]
    exact namedRunTotal_agrees fun address member => retained _ _ (List.mem_filter.mp member).2
  have droppedSum : collected.visible.namedRunTotal ByteArray.size (rest.filter fun address => !keep address) = 0 := by
    rw [← namedRunTotal_empty (rest.filter fun address => !keep address)]
    apply namedRunTotal_agrees
    intro address member
    exact removed _ _ (by simpa [keep] using (List.mem_filter.mp member).2)
  have selectedSum := (partition.map
    (fun (generation, index) => ((collected.visible generation index).map ByteArray.size).getD 0)).sum_nat
  refine ⟨catalogUnique, ?_, ?_⟩
  · intro generation index bytes present
    cases kept : retainRunGeneration state.installed.generation reports.held generation with
    | false => rw [removed _ _ kept] at present; contradiction
    | true => exact initialCatalog generation index bytes ((retained _ _ kept).symm.trans present)
  · rw [namedRunTotal_filter _ _ selected.contains]
    change _ + collected.visible.namedRunTotal ByteArray.size rest = _
    rw [namedRunTotal_filter _ rest keep, keptSum, droppedSum, Nat.add_zero]
    exact congrArg (· + runs.visible.namedRunTotal ByteArray.size extra) selectedSum

/-- A complete scheduled maintenance cycle bounds the data bytes under
canonical run and WAL segment names. The caller chooses an active segment
width cap and a budget for unselected run names that the policy keeps. The
checkpoint covers every acknowledged frame at this cut. This is a namespace
payload budget under the reported successful effects and inventories. -/
theorem SegmentedCheckpointReport.Installs.maintainedNamedPayload {directory descriptor}
    {before published : SegmentedWriterState} {table : PackedTable}
    (ready : before.RetainedReady directory descriptor)
    (pass : PackedTable.RunRetentionSteps 0 before.installed.table.runs.length before.installed.table table)
    (empty : table.memoryIsEmpty = true)
    {attempt : SegmentedCheckpointReport directory (before.withTable table)}
    (observed : attempt.Valid) (installed : attempt.Installs published)
    {runs : RunUnlinkImage} (reports : SegmentedRunCollectionReports directory published runs)
    (unique : reports.inventory.names.Nodup)
    (complete : ∀ generation index bytes, runs.visible generation index = some bytes →
      renderRunFileName generation index ∈ reports.inventory.names)
    (regular : ∀ generation index bytes, runs.visible generation index = some bytes →
      generation < published.installed.generation → generation ∉ reports.held →
      reports.inventory.kindAt (directory.file (.run generation index)) = .ok .file)
    (healthy : RunUnlinkScheduleHealthy runs (RunCollection.steps reports.selected) reports.perform)
    {walReport : SegmentedCollectionReport directory
      (published.afterRunCollection (runs.finishPass reports.selected).guaranteed)}
    {after : SegmentedWriterState} (walInstalled : walReport.Installs after)
    (walComplete : walReport.offsets = published.wal.collectionOffsets)
    {cap : Nat} (width : before.wal.active.last - before.wal.active.first ≤ cap) :
    let catalog := reports.inventory.names.filterMap parseRunFileName
    let selected := (List.range table.runs.length).map fun index => (published.installed.generation, index)
    let extra := catalog.filter fun address =>
      !selected.contains address && retainRunGeneration published.installed.generation reports.held address.1
    let runBytes := after.published.durable.namedRunTotal ByteArray.size catalog
    let walBytes := (WalSegment.concatenate after.wal.segments).size
    reports.run = .ok () (runs.finishPass reports.selected) ∧
    catalog.Nodup ∧
    (∀ generation index bytes, after.published.durable generation index = some bytes → (generation, index) ∈ catalog) ∧
    after.RetainedReady directory descriptor ∧ after.owners = before.owners ∧ after.history = before.history ∧
    runBytes = (table.runs.map (·.run.bytes.size)).sum + runs.visible.namedRunTotal ByteArray.size extra ∧
    walBytes = before.wal.active.bytes.size ∧ walBytes ≤ cap * frameSize ∧
    after.wal.segments =
      (before.wal.sealed.filter fun segment => decide (segment.first = segment.last)) ++ [before.wal.active] ∧
    ∀ extraBudget, runs.visible.namedRunTotal ByteArray.size extra ≤ extraBudget →
      runBytes + walBytes ≤
        16 * before.installed.table.runs.length +
          32 * (before.installed.table.runs.map (fun run =>
            retentionRowBound run.history.rows before.installed.table.pins.floor)).sum +
          extraBudget + cap * frameSize := by
  intro catalog selected extra runBytes walBytes
  let collected := runs.finishPass reports.selected
  let postRun := published.afterRunCollection collected.guaranteed
  let files := table.runs.map (·.run.bytes)
  obtain ⟨returned, _, _, collectedReady, _, _, _, exactFiles, selectedBytes, boundedRuns⟩ :=
    installed.collectRetainedRunPayload ready pass empty observed reports
      (fun generation index bytes present older unheld =>
        ⟨complete generation index bytes present, regular generation index bytes present older unheld⟩) healthy
  have initialPresent (index : Nat) (within : index < table.runs.length) :
      ∃ bytes, runs.visible published.installed.generation index = some bytes := by
    have inside : index < files.length := by simpa [files] using within
    have exactFile := exactFiles index inside
    rw [(runs.finishPass_binding reports.selected (published.installed.generation, index)).1] at exactFile
    split at exactFile
    · contradiction
    · exact ⟨_, exactFile⟩
  have retained := (SegmentedWriterTrace.empty.retainRuns pass).preservesRetained ready
  have publishedReady := (installed.preservesRetained observed retained.1).1
  obtain ⟨uniqueCatalog, catalogComplete, runSum⟩ :=
    reports.finishedNamedBytes publishedReady unique complete initialPresent regular
  have runMap : after.published.durable = collected.visible := by
    obtain ⟨_, _, rfl⟩ := walInstalled
    exact congrArg Image.durable (RunUnlinkImage.project_settled collected.visible published.published.manifest)
  have namedRuns : runBytes =
      (table.runs.map (·.run.bytes.size)).sum + runs.visible.namedRunTotal ByteArray.size extra := by
    change after.published.durable.namedRunTotal ByteArray.size catalog = _
    rw [runMap, runSum]
    have bytes := congrArg (· + runs.visible.namedRunTotal ByteArray.size extra) selectedBytes
    simpa only [catalog, selected, files, List.length_map, List.map_map, Function.comp_def] using bytes
  obtain ⟨nextReady, _, _, _, _, _, owners, _⟩ := walInstalled.outcome collectedReady
  have full : postRun.target.range.through = postRun.target.range.watermark := by
    obtain ⟨base, restored, _, committed⟩ := installed.restored
    have checkpointWatermark := collectedReady.resumed.selected.watermark
    change selectedCheckpointWatermark published.target.pair.manifest =
      some (published.checkpoint.getD (.empty, 0)).1.committed.toNat at checkpointWatermark
    rw [restored] at checkpointWatermark
    have selectedClock := (DirectoryPublication.Bindings.walRange_accounting postRun.target.decoded).1
    calc
      postRun.target.range.through = published.history.length := collectedReady.resumed.through
      _ = base.committed.toNat := committed.symm
      _ = postRun.target.range.watermark := Option.some.inj (checkpointWatermark.symm.trans selectedClock)
  have keeperPayload : WalSegment.concatenate after.wal.segments = before.wal.active.bytes := by
    rw [walInstalled.collectedWalPayload_checkpointCovered collectedReady walComplete full]
    change published.wal.active.bytes = before.wal.active.bytes
    rw [installed.wal]
    rfl
  have namedWal : walBytes ≤ cap * frameSize := by
    change (WalSegment.concatenate after.wal.segments).size ≤ cap * frameSize
    rw [keeperPayload, ready.layout.activeBytes, WAL.encode_size, List.length_drop, ← ready.layout.activeEnd, Nat.mul_comm]
    exact Nat.mul_le_mul_right _ width
  have keeperCovered : postRun.wal.active.first ≤ postRun.target.range.watermark := by
    have member : postRun.wal.active ∈ postRun.wal.segments :=
      List.mem_append_right _ (List.mem_singleton_self _)
    have ends : postRun.wal.active.last = postRun.target.range.watermark :=
      collectedReady.layout.activeEnd.trans (collectedReady.resumed.through.symm.trans full)
    exact ends ▸ collectedReady.layout.forward _ member
  have names : after.wal.segments =
      (before.wal.sealed.filter fun segment => decide (segment.first = segment.last)) ++ [before.wal.active] := by
    rw [walInstalled.retainedWalNames_keeperCovered collectedReady walComplete keeperCovered]
    change (published.wal.sealed.filter fun segment => decide (segment.first = segment.last)) ++
      [published.wal.active] = _
    rw [installed.wal]
    rfl
  refine ⟨returned, uniqueCatalog, ?_, nextReady, owners.trans installed.owners,
    walInstalled.history.trans installed.history, namedRuns, congrArg ByteArray.size keeperPayload, namedWal, names, ?_⟩
  · rw [runMap]
    exact catalogComplete
  · intro extraBudget extraLimit
    rw [namedRuns]
    have bytes := Nat.add_le_add
      (show (table.runs.map (·.run.bytes.size)).sum ≤ _ by
        simpa only [files, List.map_map, Function.comp_def] using boundedRuns) extraLimit
    exact Nat.add_le_add bytes namedWal

end Alvoki.Storage.DiskSession
