import Alvoki.Experiments.L0.ManifestRecovery
import Alvoki.Experiments.L0.NativeBridge
import Alvoki.Experiments.L0.ScheduleSteps

namespace ExperimentalL0
open ManifestComposition DurableBlob
open WalRecoverySlice.Segmented

/-- The reached create in the nonempty flush path supplies both proposals
against one installed catalog. -/
theorem flushChoicesAtCreate {tableId : UInt64}
    {ops : Components (StorageM σ)} {selected : σ → Selected} {ns : TableNamespace σ}
    (evidence : NativeBridge.CallbackEvidence ops selected ns)
    (installed : Installed session (selected start) history)
    (scanned : ops.scan start = .ok view scannedState)
    (fits : view.tail < UInt64.size)
    (created : ops.tables.create session.mem.toList scannedState = .ok tableId stored) :
    let proposal : L0Manifest.Version := ⟨tableId :: session.version.tables, view.tail.toUInt64⟩
    Nonempty (Durable (selected stored) history) ∧
    Nonempty (Durable ((selected stored).publish proposal) history) := by
  obtain ⟨prior, version, mem⟩ := installed
  have scan := evidence.effects.scan start
  rw [scanned] at scan
  obtain ⟨rfl, equal⟩ := scan
  have creation := evidence.effects.create scannedState session.mem.toList (rows_ordered session.mem)
  rw [created, equal] at creation
  obtain ⟨sameWal, sameVersion, added⟩ := creation
  have contents (key : UInt64) : lookupRows session.mem.toList key = latest prior.pending key := by
    simp [rows_lookup, mem, replay_lookup]
  let choices := flushPublicationChoices prior sameWal sameVersion added contents
    (rows_ordered session.mem) fits
  exact ⟨⟨choices.1⟩, ⟨by simpa [version] using choices.2⟩⟩

private theorem checksKeepCatalog {ops : Tables (StorageM σ)} {ns : TableNamespace σ}
    (keeps : ∀ s id, match ops.check id s with
      | .ok _ after | .error _ after => ns.Keeps s after tables) (ids : List UInt64) (s : σ) :
    match checkTables ops ids s with
    | .ok _ after | .error _ after => ns.Keeps s after tables := by
  induction ids generalizing s with
  | nil => exact fun _ _ _ _ _ name content => ⟨name, content⟩
  | cons id ids ih =>
    have first := keeps s id
    cases checked : ops.check id s with
    | error error after =>
      simpa [checkTables, Bind.bind, EStateM.bind, checked] using first
    | ok result middle =>
      rw [checked] at first
      have rest := ih middle
      cases ran : checkTables ops ids middle <;>
        rw [ran] at rest <;>
        simpa [checkTables, Bind.bind, EStateM.bind, checked, ran] using first.trans rest

/-- Every path through public recover preserves the durable table namespace
when each reached manifest, WAL and scoped check call frames it. -/
theorem recoverKeepsCatalog {ops : Components (StorageM σ)} {ns : TableNamespace σ}
    (manifest : ∀ s, match ops.manifest.reopen s with
      | .ok _ after | .error _ after => ns.Keeps s after tables)
    (wal : ∀ s, match ops.reopenWal s with
      | .ok _ after | .error _ after => ns.Keeps s after tables)
    (check : ∀ s id, match ops.tables.check id s with
      | .ok _ after | .error _ after => ns.Keeps s after tables) (s : σ) :
    match recover ops s with
    | .ok _ after | .error _ after => ns.Keeps s after tables := by
  have opened := manifest s
  cases manifestRan : ops.manifest.reopen s with
  | error error after =>
    simpa [recover, Bind.bind, EStateM.bind, manifestRan] using opened
  | ok version middle =>
    rw [manifestRan] at opened
    have recovered := wal middle
    cases walRan : ops.reopenWal middle with
    | error error after =>
      rw [walRan] at recovered
      simpa [recover, Bind.bind, EStateM.bind, manifestRan, walRan] using opened.trans recovered
    | ok view checked =>
      rw [walRan] at recovered
      have header := opened.trans recovered
      by_cases bounds : view.base ≤ version.flushedThrough.toNat ∧
          version.flushedThrough.toNat ≤ view.tail
      · cases decoded : (view.batches.drop (version.flushedThrough.toNat - view.base)).mapM decode with
        | none =>
          simp only [recover, Bind.bind, EStateM.bind, manifestRan, walRan, bounds, decoded]
          exact header
        | some rows =>
          have all := checksKeepCatalog check version.tables checked
          cases tableRan : checkTables ops.tables version.tables checked <;>
            rw [tableRan] at all <;>
            simpa [recover, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure,
              manifestRan, walRan, bounds, decoded, tableRan] using header.trans all
      · simp only [recover, Bind.bind, EStateM.bind, manifestRan, walRan, bounds, ite_false]
        exact header

private theorem checkTablesKeepsImage {ops : Tables (StorageM σ)} (image : σ → Image)
    (keeps : ∀ s id after, ops.check id s = .ok () after → image after = image s)
    (ran : checkTables ops ids s = .ok () after) : image after = image s := by
  induction ids generalizing s with
  | nil =>
    cases ran
    rfl
  | cons id ids ih =>
    cases checked : ops.check id s with
    | error error reached => simp [checkTables, Bind.bind, EStateM.bind, checked] at ran
    | ok value middle =>
      cases value
      have rest : checkTables ops ids middle = .ok () after := by
        simpa [checkTables, Bind.bind, EStateM.bind, checked] using ran
      exact (ih rest).trans (keeps s id middle checked)

private theorem recoverKeepsOpenedImage {ops : Components (StorageM σ)} (image : σ → Image)
    (opened : ops.manifest.reopen start = .ok version middle)
    (walKeeps : ∀ s view after, ops.reopenWal s = .ok view after → image after = image s)
    (checkKeeps : ∀ s id after, ops.tables.check id s = .ok () after → image after = image s)
    (ran : recover ops start = .ok session after) :
    image after = image middle := by
  cases reopened : ops.reopenWal middle with
  | error error reached => simp [recover, Bind.bind, EStateM.bind, opened, reopened] at ran
  | ok view checked =>
    by_cases bounds : view.base ≤ version.flushedThrough.toNat ∧
        version.flushedThrough.toNat ≤ view.tail
    · cases decoded : (view.batches.drop (version.flushedThrough.toNat - view.base)).mapM decode with
      | none =>
        simp only [recover, Bind.bind, EStateM.bind, opened, reopened, bounds, decoded] at ran
        cases ran
      | some rows =>
        cases checkedAll : checkTables ops.tables version.tables checked with
        | error error reached =>
          simp [recover, Bind.bind, EStateM.bind, opened, reopened, bounds, decoded, checkedAll] at ran
        | ok value reached =>
          simp [recover, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure,
            opened, reopened, bounds, decoded, checkedAll] at ran
          obtain ⟨rfl, rfl⟩ := ran
          cases value
          exact (checkTablesKeepsImage image checkKeeps checkedAll).trans
            (walKeeps middle view checked reopened)
    · simp only [recover, Bind.bind, EStateM.bind, opened, reopened, bounds, ite_false] at ran
      cases ran

/-- A selected restart image feeds the existing L0 recover schedule and
client trace. Each recovery consumes the durable invariant for the exact
state on which it runs. -/
theorem recoverTwiceTrace
    {ops : Components (StorageM σ)} {selected : σ → Selected} {ns : TableNamespace σ}
    (evidence : NativeBridge.CallbackEvidence ops selected ns)
    (prior : Execution.Run events (some session) (selected start))
    (observation : FlushObservation (flush ops session start))
    (uncertain : observation.event = .flushUncertain)
    (manifestFrame : ∀ s, match ops.manifest.reopen s with
      | .ok _ after | .error _ after => ns.Keeps s after tables)
    (walFrame : ∀ s, match ops.reopenWal s with
      | .ok _ after | .error _ after => ns.Keeps s after tables)
    (checkFrame : ∀ s id, match ops.tables.check id s with
      | .ok _ after | .error _ after => ns.Keeps s after tables)
    (catalog : ns.Represents restarted tables)
    (durable : ∀ history, Installed session (selected start) history →
      Nonempty (Durable (selected restarted) history))
    (failed : recover ops restarted = .error error afterFailure)
    (opened : recover ops afterFailure = .ok first afterFirst)
    (same : selected nextBoot = selected afterFirst)
    (survives : ns.Keeps afterFirst nextBoot tables)
    (reopened : recover ops nextBoot = .ok second afterSecond) :
    Execution.Run (((events ++ [observation.event]) ++ [.openFailed]) ++
      [.reopened] ++ [.stop] ++ [.reopened]) (some second) (selected afterSecond) ∧ ns.Represents afterSecond tables := by
  have stopped := Execution.Run.flushUncertain prior durable
  have offline := stopped.recoverError evidence.effects failed
  have online := offline.recoverOk evidence.effects opened
  have again := Execution.Run.stop online
  rw [← same] at again
  have keptFailure := recoverKeepsCatalog manifestFrame walFrame checkFrame restarted
  have keptFirst := recoverKeepsCatalog manifestFrame walFrame checkFrame afterFailure
  have keptSecond := recoverKeepsCatalog manifestFrame walFrame checkFrame nextBoot
  rw [failed] at keptFailure
  rw [opened] at keptFirst
  rw [reopened] at keptSecond
  rw [uncertain]
  exact ⟨again.recoverOk evidence.effects reopened,
    catalog.frame (keptFailure.trans (keptFirst.trans (survives.trans keptSecond)))⟩

/-- Connect the reached flush creation to the component restart choice.
The manifest is interpreted from the reached publication, while WAL and
catalog correspond to the state whose parent-directory sync succeeded. -/
theorem recoverReachedFlush {tableId : UInt64}
    {ops : Components (StorageM σ)} {selected : σ → Selected} {ns : TableNamespace σ}
    (evidence : NativeBridge.CallbackEvidence ops selected ns)
    (prior : Execution.Run events (some session) (selected start))
    (observation : FlushObservation (flush ops session start))
    (uncertain : observation.event = .flushUncertain)
    (installed : Installed session (selected start) history)
    (nonempty : session.mem.isEmpty = false)
    (scanned : ops.scan start = .ok view scannedState)
    (fits : view.tail < UInt64.size)
    (created : ops.tables.create session.mem.toList scannedState = .ok tableId stored)
    (catalogBefore : ns.Represents scannedState (selected scannedState).tables)
    (creationKeeps : ns.Keeps scannedState stored (selected scannedState).tables)
    (creationCatalog : (selected stored).tables = fun key =>
      if key = tableId then some session.mem.toList else (selected scannedState).tables key)
    (manifest : Interpretation ops.manifest selected)
    (stable : (manifest.image stored).Stable (L0Manifest.encode (selected stored).version))
    (restart :
      let proposal : L0Manifest.Version := ⟨tableId :: session.version.tables, view.tail.toUInt64⟩
      let reached := match (LinuxEffects.backend manifest.directory
          (manifest.publishReports stored proposal)).publish
          (L0Manifest.encode proposal) (manifest.image stored) with
        | .ok _ image | .error _ image => image
      restarted = reached ∨ ∃ survivor ∈ reached.survivors, restarted = .settled survivor)
    (failure : (LinuxEffects.backend manifest.directory (manifest.openReports recoveryState)).reopen restarted = .error () afterFailure)
    (success : (LinuxEffects.backend manifest.directory (manifest.openReports failedState)).reopen afterFailure = .ok bytes settled)
    (nextRestart : nextBoot = settled ∨
      ∃ survivor ∈ settled.survivors, nextBoot = .settled survivor)
    (successAgain : (LinuxEffects.backend manifest.directory (manifest.openReports secondBoot)).reopen nextBoot = .ok later laterState)
    (walKeepsManifest : ∀ s view after, ops.reopenWal s = .ok view after →
      manifest.image after = manifest.image s)
    (checkKeepsManifest : ∀ s id after, ops.tables.check id s = .ok () after →
      manifest.image after = manifest.image s)
    (boot : recoveryState = manifest.install stored restarted)
    (installKeepsTables : ∀ s image,
      ns.Keeps s (manifest.install s image) (selected stored).tables)
    (walFrame : ∀ s, match ops.reopenWal s with
      | .ok _ after | .error _ after => ns.Keeps s after (selected stored).tables)
    (checkFrame : ∀ s id, match ops.tables.check id s with
      | .ok _ after | .error _ after => ns.Keeps s after (selected stored).tables)
    (failedRecovery : recover ops recoveryState = .error error failedState)
    (firstRecovery : recover ops failedState = .ok first firstState)
    (bootAgain : secondBoot = manifest.install firstState nextBoot)
    (secondRecovery : recover ops secondBoot = .ok second finalState) :
    (let proposal : L0Manifest.Version := ⟨tableId :: session.version.tables, view.tail.toUInt64⟩;
      flush ops session start =
        (match ops.manifest.publish proposal stored with
        | .ok _ after => .ok ⟨proposal, ∅⟩ after
        | .error error after => .error error after)) ∧
    ∃ version, (backend manifest.directory (manifest.openReports failedState)).reopen afterFailure = .ok version settled ∧
      (backend manifest.directory (manifest.openReports secondBoot)).reopen nextBoot = .ok version laterState ∧
      manifest.image firstState = settled ∧ manifest.image finalState = laterState ∧
      settled.Stable (L0Manifest.encode version) ∧
      Nonempty (Durable ((selected stored).publish version) history) ∧
      ns.Represents finalState (selected finalState).tables ∧
      (∀ history, Installed second (selected finalState) history → ∀ key,
        match get ops second key finalState with
        | .ok result after => result = denote history key ∧ selected after = selected finalState
        | .error _ after => selected after = selected finalState) ∧
      Execution.Run (events ++ [observation.event] ++ [.openFailed] ++ [.reopened] ++ [.stop] ++
        [.reopened]) (some second) (selected finalState) := by
  have choose (history : Rows) (installed : Installed session (selected start) history) :
      ∃ version, (backend manifest.directory (manifest.openReports failedState)).reopen afterFailure = .ok version settled ∧
        settled.Stable (L0Manifest.encode version) ∧
        Nonempty (Durable ((selected stored).publish version) history) := by
    obtain ⟨⟨old⟩, ⟨new⟩⟩ := flushChoicesAtCreate evidence installed scanned fits created
    obtain ⟨chosen, openedOnce, pinned, durable, _⟩ :=
      recoverPublication manifest.directory (manifest.publishReports stored _) (manifest.openReports recoveryState) (manifest.openReports failedState)
        (selected stored).view (selected stored).tables history old new stable restart failure success
    exact ⟨chosen, openedOnce, pinned, durable⟩
  obtain ⟨version, observed, pinned, ⟨durable⟩⟩ := choose history installed
  have openedAgain := reopenAfterRestart manifest.directory (manifest.openReports secondBoot) pinned durable.unique
    nextRestart successAgain
  have failedBinding := LinuxEffects.reopenBinding manifest.directory (manifest.openReports recoveryState) restarted
  rw [failure] at failedBinding
  have openedBinding := LinuxEffects.reopenBinding manifest.directory (manifest.openReports failedState) afterFailure
  rw [success] at openedBinding
  have restartedActive : restarted.active = L0Manifest.encode version := by
    rw [← failedBinding, ← openedBinding.1, ← openedBinding.2.1]
    exact pinned.1
  have chosenValid : version.Valid := durable.unique
  have bootImage : manifest.image recoveryState = restarted := by
    rw [boot, manifest.imageInstalled _ _ ⟨version, chosenValid, restartedActive⟩]
  have live : (manifest.image recoveryState).active = L0Manifest.encode version :=
    (congrArg Image.active bootImage).trans restartedActive
  have bootWal : (selected recoveryState).view = (selected stored).view :=
    boot.symm ▸ manifest.walFrame stored restarted
  have bootCatalog : (selected recoveryState).tables = (selected stored).tables :=
    boot.symm ▸ manifest.tableFrame stored restarted
  have physical : ns.Keeps stored recoveryState (selected stored).tables :=
    boot.symm ▸ installKeepsTables stored restarted
  obtain ⟨valid, encoded⟩ := manifest.projection recoveryState
  have decoded := encoded.symm.trans live
  have versionEq : (selected recoveryState).version = version := by
    have equal := congrArg L0Manifest.decode decoded
    have chosenValid : version.Valid := durable.unique
    rw [L0Manifest.decode_encode valid, L0Manifest.decode_encode chosenValid] at equal
    exact Option.some.inj equal
  have fields {a b : Selected} (view : a.view = b.view) (version : a.version = b.version)
      (tables : a.tables = b.tables) : a = b := by cases a; cases b; simp_all
  have picked : selected recoveryState = (selected stored).publish version :=
    fields bootWal versionEq bootCatalog
  have restartActive : nextBoot.active = L0Manifest.encode version := by
    rcases nextRestart with same | ⟨survivor, survives, same⟩
    · exact same ▸ pinned.1
    · have survivorEq : survivor = L0Manifest.encode version := by simpa [pinned.2] using survives
      rw [same, survivorEq]
      rfl
  have secondBootImage : manifest.image secondBoot = nextBoot := by
    rw [bootAgain, manifest.imageInstalled _ _ ⟨version, chosenValid, restartActive⟩]
  have survivesAgain : ns.Keeps firstState secondBoot (selected stored).tables :=
    bootAgain.symm ▸ installKeepsTables firstState nextBoot
  obtain ⟨secondValid, secondEncoded⟩ := manifest.projection secondBoot
  rw [secondBootImage, restartActive] at secondEncoded
  have secondVersion : (selected secondBoot).version = version := by
    have equal := congrArg L0Manifest.decode secondEncoded.symm
    have chosenValid : version.Valid := durable.unique
    rw [L0Manifest.decode_encode secondValid, L0Manifest.decode_encode chosenValid] at equal
    exact Option.some.inj equal
  have typedFailure : (backend manifest.directory (manifest.openReports recoveryState)).reopen restarted =
      .error () afterFailure := by
    simp [backend, L0Manifest.backend, Bind.bind, EStateM.bind, failure]
  have failedCall : ops.manifest.reopen recoveryState =
      .error "manifest reopen failed" (manifest.install recoveryState afterFailure) := by
    refine (congrArg (fun b : Backend (StorageM σ) L0Manifest.Version =>
      b.reopen recoveryState) manifest.schedule).trans ?_
    simp [callbacks, bootImage, typedFailure]
  have failureState : failedState = manifest.install recoveryState afterFailure := by
    simp [recover, Bind.bind, EStateM.bind, failedCall] at failedRecovery
    exact failedRecovery.2.symm
  have canonicalFailure : afterFailure.active = L0Manifest.encode version :=
    failedBinding.trans (bootImage ▸ live)
  have exactFailure : manifest.image failedState = afterFailure := by
    rw [failureState, manifest.imageInstalled _ _ ⟨version, chosenValid, canonicalFailure⟩]
  have firstCall : ops.manifest.reopen failedState =
      .ok version (manifest.install failedState settled) := by
    refine (congrArg (fun b : Backend (StorageM σ) L0Manifest.Version =>
      b.reopen failedState) manifest.schedule).trans ?_
    simp [callbacks, exactFailure, observed]
  have secondCall : ops.manifest.reopen secondBoot =
      .ok version (manifest.install secondBoot laterState) := by
    refine (congrArg (fun b : Backend (StorageM σ) L0Manifest.Version =>
      b.reopen secondBoot) manifest.schedule).trans ?_
    simp [callbacks, secondBootImage, openedAgain.1]
  have exactFirst := recoverKeepsOpenedImage manifest.image firstCall walKeepsManifest
    checkKeepsManifest firstRecovery
  rw [manifest.imageInstalled _ _ ⟨version, chosenValid, pinned.1⟩] at exactFirst
  have exactSecond := recoverKeepsOpenedImage manifest.image secondCall walKeepsManifest
    checkKeepsManifest secondRecovery
  rw [manifest.imageInstalled _ _ ⟨version, chosenValid, openedAgain.2.1⟩] at exactSecond
  have firstDurable : Durable (selected recoveryState) history := picked.symm ▸ durable
  have firstFailure := recover_refines evidence.effects recoveryState firstDurable
  rw [failedRecovery] at firstFailure
  have firstOpened := recover_refines evidence.effects failedState (firstFailure.symm ▸ firstDurable)
  rw [firstRecovery] at firstOpened
  have selectedFirst := firstOpened.1.trans (firstFailure.trans picked)
  have firstWal := congrArg Selected.view selectedFirst
  have firstCatalog := congrArg Selected.tables selectedFirst
  have secondBootWal : (selected secondBoot).view = (selected stored).view :=
    (bootAgain.symm ▸ manifest.walFrame firstState nextBoot).trans
      firstWal
  have secondBootCatalog : (selected secondBoot).tables = (selected stored).tables :=
    (bootAgain.symm ▸ manifest.tableFrame firstState nextBoot).trans
      firstCatalog
  have sameSelection : selected secondBoot = selected firstState :=
    (fields (b := (selected stored).publish version) secondBootWal secondVersion secondBootCatalog).trans selectedFirst.symm
  obtain ⟨producer⟩ := evidence.create
  have publishedCatalog := producer.catalogAfter catalogBefore created
    creationKeeps creationCatalog
  have manifestFrame (s : σ) : match ops.manifest.reopen s with
      | .ok _ after | .error _ after => ns.Keeps s after (selected stored).tables := by
    rw [congrArg (fun b : Backend (StorageM σ) L0Manifest.Version => b.reopen s) manifest.schedule]
    cases ran : (backend manifest.directory (manifest.openReports s)).reopen (manifest.image s) with
    | ok version image => simpa [callbacks, ran] using installKeepsTables s image
    | error error image => simpa [callbacks, ran] using installKeepsTables s image
  have ⟨trace, catalog⟩ := recoverTwiceTrace evidence prior observation uncertain manifestFrame walFrame checkFrame
    (publishedCatalog.frame physical)
    (fun history installed => by
      obtain ⟨chosen, opened, _, durable⟩ := choose history installed
      rw [observed] at opened
      cases opened
      exact picked.symm ▸ durable)
    failedRecovery firstRecovery sameSelection survivesAgain secondRecovery
  have secondDurable : Durable (selected secondBoot) history :=
    (fields (b := (selected stored).publish version) secondBootWal secondVersion secondBootCatalog).symm ▸ durable
  have secondOpened := recover_refines evidence.effects secondBoot secondDurable
  rw [secondRecovery] at secondOpened
  have finalCatalog : (selected finalState).tables = (selected stored).tables :=
    (congrArg Selected.tables secondOpened.1).trans secondBootCatalog
  have reachedCatalog : ns.Represents finalState (selected finalState).tables :=
    finalCatalog.symm ▸ catalog
  refine ⟨?_, version, observed, openedAgain.1, exactFirst, exactSecond, pinned, ⟨durable⟩,
    reachedCatalog, (fun _ installed key => evidence.get reachedCatalog installed key), trace⟩
  simp only [flush, nonempty, Bool.false_eq_true, ite_false, Bind.bind, EStateM.bind,
    scanned, fits, ite_true, created]
  split <;> (rename_i issued; rw [issued] <;> rfl)

end ExperimentalL0
