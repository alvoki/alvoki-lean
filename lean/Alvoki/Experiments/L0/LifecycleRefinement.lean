import Alvoki.Experiments.L0.Lifecycle
import Alvoki.Experiments.L0.NativeBridge
import Alvoki.Experiments.L0.RestartRefinement

namespace ExperimentalL0.Lifecycle
open Proof

variable {W S : Type}
variable {callbacks : Callbacks (EStateM String S) W}
variable {unavailable : String}
local notation "ops" => callbacksWithPhase callbacks unavailable
variable {selected : S → Selected}
variable {namespaceState : TableNamespace S}
local notation "tns" => namespaceState.storage (phase := Phase W)

/-- An initialized empty table catalog needs no inode witnesses. The
durable logical state is the same one that starts the client trace. -/
theorem initialCatalog (image : S)
    (empty : (selected image).tables = fun _ => none)
    (initial : Durable (selected image) []) :
    Execution.Run [] none (selected image) ∧
      namespaceState.Represents image (selected image).tables :=
  ⟨.initial ⟨initial⟩, empty.symm ▸ namespaceState.empty image⟩

private theorem offlineDurable (prior : Execution.Run events none image) :
    ∃ history, Nonempty (Durable image history) := by
  obtain ⟨_ | _, _, represents⟩ := prior.refines
  · obtain ⟨_, _, impossible, _, _⟩ := represents
    cases impossible
  · exact ⟨_, represents.2.choose_spec.2⟩

/-- One reached recovery result justifies both the actual scope's publication
of the recovered session and the client trace step. Phase writes leave the
storage carrier untouched. -/
theorem recovery_online
    (prior : Execution.Run events none (selected before))
    (evidence : NativeBridge.CallbackEvidence ops (selected ∘ Prod.snd) tns)
    (catalog : namespaceState.Represents before (selected before).tables)
    (manifestFrame : ∀ s, match (ops).manifest.reopen s with
      | .ok _ after | .error _ after => (tns).Keeps s after ((selected ∘ Prod.snd) ((Phase.opening : Phase W), before)).tables)
    (walFrame : ∀ s, match (ops).reopenWal s with
      | .ok _ after | .error _ after => (tns).Keeps s after ((selected ∘ Prod.snd) ((Phase.opening : Phase W), before)).tables)
    (checkFrame : ∀ s id, match (ops).tables.check id s with
      | .ok _ after | .error _ after => (tns).Keeps s after ((selected ∘ Prod.snd) ((Phase.opening : Phase W), before)).tables)
    (ran : recover ops (.opening, before) = .ok session after)
    (use : StorageM (Phase W × S) α)
    (invalid : String) (closeWal : W → StorageM (Phase W × S) Unit) (unlock : StorageM (Phase W × S) Unit) :
    ∃ handle, after.1 = .recovering handle ∧
      Execution.Run (events ++ [.reopened]) (some session) (selected after.2) ∧
      namespaceState.Represents after.2 (selected after.2).tables ∧
      Cell.withSession stateCell invalid (recover ops) use closeWal unlock (.opening, before) =
        finish (ε := String) use (finish (ε := String) (Cell.close stateCell closeWal) unlock)
          (.online handle session, after.2) := by
  obtain ⟨_, ⟨durable⟩⟩ := offlineDurable prior
  have kept := recoverCatalog (ns := tns) evidence.effects (s := (Phase.opening, before)) durable catalog
    (by
      intro s
      have frame := manifestFrame s
      cases reached : (ops).manifest.reopen s <;> simpa [reached] using frame)
    (by
      intro s
      have frame := walFrame s
      cases reached : (ops).reopenWal s <;> simpa [reached] using frame)
    (by
      intro s id
      have frame := checkFrame s id
      cases reached : (ops).tables.check id s <;> simpa [reached] using frame)
  rw [ran] at kept
  obtain ⟨handle, attached⟩ := recover_attached callbacks unavailable before session after ran
  obtain ⟨phase, storage⟩ := after
  change phase = .recovering handle at attached
  subst phase
  exact ⟨handle, rfl,
    Execution.Run.recoverOk (s := (.opening, before)) prior evidence.effects ran, kept,
    successful_recovery_publishes (recover ops) use invalid closeWal unlock handle session
      before storage ran⟩

/-- The callback's finite trace is already observed when outer cleanup runs.
A cleanup error ends the scope with the same client history and reached storage. -/
theorem scope_refines
    (use : StorageM (Phase W × S) α)
    (invalid : String) (closeWal : W → StorageM (Phase W × S) Unit)
    (unlock : StorageM (Phase W × S) Unit)
    (ran : recover ops (.opening, before) = .ok session (.recovering handle, after))
    (closeFrame : ∀ h storage, reached (closeWal h (.offline, storage)) = (.offline, storage))
    (unlockFrame : ∀ storage, reached (unlock (.offline, storage)) = (.offline, storage))
    (client : Execution.Run events visible (selected (reached (use (.online handle session, after))).2))
    (catalog : namespaceState.Represents (reached (use (.online handle session, after))).2
      (selected (reached (use (.online handle session, after))).2).tables) :
    let final := reached (Cell.withSession stateCell invalid (recover ops) use closeWal unlock
      (.opening, before))
    final.1 = .offline ∧ namespaceState.Represents final.2 (selected final.2).tables ∧
      ∃ state, Client.Allows (events ++ [.stop]) state ∧
        Execution.Represents none (selected final.2) state := by
  dsimp only
  rw [successful_recovery_cleanup (recover ops) use invalid closeWal unlock handle session before after
    ran closeFrame unlockFrame]
  exact ⟨rfl, catalog, (Execution.Run.stop client).refines⟩

/-- Use the healthy WAL producer at the state reached by the manifest
open, then check each required table on the state reached by its predecessor. -/
theorem recovery_progress
    (evidence : NativeBridge.CallbackEvidence ops (selected ∘ Prod.snd) tns)
    (wal : WalRecovery.Interpretation ops (selected ∘ Prod.snd))
    (durable : Durable (selected before) history)
    (blob : ManifestComposition.Interpretation (ops).manifest (selected ∘ Prod.snd))
    (readActive : (blob.openReports (Phase.opening, before)).readActive = true)
    (openDirectory : (blob.openReports (Phase.opening, before)).openDirectory = true)
    (syncDirectory : (blob.openReports (Phase.opening, before)).syncDirectory = .ok)
    (middleInstalled : middle = blob.install (Phase.opening, before)
      (blob.image (Phase.opening, before)).barrier)
    {owned : WalRecoverySlice.Segmented.Model.RootBinding wal.directory wal.lock}
    (binding : wal.binding middle = .ok owned)
    (rootOK : WalRecoverySlice.Segmented.Model.HealthyRoot (wal.reports middle))
    (childrenOK : WalRecoverySlice.Segmented.Model.HealthyChildren (wal.childReports middle))
    (closeOK : wal.closeError middle = none) (unlockOK : wal.unlockError middle = none)
    (representable : ∀ c, (wal.diskState middle).disk.liveControl = some c →
      c.capacity ≤ 255 ∧ c.active ≤ WalRecoverySlice.Segmented.ControlCodec.wordMax ∧
      c.discarded ≤ WalRecoverySlice.Segmented.ControlCodec.wordMax)
    (reads : NativeTableReads.Interpretation (ops).tables (selected ∘ Prod.snd) tns)
    (catalog : namespaceState.Represents middle.2 (selected middle.2).tables)
    (openKeeps : ∀ checked view, (ops).reopenWal middle = .ok view checked →
      (tns).Keeps middle checked (selected middle.2).tables)
    (walKeepsManifest : ∀ checked view, (ops).reopenWal middle = .ok view checked →
      blob.image checked = blob.image middle)
    (checkKeepsStorage : ∀ state id next, (ops).tables.check id state = .ok () next →
      blob.image next = blob.image state ∧
        wal.phase next = wal.phase state ∧ wal.diskState next = wal.diskState state)
    (tablePrimitives : ∀ state id rows, id ∈ (selected before).version.tables →
      (tns).Bound state id rows → NativeTableReads.HealthySource tns state id (reads.world state)) :
    ∃ session after, recover ops (Phase.opening, before) = .ok session after ∧
      Installed session (selected after.2) history ∧
      namespaceState.Represents after.2 (selected after.2).tables ∧
      (blob.image after).Stable (L0Manifest.encode (selected after.2).version) ∧
      ∃ store walSession, wal.phase after = .ready store walSession ∧
        store.activeId = walSession.control.active ∧
        WalRecoverySlice.Segmented.Installed walSession (wal.diskState after).disk ∧
        walSession.view = (selected after.2).view ∧
        wal.runOpen middle = .ok (.ok (.ready store walSession, ())) (wal.diskState after, true) := by
  obtain ⟨checked, opened, _⟩ :=
    wal.reopenHealthy middle binding rootOK childrenOK closeOK unlockOK representable
  have walReached := wal.reopenReached middle
  rw [opened] at walReached
  obtain ⟨_, _, store, walSession, walPhase, active, walInstalled, walView, walRan⟩ := walReached
  have healthyManifest := blob.reopenHealthy (Phase.opening, before) readActive openDirectory syncDirectory
  have manifest : (ops).manifest.reopen (Phase.opening, before) = .ok (selected before).version middle :=
    middleInstalled.symm ▸ healthyManifest.1
  have manifestEffect := evidence.effects.reopenManifest (Phase.opening, before)
  rw [manifest] at manifestEffect
  have walEffect := evidence.effects.reopenWal middle
  rw [opened] at walEffect
  have selectedChecked : selected checked.2 = selected before := walEffect.2.trans manifestEffect.2
  have boundCatalog : (tns).Represents checked (selected before).tables := by
    have kept := TableNamespace.Represents.frame (ns := tns) (before := middle) catalog
      (openKeeps _ _ opened)
    have same : selected middle.2 = selected before := manifestEffect.2
    rw [same] at kept
    exact kept
  have healthy (ids : List UInt64) (included : ∀ id, id ∈ ids → id ∈ (selected before).version.tables)
      (state : Phase W × S) (same : selected state.2 = selected before)
      (catalog : (tns).Represents state (selected before).tables) :
      ∃ after, checkTables (ops).tables ids state = .ok () after ∧
        selected after.2 = selected before ∧
        (tns).Represents after (selected before).tables ∧ blob.image after = blob.image state ∧
        wal.phase after = wal.phase state ∧ wal.diskState after = wal.diskState state := by
    induction ids generalizing state with
    | nil => exact ⟨state, rfl, same, catalog, rfl, rfl, rfl⟩
    | cons id ids ih =>
      have member := included id (by simp)
      obtain ⟨rows, bound⟩ := durable.boundTable id member
      have source := catalog id rows bound
      obtain ⟨next, first, keeps⟩ :=
        reads.checkHealthy source (tablePrimitives state id rows member source)
      have nextSelected := reads.checkEffect state id
      rw [first] at nextSelected
      have kept : (tns).Represents next (selected before).tables := by
        apply catalog.frame
        simpa [Function.comp_apply, same] using keeps
      obtain ⟨after, rest, selectedAfter, catalogAfter, imageAfter, phaseAfter, diskAfter⟩ :=
        ih (fun key member => included key (List.mem_cons_of_mem _ member))
          next (nextSelected.trans same) kept
      obtain ⟨imageFrame, phaseFrame, diskFrame⟩ := checkKeepsStorage state id next first
      exact ⟨after, by simp [checkTables, Bind.bind, EStateM.bind, first, rest],
        selectedAfter, catalogAfter, imageAfter.trans imageFrame, phaseAfter.trans phaseFrame, diskAfter.trans diskFrame⟩
  obtain ⟨after, tables, selectedAfter, catalogAfter, imageAfter, phaseAfter, diskAfter⟩ := healthy (selected before).version.tables (fun _ member => member) checked
    selectedChecked boundCatalog
  obtain ⟨session, ran, ready⟩ := recover_progress (s := (Phase.opening, before)) evidence.effects durable manifest opened tables
  refine ⟨session, after, ran, ready, ?_, ?_, ?_⟩
  · rw [selectedAfter]
    exact catalogAfter
  · rw [selectedAfter, imageAfter, walKeepsManifest _ _ opened, middleInstalled]
    exact healthyManifest.2
  · refine ⟨store, walSession, phaseAfter.trans walPhase, active, ?_, ?_, ?_⟩
    · rw [diskAfter]
      exact walInstalled
    · have middleSelected : selected middle.2 = selected before := manifestEffect.2
      rw [selectedAfter, ← middleSelected]
      exact walView
    · rw [diskAfter]
      exact walRan

/-- Failed recovery records only an offline client step. Phase cleanup
detaches the handle even when closing the WAL or releasing the lock fails. -/
theorem recovery_offline
    (prior : Execution.Run events none (selected before))
    (evidence : NativeBridge.CallbackEvidence ops (selected ∘ Prod.snd) tns)
    (catalog : namespaceState.Represents before (selected before).tables)
    (manifestFrame : ∀ s, match (ops).manifest.reopen s with
      | .ok _ after | .error _ after => (tns).Keeps s after ((selected ∘ Prod.snd) ((Phase.opening : Phase W), before)).tables)
    (walFrame : ∀ s, match (ops).reopenWal s with
      | .ok _ after | .error _ after => (tns).Keeps s after ((selected ∘ Prod.snd) ((Phase.opening : Phase W), before)).tables)
    (checkFrame : ∀ s id, match (ops).tables.check id s with
      | .ok _ after | .error _ after => (tns).Keeps s after ((selected ∘ Prod.snd) ((Phase.opening : Phase W), before)).tables)
    (ran : recover ops (.opening, before) = .error error after)
    (use : StorageM (Phase W × S) α)
    (invalid : String) (closeWal : W → StorageM (Phase W × S) Unit) (unlock : StorageM (Phase W × S) Unit)
    (closeFrame : ∀ handle storage, reached (closeWal handle (.offline, storage)) = (.offline, storage))
    (unlockFrame : ∀ storage, reached (unlock (.offline, storage)) = (.offline, storage)) :
    Execution.Run (events ++ [.openFailed]) none (selected after.2) ∧
      namespaceState.Represents after.2 (selected after.2).tables ∧
      Cell.withSession stateCell invalid (recover ops) use closeWal unlock (.opening, before) =
        .error error (.offline, after.2) ∧
      (∀ (wal : WalRecovery.Interpretation ops (selected ∘ Prod.snd)) version middle disk held,
        (ops).manifest.reopen (.opening, before) = .ok version middle →
        wal.runOpen middle = .ok (.error error) (disk, held) →
        held = false ∧ wal.diskState after = disk ∧
          ∀ owned, wal.binding middle = .ok owned →
            WalRecoverySlice.Segmented.Model.ScopedFailureReleased owned.root (wal.reports middle)
              (wal.childReports middle) (wal.closeError middle) (wal.diskState middle) disk error) := by
  obtain ⟨_, ⟨durable⟩⟩ := offlineDurable prior
  have kept := recoverCatalog (ns := tns) evidence.effects (s := (Phase.opening, before)) durable catalog
    (by
      intro s
      have frame := manifestFrame s
      cases reached : (ops).manifest.reopen s <;> simpa [reached] using frame)
    (by
      intro s
      have frame := walFrame s
      cases reached : (ops).reopenWal s <;> simpa [reached] using frame)
    (by
      intro s id
      have frame := checkFrame s id
      cases reached : (ops).tables.check id s <;> simpa [reached] using frame)
  rw [ran] at kept
  refine ⟨Execution.Run.recoverError (s := (.opening, before)) prior evidence.effects ran, kept,
    failed_recovery_closes (recover ops) use invalid error closeWal unlock before after ran
      closeFrame unlockFrame, ?_⟩
  intro wal version middle disk held manifest opened
  obtain ⟨reopen, released, recoverable, childReleased⟩ := wal.reportedFailure opened
  have actual : recover ops (.opening, before) = .error error (wal.install middle disk .closed) := by
    simp [recover, Bind.bind, EStateM.bind, manifest, reopen]
  have same := (EStateM.Result.error.inj (ran.symm.trans actual)).2
  have installed := wal.installReached middle disk .closed recoverable trivial
  exact ⟨released, same ▸ installed.2.2, childReleased⟩

/-- Put and delete use this same write schedule. Publication changes only
phase custody, as does hiding the previous session before the call. -/
theorem write_online
    (prior : Execution.Run events (some old) (selected before))
    (evidence : NativeBridge.CallbackEvidence ops (selected ∘ Prod.snd) tns)
    (catalog : namespaceState.Represents before (selected before).tables)
    (scanFrame : ∀ s, match (ops).scan s with
      | .ok _ after | .error _ after => (tns).Keeps s after ((selected ∘ Prod.snd) s).tables)
    (appendFrame : ∀ s batch, match (ops).append batch s with
      | .ok _ after | .error _ after => (tns).Keeps s after ((selected ∘ Prod.snd) s).tables)
    (change : Change)
    (ran : write ops old change (.updating handle, before) = .ok next after)
    (invalid : String) (closeWal : W → StorageM (Phase W × S) Unit) :
    Execution.Run (events ++ [.written change]) (some next) (selected after.2) ∧
      namespaceState.Represents after.2 (selected after.2).tables ∧
      Cell.update stateCell invalid (fun session => write ops session change) closeWal
        (.online handle old, before) = .ok () (.online handle next, after.2) := by
  have kept := evidence.writeCatalog (s := (Phase.updating handle, before)) catalog
    (by
      intro s
      have frame := scanFrame s
      cases reached : (ops).scan s <;> simpa [reached] using frame)
    (by
      intro s batch
      have frame := appendFrame s batch
      cases reached : (ops).append batch s <;> simpa [reached] using frame) old change
  rw [ran] at kept
  have frame := write_keepsPhase callbacks unavailable old change (.updating handle, before)
  rw [ran] at frame
  rcases after with ⟨phase, storage⟩
  change phase = .updating handle at frame
  subst phase
  exact ⟨Execution.Run.writeOk (s := (.updating handle, before)) prior evidence.effects ran, kept,
    update_success _ invalid closeWal handle old next before storage ran⟩

theorem write_offline
    (prior : Execution.Run events (some old) (selected before))
    (evidence : NativeBridge.CallbackEvidence ops (selected ∘ Prod.snd) tns)
    (catalog : namespaceState.Represents before (selected before).tables)
    (scanFrame : ∀ s, match (ops).scan s with
      | .ok _ after | .error _ after => (tns).Keeps s after ((selected ∘ Prod.snd) s).tables)
    (appendFrame : ∀ s batch, match (ops).append batch s with
      | .ok _ after | .error _ after => (tns).Keeps s after ((selected ∘ Prod.snd) s).tables)
    (change : Change)
    (ran : write ops old change (.updating handle, before) = .error error after)
    (invalid : String) (closeWal : W → StorageM (Phase W × S) Unit)
    (closeFrame : ∀ handle storage, reached (closeWal handle (.offline, storage)) = (.offline, storage)) :
    Execution.Run (events ++ [.writeUncertain change]) none (selected after.2) ∧
      namespaceState.Represents after.2 (selected after.2).tables ∧
      Cell.update stateCell invalid (fun session => write ops session change) closeWal
        (.online handle old, before) = .error error (.offline, after.2) := by
  have kept := evidence.writeCatalog (s := (Phase.updating handle, before)) catalog
    (by
      intro s
      have frame := scanFrame s
      cases reached : (ops).scan s <;> simpa [reached] using frame)
    (by
      intro s batch
      have frame := appendFrame s batch
      cases reached : (ops).append batch s <;> simpa [reached] using frame) old change
  rw [ran] at kept
  exact ⟨Execution.Run.writeInterrupted (s := (.updating handle, before)) prior evidence.effects ran, kept,
    update_error _ invalid error closeWal handle old before after ran closeFrame⟩

theorem flush_online
    (prior : Execution.Run events (some old) (selected before))
    (evidence : NativeBridge.CallbackEvidence ops (selected ∘ Prod.snd) tns)
    (catalog : namespaceState.Represents before (selected before).tables)
    (scanFrame : ∀ s, match (ops).scan s with
      | .ok _ after | .error _ after => (tns).Keeps s after ((selected ∘ Prod.snd) s).tables)
    (createFrame : ∀ s rows, match (ops).tables.create rows s with
      | .ok _ after | .error _ after => (tns).Keeps s after ((selected ∘ Prod.snd) s).tables)
    (publishFrame : ∀ s version, match (ops).manifest.publish version s with
      | .ok _ after | .error _ after =>
        ((selected ∘ Prod.snd) after).tables = ((selected ∘ Prod.snd) s).tables ∧
        (tns).Keeps s after ((selected ∘ Prod.snd) s).tables)
    (ran : flush ops old (.updating handle, before) = .ok next after)
    (invalid : String) (closeWal : W → StorageM (Phase W × S) Unit) :
    Execution.Run (events ++ [.flushed]) (some next) (selected after.2) ∧
      namespaceState.Represents after.2 (selected after.2).tables ∧
      Cell.update stateCell invalid (flush ops) closeWal
        (.online handle old, before) = .ok () (.online handle next, after.2) := by
  have kept := evidence.flushCatalog (s := (Phase.updating handle, before)) catalog
    (by
      intro s
      have frame := scanFrame s
      cases reached : (ops).scan s <;> simpa [reached] using frame)
    (by
      intro s rows
      have frame := createFrame s rows
      cases reached : (ops).tables.create rows s <;> simpa [reached] using frame)
    (by
      intro s version
      have frame := publishFrame s version
      cases reached : (ops).manifest.publish version s <;> simpa [reached] using frame) old
  rw [ran] at kept
  have frame := flush_keepsPhase callbacks unavailable old (.updating handle, before)
  rw [ran] at frame
  rcases after with ⟨phase, storage⟩
  change phase = .updating handle at frame
  subst phase
  exact ⟨Execution.Run.flushObserved (s := (.updating handle, before)) prior evidence.effects ran .delivered, kept,
    update_success _ invalid closeWal handle old next before storage ran⟩

theorem flush_offline
    (prior : Execution.Run events (some old) (selected before))
    (evidence : NativeBridge.CallbackEvidence ops (selected ∘ Prod.snd) tns)
    (catalog : namespaceState.Represents before (selected before).tables)
    (scanFrame : ∀ s, match (ops).scan s with
      | .ok _ after | .error _ after => (tns).Keeps s after ((selected ∘ Prod.snd) s).tables)
    (createFrame : ∀ s rows, match (ops).tables.create rows s with
      | .ok _ after | .error _ after => (tns).Keeps s after ((selected ∘ Prod.snd) s).tables)
    (publishFrame : ∀ s version, match (ops).manifest.publish version s with
      | .ok _ after | .error _ after =>
        ((selected ∘ Prod.snd) after).tables = ((selected ∘ Prod.snd) s).tables ∧
        (tns).Keeps s after ((selected ∘ Prod.snd) s).tables)
    (ran : flush ops old (.updating handle, before) = .error error after)
    (invalid : String) (closeWal : W → StorageM (Phase W × S) Unit)
    (closeFrame : ∀ handle storage, reached (closeWal handle (.offline, storage)) = (.offline, storage)) :
    Execution.Run (events ++ [.flushUncertain]) none (selected after.2) ∧
      namespaceState.Represents after.2 (selected after.2).tables ∧
      Cell.update stateCell invalid (flush ops) closeWal
        (.online handle old, before) = .error error (.offline, after.2) := by
  have kept := evidence.flushCatalog (s := (Phase.updating handle, before)) catalog
    (by
      intro s
      have frame := scanFrame s
      cases reached : (ops).scan s <;> simpa [reached] using frame)
    (by
      intro s rows
      have frame := createFrame s rows
      cases reached : (ops).tables.create rows s <;> simpa [reached] using frame)
    (by
      intro s version
      have frame := publishFrame s version
      cases reached : (ops).manifest.publish version s <;> simpa [reached] using frame) old
  rw [ran] at kept
  exact ⟨Execution.Run.flushObserved (s := (.updating handle, before)) prior evidence.effects ran .reportedError, kept,
    update_error _ invalid error closeWal handle old before after ran closeFrame⟩


theorem get_online
    (prior : Execution.Run events (some session) (selected before))
    (reads : NativeTableReads.Interpretation (ops).tables (selected ∘ Prod.snd) tns)
    (catalog : namespaceState.Represents before (selected before).tables)
    (ran : get ops session key (.online handle session, before) =
      .ok value after) (invalid : String) :
    Execution.Run (events ++ [.got key value]) (some session) (selected after.2) ∧
      namespaceState.Represents after.2 (selected after.2).tables ∧
      Cell.get stateCell invalid ops key
        (.online handle session, before) = .ok value (.online handle session, after.2) := by
  have frame := get_keepsPhase callbacks unavailable session key (.online handle session, before)
  rw [ran] at frame
  rcases after with ⟨phase, storage⟩
  change phase = .online handle session at frame
  subst phase
  have effect (history : Rows) (installed : Installed session (selected before) history) := reads.get (s := (Phase.online handle session, before)) catalog installed key
  obtain ⟨_, installed⟩ := prior.onlineInstalled
  have reached := effect _ installed
  rw [ran] at reached
  refine ⟨Execution.Run.getOk (selected := selected ∘ Prod.snd) (s := (Phase.online handle session, before)) prior ?_ ran,
    reached.2.2, (useSession_online _ invalid handle session before).trans ran⟩
  intro history installed
  have read := effect history installed
  rw [ran] at read ⊢
  exact ⟨read.1, read.2.1⟩

theorem get_online_error
    (prior : Execution.Run events (some session) (selected before))
    (reads : NativeTableReads.Interpretation (ops).tables (selected ∘ Prod.snd) tns)
    (catalog : namespaceState.Represents before (selected before).tables)
    (ran : get ops session key (.online handle session, before) =
      .error error after) (invalid : String) :
    Execution.Run events (some session) (selected after.2) ∧
      namespaceState.Represents after.2 (selected after.2).tables ∧
      Cell.get stateCell invalid ops key
        (.online handle session, before) = .error error (.online handle session, after.2) := by
  have frame := get_keepsPhase callbacks unavailable session key (.online handle session, before)
  rw [ran] at frame
  rcases after with ⟨phase, storage⟩
  change phase = .online handle session at frame
  subst phase
  have effect (history : Rows) (installed : Installed session (selected before) history) := reads.get (s := (Phase.online handle session, before)) catalog installed key
  obtain ⟨_, installed⟩ := prior.onlineInstalled
  have reached := effect _ installed
  rw [ran] at reached
  refine ⟨Execution.Run.getError (selected := selected ∘ Prod.snd) (s := (Phase.online handle session, before)) prior ?_ ran,
    reached.2, (useSession_online _ invalid handle session before).trans ran⟩
  intro history installed
  have read := effect history installed
  rw [ran] at read ⊢
  exact read.1

private def readSequence [Monad m] [MonadExceptOf String m]
    (read : UInt64 → m (Option UInt64)) (keys : List UInt64) : m (List (Except String (Option UInt64))) :=
  keys.mapM (fun key => MonadExceptOf.tryCatch (ε := String)
    (read key >>= fun value => pure (Except.ok value))
    (fun error => pure (Except.error error)))

/-- Interpret a finite callback of public gets. Reported read errors
remain in the returned list and do not add a successful client event. -/
theorem getList_online
    (keys : List UInt64) (handle : W)
    (tableReads : NativeTableReads.Interpretation (ops).tables (selected ∘ Prod.snd) tns)
    (invalid : String)
    (prior : Execution.Run events (some session) (selected before))
    (catalog : namespaceState.Represents before (selected before).tables) :
    ∃ results after,
      readSequence (Cell.get stateCell invalid ops) keys (.online handle session, before) =
        .ok results (.online handle session, after) ∧
      Execution.Run (events ++ (keys.zip results).filterMap (fun (key, result) =>
        match result with | .ok value => some (.got key value) | .error _ => none))
        (some session) (selected after) ∧
      namespaceState.Represents after (selected after).tables := by
  induction keys generalizing events before with
  | nil => exact ⟨[], before, rfl, by simpa using prior, catalog⟩
  | cons key keys ih =>
    cases ran : get ops session key (.online handle session, before) with
    | ok value next =>
      obtain ⟨trace, kept, dispatch⟩ := get_online prior tableReads catalog ran invalid
      obtain ⟨results, after, reads, trace, kept⟩ := ih trace kept
      refine ⟨.ok value :: results, after, ?_, ?_, kept⟩
      · simp only [readSequence, Bind.bind, MonadExceptOf.tryCatch, Pure.pure] at reads
        simp [readSequence, List.mapM_cons, Bind.bind, EStateM.bind, MonadExceptOf.tryCatch,
          EStateM.tryCatch, Pure.pure, EStateM.pure, dispatch, reads]
      · simpa [List.append_assoc] using trace
    | error error next =>
      obtain ⟨trace, kept, dispatch⟩ := get_online_error prior tableReads catalog ran invalid
      obtain ⟨results, after, reads, trace, kept⟩ := ih trace kept
      refine ⟨.error error :: results, after, ?_, ?_, kept⟩
      · simp only [readSequence, Bind.bind, MonadExceptOf.tryCatch, Pure.pure] at reads
        simp [readSequence, List.mapM_cons, Bind.bind, EStateM.bind, MonadExceptOf.tryCatch,
          EStateM.tryCatch, Pure.pure, EStateM.pure, dispatch, reads,
          EStateM.Backtrackable.restore, EStateM.dummyRestore]
      · simpa using trace

/-- A recovered session, arbitrarily many public reads, and scope exit
share one client trace. The scope result may report a cleanup error. -/
theorem getScope_refines
    (keys : List UInt64)
    (evidence : NativeBridge.CallbackEvidence ops (selected ∘ Prod.snd) tns)
    (invalid : String) (closeWal : W → StorageM (Phase W × S) Unit)
    (unlock : StorageM (Phase W × S) Unit)
    (prior : Execution.Run events none (selected before))
    (ran : recover ops (.opening, before) = .ok session (.recovering handle, opened))
    (catalog : namespaceState.Represents opened (selected opened).tables)
    (closeFrame : ∀ h storage, reached (closeWal h (.offline, storage)) = (.offline, storage))
    (unlockFrame : ∀ storage, reached (unlock (.offline, storage)) = (.offline, storage)) :
    let use := readSequence (Cell.get stateCell invalid ops) keys
    let final := reached (Cell.withSession stateCell invalid (recover ops) use closeWal unlock (.opening, before))
    ∃ results after,
      use (.online handle session, opened) = .ok results (.online handle session, after) ∧
      final = (.offline, after) ∧
      namespaceState.Represents after (selected after).tables ∧
      ∃ state,
        Client.Allows ((events ++ [.reopened]) ++ (keys.zip results).filterMap (fun (key, result) =>
          match result with | .ok value => some (.got key value) | .error _ => none) ++ [.stop]) state ∧
        Execution.Represents none (selected after) state := by
  dsimp only
  have reopened := Execution.Run.recoverOk (s := (.opening, before)) prior evidence.effects ran
  obtain ⟨tableReads⟩ := evidence.reads
  obtain ⟨results, after, reads, trace, kept⟩ := getList_online keys handle tableReads invalid reopened catalog
  let use := readSequence (Cell.get stateCell invalid ops) keys
  have closed := successful_recovery_cleanup (recover ops) use invalid closeWal unlock handle session
    before opened ran closeFrame unlockFrame
  change use (.online handle session, opened) = _ at reads
  rw [reads] at closed
  refine ⟨results, after, reads, closed, kept, ?_⟩
  have scope := scope_refines use invalid closeWal unlock ran closeFrame unlockFrame
    (by rw [reads]; exact trace) (by rw [reads]; exact kept)
  rw [closed] at scope
  exact scope.2.2

end ExperimentalL0.Lifecycle
