import Alvoki.Storage.Disk.NativeOpenWrite
import Alvoki.Storage.Disk.NativeOpenedPosition
import Alvoki.Storage.Disk.NativeRawWriteCustody
import Alvoki.Storage.Disk.NativeWalPublicationTail

namespace Alvoki.Storage.DiskSession

open System SyncHandleRouting WalSegmentCommit WalSegmentRepair CheckpointPublication

/-- Presence of canonical WAL names in a given replay window. Older names
may already have been collected. Names beyond the window belong to later
repair. Inode identity and bytes have independent invariants. -/
def _root_.Alvoki.Storage.WalSegmentImage.NamespaceWindow (wal : WalSegmentImage)
    (directory : DiskDirectory) (first through : Nat) (names : FilePath → Option Nat) : Prop :=
  ∀ start, first ≤ start → start ≤ through →
    ((names (directory.file (.walSegment start))).isSome = true ↔ start ∈ wal.segments.map WalSegment.first)

theorem _root_.Alvoki.Storage.WalSegmentImage.NamespaceWindow.frame
    {wal : WalSegmentImage} {directory : DiskDirectory} {first through : Nat}
    {before after : FilePath → Option Nat} (initial : wal.NamespaceWindow directory first through before)
    (presence : ∀ start, first ≤ start → start ≤ through →
      (after (directory.file (.walSegment start))).isSome = (before (directory.file (.walSegment start))).isSome) :
    wal.NamespaceWindow directory first through after :=
  fun start lower upper => presence start lower upper ▸ initial start lower upper

theorem _root_.Alvoki.Storage.WalSegmentImage.NamespaceWindow.restrict
    {wal : WalSegmentImage} {directory : DiskDirectory} {first through lower upper : Nat}
    {names : FilePath → Option Nat} (initial : wal.NamespaceWindow directory first through names)
    (starts : first ≤ lower) (ends : upper ≤ through) : wal.NamespaceWindow directory lower upper names :=
  fun start after before => initial start (Nat.le_trans starts after) (Nat.le_trans before ends)

/-- In the requested interval, the live directory and every joint crash
map name exactly the modeled WAL segments, including the gaps. -/
abbrev _root_.Alvoki.Storage.WalSegmentImage.SettledNamespaceWindow
    (wal : WalSegmentImage) (directory : DiskDirectory) (first through : Nat)
    (storage : CheckpointStorageObservation) : Prop :=
  wal.NamespaceWindow directory first through storage.files.names ∧
    ∀ names ∈ storage.crashNames, wal.NamespaceWindow directory first through names

/-- Preserve canonical WAL name presence in the selected interval. A
later crash map uses one earlier live or crash map for the whole interval.
The frame does not constrain inode identity or file contents. -/
structure WalNamePresenceFrame (directory : DiskDirectory) (first through : Nat)
    (entry reached : CheckpointStorageObservation) : Prop where
  live : ∀ start, first ≤ start → start ≤ through →
    (reached.files.names (directory.file (.walSegment start))).isSome =
      (entry.files.names (directory.file (.walSegment start))).isSome
  survivors : ∀ names ∈ reached.crashNames, ∃ prior, (prior = entry.files.names ∨ prior ∈ entry.crashNames) ∧
    ∀ start, first ≤ start → start ≤ through →
      (names (directory.file (.walSegment start))).isSome = (prior (directory.file (.walSegment start))).isSome

namespace WalNamePresenceFrame

variable {directory : DiskDirectory} {first through : Nat} {entry middle reached : CheckpointStorageObservation}

theorem refl (entry : CheckpointStorageObservation) :
    WalNamePresenceFrame directory first through entry entry :=
  ⟨fun _ _ _ => rfl, fun names possible => ⟨names, .inr possible, fun _ _ _ => rfl⟩⟩

theorem trans (earlier : WalNamePresenceFrame directory first through entry middle)
    (later : WalNamePresenceFrame directory first through middle reached) :
    WalNamePresenceFrame directory first through entry reached := by
  refine ⟨fun start low high => (later.live start low high).trans (earlier.live start low high), ?_⟩
  intro names possible
  obtain ⟨prior, issued, same⟩ := later.survivors names possible
  rcases issued with rfl | survived
  · exact ⟨_, .inl rfl, fun start low high => (same start low high).trans (earlier.live start low high)⟩
  · obtain ⟨original, priorAllowed, kept⟩ := earlier.survivors prior survived
    exact ⟨original, priorAllowed, fun start low high => (same start low high).trans (kept start low high)⟩

theorem ofStorageFrame {scope : FilePath → Prop} (frame : entry.Frames scope reached)
    (includes : ∀ start, first ≤ start → start ≤ through → scope (directory.file (.walSegment start))) :
    WalNamePresenceFrame directory first through entry reached := by
  refine ⟨fun start low high => congrArg Option.isSome (frame.visible _ (includes start low high)).1, ?_⟩
  intro names possible
  obtain ⟨prior, earlier, kept⟩ := frame.survivors names possible
  exact ⟨prior, .inr earlier, fun start low high => congrArg Option.isSome (kept _ (includes start low high))⟩

theorem ofFileSync {inode : Nat} {bytes : List ByteArray} (effect : RegularFileSyncEffect inode bytes entry reached) :
    WalNamePresenceFrame directory first through entry reached := by
  refine ⟨fun start _ _ => congrArg Option.isSome (congrFun effect.names (directory.file (.walSegment start))), ?_⟩
  intro names possible
  exact ⟨names, .inr (effect.crashNames ▸ possible), fun _ _ _ => rfl⟩

theorem ofMarkerRename {inode : Nat} {effective : Bool}
    (effect : WalMarkerRenameEffect directory inode effective entry reached) :
    WalNamePresenceFrame directory first through entry reached := by
  refine ⟨fun start _ _ => congrArg Option.isSome ?_, ?_⟩
  · simpa only [walMarkerRenameBinding, Function.comp_apply, ite_self] using effect.visible (.walSegment start)
  · intro names possible
    obtain ⟨prior, earlier, published, _, kept⟩ := effect.survivors names possible
    refine ⟨prior, .inr earlier, fun start _ _ => congrArg Option.isSome ?_⟩
    simpa only [walMarkerRenameBinding, Function.comp_apply, ite_self] using kept (.walSegment start)

theorem ofRootSync {effective : Bool} (effect : WalRootSyncEffect directory effective entry reached) :
    WalNamePresenceFrame directory first through entry reached := by
  refine ⟨fun start _ _ => congrArg Option.isSome (effect.visible (.walSegment start)), ?_⟩
  intro names possible
  cases applied : effective with
  | false =>
    obtain ⟨prior, earlier, kept⟩ := effect.unchanged applied names possible
    exact ⟨prior, .inr earlier, fun start _ _ => congrArg Option.isSome (kept (.walSegment start))⟩
  | true =>
    exact ⟨entry.files.names, .inl rfl, fun start _ _ => congrArg Option.isSome
      ((effect.settled applied names possible (.walSegment start)).trans (effect.visible (.walSegment start)))⟩

end WalNamePresenceFrame

theorem WalNamePresenceFrame.preservesNamespaceWindow
    {wal : WalSegmentImage} {directory : DiskDirectory} {first through : Nat}
    {entry reached : CheckpointStorageObservation}
    (frame : WalNamePresenceFrame directory first through entry reached)
    (initial : wal.SettledNamespaceWindow directory first through entry) :
    wal.SettledNamespaceWindow directory first through reached := by
  refine ⟨initial.1.frame frame.live, ?_⟩
  intro names survives
  obtain ⟨prior, fromLive | fromCrash, same⟩ := frame.survivors names survives
  · exact initial.1.frame (fromLive ▸ same)
  · exact (initial.2 prior fromCrash).frame same

/-- The selected WAL segment starts and the live and joint-crash
catalogs within the finite interval needed by a subsequent request. -/
abbrev NativeOpenedPosition.WalWindowAt {heap : Type} {opened : NativeOpenedHandle heap} (position : NativeOpenedPosition opened)
    (storage : heap → CheckpointStorageObservation) (first through : Nat) : Prop :=
  let state := position.current.ready.state
  (∀ offset ∈ state.writer.wal.segments.map WalSegment.first, first ≤ offset) ∧
  state.writer.wal.SettledNamespaceWindow state.session.directory first through (storage position.reached)

theorem NativeOpenedPosition.WalWindowAt.restrictUpper {heap : Type} {opened : NativeOpenedHandle heap}
    {position : NativeOpenedPosition opened} {storage : heap → CheckpointStorageObservation}
    {first through upper : Nat} (window : position.WalWindowAt storage first through)
    (within : upper ≤ through) : position.WalWindowAt storage first upper :=
  ⟨window.1, window.2.1.restrict (Nat.le_refl _) within,
    fun names survives => (window.2.2 names survives).restrict (Nat.le_refl _) within⟩

/-- File callbacks preserve the original phase cell independently of
their WAL effects. Keep authority and the protected files through the
same reached-state frame as for an acknowledged write. -/
def NativeOpenedPosition.framesRawWrite {heap image : Type} {opened : NativeOpenedHandle heap}
    (current : NativeOpenedPosition opened) (view : OpenCloseHeapView heap image)
    (directoryRef : IO.Ref (Option IO.FS.Handle)) (storage : heap → CheckpointStorageObservation)
    (entry reached : heap) : Prop :=
  view.framesWrite current.current.ready.state directoryRef storage entry reached ∧
    opened.contents reached opened.phase = opened.contents entry opened.phase

section

variable {heap image : Type} {opened : NativeOpenedHandle heap}
  (current : NativeOpenedPosition opened)
  (appender : RawWalAppendCalls heap) (stager : RawWalStageCalls heap) (syncer : RawSyncCalls heap)
  (view : OpenCloseHeapView heap image)
  (cache : OpenSyncCacheRefs opened.files current.current.ready.state.session.directory.path)

local notation "before" => current.current.ready.state
local notation "dir" => current.current.ready.state.session.directory
local notation "oldInstalled" => current.current.ready.state.writer.installed
local notation "append" => appender.run cache.active
local notation "stage" => stager.run cache.pending
local notation "sync" => syncer.group current.current.ready.state.session.directory.path cache.directory cache.active cache.pending

/-- The actual public return determines the reached preparation, poison
assignment and failing publication step from the same callbacks. -/
theorem NativeOpenedPosition.classifiesCommitUnknown
    (request : WriteRequest)
    (lookup : FilePath → EStateM IO.Error heap IO.FS.Metadata)
    (rename : FilePath → FilePath → EStateM IO.Error heap Unit)
    {cause : IO.Error} {reached : heap}
    (nonempty : request.rows ≠ [])
    (returned : request.runOnRawOpenPhase dir lookup append stage sync rename
      opened.phase opened.get opened.set current.reached = .error (.commitUnknown cause) reached) :
    ∃ batch table guarded poisoned,
      prepareBatch (oldInstalled).table request.rows = some (batch, table) ∧
      (oldInstalled).walBytes + WAL.frameSize * request.rows.length < UInt64.size ∧
      checkActiveSegmentWith dir oldInstalled lookup current.reached = .ok () guarded ∧
      opened.set opened.phase .poisoned guarded = .ok () poisoned ∧
      commitBytesAt dir (oldInstalled).activeFirst (WAL.encodeBatch batch)
        ((oldInstalled).walBytes + WAL.frameSize * request.rows.length)
        append stage sync rename poisoned = .error cause reached ∧
      syncer.PublicationOutcome cache appender stager rename (oldInstalled).activeFirst
        ((oldInstalled).walBytes + WAL.frameSize * request.rows.length) (WAL.encodeBatch batch) poisoned
        (.error cause reached) := by
  have valid := current.current.ready.readPrefix.refines.1
  have loaded := opened.phaseEffects.reads current.reached opened.phase _ (current.stored.trans (congrArg some valid.phase))
  obtain ⟨batch, table, prepared, fits⟩ := request.runOnRawOpenPhase_prepared dir lookup
    append stage sync rename opened.phase opened.get opened.set loaded nonempty (by rw [returned]; trivial)
  obtain ⟨guarded, poisoned, guard, excluded, failed, _, _⟩ :=
    request.runOnRawOpenPhase_commitUnknown dir lookup append stage sync rename opened.phase opened.get opened.set
      loaded nonempty prepared fits returned
  have outcome := syncer.publicationOutcome cache appender stager rename (first := (oldInstalled).activeFirst)
    (count := (oldInstalled).walBytes + WAL.frameSize * request.rows.length) (bytes := WAL.encodeBatch batch) poisoned
  rw [failed] at outcome
  exact ⟨batch, table, guarded, poisoned, prepared, fits, guard, excluded, failed, outcome⟩

/-- Frames at the callbacks actually reached after preparation.
Only a successful callback exposes the next frame in the schedule. -/
structure NativeOpenedPosition.PublicationCallbackFrames
    (request : WriteRequest)
    (lookup : FilePath → EStateM IO.Error heap IO.FS.Metadata)
    (rename : FilePath → FilePath → EStateM IO.Error heap Unit)
    (frame : heap → heap → Prop) : Prop where
  atPoison : ∀ {batch table guarded poisoned},
    prepareBatch (oldInstalled).table request.rows = some (batch, table) →
    checkActiveSegmentWith dir oldInstalled lookup current.reached = .ok () guarded →
    opened.set opened.phase .poisoned guarded = .ok () poisoned →
    let keeper := (dir).file (.walSegment (oldInstalled).activeFirst)
    let scratch := (dir).file .stagedWalBoundary
    let marker := (dir).file .walBoundary
    let writeKeeper := append keeper (WAL.encodeBatch batch)
    let stageMarker := stage scratch (WAL.Boundary.encode ((oldInstalled).walBytes + WAL.frameSize * request.rows.length).toUInt64)
    let syncFiles := sync #[keeper, scratch]
    let renameMarker := rename scratch marker
    frame poisoned (reachedState (writeKeeper poisoned)) ∧
    ∀ {appended}, writeKeeper poisoned = .ok () appended →
      frame appended (reachedState (stageMarker appended)) ∧
      ∀ {staged}, stageMarker appended = .ok () staged →
        frame staged (reachedState (syncFiles staged)) ∧
        ∀ {grouped}, syncFiles staged = .ok () grouped →
          frame grouped (reachedState (renameMarker grouped)) ∧
          ∀ {renamed}, renameMarker grouped = .ok () renamed →
            frame renamed (reachedState (sync #[(dir).path] renamed))

/-- The guard and poison callback frame joins the publication schedule
to the reached ready position. -/
structure NativeOpenedPosition.WriteCallbackFrames
    (request : WriteRequest)
    (lookup : FilePath → EStateM IO.Error heap IO.FS.Metadata)
    (rename : FilePath → FilePath → EStateM IO.Error heap Unit)
    (frame : heap → heap → Prop) : Prop
    extends current.PublicationCallbackFrames appender stager syncer cache request lookup rename frame where
  guard : ∀ {guarded}, checkActiveSegmentWith dir oldInstalled lookup current.reached = .ok () guarded →
    frame current.reached guarded
  poison : ∀ {guarded poisoned}, checkActiveSegmentWith dir oldInstalled lookup current.reached = .ok () guarded →
    opened.set opened.phase .poisoned guarded = .ok () poisoned →
    frame guarded poisoned

/-- The write's scope can be bounded to WAL namespace presence. -/
abbrev NativeOpenedPosition.WalNameEffects
    (request : WriteRequest)
    (lookup : FilePath → EStateM IO.Error heap IO.FS.Metadata)
    (rename : FilePath → FilePath → EStateM IO.Error heap Unit)
    (storage : heap → CheckpointStorageObservation) (first through : Nat) : Prop :=
  current.WriteCallbackFrames appender stager syncer cache request lookup rename
    (fun entry after => WalNamePresenceFrame dir first through (storage entry) (storage after))

variable {current appender stager syncer cache} in
/-- Compose the file callbacks in issue order to the actual result. -/
theorem NativeOpenedPosition.PublicationCallbackFrames.throughCommit
    {request : WriteRequest}
    {lookup : FilePath → EStateM IO.Error heap IO.FS.Metadata}
    {rename : FilePath → FilePath → EStateM IO.Error heap Unit}
    {frame : heap → heap → Prop}
    (effects : current.PublicationCallbackFrames appender stager syncer cache request lookup rename frame)
    (trans : ∀ {entry middle after}, frame entry middle → frame middle after → frame entry after)
    {batch : List WAL.Write} {table : PackedTable} {guarded poisoned : heap}
    (prepared : prepareBatch (oldInstalled).table request.rows = some (batch, table))
    (checked : checkActiveSegmentWith dir oldInstalled lookup current.reached = .ok () guarded)
    (assigned : opened.set opened.phase .poisoned guarded = .ok () poisoned)
    {result : EStateM.Result IO.Error heap Unit}
    (outcome : syncer.PublicationOutcome cache appender stager rename (oldInstalled).activeFirst
      ((oldInstalled).walBytes + WAL.frameSize * request.rows.length) (WAL.encodeBatch batch) poisoned result) :
    frame poisoned (reachedState result) := by
  have frames := effects.atPoison prepared checked assigned
  have reached {entry after : heap} {ran : EStateM.Result IO.Error heap Unit}
      (kept : frame entry (reachedState ran)) (returned : ran = .ok () after) : frame entry after := by
    simpa only [returned, reachedState] using kept
  have throughStage {appended : heap}
      (wrote : append ((dir).file (.walSegment (oldInstalled).activeFirst)) (WAL.encodeBatch batch) poisoned =
        .ok () appended) :=
    trans (reached frames.1 wrote) (frames.2 wrote).1
  cases outcome with
  | appendError failed => simpa only [failed] using frames.1
  | stageError wrote failed => simpa only [failed] using throughStage wrote
  | groupError wrote staged failed =>
    exact trans (reached (throughStage wrote) staged) (by simpa only [failed] using ((frames.2 wrote).2 staged).1)
  | renameError wrote staged grouped failed =>
    have group := (frames.2 wrote).2 staged
    exact trans (reached (throughStage wrote) staged)
      (trans (reached group.1 grouped) (by simpa only [failed] using (group.2 grouped).1))
  | directory wrote staged grouped moved returned =>
    have group := (frames.2 wrote).2 staged
    have rename := group.2 grouped
    exact trans (reached (throughStage wrote) staged)
      (trans (reached group.1 grouped) (trans (reached rename.1 moved) (by simpa only [returned] using rename.2 moved)))

variable {current appender stager syncer cache} in
/-- The same reached callback fold carries any preserved relation from
the ready entry through the exact publication result. -/
theorem NativeOpenedPosition.WriteCallbackFrames.throughPublication
    {request : WriteRequest}
    {lookup : FilePath → EStateM IO.Error heap IO.FS.Metadata}
    {rename : FilePath → FilePath → EStateM IO.Error heap Unit}
    {frame : heap → heap → Prop}
    (effects : current.WriteCallbackFrames appender stager syncer cache request lookup rename frame)
    (trans : ∀ {entry middle after}, frame entry middle → frame middle after → frame entry after)
    {batch : List WAL.Write} {table : PackedTable} {guarded poisoned : heap}
    (prepared : prepareBatch (oldInstalled).table request.rows = some (batch, table))
    (checked : checkActiveSegmentWith dir oldInstalled lookup current.reached = .ok () guarded)
    (assigned : opened.set opened.phase .poisoned guarded = .ok () poisoned)
    {result : EStateM.Result IO.Error heap Unit}
    (outcome : syncer.PublicationOutcome cache appender stager rename (oldInstalled).activeFirst
      ((oldInstalled).walBytes + WAL.frameSize * request.rows.length) (WAL.encodeBatch batch) poisoned result) :
    frame current.reached (reachedState result) :=
  trans (effects.guard checked) (trans (effects.poison checked assigned)
    (effects.toPublicationCallbackFrames.throughCommit trans prepared checked assigned outcome))

/-- An ordinary uncertain return preserves the selected WAL name window
at the failed publication's reached heap. -/
theorem NativeOpenedPosition.preservesWalNamesAfterCommitUnknown
    (request : WriteRequest)
    (lookup : FilePath → EStateM IO.Error heap IO.FS.Metadata)
    (rename : FilePath → FilePath → EStateM IO.Error heap Unit)
    {cause : IO.Error} {reached : heap}
    (nonempty : request.rows ≠ [])
    (returned : request.runOnRawOpenPhase dir lookup append stage sync rename
      opened.phase opened.get opened.set current.reached = .error (.commitUnknown cause) reached)
    {storage : heap → CheckpointStorageObservation} {first through : Nat}
    (effects : current.WalNameEffects appender stager syncer cache request lookup rename storage first through) :
    WalNamePresenceFrame dir first through (storage current.reached) (storage reached) := by
  obtain ⟨_, _, _, _, prepared, _, checked, assigned, _, outcome⟩ :=
    current.classifiesCommitUnknown appender stager syncer cache request lookup rename nonempty returned
  exact effects.throughPublication WalNamePresenceFrame.trans prepared checked assigned outcome

/-- A successful nonempty write frames WAL names through publication
and the actual phase update that returns the table to ready. -/
theorem NativeOpenedPosition.preservesWalNamesAfterAcknowledgement
    (request : WriteRequest)
    (lookup : FilePath → EStateM IO.Error heap IO.FS.Metadata)
    (rename : FilePath → FilePath → EStateM IO.Error heap Unit)
    {sequence : UInt64} {reached : heap}
    (nonempty : request.rows ≠ [])
    (returned : request.runOnRawOpenPhase dir lookup append stage sync rename
      opened.phase opened.get opened.set current.reached = .ok sequence reached)
    {storage : heap → CheckpointStorageObservation} {first through : Nat}
    (effects : current.WalNameEffects appender stager syncer cache request lookup rename storage first through)
    (restoreFrame : ∀ {settled value}, opened.set opened.phase (.ready value) settled = .ok () reached →
      WalNamePresenceFrame dir first through (storage settled) (storage reached)) :
    WalNamePresenceFrame dir first through (storage current.reached) (storage reached) := by
  have valid := current.current.ready.readPrefix.refines.1
  have loaded := opened.phaseEffects.reads current.reached opened.phase _ (current.stored.trans (congrArg some valid.phase))
  obtain ⟨batch, table, prepared, fits⟩ := request.runOnRawOpenPhase_prepared dir lookup append stage sync rename
    opened.phase opened.get opened.set loaded nonempty (by rw [returned]; trivial)
  obtain ⟨_, poisoned, _, checked, assigned, committed, installed, _, _⟩ :=
    request.runOnRawOpenPhase_acknowledges dir lookup append stage sync rename opened.phase opened.get opened.set
      loaded nonempty prepared fits returned
  have outcome := syncer.publicationOutcome cache appender stager rename
    (first := (oldInstalled).activeFirst) (count := (oldInstalled).walBytes + WAL.frameSize * request.rows.length)
    (bytes := WAL.encodeBatch batch) poisoned
  rw [committed] at outcome
  exact (effects.throughPublication WalNamePresenceFrame.trans prepared checked assigned outcome).trans (restoreFrame installed)

/-- An ordinary uncertain write returns on the original opened phase
and cache. Follow the reached guard, poison assignment and failed
commit to obtain the still-held authority and the exact protected-file
frame. The returned heap can supply a later release or crash observation. -/
theorem NativeOpenedPosition.returnsCommitUnknown
    (request : WriteRequest)
    (lookup : FilePath → EStateM IO.Error heap IO.FS.Metadata)
    (rename : FilePath → FilePath → EStateM IO.Error heap Unit)
    {cause : IO.Error} {reached : heap}
    (nonempty : request.rows ≠ [])
    (returned : request.runOnRawOpenPhase dir lookup append stage sync rename
      opened.phase opened.get opened.set current.reached = .error (.commitUnknown cause) reached)
    (entryCensus : view.descriptors current.reached = (before).census)
    (entryCache : view.cacheAt current.reached cache.directory cache.active cache.pending = (before).cache)
    (storage : heap → CheckpointStorageObservation)
    (old : NativeReadyProtectedStorage before (storage current.reached).files)
    (root : ∀ literal, view.directory current.reached cache.directory = some literal →
      (storage current.reached).files.names (dir).path = some ((view.handle current.reached literal).1.inode
        (view.handle current.reached literal).2.1.description))
    (guardFrame : ∀ {guarded}, checkActiveSegmentWith dir oldInstalled lookup current.reached = .ok () guarded →
      current.framesRawWrite view cache.directory storage current.reached guarded)
    (poisonFrame : ∀ {guarded poisoned}, opened.set opened.phase .poisoned guarded = .ok () poisoned →
      view.framesWrite before cache.directory storage guarded poisoned)
    (commitFrames : current.PublicationCallbackFrames appender stager syncer cache request lookup rename
      (current.framesRawWrite view cache.directory storage)) :
    opened.table.UsesOpenWriteSchedules dir opened.files opened.phase ∧
    opened.contents reached opened.phase = some .poisoned ∧
    (storage current.reached).Frames (before).writeFramePath (storage reached) ∧
    (∃ custody : NativePendingWriteCensus before (view.cacheAt reached cache.directory cache.active cache.pending),
      custody.reached = view.descriptors reached ∧ custody.bindings = (storage reached).files.names) ∧
    ∃ batch table guarded poisoned,
      prepareBatch (oldInstalled).table request.rows = some (batch, table) ∧
      (oldInstalled).walBytes + WAL.frameSize * request.rows.length < UInt64.size ∧
      checkActiveSegmentWith dir oldInstalled lookup current.reached = .ok () guarded ∧
      opened.set opened.phase .poisoned guarded = .ok () poisoned ∧
      syncer.PublicationOutcome cache appender stager rename (oldInstalled).activeFirst
        ((oldInstalled).walBytes + WAL.frameSize * request.rows.length) (WAL.encodeBatch batch) poisoned
        (.error cause reached) := by
  have valid := current.current.ready.readPrefix.refines.1
  obtain ⟨batch, table, guarded, poisoned, prepared, fits, guard, excluded, _, outcome⟩ :=
    current.classifiesCommitUnknown appender stager syncer cache request lookup rename nonempty returned
  have afterGuard := guardFrame guard
  have present := afterGuard.2.trans current.stored
  obtain ⟨actual, assigned, stored⟩ := opened.phaseEffects.writes guarded opened.phase _ .poisoned present
  have samePoisoned := (EStateM.Result.ok.inj (assigned.symm.trans excluded)).2
  have atPoisoned : opened.contents poisoned opened.phase = some .poisoned := samePoisoned ▸ stored
  let frame := current.framesRawWrite view cache.directory storage
  have frameTrans {entry mid after : heap} (first : frame entry mid) (last : frame mid after) : frame entry after :=
    ⟨⟨last.1.1.trans first.1.1, first.1.2.trans last.1.2⟩, last.2.trans first.2⟩
  have afterCommit := commitFrames.throughCommit frameTrans prepared guard excluded outcome
  have afterPoison := poisonFrame excluded
  have authority := afterCommit.1.1.trans (afterPoison.1.trans afterGuard.1.1)
  have protectedFrame := afterGuard.1.2.trans (afterPoison.2.trans afterCommit.1.2)
  let custody := NativePendingWriteCensus.ofRawAuthority view cache valid entryCensus entryCache authority
    old root protectedFrame.visible
  exact ⟨current.uses.writeSchedules, afterCommit.2.trans atPoisoned, protectedFrame, ⟨custody, rfl, rfl⟩,
    batch, table, guarded, poisoned, prepared, fits, guard, excluded, outcome⟩

end

/-- The prepared group has the byte count supplied to the actual
commit marker schedule. -/
theorem NativeReadyState.preparedWalCount {state : NativeReadyState} (valid : state.Valid)
    {rows : List (UInt64 × Option UInt64)} {batch : List WAL.Write} {next : PackedTable}
    (prepared : prepareBatch state.writer.installed.table rows = some (batch, next)) :
    (WAL.encode (state.writer.history ++ batch)).size = state.writer.installed.walBytes + WAL.frameSize * rows.length := by
  have appendSize : (WAL.encode batch).size = WAL.frameSize * rows.length := by
    rw [WAL.encode_size, (prepareBatch_spec prepared).1]
  rw [WAL.encode_append, ByteArray.size_append, appendSize, valid.retained.resumed.bytes]

/-- Read the marker and keeper from one namespace and inode-byte choice.
The checkpoint binding is supplied separately by the protected-file frame. -/
theorem NativeReadyState.selectsWriteWal {state : NativeReadyState} (valid : state.Valid)
    {batch : List WAL.Write} (fits : (WAL.encode (state.writer.history ++ batch)).size < UInt64.size)
    (names : FilePath → Option Nat) (contents : Nat → ByteArray) {marker keeper : Nat}
    (marked : names (state.session.directory.file .walBoundary) = some marker)
    (bound : names (state.session.directory.file (.walSegment state.writer.wal.active.first)) = some keeper)
    (selected :
      (contents marker = WAL.Boundary.encode (WAL.encode state.writer.history).size.toUInt64 ∧
        ∃ tail, contents keeper = state.writer.wal.active.bytes ++ tail) ∨
      (contents marker = WAL.Boundary.encode (WAL.encode (state.writer.history ++ batch)).size.toUInt64 ∧
        contents keeper = state.writer.wal.active.bytes ++ WAL.encode batch)) :
    ∃ target, BatchRetryTarget state.writer.history batch state.writer.wal.active.first target ∧
      target.pair = ⟨state.writer.target.pair.manifest, (names (state.session.directory.file .walBoundary)).map contents⟩ ∧
      target.Accepts ((names (state.session.directory.file (.walSegment state.writer.wal.active.first))).map contents) := by
  have starts := valid.retained.layout.forward state.writer.wal.active (by simp [WalSegmentImage.segments])
  rw [valid.retained.layout.activeEnd] at starts
  rw [valid.retained.layout.activeBytes] at selected
  obtain ⟨history, allowed, markerBytes, keeperBytes⟩ := selectSegment_atBatchBoundary starts fits selected
  obtain ⟨checkpoint, covered, _⟩ := state.writer.target.pair.walRange_accounting state.writer.target.decoded
  have covers : state.writer.target.range.watermark ≤ state.writer.history.length :=
    valid.retained.resumed.through ▸ covered
  let pair : DirectoryPublication.Bindings :=
    ⟨state.writer.target.pair.manifest, (names (state.session.directory.file .walBoundary)).map contents⟩
  have markerCount : pair.walBoundary = some (WAL.Boundary.encode (WAL.encode history).size.toUInt64) := by
    simp only [pair, marked, Option.map_some, markerBytes]
  obtain ⟨target, authorized, same, _, _, _, accepts⟩ :=
    BatchRetryTarget.ofSelected starts covers fits (pair := pair) checkpoint allowed markerCount keeperBytes
  exact ⟨target, authorized, same, by simpa only [bound, Option.map_some] using accepts⟩

/-- A reported survivor samples the bytes of the exact inodes named
by its one map. The same cutoff proof handles either surviving marker
of an uncertain rename or directory sync. -/
theorem WalPublicationPayloads.Selection.retryTarget {state : NativeReadyState} (valid : state.Valid)
    {rows : List (UInt64 × Option UInt64)} {batch : List WAL.Write} {table : PackedTable}
    (prepared : prepareBatch state.writer.installed.table rows = some (batch, table))
    (fits : state.writer.installed.walBytes + WAL.frameSize * rows.length < UInt64.size)
    {payloads : WalPublicationPayloads} {atHeap : CheckpointStorageObservation} {names : FilePath → Option Nat}
    {published : Bool} (selected : payloads.Selection state.session.directory state.writer.wal.active.first
      atHeap names published) (contents : Nat → ByteArray)
    (keeper : contents payloads.keeper ∈ atHeap.files.bytes payloads.keeper)
    (marker : contents (payloads.markerInode published) ∈ atHeap.files.bytes (payloads.markerInode published))
    (sameKeeper : payloads.keeperBytes = state.writer.wal.active.bytes ++ WAL.encodeBatch batch)
    (oldMarker : payloads.oldMarkerBytes = WAL.Boundary.encode (WAL.encode state.writer.history).size.toUInt64)
    (newMarker : payloads.newMarkerBytes =
      WAL.Boundary.encode (state.writer.installed.walBytes + WAL.frameSize * rows.length).toUInt64) :
    ∃ target, BatchRetryTarget state.writer.history batch state.writer.wal.active.first target ∧
      target.pair = ⟨state.writer.target.pair.manifest, (names (state.session.directory.file .walBoundary)).map contents⟩ ∧
      target.Accepts ((names (state.session.directory.file (.walSegment state.writer.wal.active.first))).map contents) := by
  have keeperBytes : contents payloads.keeper = payloads.keeperBytes :=
    List.mem_singleton.mp (selected.keeperStored ▸ keeper)
  have markerBytes : contents (payloads.markerInode published) = payloads.markerBytes published :=
    List.mem_singleton.mp (selected.markerStored ▸ marker)
  have count := NativeReadyState.preparedWalCount valid prepared
  rw [WAL.encodeBatch_eq] at sameKeeper
  rw [← count] at newMarker
  apply NativeReadyState.selectsWriteWal valid (count.symm ▸ fits) names contents selected.markerNamed selected.keeperNamed
  cases published
  · exact .inl ⟨markerBytes.trans oldMarker, WAL.encode batch, keeperBytes.trans sameKeeper⟩
  · exact .inr ⟨markerBytes.trans newMarker, keeperBytes.trans sameKeeper⟩

/-- One chosen namespace keeps the original bindings of the protected
paths across the write, including the root and lock when no file bytes
are sampled for those paths. -/
theorem NativeReadyStorage.chosenWriteBinding {state : NativeReadyState} {entry reached : CheckpointStorageObservation}
    (old : NativeReadyStorage state entry) (frame : entry.Frames state.writeFramePath reached)
    (names : FilePath → Option Nat) (chosen : names ∈ reached.crashNames)
    {path : FilePath} (protectedPath : state.writeFramePath path) : names path = entry.files.names path :=
  old.chosenBinding frame names chosen protectedPath
    (NativeReadyState.crashPath_iff_write.mpr (.inr (.inr protectedPath)))

/-- A selected regular file retains its original bound inode and the
settled bytes when sampled in a joint survivor of the write. -/
theorem NativeReadyStorage.sampleWriteFile {state : NativeReadyState} {entry reached : CheckpointStorageObservation}
    (old : NativeReadyStorage state entry) (frame : entry.Frames state.writeFramePath reached)
    {path : FilePath} (protectedPath : state.writeFramePath path) {payload : ByteArray}
    (stored : entry.files.Stored path payload)
    (names : FilePath → Option Nat) (chosen : names ∈ reached.crashNames) (contents : Nat → ByteArray)
    (sample : ∀ inode, names path = some inode → contents inode ∈ reached.files.bytes inode) :
    ∃ inode, entry.files.names path = some inode ∧ names path = some inode ∧ contents inode = payload :=
  old.sampleFile frame protectedPath (NativeReadyState.crashPath_iff_write.mpr (.inr (.inr protectedPath)))
    stored names chosen contents sample

/-- The write's protected-file frame keeps the selected checkpoint
binding and bytes in each reached joint map, independently of the WAL
marker selected in that map. -/
theorem NativeReadyStorage.selectedWriteManifest {state : NativeReadyState} {entry reached : CheckpointStorageObservation}
    (old : NativeReadyStorage state entry) (frame : entry.Frames state.writeFramePath reached)
    (names : FilePath → Option Nat) (chosen : names ∈ reached.crashNames) (contents : Nat → ByteArray)
    (sample : ∀ inode, names (state.session.directory.file .manifest) = some inode →
      contents inode ∈ reached.files.bytes inode) :
    (names (state.session.directory.file .manifest)).map contents = state.writer.target.pair.manifest := by
  let path := state.session.directory.file .manifest
  have protectedPath : state.writeFramePath path := .inr (.inr (.inl rfl))
  have manifest := old.manifest
  cases present : state.writer.target.pair.manifest with
  | none =>
    rw [present] at manifest
    rw [old.chosenWriteBinding frame names chosen protectedPath, manifest]
    rfl
  | some bytes =>
    rw [present] at manifest
    obtain ⟨_, _, bound, exactBytes⟩ := old.sampleWriteFile frame protectedPath manifest names chosen contents sample
    rw [bound, Option.map_some, exactBytes]

/-- A recovery step chooses one joint map and samples its durable
payloads. The returned write can use either of the publication-tail
proofs to supply this same input to recovery. -/
theorem WalPublicationPayloads.Selections.retryTargets {state : NativeReadyState} (valid : state.Valid)
    {rows : List (UInt64 × Option UInt64)} {batch : List WAL.Write} {table : PackedTable}
    (prepared : prepareBatch state.writer.installed.table rows = some (batch, table))
    (fits : state.writer.installed.walBytes + WAL.frameSize * rows.length < UInt64.size)
    {payloads : WalPublicationPayloads} {entry atHeap : CheckpointStorageObservation}
    (old : NativeReadyStorage state entry) (protectedFiles : entry.Frames state.writeFramePath atHeap)
    {liveNew : Bool} {allows : Bool → Prop}
    (selected : payloads.Selections state.session.directory state.writer.wal.active.first atHeap liveNew allows)
    (sameKeeper : payloads.keeperBytes = state.writer.wal.active.bytes ++ WAL.encodeBatch batch)
    (oldMarker : payloads.oldMarkerBytes = WAL.Boundary.encode (WAL.encode state.writer.history).size.toUInt64)
    (newMarker : payloads.newMarkerBytes =
      WAL.Boundary.encode (state.writer.installed.walBytes + WAL.frameSize * rows.length).toUInt64)
    (names : FilePath → Option Nat) (chosen : names ∈ atHeap.crashNames) (contents : Nat → ByteArray)
    (sample : ∀ path inode,
      (path = state.session.directory.file .manifest ∨ path = state.session.directory.file .walBoundary ∨
        path = state.session.directory.file (.walSegment state.writer.wal.active.first)) →
      names path = some inode → contents inode ∈ atHeap.files.bytes inode) :
    ∃ target, BatchRetryTarget state.writer.history batch state.writer.wal.active.first target ∧
      target.pair = ⟨(names (state.session.directory.file .manifest)).map contents,
        (names (state.session.directory.file .walBoundary)).map contents⟩ ∧
      target.Accepts ((names (state.session.directory.file (.walSegment state.writer.wal.active.first))).map contents) := by
  obtain ⟨_, _, survivor⟩ := selected.survivors names chosen
  have manifest := old.selectedWriteManifest protectedFiles names chosen contents (fun inode => sample _ inode (.inl rfl))
  rw [manifest]
  exact survivor.retryTarget valid prepared fits contents (sample _ _ (.inr (.inr rfl)) survivor.keeperNamed)
    (sample _ _ (.inr (.inl rfl)) survivor.markerNamed) sameKeeper oldMarker newMarker

section

variable {prior : List WAL.Write} {log : List DatabaseSubmissions} (current : NativeReadPosition prior log)

local notation "state" => current.state

/-- The bounded reader input derived from one admitted WAL target. -/
structure NativeReadPosition.SelectedWritePlan (batch : List WAL.Write) (target : Target) (image : FileImage) where
  history : List WAL.Write
  allowed : history = prior ∨ history = prior ++ batch
  layout : CanonicalKeeperLayout image history
  targetEq : layout.target = target
  walLayout : ((state).writer.wal.appendSelectedView image.directory.active history).ReadLayout history
  walValid : ((state).writer.wal.appendSelectedView image.directory.active history).Valid history
  keeper : layout.keeper = ((state).writer.wal.appendSelectedView image.directory.active history).active
  descriptors : layout.sealed ++ [layout.keeper] =
    ((state).writer.wal.appendSelectedView image.directory.active history).readDescriptors layout.range.watermark
  offsets : selectWalSegmentReads (((state).writer.wal.appendSelectedView image.directory.active history).segments.map
    WalSegment.first) layout.range.watermark = some
      (layout.first, (((state).writer.wal.appendSelectedView image.directory.active history).readDescriptors
        layout.range.watermark).map WalSegment.first)
  prepared : Prepared image layout.target layout.plan
  selected : SelectedIntegrityCheckpoint (state).writer.published.durable image.directory.active.manifest
    (state).writer.checkpoint
  accepted : (state).writer.published.AcceptsVersioned history.length.toUInt64
    (WAL.Boundary.CheckpointRepresentsPrefix history) image.directory.active.manifest
  ordered : WAL.OrdinalsFrom 1 history
  pending : PendingClientReplay (log ++ [.uncertainBatch batch]) current.reads history
  bounded : ∀ read ∈ current.reads, read.BoundedBy history.length

/-- Every selected seal belongs to the original immutable seal set. -/
theorem NativeReadPosition.SelectedWritePlan.retainsSeal {batch : List WAL.Write} {target : Target} {image : FileImage}
    (plan : current.SelectedWritePlan batch target image) {segment : WalSegment} (chosen : segment ∈ plan.layout.sealed) :
    segment ∈ (state).writer.wal.sealed := by
  let wal := (state).writer.wal.appendSelectedView image.directory.active plan.history
  have descriptors := plan.descriptors
  change plan.layout.sealed ++ [plan.layout.keeper] = wal.readDescriptors plan.layout.range.watermark at descriptors
  rw [WalSegmentImage.readDescriptors] at descriptors
  split at descriptors
  · rename_i covered
    have fromSeals : plan.layout.sealed = wal.sealed.filter (fun s => decide (plan.layout.range.watermark < s.last)) :=
      (List.append_singleton_inj.mp (by simpa [WalSegmentImage.afterWatermark, WalSegmentImage.segments,
        List.filter_append, covered] using descriptors)).1
    rw [fromSeals] at chosen
    exact (List.mem_filter.mp chosen).1
  · have empty := (List.append_singleton_inj.mp (show plan.layout.sealed ++ [plan.layout.keeper] = [] ++ [wal.active]
      from descriptors)).1
    simp [empty] at chosen

/-- Rebuild the bounded reader and replay at an image that implements
an already selected target. Repair may change the keeper and later names. -/
theorem NativeReadPosition.preparesSelectedWrite
    {rows : List (UInt64 × Option UInt64)} {batch : List WAL.Write} {table : PackedTable}
    (prepared : prepareBatch (state).writer.installed.table rows = some (batch, table))
    (fits : (state).writer.installed.walBytes + WAL.frameSize * rows.length < UInt64.size)
    {target : Target} (admitted : BatchRetryTarget (state).writer.history batch (state).writer.wal.active.first target)
    {image : FileImage} (observed : image.Valid target)
    (manifest : target.pair.manifest = (state).writer.target.pair.manifest) :
    Nonempty (current.SelectedWritePlan batch target image) := by
  have imageManifest := (congrArg DirectoryPublication.Bindings.manifest observed.selected).trans manifest
  obtain ⟨valid, priorHistory, replay⟩ := current.readPrefix.refines
  let ready := valid.retained
  have oldRange : (state).writer.wal.directory.active.walRange =
      some ⟨(state).writer.target.range.watermark, (state).writer.history.length⟩ := by
    rw [ready.walPair, (state).writer.target.decoded, ← ready.resumed.through]
  have sameManifest : target.pair.manifest = (state).writer.wal.directory.active.manifest := by
    rw [ready.walPair]
    exact manifest
  have checkpoint : (state).writer.published.AcceptsVersioned (state).writer.history.length.toUInt64
      (WAL.Boundary.CheckpointRepresentsPrefix (state).writer.history) (state).writer.wal.directory.active.manifest := by
    rw [ready.walPair]
    exact ready.resumed.accepted
  obtain ⟨_, refined, represented⟩ := ready.resumed.canonical
  have committed : (state).writer.history.length = (state).writer.installed.table.committed.toNat :=
    represented.committed_count.symm.trans (congrArg UInt64.toNat refined.committed).symm
  have count := NativeReadyState.preparedWalCount valid prepared
  obtain ⟨history, allowed, _, layoutValid, walValid, layout, targetEq, _, _, exactKeeper,
    descriptors, offsets, plan, accepted, ordered, _⟩ :=
    selectedBatchReopenLayout ready.layout ready.valid oldRange ready.resumed.ordered committed prepared
      (count.symm ▸ fits) checkpoint admitted sameManifest observed.selected observed.keeper observed.later
  have selectedHistory := allowed.imp (·.trans priorHistory) (·.trans (congrArg (· ++ batch) priorHistory))
  obtain ⟨pending, bounded⟩ := replay.appendUncertain current.readPrefix.readsBounded selectedHistory ordered
  exact ⟨⟨history, selectedHistory, layout, targetEq, layoutValid, walValid, exactKeeper, descriptors, offsets, plan,
    imageManifest.symm ▸ ready.resumed.selected, accepted, ordered, pending, bounded⟩⟩

end

end Alvoki.Storage.DiskSession
