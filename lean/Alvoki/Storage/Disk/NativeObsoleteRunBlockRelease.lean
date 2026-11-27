import Alvoki.Storage.Disk.Proofs.Checkpoint.NativeCheckpointRunCollection
import Alvoki.Storage.Disk.ObsoleteRunInodeLifetime
import Alvoki.Storage.Disk.WalCollectionStorageRelease

namespace Alvoki.Storage.DiskSession

open System CheckpointPublication

variable {state : NativeReadyState}

/-- The no-follow probe that feeds the completed collector's selector
identifies this original inode. The raw unlink projection applies only
to the chosen callback at a reached prefix of this same checked pass. -/
structure NativeObsoleteRunInodeReport (seen : NativeObsoleteRunCollection state) (name : RunAddress) where
  lookup : RunChildLookup seen.lifetime.root (renderRunFileName name.1 name.2) seen.lifetime.namespaceView
  metadata : IO.FS.Metadata
  rawStat : FilePath → Except IO.Error (IO.FS.Metadata × DeviceInode)
  identified : rawStat (state.session.directory.file (.run name.1 name.2)) = .ok (metadata, lookup.child)
  statProjection : seen.stat (state.session.directory.file (.run name.1 name.2)) =
    (rawStat (state.session.directory.file (.run name.1 name.2))).map Prod.fst
  entry : seen.pathObject (state.census, seen.initial) (state.session.directory.file (.run name.1 name.2)) = some lookup.child
  member : seen.initial.visible name.1 name.2 ≠ none
  older : name.1 < state.writer.installed.generation
  unheld : name.1 ∉ seen.reports.held
  earlierUnlinks : ∀ (done : List RunAddress) next remaining issue after,
    seen.reports.selected = done ++ next :: remaining →
    ((done.map RunCollection.Step.unlink).forM seen.reports.perform) seen.initial = .ok () issue →
    seen.reports.perform (.unlink next) issue = .ok () after → next ≠ name → name ∉ done →
    let path := state.session.directory.file (.run name.1 name.2)
    seen.pathObject (state.census, after) path = seen.pathObject (state.census, issue) path
  issueCustody : ∀ (done remaining : List RunAddress) issue,
    seen.reports.selected = done ++ name :: remaining →
    ((done.map RunCollection.Step.unlink).forM seen.reports.perform) seen.initial = .ok () issue →
    seen.pathObject (state.census, issue) state.session.directory.path = some seen.lifetime.root ∧
    seen.pathObject (state.census, issue) (state.session.directory.file .lock) = some seen.lifetime.lock
  remove : FilePath → EStateM IO.Error (DescriptorInventory × RunUnlinkImage) (Except IO.Error Unit)
  projected : ∀ (done remaining : List RunAddress) issue result after,
    seen.reports.selected = done ++ name :: remaining →
    ((done.map RunCollection.Step.unlink).forM seen.reports.perform) seen.initial = .ok () issue →
    let path := state.session.directory.file (.run name.1 name.2)
    seen.reports.removeFile path issue = .ok result after →
    remove path (state.census, issue) = .ok result (state.census, after)
  missing : ∀ issue after source message,
    let path := state.session.directory.file (.run name.1 name.2)
    remove path (state.census, issue) = .ok (.error (.noFileOrDirectory source 2 message)) (state.census, after) →
    seen.pathObject (state.census, issue) path = none
  detaches : ∀ issue after,
    let path := state.session.directory.file (.run name.1 name.2)
    remove path (state.census, issue) = .ok (.ok ()) (state.census, after) →
    seen.pathObject (state.census, after) path = none

/-- Locate the first selected occurrence in the actual successful unlink
program and compose a projection along precisely its completed prefix. -/
private theorem firstReachedUnlink {view : Type}
    (perform : RunCollection.Step RunAddress → EStateM IO.Error RunUnlinkImage Unit)
    (project : RunUnlinkImage → view) (selected : RunAddress)
    {targets : List RunAddress} {initial final : RunUnlinkImage} (member : selected ∈ targets)
    (ran : ((targets.map RunCollection.Step.unlink).forM perform) initial = .ok () final)
    (frame : ∀ (done : List RunAddress) next remaining issue after, targets = done ++ next :: remaining →
      ((done.map RunCollection.Step.unlink).forM perform) initial = .ok () issue →
      perform (.unlink next) issue = .ok () after → next ≠ selected → selected ∉ done →
      project after = project issue) :
    ∃ (done remaining : List RunAddress) (issue after : RunUnlinkImage),
      targets = done ++ selected :: remaining ∧ selected ∉ done ∧
      ((done.map RunCollection.Step.unlink).forM perform) initial = .ok () issue ∧
      perform (.unlink selected) issue = .ok () after ∧ project issue = project initial := by
  induction targets generalizing initial with
  | nil => contradiction
  | cons first rest ih =>
    change EStateM.bind (perform (.unlink first)) (fun _ =>
      (rest.map RunCollection.Step.unlink).forM perform) initial = _ at ran
    cases next : perform (.unlink first) initial with
    | error cause reached => simp only [EStateM.bind, next] at ran; cases ran
    | ok value reached =>
      cases value
      simp only [EStateM.bind, next] at ran
      by_cases same : first = selected
      · exact ⟨[], rest, initial, reached, congrArg (· :: rest) same, by simp, rfl, same ▸ next, rfl⟩
      · obtain ⟨done, remaining, issue, after, order, beforeTarget, preceding, accepted, kept⟩ :=
          ih ((List.mem_cons.mp member).resolve_left (Ne.symm same)) ran (by
            intro done address todo before after order earlier returned different without
            apply frame (first :: done) address todo before after (congrArg (List.cons first) order) ?_ returned different
              (by simp [Ne.symm same, without])
            change EStateM.bind (perform (.unlink first)) (fun _ => (done.map RunCollection.Step.unlink).forM perform)
              initial = _
            simpa only [EStateM.bind, next] using earlier)
        have precedingFirst : (((first :: done).map RunCollection.Step.unlink).forM perform) initial = .ok () issue := by
          change EStateM.bind (perform (.unlink first)) (fun _ => (done.map RunCollection.Step.unlink).forM perform) initial = _
          simpa only [EStateM.bind, next] using preceding
        exact ⟨first :: done, remaining, issue, after, congrArg (List.cons first) order,
          by simp [Ne.symm same, beforeTarget], precedingFirst, accepted,
          kept.trans (frame [] first rest initial reached rfl rfl next same (by simp))⟩

private theorem acceptedRawRunUnlink
    (seen : NativeObsoleteRunCollection state) {name : RunAddress} {issue after : RunUnlinkImage}
    (accepted : seen.reports.perform (.unlink name) issue = .ok () after) :
    ∃ result, seen.reports.removeFile (state.session.directory.file (.run name.1 name.2)) issue = .ok result after ∧
      RunCollection.ownedUnlinkResult result = .ok () := by
  unfold SegmentedRunCollectionReports.perform at accepted
  simp only [RunCollection.performPaths, Bind.bind, EStateM.bind] at accepted
  cases raw : seen.reports.removeFile (state.session.directory.file (.run name.1 name.2)) issue with
  | error cause reached => rw [raw] at accepted; cases accepted
  | ok result reached =>
    rw [raw] at accepted
    cases checked : RunCollection.ownedUnlinkResult result with
    | error cause =>
      simp only [checked, throw, throwThe, MonadExceptOf.throw, EStateM.throw] at accepted
      cases accepted
    | ok value =>
      cases value
      simp only [checked, Pure.pure, EStateM.pure, EStateM.Result.ok.injEq, true_and] at accepted
      exact ⟨result, by rw [accepted], checked⟩

namespace NativeObsoleteRunInodeReport

variable {seen : NativeObsoleteRunCollection state} {name : RunAddress}

abbrev path (_observed : NativeObsoleteRunInodeReport seen name) : FilePath :=
  state.session.directory.file (.run name.1 name.2)

def inode (observed : NativeObsoleteRunInodeReport seen name) : Nat :=
  seen.lifetime.namespaceView.modelObject observed.lookup.child

theorem stat (observed : NativeObsoleteRunInodeReport seen name) : seen.stat observed.path = .ok observed.metadata := by
  rw [observed.statProjection, observed.identified]
  rfl

/-- The reported detach at the reached position of the checked program. -/
def DetachesOriginal (observed : NativeObsoleteRunInodeReport seen name) : Prop :=
    ∃ (done remaining : List RunAddress) (issue after : RunUnlinkImage),
      seen.reports.selected = done ++ name :: remaining ∧
      ((done.map RunCollection.Step.unlink).forM seen.reports.perform) seen.initial = .ok () issue ∧
      observed.rawStat observed.path = .ok (observed.metadata, observed.lookup.child) ∧
      seen.stat observed.path = .ok observed.metadata ∧ observed.metadata.type = .file ∧
      seen.pathObject (state.census, issue) state.session.directory.path = some seen.lifetime.root ∧
      seen.pathObject (state.census, issue) (state.session.directory.file .lock) = some seen.lifetime.lock ∧
      seen.pathObject (state.census, issue) observed.path = some observed.lookup.child ∧
      observed.remove observed.path (state.census, issue) = .ok (.ok ()) (state.census, after) ∧
      seen.pathObject (state.census, after) observed.path = none

/-- The actually issued unlink starts below the held root and removes the
object identified by the selector's earlier no-follow lookup. A name
bound at that reached state cannot take the accepted ENOENT branch. -/
theorem detachesOriginal (observed : NativeObsoleteRunInodeReport seen name) (valid : state.Valid) :
    observed.DetachesOriginal := by
  obtain ⟨bytes, visible⟩ := Option.ne_none_iff_exists'.mp observed.member
  obtain ⟨listed, regular⟩ := seen.complete name.1 name.2 bytes visible observed.older observed.unheld
  have inInventory := seen.toNativeObsoleteRunPass.toNativeObsoleteRunPlan.checkedNames.mem_iff.mpr listed
  have chosen := (seen.reports.selected_eligible valid.retained).mpr ⟨inInventory, observed.older, observed.unheld, regular⟩
  have file := seen.toNativeObsoleteRunPass.toNativeObsoleteRunPlan.reportedRegular
    inInventory observed.older observed.unheld observed.stat regular
  obtain ⟨done, remaining, issue, after, order, _, prefixRan, accepted, kept⟩ :=
    firstReachedUnlink seen.reports.perform (fun reached => seen.pathObject (state.census, reached) observed.path)
      name chosen seen.unlinked observed.earlierUnlinks
  obtain ⟨result, reported, checked⟩ := acceptedRawRunUnlink seen accepted
  have raw := observed.projected done remaining issue result after order prefixRan reported
  have bound := kept.trans observed.entry
  have success : result = .ok () := by
    rcases RunCollection.ownedUnlinkResult_ok_iff.mp checked with success | ⟨source, message, missing⟩
    · exact success
    · rw [missing] at raw
      exact False.elim (Option.some_ne_none _ (bound.symm.trans (observed.missing issue after source message raw)))
  rw [success] at raw
  obtain ⟨root, lock⟩ := observed.issueCustody done remaining issue order prefixRan
  exact ⟨done, remaining, issue, after, order, prefixRan, observed.identified, observed.stat, file, root, lock, bound, raw,
    observed.detaches issue after raw⟩

/-- Complete global link observations for this inode, including aliases
outside the database directory. They use the collector's same visible
namespace and align each reported crash namespace with its run map. -/
structure LinkCensus (observed : NativeObsoleteRunInodeReport seen name) where
  links : RunInodeLinkReports observed.path name observed.inode seen.initial seen.atBarrier.syncDirectory
  entry : links.entry observed.path =
    (seen.pathObject (state.census, seen.initial) observed.path).map seen.lifetime.namespaceView.modelObject
  returned : ∀ path, links.visible path = some observed.inode ↔
    (seen.pathObject (seen.toNativeObsoleteRunPass.returnCensus, seen.atBarrier.syncDirectory) path).map
      seen.lifetime.namespaceView.modelObject = some observed.inode

/-- The checked pass really detached the observed object and settled its
absence. After the reported last slot drops, completed filesystem
eviction releases its reported exclusive blocks. A separate observation
excludes non-descriptor kernel references and unrelated reallocation. -/
theorem releasesBlocks (observed : NativeObsoleteRunInodeReport seen name) (valid : state.Valid)
    (census : observed.LinkCensus)
    (last : InodeLastObservedDrop observed.inode seen.toNativeObsoleteRunPass.returnCensus)
    (eviction : InodeBlockEviction observed.inode census.links.visible census.links.crashImages last.after)
    (noOutside : eviction.outside = []) :
    observed.DetachesOriginal ∧
    seen.atBarrier.syncDirectory.DurablyAbsent name ∧
    (∀ path, (seen.pathObject (seen.toNativeObsoleteRunPass.returnCensus, seen.atBarrier.syncDirectory) path).map
      seen.lifetime.namespaceView.modelObject ≠ some observed.inode) ∧
    (∀ bindings ∈ census.links.crashImages, ∀ path, bindings path ≠ some observed.inode) ∧
    (∃ slot ∈ last.before.slots, last.before.inode slot.description = observed.inode) ∧
    (∀ slot ∈ last.after.slots, last.after.inode slot.description ≠ observed.inode) ∧
    ∀ block ∈ eviction.exclusiveBlocks,
      eviction.ownersBefore block = [observed.inode] ∧ eviction.allocatedBefore block ∧ ¬eviction.allocatedAfter block := by
  have absent := (seen.reclaims valid).2.1 name.1 name.2 observed.older observed.unheld
  obtain ⟨visible, crashes⟩ := census.links.noLinks absent
  exact ⟨observed.detachesOriginal valid, absent, fun path found => visible path ((census.returned path).mpr found),
    crashes, last.endsSlots.1, last.endsSlots.2.2, eviction.releases visible crashes last.endsSlots.2.2 noOutside⟩

end NativeObsoleteRunInodeReport

variable {image : Type}
  {attempt : SegmentedCheckpointReport state.session.directory state.writer}
  {reports : CheckpointCompletionReports (CensusDirectoryCache × image) attempt}
  {checkpoint : NativeReadyCheckpoint state reports} {writer : SegmentedWriterState} {held : List UInt64}

/-- Use the completed checkpoint's run image and descriptor census for
the actual collector. The raw entry link identifies the old inode in the
checkpoint's last binding report. Blocks released later belong to
that inode, while current and caller-held run payloads stay protected. -/
theorem CheckpointRunCollectionReports.releasesObsoleteBlocks
    (seen : CheckpointRunCollectionReports checkpoint writer held) (completed : checkpoint.Completed writer)
    {name : RunAddress} (observed : NativeObsoleteRunInodeReport seen.collector name)
    (census : observed.LinkCensus)
    (entry : (seen.collector.pathObject ((checkpoint.next writer).census, seen.collector.initial) observed.path).map
      seen.collector.lifetime.namespaceView.modelObject = checkpoint.bindings reports.observed.completed.2 observed.path)
    (last : InodeLastObservedDrop observed.inode seen.collector.toNativeObsoleteRunPass.returnCensus)
    (eviction : InodeBlockEviction observed.inode census.links.visible census.links.crashImages last.after)
    (noOutside : eviction.outside = []) :
    checkpoint.bindings reports.observed.completed.2 observed.path = some observed.inode ∧
    seen.collector.run = .ok () (seen.collector.next.session.phase,
      ⟨(seen.collector.next.cache, seen.collector.atBarrier.syncDirectory), seen.collector.next.files.owners⟩) ∧
    observed.DetachesOriginal ∧
    seen.collector.atBarrier.syncDirectory.DurablyAbsent name ∧
    (∀ slot ∈ last.after.slots, last.after.inode slot.description ≠ observed.inode) ∧
    (∀ generation index bytes, writer.installed.generation ≤ generation ∨ generation ∈ held →
      (reports.runs reports.observed.completed).guaranteed generation index = some bytes →
      seen.collector.atBarrier.syncDirectory.guaranteed generation index = some bytes) ∧
    ∀ block ∈ eviction.exclusiveBlocks,
      eviction.ownersBefore block = [observed.inode] ∧ eviction.allocatedBefore block ∧ ¬eviction.allocatedAfter block := by
  have released := observed.releasesBlocks completed.valid census last eviction noOutside
  have collection := seen.completes completed
  exact ⟨entry.symm.trans (census.entry.symm.trans census.links.entryBound), collection.1, released.1, released.2.1,
    released.2.2.2.2.2.1, collection.2.2.1, released.2.2.2.2.2.2⟩

end Alvoki.Storage.DiskSession
