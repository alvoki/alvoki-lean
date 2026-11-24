import Alvoki.Storage.Disk.DiskTable
import Alvoki.Storage.Disk.MarkedWalReopenModel
import Alvoki.Storage.Publication.CheckpointPublicationModel

namespace Alvoki.Storage
open Alvoki.Compaction (CheckedRun)

/-- A selected manifest and its exact ordered run bytes describe a flushed
checkpoint. An absent manifest uses the same empty base as the Linux adapter. -/
inductive CheckpointForRecovery : Option ByteArray → List ByteArray → PackedTable → Prop where
  | absent : CheckpointForRecovery none [] .empty
  | written (header : Manifest.Checkpoint) (checkpoint : PackedTable)
      (flushed : checkpoint.memory = Alvoki.Sequential.History.empty)
      (count : checkpoint.runs.length = header.runCount.toNat)
      (watermark : header.committed = checkpoint.committed)
      (floor : header.floor = checkpoint.pins.floor)
      (validFloor : header.floor ≤ header.committed)
      (bounded : ∀ run ∈ checkpoint.runs, ∀ row ∈ run.history.rows, row.sequence ≤ header.committed) :
      CheckpointForRecovery (some (Manifest.encode header))
        (checkpoint.runs.map (·.run.bytes)) checkpoint

theorem CheckpointForRecovery.rowBounds {manifest : Option ByteArray} {files : List ByteArray}
    {checkpoint : PackedTable} (written : CheckpointForRecovery manifest files checkpoint) :
    checkpoint.RowBounds := by
  cases written with
  | absent => exact PackedTable.empty_rowBounds
  | written _ _ flushed _ watermark _ _ bounded =>
    exact ⟨fun run mem row inside => watermark ▸ bounded run mem row inside,
      by simp [flushed, Alvoki.Sequential.History.empty]⟩

theorem CheckpointForRecovery.loads {manifest : Option ByteArray} {files : List ByteArray}
    {checkpoint : PackedTable} (written : CheckpointForRecovery manifest files checkpoint) :
    ∃ base, (match manifest with
      | none => Except.ok PackedTable.empty
      | some bytes => do
        let header ← Manifest.decode bytes
        loadRunSet header files) = .ok base ∧ base.SameData checkpoint := by
  cases written with
  | absent => exact ⟨.empty, rfl, ⟨rfl, rfl, rfl, rfl⟩⟩
  | written header checkpoint flushed count watermark floor validFloor bounded =>
    obtain ⟨base, loaded, restored⟩ := loadRunSet_written header checkpoint.runs count validFloor bounded
    rw [watermark, floor] at restored
    refine ⟨base, ?_, PackedTable.restore_sameData flushed restored⟩
    change (do
      let decoded ← Manifest.decode (Manifest.encode header)
      loadRunSet decoded (checkpoint.runs.map fun run : CheckedRun => run.run.bytes)) = .ok base
    rw [Manifest.decode_encode header validFloor]
    exact loaded

theorem CheckpointForRecovery.recoverSelected_rowBounds {manifest : Option ByteArray}
    {bytes : ByteArray} {runs : List ByteArray} {checkpoint result : PackedTable}
    (written : CheckpointForRecovery manifest runs checkpoint)
    (recovered : (manifest.elim (Except.ok PackedTable.empty)
      (fun header => Manifest.decode header >>= fun decoded => loadRunSet decoded runs) >>= fun base =>
        recoverSelected base bytes) = .ok result) : result.RowBounds := by
  obtain ⟨base, loaded, same⟩ := written.loads
  have load : manifest.elim (Except.ok PackedTable.empty)
      (fun header => Manifest.decode header >>= fun decoded => loadRunSet decoded runs) = .ok base := by
    cases manifest <;> exact loaded
  rw [load] at recovered
  exact Alvoki.Storage.recoverSelected_rowBounds (same.rowBounds written.rowBounds) recovered

/-- The native checkpoint's prepared table and exact run bytes witness
recovery. The input rows must already be covered by the committed watermark.
The abstract table takes the same flush decision as the adapter. -/
theorem CheckpointForRecovery.of_flushForCheckpoint
    {before checkpoint : PackedTable} {model : Alvoki.Sequential.SnapshotTable UInt64}
    (prepared : (flushForCheckpoint before id : Except String PackedTable) = .ok checkpoint)
    (refines : before.Refines model) (fits : checkpoint.runs.length < UInt64.size)
    (runBound : ∀ run ∈ before.runs, ∀ row ∈ run.history.rows, row.sequence ≤ before.committed)
    (memoryBound : ∀ row ∈ before.memory.rows, row.sequence ≤ before.committed)
    (generation : UInt64) :
    CheckpointForRecovery (some (Manifest.encode (checkpointHeader checkpoint generation)))
      (checkpoint.runs.map (·.run.bytes)) checkpoint ∧
    checkpoint.committed = before.committed ∧
    checkpoint.Refines (if before.memory.rows.isEmpty then model else model.flush) := by
  obtain ⟨empty, committed, bounded, relation⟩ :
      checkpoint.memory = Alvoki.Sequential.History.empty ∧
      checkpoint.committed = before.committed ∧
      checkpoint.RowBounds ∧
      checkpoint.Refines (if before.memory.rows.isEmpty then model else model.flush) := by
    unfold flushForCheckpoint at prepared
    split at prepared
    · rename_i emptyRows
      change Except.ok before = .ok checkpoint at prepared
      cases Except.ok.inj prepared
      refine ⟨Alvoki.Sequential.History.ext_rows ?_, rfl, ⟨runBound, memoryBound⟩, ?_⟩
      · exact List.isEmpty_iff.mp emptyRows
      · simpa only [emptyRows, ↓reduceIte] using refines
    · rename_i nonempty
      change before.flush = .ok checkpoint at prepared
      have refined := PackedTable.flush_refines refines prepared
      have bounded := (⟨runBound, memoryBound⟩ : before.RowBounds).flush prepared
      unfold PackedTable.flush at prepared
      cases encoded : CheckedRun.ofHistory before.memory with
      | error message => simp [encoded] at prepared
      | ok run =>
        rw [encoded] at prepared
        cases prepared
        exact ⟨rfl, rfl, bounded, by simpa [nonempty] using refined⟩
  have floor : checkpoint.pins.floor ≤ checkpoint.committed := by
    rw [relation.pins, relation.committed]
    exact (if before.memory.rows.isEmpty then model else model.flush).floor_committed
  exact ⟨.written _ _ empty (UInt64.toNat_ofNat_of_lt' fits).symm rfl rfl floor bounded.runs,
    committed, relation⟩

private theorem read_ordered_runs (read : Nat → Option ByteArray) (first : Nat)
    (files : List ByteArray)
    (durable : ∀ index, index < files.length → read (first + index) = files[index]?) :
    (List.range' first files.length).mapM read = some files := by
  induction files generalizing first with
  | nil => rfl
  | cons bytes files ih =>
    have head : read first = some bytes := by
      simpa using durable 0 (by simp)
    have tail : (List.range' (first + 1) files.length).mapM read = some files := by
      apply ih
      intro index within
      simpa [Nat.add_assoc, Nat.add_comm 1 index] using durable (index + 1) (by simpa using within)
    simp [List.range'_succ, List.mapM_cons, head, tail]

/-- Read the known durable run names in the manifest's recovery order. -/
def CheckpointPublication.Image.readDurableCheckpointRuns (image : CheckpointPublication.Image) :
    Option ByteArray → Option (List ByteArray)
  | none => some []
  | some bytes => do
    let header ← (Manifest.decode bytes).toOption
    (List.range header.runCount.toNat).mapM (image.durable header.generation)

private theorem read_durable_runs {image : CheckpointPublication.Image} {bytes : ByteArray}
    {header : Manifest.Checkpoint} {files : List ByteArray}
    (decoded : Manifest.decode bytes = .ok header) (count : header.runCount.toNat = files.length)
    (durable : ∀ index, index < files.length → image.durable header.generation index = files[index]?) :
    image.readDurableCheckpointRuns (some bytes) = some files := by
  simp only [CheckpointPublication.Image.readDurableCheckpointRuns, decoded, Except.toOption]
  change (List.range header.runCount.toNat).mapM (image.durable header.generation) = some files
  rw [count, List.range_eq_range']
  exact read_ordered_runs _ 0 files (by simpa using durable)

/-- A manifest accepted by the publication model supplies exact ordered run
bytes and a loader witness with the caller's checkpoint invariant. An absent
manifest uses the empty checkpoint. -/
theorem CheckpointForRecovery.of_durable_manifest_with {image : CheckpointPublication.Image}
    {walSequence : UInt64} {manifest : Option ByteArray}
    {expected : Manifest.Checkpoint → List ByteArray → Prop} {invariant : PackedTable → Prop}
    (accepted : image.Accepts walSequence expected manifest)
    (emptyValid : invariant .empty)
    (witness : ∀ header files, expected header files →
      ∃ checkpoint, CheckpointForRecovery (some (Manifest.encode header)) files checkpoint ∧
        invariant checkpoint) :
    ∃ files checkpoint, CheckpointForRecovery manifest files checkpoint ∧
      image.readDurableCheckpointRuns manifest = some files ∧ invariant checkpoint := by
  cases manifest with
  | none => exact ⟨[], .empty, .absent, rfl, emptyValid⟩
  | some bytes =>
    obtain ⟨header, files, decoded, valid, _, count, durable⟩ := accepted
    obtain ⟨checkpoint, written, property⟩ := witness header files valid
    refine ⟨files, checkpoint, ?_, read_durable_runs decoded count durable, property⟩
    simpa only [Manifest.decode_reencode decoded] using written

/-- The physical loader witness for a manifest whose published exact run bytes
come with a checkpoint witness. -/
theorem CheckpointForRecovery.of_durable_manifest {image : CheckpointPublication.Image}
    {walSequence : UInt64} {manifest : Option ByteArray}
    (accepted : image.Accepts walSequence (fun header files =>
      ∃ checkpoint, CheckpointForRecovery (some (Manifest.encode header)) files checkpoint) manifest) :
    ∃ files checkpoint, CheckpointForRecovery manifest files checkpoint ∧
      image.readDurableCheckpointRuns manifest = some files := by
  obtain ⟨files, checkpoint, written, durable, _⟩ :=
    of_durable_manifest_with (invariant := fun _ => True) accepted trivial
      (fun _ _ ⟨checkpoint, loader⟩ => ⟨checkpoint, loader, trivial⟩)
  exact ⟨files, checkpoint, written, durable⟩

/-- A selected checkpoint with the exact ordered durable files can serve as
the fixed checkpoint of a later session. Its own watermark suffices for
acceptance once the observed manifest and files have been identified. -/
theorem CheckpointForRecovery.accepts_exact_durable {image : CheckpointPublication.Image}
    {walSequence : UInt64} {manifest : Option ByteArray} {files : List ByteArray}
    {checkpoint : PackedTable} {expected : Manifest.Checkpoint → List ByteArray → Prop}
    (written : CheckpointForRecovery manifest files checkpoint)
    (accepted : image.Accepts walSequence expected manifest)
    (durable : image.readDurableCheckpointRuns manifest = some files) :
    image.Accepts checkpoint.committed (fun header stored =>
      CheckpointForRecovery (some (Manifest.encode header)) stored checkpoint) manifest := by
  cases written with
  | absent => trivial
  | written header checkpoint flushed count watermark floor validFloor bounded =>
    obtain ⟨found, stored, decoded, _, _, runCount, names⟩ := accepted
    have sameHeader := Except.ok.inj (decoded.symm.trans (Manifest.decode_encode header validFloor))
    subst found
    have sameFiles := Option.some.inj ((read_durable_runs decoded runCount names).symm.trans durable)
    subst stored
    exact ⟨header, _, decoded, .written header checkpoint flushed count watermark floor validFloor bounded,
      UInt64.le_of_eq watermark, runCount, names⟩

/-- The executable loop reads exactly the manifest's run indices in order. -/
theorem readCheckpointRunBytes_eq_mapM [Monad m] [LawfulMonad m]
    (read : UInt64 → Nat → m ByteArray) (header : Manifest.Checkpoint) :
    readCheckpointRunBytes read header =
      (List.range header.runCount.toNat).mapM (read header.generation) := by
  simp [readCheckpointRunBytes, Std.Legacy.Range.size, ← List.range_eq_range']

private theorem observed_ordered_runs {indices : List Nat} {durableFiles files : List ByteArray}
    {durable : Nat → Option ByteArray} {read : Nat → Except String ByteArray}
    (agrees : ∀ index bytes expected,
      read index = .ok bytes → durable index = some expected → bytes = expected)
    (known : indices.mapM durable = some durableFiles)
    (observed : indices.mapM read = .ok files) :
    files = durableFiles := by
  induction indices generalizing durableFiles files with
  | nil =>
    cases known
    cases observed
    rfl
  | cons index rest ih =>
    cases durableHead : durable index with
    | none => simp [List.mapM_cons, durableHead] at known
    | some expected =>
      cases durableRest : rest.mapM durable with
      | none => simp [List.mapM_cons, durableHead, durableRest] at known
      | some expectedRest =>
        cases readHead : read index with
        | error message => simp [List.mapM_cons, readHead, bind, Except.bind] at observed
        | ok bytes =>
          cases readRest : rest.mapM read with
          | error message => simp [List.mapM_cons, readHead, bind, Except.bind, readRest] at observed
          | ok tail =>
            simp [List.mapM_cons, durableHead, durableRest] at known
            simp [List.mapM_cons, readHead, readRest, bind, Except.bind, pure, Except.pure] at observed
            rw [← observed, ← known, agrees index bytes expected readHead durableHead,
              ih durableRest readRest]

/-- Successful checkpoint reads under the database lock observe the selected
manifest and the contents of the durable run files it names. Read errors are
retained. An untracked run path is outside this part of the model. -/
structure CheckpointReadObservations (image : CheckpointPublication.Image) (manifest : Option ByteArray) where
  readManifest : Except String (Option ByteArray)
  readRun : UInt64 → Nat → Except String ByteArray
  manifestVisible : ∀ value, readManifest = .ok value → value = manifest
  runDurable : ∀ generation index value expected, readRun generation index = .ok value →
    image.durable generation index = some expected → value = expected

def CheckpointReadObservations.result {image : CheckpointPublication.Image} {manifest : Option ByteArray}
    (reads : CheckpointReadObservations image manifest) : Except String (Option (PackedTable × UInt64)) :=
  readCheckpoint reads.readManifest reads.readRun (fun result => result)

/-- A successful run of the native checkpoint read protocol obtains exactly
the validated checkpoint and its manifest generation. The filesystem contract
applies to each primitive read, including the optional manifest lookup. -/
theorem CheckpointReadObservations.loaded {image : CheckpointPublication.Image}
    {manifest : Option ByteArray} {files : List ByteArray} {loaded : Option (PackedTable × UInt64)}
    (reads : CheckpointReadObservations image manifest)
    (durable : image.readDurableCheckpointRuns manifest = some files)
    (opened : reads.result = .ok loaded) :
    (match manifest with
      | none => Except.ok none
      | some bytes => do
        let header ← Manifest.decode bytes
        let table ← loadRunSet header files
        return some (table, header.generation)) = .ok loaded := by
  cases observedManifest : reads.readManifest with
  | error =>
    simp [CheckpointReadObservations.result, readCheckpoint, observedManifest, bind, Except.bind] at opened
  | ok value =>
    have visible := reads.manifestVisible value observedManifest
    subst manifest
    cases value with
    | none =>
      simpa [CheckpointReadObservations.result, readCheckpoint, observedManifest, bind, Except.bind,
        pure, Except.pure] using opened
    | some bytes =>
      simp only [CheckpointReadObservations.result, readCheckpoint, observedManifest, bind, Except.bind] at opened
      cases decoded : Manifest.decode bytes with
      | error => rw [decoded] at opened; contradiction
      | ok header =>
        simp only [CheckpointPublication.Image.readDurableCheckpointRuns, decoded, Except.toOption] at durable
        rw [decoded] at opened
        change (do
          let observedFiles ← readCheckpointRunBytes reads.readRun header
          let table ← loadRunSet header observedFiles
          pure (some (table, header.generation))) = .ok loaded at opened
        rw [readCheckpointRunBytes_eq_mapM] at opened
        cases observedFiles : (List.range header.runCount.toNat).mapM (reads.readRun header.generation) with
        | error => rw [observedFiles] at opened; contradiction
        | ok runFiles =>
          have same := observed_ordered_runs (reads.runDurable header.generation) durable observedFiles
          subst runFiles
          simpa only [decoded, observedFiles, bind, Except.bind] using opened

private theorem CheckpointForRecovery.written_files {bytes : ByteArray} {files : List ByteArray}
    {checkpoint : PackedTable} (written : CheckpointForRecovery (some bytes) files checkpoint) :
    files = checkpoint.runs.map (·.run.bytes) := by
  cases written
  rfl

private theorem CheckpointForRecovery.ordered_durable_runs {image : CheckpointPublication.Image}
    {walSequence : UInt64} {manifest : Option ByteArray} {files : List ByteArray} {checkpoint : PackedTable}
    (written : CheckpointForRecovery manifest files checkpoint)
    (accepted : image.Accepts walSequence (fun header stored =>
      CheckpointForRecovery (some (Manifest.encode header)) stored checkpoint) manifest) :
    image.readDurableCheckpointRuns manifest = some files := by
  cases manifest with
  | none => cases written; rfl
  | some bytes =>
    obtain ⟨header, stored, decoded, witness, _, count, durable⟩ := accepted
    have same := witness.written_files.trans written.written_files.symm
    subst stored
    exact read_durable_runs decoded count durable

/-- Project the native checkpoint read to its replay base, using the exact
ordered run bytes from durability. An absent manifest supplies the empty table. -/
theorem CheckpointReadObservations.loaded_table {image : CheckpointPublication.Image}
    {manifest : Option ByteArray} {files : List ByteArray} {loaded : Option (PackedTable × UInt64)}
    (reads : CheckpointReadObservations image manifest)
    (durable : image.readDurableCheckpointRuns manifest = some files)
    (opened : reads.result = .ok loaded) :
    (match manifest with
    | none => Except.ok PackedTable.empty
    | some bytes => do
      let header ← Manifest.decode bytes
      loadRunSet header files) = .ok (loaded.getD (.empty, 0)).1 := by
  have exactLoaded := reads.loaded durable opened
  have table := congrArg (fun (result : Except String (Option (PackedTable × UInt64))) =>
    (fun checkpoint => (checkpoint.getD (.empty, 0)).1) <$> result) exactLoaded
  cases manifest <;> simp [← bind_pure_comp, bind_assoc] at table <;> exact table

/-- Connecting the successful native read protocol to recovery's loading
equation identifies the exact base table supplied to WAL replay. -/
theorem CheckpointForRecovery.loaded_observation {image : CheckpointPublication.Image}
    {walSequence : UInt64} {manifest : Option ByteArray} {files : List ByteArray} {checkpoint : PackedTable}
    {loaded : Option (PackedTable × UInt64)}
    (written : CheckpointForRecovery manifest files checkpoint)
    (accepted : image.Accepts walSequence (fun header stored =>
      CheckpointForRecovery (some (Manifest.encode header)) stored checkpoint) manifest)
    (reads : CheckpointReadObservations image manifest)
    (opened : reads.result = .ok loaded) :
    (match manifest with
    | none => Except.ok PackedTable.empty
    | some bytes => do
      let header ← Manifest.decode bytes
      loadRunSet header files) = .ok (loaded.getD (.empty, 0)).1 := by
  exact reads.loaded_table (written.ordered_durable_runs accepted) opened

/-- The session uses generation zero for an absent manifest and the decoded
generation for a successfully loaded manifest. -/
theorem CheckpointForRecovery.loaded_generation {image : CheckpointPublication.Image}
    {walSequence : UInt64} {manifest : Option ByteArray} {files : List ByteArray} {checkpoint : PackedTable}
    {loaded : Option (PackedTable × UInt64)}
    (written : CheckpointForRecovery manifest files checkpoint)
    (accepted : image.Accepts walSequence (fun header stored =>
      CheckpointForRecovery (some (Manifest.encode header)) stored checkpoint) manifest)
    (reads : CheckpointReadObservations image manifest)
    (opened : reads.result = .ok loaded) :
    ((manifest.mapM fun bytes => (Manifest.decode bytes).map (·.generation)).map (·.getD 0) :
      Except String UInt64) = .ok (loaded.getD (.empty, 0)).2 := by
  have exactLoaded := reads.loaded (written.ordered_durable_runs accepted) opened
  cases manifest with
  | none =>
    cases Except.ok.inj exactLoaded
    rfl
  | some bytes =>
    change (do
      let header ← Manifest.decode bytes
      let table ← loadRunSet header files
      pure (some (table, header.generation))) = .ok loaded at exactLoaded
    cases decoded : Manifest.decode bytes with
    | error =>
      rw [decoded] at exactLoaded
      contradiction
    | ok header =>
      rw [decoded] at exactLoaded
      cases runSet : loadRunSet header files with
      | error =>
        simp [Bind.bind, Except.bind, runSet] at exactLoaded
      | ok table =>
        simp only [Bind.bind, Except.bind, runSet, Pure.pure, Except.pure] at exactLoaded
        cases Except.ok.inj exactLoaded
        simp [Option.mapM, decoded, Functor.map, Except.map]

/-- A successful marked reopen gets its installed generation from the
checkpoint read and its installed byte count from the decoded marker.
The latter is the length of the WAL left in the visible binding after the
shared durability schedule. Successful primitive reads obey the locked
filesystem observation contract. -/
theorem CheckpointForRecovery.marked_reopen_metadata {image : CheckpointPublication.Image}
    {walSequence : UInt64} {files : List ByteArray} {checkpoint table : PackedTable}
    {before after : WAL.Boundary.ReopenImage}
    (written : CheckpointForRecovery before.directory.active.manifest files checkpoint)
    (accepted : image.Accepts walSequence (fun header stored =>
      CheckpointForRecovery (some (Manifest.encode header)) stored checkpoint)
      before.directory.active.manifest)
    (checkpointReads : CheckpointReadObservations image before.directory.active.manifest)
    (walReads : WAL.Boundary.MarkedWalReads before)
    (bound : WAL.Boundary.MarkerBound before.directory)
    {report : Publication.Step → WAL.Boundary.RepairReport} {aligned : WAL.Boundary.AlignedSyncReport}
    (opened : WAL.Boundary.runMarkedReopen
      (WAL.Boundary.MarkedReopenReads.mk walReads
        (checkpointReads.result.map fun loaded => (loaded.getD (.empty, 0)).1)).preflight
      report false aligned before = .ok table after) :
    ∃ loaded marker length selected,
      checkpointReads.result = .ok loaded ∧
      ((before.directory.active.manifest.mapM fun bytes =>
        (Manifest.decode bytes).map (·.generation)).map (·.getD 0) :
        Except String UInt64) = .ok (loaded.getD (.empty, 0)).2 ∧
      before.directory.active.walBoundary = some marker ∧
      WAL.Boundary.decode marker = .ok length ∧
      after.wal.active = some selected ∧ selected.size = length.toNat := by
  obtain ⟨base, marker, _, selected, length, loadedBase, markerVisible, _, decoded,
    selectedResult, _, _, walActive, _⟩ := WAL.Boundary.MarkedReopenReads.success _ bound opened
  change (checkpointReads.result.map fun loaded => (loaded.getD (.empty, 0)).1) = .ok base
    at loadedBase
  cases loaded : checkpointReads.result with
  | error => rw [loaded] at loadedBase; contradiction
  | ok checkpoint =>
    exact ⟨checkpoint, marker, length, selected, rfl,
      written.loaded_generation accepted checkpointReads loaded, markerVisible, decoded,
      walActive, WAL.Boundary.select_size selectedResult⟩

private theorem ordinals_prefix {first : Nat} {initial suffix : List WAL.Write}
    (ordered : WAL.OrdinalsFrom first (initial ++ suffix)) : WAL.OrdinalsFrom first initial := by
  induction initial generalizing first with
  | nil => trivial
  | cons event rest ih => exact ⟨ordered.1, ih ordered.2⟩

theorem PackedTable.SameData.symm {left right : PackedTable} (same : left.SameData right) :
    right.SameData left :=
  ⟨same.runs.symm, same.memory.symm, same.committed.symm, same.floor.symm⟩

/-- For a supplied manifest and marker pair, the production loader, selector
and replay recover the old or extended history. The reference replays from
the original checkpoint and may have a different pin registry. Given an
abstract checkpoint, replay applies the exact selected suffix and newly
acquired pins read that abstract result at every supported snapshot. A trace
invariant must establish that the selected pair is reachable and the checkpoint
represents the covered prefix. -/
theorem recoverWriteCutSelectedPair {manifest marker : Option ByteArray} {files : List ByteArray}
    {checkpoint : PackedTable} {covered pending : List WAL.Write}
    {event : WAL.Write} {wal : ByteArray} {image : Publication.Image}
    (written : CheckpointForRecovery manifest files checkpoint)
    (cut : WAL.Boundary.WriteCut (covered ++ pending) event wal image)
    (chosen : marker = image.active ∨ marker ∈ image.crashImages)
    (oldFits : (WAL.encode (covered ++ pending)).size < UInt64.size)
    (newFits : (WAL.encode ((covered ++ pending) ++ [event])).size < UInt64.size)
    (ordered : WAL.OrdinalsFrom 1 ((covered ++ pending) ++ [event]))
    (watermark : covered.length = checkpoint.committed.toNat) :
    ∃ markerBytes events base reopened reference, marker = some markerBytes ∧
      markerBytes = WAL.Boundary.encode (WAL.encode events).size.toUInt64 ∧
      (match manifest with
      | none => Except.ok PackedTable.empty
      | some bytes => do
        let header ← Manifest.decode bytes
        loadRunSet header files) = .ok base ∧
      (do
        let count ← WAL.Boundary.decode markerBytes
        WAL.Boundary.select count wal) = .ok (WAL.encode events) ∧
      recoverSelected base (WAL.encode events) = .ok reopened ∧
      (events = covered ++ pending ∨ events = (covered ++ pending) ++ [event]) ∧
      reopened.committed.toNat = events.length ∧
      replay checkpoint (events.drop covered.length) = .ok reference ∧
      reference.SameData reopened ∧
      (∀ model : Sequential.SnapshotTable UInt64, checkpoint.Refines model →
        ∃ abstract, SnapshotWalReplay model (events.drop covered.length) abstract ∧
          abstract.committed.toNat = events.length ∧
          ∀ snapshot : UInt64, abstract.pins.floor ≤ snapshot → snapshot.toNat ≤ events.length →
            ∃ pin pinned, reopened.acquireAt snapshot = some (pin, pinned) ∧
              (∀ key, pinned.lookup pin.handle key = some (abstract.table.lookup key snapshot)) ∧
              (∀ start stop, pinned.range pin.handle start stop =
                some (abstract.table.range start stop snapshot))) := by
  obtain ⟨base, loaded, same⟩ := written.loads
  obtain ⟨markerBytes, events, bound, markerEncoding, history, selected⟩ :=
    WAL.Boundary.write_cut_selects_old_or_new cut oldFits newFits chosen
  obtain ⟨suffix, split, ordinals⟩ :
      ∃ suffix, events = covered ++ suffix ∧ WAL.OrdinalsFrom 1 (covered ++ suffix) := by
    rcases history with prior | advanced
    · exact ⟨pending, prior, ordinals_prefix ordered⟩
    · exact ⟨pending ++ [event], by simpa only [List.append_assoc] using advanced,
        by simpa only [List.append_assoc] using ordered⟩
  subst events
  have count : covered.length = base.committed.toNat := by simpa only [same.committed] using watermark
  obtain ⟨reopened, recovered, sequence⟩ := recoverSelected_encoded_complete base covered suffix ordinals count
  have replayed := (recoverSelected_encoded base covered suffix ordinals count).symm.trans recovered
  obtain ⟨reference, expected, agrees⟩ := replay_sameData same.symm suffix replayed
  have finalCount : reopened.committed.toNat = (covered ++ suffix).length := by
    simpa only [List.length_append] using sequence
  refine ⟨markerBytes, covered ++ suffix, base, reopened, reference, bound, markerEncoding, loaded, selected,
    recovered, history, finalCount, by simpa only [List.drop_left] using expected, agrees, ?_⟩
  intro model represents
  obtain ⟨abstract, modeled, refined⟩ := replay_refines represents expected
  refine ⟨abstract, by simpa only [List.drop_left] using modeled, ?_, ?_⟩
  · rw [← refined.committed, agrees.committed, finalCount]
  · intro snapshot retained within
    have floor : reference.pins.floor ≤ snapshot := by simpa only [refined.pins] using retained
    have committed : snapshot ≤ reference.committed := UInt64.le_iff_toNat_le.mpr (by
      simpa only [agrees.committed, finalCount] using within)
    simpa only [refined.table] using agrees.symm.acquireAt_reads floor committed

end Alvoki.Storage

namespace Alvoki.WAL.Boundary
open Storage

private theorem encoded_history_grows (before : List WAL.Write) (event : WAL.Write) :
    (WAL.encode before).size < (WAL.encode (before ++ [event])).size := by
  simp [WAL.frameSize, Nat.mul_add]

private theorem marker_chosen_of_pair {directory : DirectoryPublication.Image}
    {image : Publication.Image} {pair : DirectoryPublication.Bindings}
    (chosen : pair ∈ directory.active :: directory.crashImages)
    (visible : image.active = directory.active.walBoundary)
    (candidates : ∀ pair ∈ directory.crashImages, pair.walBoundary ∈ image.crashImages) :
    pair.walBoundary = image.active ∨ pair.walBoundary ∈ image.crashImages := by
  rcases List.mem_cons.mp chosen with rfl | afterCrash
  · exact Or.inl visible.symm
  · exact Or.inr (candidates pair afterCrash)

/-- Expected WAL contents for a selectable pair after an interrupted write.
At such a pair the marker is well formed, and its count is either the old or
the extended WAL length. -/
def writeCutPrefix (before : List WAL.Write) (event : WAL.Write)
    (pair : DirectoryPublication.Bindings) : ByteArray :=
  match pair.walBoundary.map decode with
  | some (.ok count) =>
    if count.toNat = (WAL.encode before).size then WAL.encode before
    else WAL.encode (before ++ [event])
  | _ => WAL.encode before

/-- Begin the marked reopen proof when each physical WAL candidate comes
from a write cut accounting for the same visible and crash-selectable
markers. Staging can differ because it does not select the replay prefix. -/
theorem ReopenImage.valid_of_writeCut {image : ReopenImage}
    {before : List WAL.Write} {event : WAL.Write}
    (survives : image.wal.crashImages ≠ [])
    (fits : (WAL.encode (before ++ [event])).size < UInt64.size)
    (physical : ∀ binding ∈ image.wal.active :: image.wal.crashImages,
      ∃ contents markerImage, binding = some contents ∧ WriteCut before event contents markerImage ∧
        markerImage.active = image.directory.active.walBoundary ∧
        ∀ pair ∈ image.directory.crashImages, pair.walBoundary ∈ markerImage.crashImages) :
    image.Valid (writeCutPrefix before event) := by
  have grows := encoded_history_grows before event
  have accept (binding : Option ByteArray) (possible : binding ∈ image.wal.active :: image.wal.crashImages) :
      ∀ pair ∈ image.directory.active :: image.directory.crashImages,
        ∃ marker contents length, pair.walBoundary = some marker ∧ binding = some contents ∧
          decode marker = .ok length ∧ select length contents = .ok (writeCutPrefix before event pair) := by
    obtain ⟨contents, markerImage, present, cut, visible, candidates⟩ := physical binding possible
    intro pair chosen
    obtain ⟨marker, events, bound, _, history, selected⟩ :=
      write_cut_selects_old_or_new cut (Nat.lt_trans grows fits) fits
        (marker_chosen_of_pair chosen visible candidates)
    cases decoded : decode marker with
    | error message =>
      rw [decoded] at selected
      contradiction
    | ok length =>
      rw [decoded] at selected
      change select length contents = .ok (WAL.encode events) at selected
      have count := select_size selected
      refine ⟨marker, contents, length, bound, present, decoded, ?_⟩
      rw [selected]
      congr 1
      rcases history with rfl | rfl
      · simp only [writeCutPrefix, bound, Option.map_some, decoded, ite_eq_left count.symm]
      · have larger : (WAL.encode before).size < length.toNat := count ▸ grows
        simp only [writeCutPrefix, bound, Option.map_some, decoded, ite_eq_right (Nat.ne_of_gt larger)]
  exact ⟨survives, accept _ (List.mem_cons_self ..),
    fun binding possible => accept binding (List.mem_cons_of_mem _ possible)⟩

/-- With a fixed matching checkpoint, a selected metadata pair after any
modeled marked reopen retries recovers its original WAL prefix. The abstract
suffix and retained snapshot reads follow from that selection. The caller
supplies the initial physical candidates, ordered history and checkpoint. -/
theorem recoverWriteCutAfterReopenRetry {initial after : ReopenImage}
    {pair : DirectoryPublication.Bindings} {walBinding : Option ByteArray} {files : List ByteArray}
    {checkpoint : PackedTable} {model : Sequential.SnapshotTable UInt64}
    {covered pending : List WAL.Write} {event : WAL.Write}
    (path : ReopenRetry initial after)
    (metadataChosen : pair ∈ after.directory.active :: after.directory.crashImages)
    (walChosen : walBinding ∈ after.wal.active :: after.wal.crashImages)
    (hasCrash : initial.wal.crashImages ≠ [])
    (fits : (WAL.encode ((covered ++ pending) ++ [event])).size < UInt64.size)
    (physical : ∀ binding ∈ initial.wal.active :: initial.wal.crashImages,
      ∃ contents markerImage, binding = some contents ∧ WriteCut (covered ++ pending) event contents markerImage ∧
        markerImage.active = initial.directory.active.walBoundary ∧
        ∀ pair ∈ initial.directory.crashImages, pair.walBoundary ∈ markerImage.crashImages)
    (written : ∀ pair ∈ initial.directory.active :: initial.directory.crashImages,
      CheckpointForRecovery pair.manifest files checkpoint)
    (represents : checkpoint.Refines model)
    (ordered : WAL.OrdinalsFrom 1 ((covered ++ pending) ++ [event]))
    (watermark : covered.length = checkpoint.committed.toNat) :
    ∃ marker contents events base reopened abstract,
      pair.walBoundary = some marker ∧ marker = encode (WAL.encode events).size.toUInt64 ∧
      walBinding = some contents ∧
      (match pair.manifest with
      | none => Except.ok PackedTable.empty
      | some bytes => do
        let header ← Manifest.decode bytes
        loadRunSet header files) = .ok base ∧
      (do let count ← decode marker; select count contents) = .ok (WAL.encode events) ∧
      recoverSelected base (WAL.encode events) = .ok reopened ∧
      (events = covered ++ pending ∨ events = (covered ++ pending) ++ [event]) ∧
      reopened.committed.toNat = events.length ∧
      SnapshotWalReplay model (events.drop covered.length) abstract ∧
      abstract.committed.toNat = events.length ∧
      ∀ snapshot : UInt64, abstract.pins.floor ≤ snapshot → snapshot.toNat ≤ events.length →
        ∃ pin pinned, reopened.acquireAt snapshot = some (pin, pinned) ∧
          (∀ key, pinned.lookup pin.handle key = some (abstract.table.lookup key snapshot)) ∧
          (∀ start stop, pinned.range pin.handle start stop =
            some (abstract.table.range start stop snapshot)) := by
  have initialChosen := path.chosen_pair_from_initial metadataChosen
  have valid := ReopenImage.valid_of_writeCut hasCrash fits physical
  obtain ⟨initialContents, markerImage, present, cut, visible, candidates⟩ :=
    physical initial.wal.active (List.mem_cons_self ..)
  have oldFits := Nat.lt_trans (encoded_history_grows (covered ++ pending) event) fits
  obtain ⟨initialMarker, events, base, reopened, _, initialBound, markerEncoding, loaded, selected, recovered,
    history, sequence, _, _, abstractReplay⟩ :=
    recoverWriteCutSelectedPair (written pair initialChosen) cut
      (marker_chosen_of_pair initialChosen visible candidates) oldFits fits ordered watermark
  obtain ⟨markerBytes, walBytes, length, sameMarker, sameWal, decoded, accepted⟩ :=
    valid.activeValid pair initialChosen
  have markerMatches := Option.some.inj (sameMarker.symm.trans initialBound)
  have walMatches := Option.some.inj (sameWal.symm.trans present)
  subst markerBytes
  subst walBytes
  have expected : writeCutPrefix (covered ++ pending) event pair = WAL.encode events := by
    rw [decoded] at selected
    exact Except.ok.inj (accepted.symm.trans selected)
  obtain ⟨marker, contents, bound, present, selectedAfter⟩ :=
    ReopenImage.select_chosen (reopenRetry_valid valid path) metadataChosen walChosen
  obtain ⟨abstract, replayed, counted, reads⟩ := abstractReplay model represents
  rw [expected] at selectedAfter
  have encoding := (Option.some.inj (bound.symm.trans initialBound)).trans markerEncoding
  exact ⟨marker, contents, events, base, reopened, abstract, bound, encoding, present, loaded, selectedAfter,
    recovered, history, sequence, replayed, counted, reads⟩

end Alvoki.WAL.Boundary
