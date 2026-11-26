import Alvoki.Storage.Disk.NativeQuietPowerLossTableOpen
import Alvoki.Storage.Disk.NativeRawManifestStatError
import Alvoki.Storage.Disk.NativeRawCheckpointChunkError
import Alvoki.Storage.Disk.NativeOpenAdmissionStorage
import Alvoki.Storage.Disk.NativeMutatingOpenRetries

namespace Alvoki.Storage.DiskSession

open System WalSegmentRepair SyncHandleRouting

private def observedFiles {heap : Type} (names : heap → FilePath → Option Nat)
    (bytes : heap → Nat → ByteArray) (atHeap : heap) : CheckpointSurvivingFiles :=
  ⟨names atHeap, fun inode => [bytes atHeap inode]⟩

section SelectedReadFiles

variable {heap : Type} {files : heap → CheckpointSurvivingFiles} {selectedPath : FilePath → Prop}

private theorem frameRefl (atHeap : heap) : (files atHeap).Frames selectedPath (files atHeap) :=
  fun _ _ => ⟨rfl, fun _ _ => rfl⟩

/-- Scope effects on the selected paths and their bound inode bytes. -/
abbrev MarkedTemporaryReadCalls.FileFrames (calls : MarkedTemporaryReadCalls heap)
    (files : heap → CheckpointSurvivingFiles) (selectedPath : FilePath → Prop) :=
  calls.ScopeFrames (fun before after => (files before).Frames selectedPath (files after))

/-- The actual ordered checkpoint run loop restores exactly the bytes
from the selected publication. The initial live footprint is transported
through the reached stat, open, chunk, and release of each run. -/
theorem MarkedTemporaryReadCalls.restoresSelectedRunBytes (calls : MarkedTemporaryReadCalls heap)
    (view : OpenCloseHeapView heap image) (names : heap → FilePath → Option Nat)
    (visible : heap → Nat → ByteArray) (directory : DiskDirectory)
    (opens : calls.OpensReadSlot view names visible) (reads : calls.ReadsAtCursor view visible)
    {durable : CheckpointPublication.RunFiles} {manifest : Manifest.IntegrityCheckpoint}
    (scope : FilePath → Prop)
    (inScope : ∀ index < manifest.header.runCount.toNat,
      scope (directory.file (.run manifest.header.generation index)))
    {initial entry reached : heap} {bytes : List ByteArray}
    (stored : ∀ index < manifest.header.runCount.toNat, ∃ payload,
      durable manifest.header.generation index = some payload ∧
      (observedFiles names visible initial).Stored (directory.file (.run manifest.header.generation index)) payload)
    (starts : (observedFiles names visible initial).Frames scope (observedFiles names visible entry))
    (sized : ∀ {path before size after}, calls.runSize path before = .ok size after →
      (observedFiles names visible before).Frames scope (observedFiles names visible after) ∧
      ∀ inode, names before path = some inode → size = (visible before inode).size)
    (scopedReads : calls.FileFrames (observedFiles names visible) scope)
    (returned : readIntegrityRunBytesSized directory manifest calls.runSize calls.runPrefix entry = .ok bytes reached) :
    (List.range manifest.header.runCount.toNat).mapM (durable manifest.header.generation) = some bytes ∧
      (observedFiles names visible initial).Frames scope (observedFiles names visible reached) := by
  apply readIntegrityRunBytesSized_refinesSuccess directory calls.runSize calls.runPrefix _ ?_ starts returned
  intro index within stamp _ before after got held receipt
  let path := directory.file (.run manifest.header.generation index)
  have admitted : scope path := inScope index within
  cases receipt with
  | @accepted afterSize _ _ measured fits readPayload size =>
    have sizeFrame := (sized measured).1
    obtain ⟨_, _, inode, _, _, _, bound, _, _, _, same, _⟩ :=
      calls.readSelectedRun view names visible opens reads path stamp.byteCount.toNat
        (fun ret => by
          obtain ⟨framed, extent⟩ := sized ret
          obtain ⟨nameSame, bytesSame⟩ := framed path admitted
          exact ⟨nameSame, fun found named =>
            ⟨extent found named, (List.cons.inj (bytesSame found named)).1⟩⟩)
        (.accepted measured fits readPayload size)
    obtain ⟨payload, durableBytes, origin, nameAtStart, exactAtStart⟩ := stored index within
    obtain ⟨nameAtRead, contentsAtRead⟩ := held path admitted
    have sameInode : origin = inode := Option.some.inj ((nameAtRead.trans nameAtStart).symm.trans bound)
    subst origin
    have live := (List.cons.inj ((contentsAtRead inode nameAtStart).trans exactAtStart)).1
    change calls.runPrefix path stamp.byteCount.toNat afterSize = .ok got after at readPayload
    have returnedFrame := calls.runPrefixFrames scopedReads
      (fun heap => frameRefl (files := observedFiles names visible) (selectedPath := scope) heap)
      CheckpointSurvivingFiles.Frames.trans path stamp.byteCount.toNat afterSize
    have prefixFrame : (observedFiles names visible afterSize).Frames scope (observedFiles names visible after) := by
      simpa only [readPayload, reachedState] using returnedFrame
    exact ⟨durableBytes.trans (congrArg some (same.trans live).symm), held.trans (sizeFrame.trans prefixFrame)⟩

/-- Derive the checkpoint selection for the actual result of the sized
reader. Only the manifest observation crosses the optional-read boundary.
Run identity and bytes follow from the local read effects and the
immutable files of the selected publication. -/
theorem MarkedTemporaryReadCalls.selectedCheckpointOfReturn (calls : MarkedTemporaryReadCalls heap)
    (view : OpenCloseHeapView heap image) (names : heap → FilePath → Option Nat)
    (visible : heap → Nat → ByteArray) (directory : DiskDirectory)
    (opens : calls.OpensReadSlot view names visible) (reads : calls.ReadsAtCursor view visible)
    {durable : CheckpointPublication.RunFiles} {binding : Option ByteArray}
    {actual : Option (PackedTable × UInt64)}
    (scope : FilePath → Prop) {initial entry reached : heap}
    (inScope : ∀ raw manifest, binding = some raw → Manifest.IntegrityCheckpoint.decode raw = .ok manifest →
      ∀ index < manifest.header.runCount.toNat, scope (directory.file (.run manifest.header.generation index)))
    (stored : ∀ raw manifest, binding = some raw → Manifest.IntegrityCheckpoint.decode raw = .ok manifest →
      ∀ index < manifest.header.runCount.toNat, ∃ payload,
      durable manifest.header.generation index = some payload ∧
      (observedFiles names visible initial).Stored (directory.file (.run manifest.header.generation index)) payload)
    (manifestAbsent : ∀ {after}, calls.readOptional directory (directory.file .manifest) entry = .ok none after →
      binding = none ∧ (observedFiles names visible initial).Frames scope (observedFiles names visible after))
    (manifestPresent : ∀ {raw manifest after},
      calls.readOptional directory (directory.file .manifest) entry = .ok (some raw) after →
      Manifest.IntegrityCheckpoint.decode raw = .ok manifest →
      binding = some raw ∧ (observedFiles names visible initial).Frames scope (observedFiles names visible after))
    (sized : ∀ {path before size after}, calls.runSize path before = .ok size after →
      (observedFiles names visible before).Frames scope (observedFiles names visible after) ∧
      ∀ inode, names before path = some inode → size = (visible before inode).size)
    (scopedReads : calls.FileFrames (observedFiles names visible) scope)
    (returned : readIntegrityCheckpointSized directory (calls.readOptional directory (directory.file .manifest))
      calls.runSize calls.runPrefix entry = .ok actual reached) :
    SelectedIntegrityCheckpoint durable binding actual ∧
      (observedFiles names visible initial).Frames scope (observedFiles names visible reached) := by
  have outcome := SizedCheckpointReadReturn.classifies directory
    (calls.readOptional directory (directory.file .manifest)) calls.runSize calls.runPrefix entry
  rw [returned] at outcome
  cases outcome with
  | absent seen =>
    obtain ⟨rfl, frame⟩ := manifestAbsent seen
    exact ⟨.absent, frame⟩
  | restored seen decoded runs loaded =>
    obtain ⟨rfl, frame⟩ := manifestPresent seen decoded
    obtain ⟨storedList, finalFrame⟩ := calls.restoresSelectedRunBytes view names visible directory opens reads
      scope (inScope _ _ rfl decoded) (stored _ _ rfl decoded) frame sized scopedReads runs
    exact ⟨.present decoded storedList loaded, finalFrame⟩

private theorem MarkedTemporaryReadCalls.runSize_stat (calls : MarkedTemporaryReadCalls heap)
    (path : FilePath) {entry reached : heap} {size : Nat}
    (returned : calls.runSize path entry = .ok size reached) :
    ∃ metadata, calls.stat path entry = .ok (.ok metadata) reached ∧ metadata.byteSize.toNat = size := by
  simp only [MarkedTemporaryReadCalls.runSize, Bind.bind, EStateM.bind] at returned
  cases raw : calls.stat path entry with
  | error error after => simp [raw] at returned
  | ok outcome after =>
    cases outcome with
    | error error => simp [raw, liftExcept, throw, throwThe, MonadExceptOf.throw, EStateM.throw] at returned
    | ok metadata =>
      simp only [raw, liftExcept, Pure.pure, EStateM.pure] at returned
      split at returned
      · have exact := EStateM.Result.ok.inj returned
        obtain ⟨rfl, rfl⟩ := exact
        exact ⟨metadata, rfl, rfl⟩
      · simp [throw, throwThe, MonadExceptOf.throw, EStateM.throw, EStateM.bind] at returned

/-- Carry an independent local frame through the actual successful
checkpoint read. The manifest selects the run traversal. Each measured
extent and bounded prefix supplies the next heap in that traversal. -/
theorem MarkedTemporaryReadCalls.framesCheckpointSuccess
    (calls : MarkedTemporaryReadCalls heap) (directory : DiskDirectory)
    {frame : heap → heap → Prop} (refl : ∀ atHeap, frame atHeap atHeap)
    (trans : ∀ {before middle after}, frame before middle → frame middle after → frame before after)
    (reads : calls.ScopeFrames frame)
    (stat : ∀ path before, frame before (reachedState (calls.stat path before)))
    {entry reached : heap} {checkpoint : Option (PackedTable × UInt64)}
    (returned : readIntegrityCheckpointSized directory (calls.readOptional directory (directory.file .manifest))
      calls.runSize calls.runPrefix entry = .ok checkpoint reached) : frame entry reached := by
  have outcome := SizedCheckpointReadReturn.classifies directory
    (calls.readOptional directory (directory.file .manifest)) calls.runSize calls.runPrefix entry
  rw [returned] at outcome
  have manifestFrame := calls.readOptionalFrames reads refl trans stat directory (directory.file .manifest) entry
  cases outcome with
  | absent read =>
    simpa only [read, reachedState] using manifestFrame
  | @restored raw manifest files table afterManifest _ read decoded runs loaded =>
    have first : frame entry afterManifest := by simpa only [read, reachedState] using manifestFrame
    have step (index : Nat) (_ : index < manifest.header.runCount.toNat) (stamp : Manifest.RunIntegrity)
        (_ : manifest.runs[index]? = some stamp) {before after : heap} {payload : ByteArray}
        (held : frame entry before)
        (receipt : ExactRecoveryFileReturn (directory.file (.run manifest.header.generation index))
          stamp.byteCount.toNat (IO.userError checkpointIntegrityMismatch) calls.runSize calls.runPrefix before
          (.ok payload after)) : True ∧ frame entry after := by
      let path := directory.file (.run manifest.header.generation index)
      cases receipt with
      | @accepted afterSize _ _ measured _ prefixRead _ =>
        obtain ⟨_, sized, _⟩ := calls.runSize_stat path measured
        have sizeFrame : frame before afterSize := by
          simpa only [sized, reachedState] using stat path before
        change calls.runPrefix path stamp.byteCount.toNat afterSize = .ok payload after at prefixRead
        have prefixFrame : frame afterSize after := by
          simpa only [prefixRead, reachedState] using
            calls.runPrefixFrames reads refl trans path stamp.byteCount.toNat afterSize
        exact ⟨trivial, trans held (trans sizeFrame prefixFrame)⟩
    exact (readIntegrityRunBytesSized_inductSuccess directory calls.runSize calls.runPrefix
      (outputsMatch := fun _ _ => True) trivial (fun _ _ => trivial) step first runs).2

/-- The current open restores the checkpoint from the protected files,
using the actual optional metadata result and each reached run callback.
The file frame includes the live manifest and runs at the selected
retry entry, and permits independent changes to other paths. -/
theorem MarkedTemporaryReadCalls.selectedCheckpointOfProtectedReturn
    (calls : MarkedTemporaryReadCalls heap) (state : NativeReadyState)
    (view : OpenCloseHeapView heap image) (names : heap → FilePath → Option Nat)
    (visible : heap → Nat → ByteArray)
    (opens : calls.OpensReadSlot view names visible) (reads : calls.ReadsAtCursor view visible)
    {initial entry reached : heap} {expected actual : Option (PackedTable × UInt64)}
    (selected : SelectedIntegrityCheckpoint state.writer.published.durable state.writer.target.pair.manifest expected)
    (footprint : NativeReadyProtectedStorage state (observedFiles names visible initial))
    (scope : FilePath → Prop)
    (includes : ∀ path, state.writeFramePath path → scope path)
    (starts : (observedFiles names visible initial).Frames scope (observedFiles names visible entry))
    (scopedReads : calls.FileFrames (observedFiles names visible) scope)
    (statFrame : ∀ path before, (observedFiles names visible before).Frames scope
      (observedFiles names visible (reachedState (calls.stat path before))))
    (statExtent : ∀ {path before metadata after inode}, calls.stat path before = .ok (.ok metadata) after →
      names before path = some inode → metadata.byteSize.toNat = (visible before inode).size)
    (statMissing : ∀ {path before name message after},
      calls.stat path before = .ok (.error (.noFileOrDirectory name 2 message)) after →
      names before path = none)
    (returned : readIntegrityCheckpointSized state.session.directory
      (calls.readOptional state.session.directory (state.session.directory.file .manifest))
      calls.runSize calls.runPrefix entry = .ok actual reached) :
    SelectedIntegrityCheckpoint state.writer.published.durable state.writer.target.pair.manifest actual ∧
      (observedFiles names visible initial).Frames scope (observedFiles names visible reached) := by
  let directory := state.session.directory
  let path := directory.file .manifest
  have manifestPath : scope path := includes path (.inr (.inr (.inl rfl)))
  have manifestFrame {found : Option ByteArray} {after : heap}
      (seen : calls.readOptional directory path entry = .ok found after) :
      (observedFiles names visible initial).Frames scope (observedFiles names visible after) := by
    have kept := calls.readOptionalFrames scopedReads
      (fun heap => frameRefl (files := observedFiles names visible) (selectedPath := scope) heap)
      CheckpointSurvivingFiles.Frames.trans statFrame directory path entry
    exact starts.trans (by simpa only [seen, reachedState] using kept)
  have sized {path before size after} (result : calls.runSize path before = .ok size after) :
      (observedFiles names visible before).Frames scope (observedFiles names visible after) ∧
      ∀ inode, names before path = some inode → size = (visible before inode).size := by
    obtain ⟨metadata, returnedStat, extent⟩ := calls.runSize_stat path result
    have frame := statFrame path before
    rw [returnedStat, reachedState] at frame
    exact ⟨frame, fun inode named => extent.symm.trans (statExtent returnedStat named)⟩
  apply calls.selectedCheckpointOfReturn view names visible directory opens reads scope
    ?_ ?_ ?_ ?_ sized scopedReads returned
  · intro raw manifest present decoded index within
    exact includes _ (.inr (.inr (.inr (.inr ⟨raw, manifest, index, present, decoded, within, rfl⟩))))
  · intro raw manifest present decoded index within
    have visit : index < selectedRunCount state.writer.target.pair.manifest := by
      simpa [selectedRunCount, present, decoded, Except.toOption] using within
    obtain ⟨otherRaw, otherManifest, payload, rawEq, manifestEq, _, stored⟩ := selected.selectedRun visit
    cases Option.some.inj (rawEq.symm.trans present)
    cases Except.ok.inj (manifestEq.symm.trans decoded)
    exact ⟨payload, stored, footprint.runs _ _ present decoded index within payload stored⟩
  · intro after seen
    obtain ⟨name, message, stat⟩ := calls.readOptional_none directory path seen
    have missing : names entry path = none := statMissing stat
    have absent := (starts path manifestPath).1.symm.trans missing
    refine ⟨?_, manifestFrame seen⟩
    cases binding : state.writer.target.pair.manifest with
    | none => rfl
    | some payload =>
      have current := footprint.manifest
      rw [binding] at current
      obtain ⟨inode, named, _⟩ := current
      rw [absent] at named
      contradiction
  · intro raw manifest after seen accepted
    have preservesStat {metadata afterStat}
        (measured : calls.stat path entry = .ok (.ok metadata) afterStat) :
        names afterStat path = names entry path ∧
        ∀ inode, names entry path = some inode →
          metadata.byteSize.toNat = (visible entry inode).size ∧ visible afterStat inode = visible entry inode := by
      have frame := statFrame path entry
      rw [measured, reachedState] at frame
      obtain ⟨sameName, sameContents⟩ := frame path manifestPath
      exact ⟨sameName, fun inode named => ⟨statExtent measured named, (List.cons.inj (sameContents inode named)).1⟩⟩
    obtain ⟨_, _, inode, _, _, _, bound, _, _, exactBytes, _⟩ :=
      calls.readSelectedManifest view names visible opens reads directory preservesStat seen accepted
    obtain ⟨nameEq, contents⟩ := starts path manifestPath
    have origin : names initial path = some inode := nameEq.symm.trans bound
    refine ⟨?_, manifestFrame seen⟩
    cases binding : state.writer.target.pair.manifest with
    | none =>
      have absent := footprint.manifest
      rw [binding] at absent
      change names initial path = none at absent
      rw [absent] at origin
      contradiction
    | some payload =>
      have current := footprint.manifest
      rw [binding] at current
      obtain ⟨expectedInode, named, stored⟩ := current
      have sameInode : expectedInode = inode := Option.some.inj (named.symm.trans origin)
      subst expectedInode
      have agrees := (List.cons.inj ((contents inode origin).trans stored)).1
      exact congrArg some (exactBytes.trans agrees).symm

end SelectedReadFiles

section ActualMarkedSelection

variable {heap : Type} {frame : heap → heap → Prop}

private theorem optionalMetadata_success_frames
    (lookup : EStateM IO.Error heap (Except IO.Error IO.FS.Metadata))
    {before after : heap} {metadata : Option IO.FS.Metadata}
    (keeps : frame before (reachedState (lookup before)))
    (returned : optionalMetadataWith lookup before = .ok metadata after) : frame before after := by
  simp only [optionalMetadataWith, Bind.bind, EStateM.bind] at returned
  cases observed : lookup before with
  | error cause reached => simp [observed] at returned
  | ok result reached =>
    have actual : frame before reached := by simpa only [observed, reachedState] using keeps
    simp only [observed] at returned
    cases result with
    | ok stat =>
      simp only [Pure.pure, EStateM.pure, EStateM.Result.ok.injEq] at returned
      exact returned.2 ▸ actual
    | error cause =>
      cases cause <;> simp [throw, throwThe, MonadExceptOf.throw, EStateM.throw] at returned
      rename_i name code message
      by_cases missing : code = 2
      · simp [missing, Pure.pure, EStateM.pure] at returned
        exact returned.2 ▸ actual
      · simp [missing, EStateM.throw] at returned

private theorem flatGuard_passed_frames (directory : DiskDirectory)
    (lookup : EStateM IO.Error heap (Except IO.Error IO.FS.Metadata))
    {before after : heap} (keeps : frame before (reachedState (lookup before)))
    (returned : rejectFlatWalWith directory (optionalMetadataWith lookup) before = .ok () after) :
    frame before after := by
  simp only [rejectFlatWalWith, Bind.bind, EStateM.bind] at returned
  cases tested : optionalMetadataWith lookup before with
  | error cause reached => simp [tested] at returned
  | ok metadata reached =>
    have known := optionalMetadata_success_frames lookup keeps tested
    cases metadata with
    | none =>
      simp [tested, Pure.pure, EStateM.pure] at returned
      exact returned ▸ known
    | some _ =>
      simp [tested, throw, throwThe, MonadExceptOf.throw, EStateM.throw] at returned

/-- The two marked-open guards compose only the frames of their reached
lookup calls. An ordinary missing legacy WAL still follows its stat. -/
theorem markedGuards_keepFrame (directory : DiskDirectory)
    (lookup : FilePath → EStateM IO.Error heap (Except IO.Error IO.FS.Metadata))
    (trans : ∀ {before middle reached}, frame before middle → frame middle reached → frame before reached)
    (keeps : ∀ path before, frame before (reachedState (lookup path before)))
    {entry checked marked : heap} {metadata : IO.FS.Metadata}
    (flat : rejectFlatWalWith directory (optionalMetadataWith (lookup (directory.file .wal))) entry = .ok () checked)
    (marker : optionalMetadataWith (lookup (directory.file .walBoundary)) checked = .ok (some metadata) marked) :
    frame entry marked :=
  trans (flatGuard_passed_frames directory _ (keeps (directory.file .wal) entry) flat)
    (optionalMetadata_success_frames _ (keeps (directory.file .walBoundary) checked) marker)

/-- The accepted marker used by the bounded production reader belongs to
the reached namespace of this retry. Framing the chosen live bytes to the
marker read identifies the byte count for the subsequent WAL selector. -/
theorem MarkedTemporaryReadCalls.acceptsMarkerFromProtectedFile
    {image : Type} (calls : MarkedTemporaryReadCalls heap) (view : OpenCloseHeapView heap image)
    (names : heap → FilePath → Option Nat) (visible : heap → Nat → ByteArray)
    (opens : calls.OpensReadSlot view names visible) (reads : calls.ReadsAtCursor view visible)
    (directory : DiskDirectory) (scope : FilePath → Prop)
    (inScope : scope (directory.file .walBoundary))
    {initial entry reached : heap} {marker observed : ByteArray} {length : UInt64}
    (stored : (observedFiles names visible initial).Stored (directory.file .walBoundary) marker)
    (starts : (observedFiles names visible initial).Frames scope (observedFiles names visible entry))
    (scopedReads : calls.FileFrames (observedFiles names visible) scope)
    (statFrame : ∀ path before, (observedFiles names visible before).Frames scope
      (observedFiles names visible (reachedState (calls.stat path before))))
    (eof : ∀ file slot inode (request : USize) before after,
      attachedReadSlot view file slot inode before → 0 < request.toNat →
      calls.readChunk file request before = .ok .empty after →
      (visible before inode).size ≤ (view.handle before file).2.2)
    (returned : calls.readOptional directory (directory.file .walBoundary) entry = .ok (some observed) reached)
    (decoded : WAL.Boundary.decode observed = .ok length) :
    observed = marker ∧
      (observedFiles names visible initial).Frames scope (observedFiles names visible reached) := by
  let path := directory.file .walBoundary
  have atStat {metadata after}
      (stat : calls.stat path entry = .ok (.ok metadata) after) :
      names after path = names entry path ∧
      ∀ inode, names entry path = some inode → visible after inode = visible entry inode := by
    have kept := statFrame path entry
    rw [stat, reachedState] at kept
    obtain ⟨nameEq, contents⟩ := kept path inScope
    exact ⟨nameEq, fun inode name => (List.cons.inj (contents inode name)).1⟩
  obtain ⟨_, _, inode, _, _, _, actualName, _, _, actualBytes, _⟩ :=
    calls.readSelectedMarker view names visible opens reads directory atStat eof returned decoded
  obtain ⟨nameEq, bytesEq⟩ := starts path inScope
  obtain ⟨savedInode, named, payload⟩ := stored
  have sameInode : savedInode = inode := Option.some.inj (named.symm.trans (nameEq.symm.trans actualName))
  subst savedInode
  have bytes := (List.cons.inj ((bytesEq inode named).trans payload)).1
  change calls.readOptional directory path entry = .ok (some observed) reached at returned
  have resultFrame := calls.readOptionalFrames scopedReads
    (fun atHeap _ _ => ⟨rfl, fun _ _ => rfl⟩) CheckpointSurvivingFiles.Frames.trans statFrame directory path entry
  exact ⟨actualBytes.trans bytes, starts.trans (by simpa only [returned, reachedState] using resultFrame)⟩

/-- Consume the literal successful marked open. Its protected manifest
and WAL marker fix the checkpoint and the exact byte limit passed to the
reached WAL reader. The frames are local to the actual admission,
guards, checkpoint calls and marker read. -/
theorem RawOpenAdmissionReport.selectsCheckpointAndMarkerFromActualOpen
    {stream : Type} {state : NativeReadyState} {input : FilePath} {inventory : DescriptorInventory}
    {retry : LockedFileState FileImage}
    {admission : CensusOpenAdmissionReports input state.session.directory inventory retry}
    {view : OpenCloseHeapView heap FileImage} {entry : heap}
    (source : RawMarkedOpenInterpreter heap stream)
    (raw : RawOpenAdmissionReport admission view source.calls entry)
    (seed : OpenSyncCacheAllocations admission.opened view source.init raw.afterFlock)
    (names : heap → FilePath → Option Nat) (visible : heap → Nat → ByteArray)
    (opens : source.fileCalls.OpensReadSlot view names visible)
    (reads : source.fileCalls.ReadsAtCursor view visible)
    {expected : Option (PackedTable × UInt64)} {chosenMarker : ByteArray}
    (selection : SelectedIntegrityCheckpoint state.writer.published.durable state.writer.target.pair.manifest expected)
    (footprint : NativeReadyProtectedStorage state (observedFiles names visible entry))
    (storedMarker : (observedFiles names visible entry).Stored (state.session.directory.file .walBoundary) chosenMarker)
    (scope : FilePath → Prop)
    (includes : ∀ path, state.selectedRetryPath path → scope path)
    (admissionEffects : raw.CacheFrames seed (fun before after =>
      (observedFiles names visible before).Frames scope (observedFiles names visible after)))
    (guardFrame : ∀ path before, (observedFiles names visible before).Frames scope
      (observedFiles names visible (reachedState (source.calls.lookup path before))))
    (scopedReads : source.fileCalls.FileFrames (observedFiles names visible) scope)
    (statFrame : ∀ path before, (observedFiles names visible before).Frames scope
      (observedFiles names visible (reachedState (source.fileCalls.stat path before))))
    (statExtent : ∀ {path before metadata after inode}, source.fileCalls.stat path before = .ok (.ok metadata) after →
      names before path = some inode → metadata.byteSize.toNat = (visible before inode).size)
    (statMissing : ∀ {path before name message after},
      source.fileCalls.stat path before = .ok (.error (.noFileOrDirectory name 2 message)) after →
      names before path = none)
    (eof : ∀ file slot inode (request : USize) before after,
      attachedReadSlot view file slot inode before → 0 < request.toNat →
      source.fileCalls.readChunk file request before = .ok .empty after →
      (visible before inode).size ≤ (view.handle before file).2.2)
    {checked marked reached : heap} {metadata : IO.FS.Metadata} {table : DiskTable}
    (flat : rejectFlatWalWith state.session.directory
      (optionalMetadataWith (source.calls.lookup (state.session.directory.file .wal))) seed.afterPending = .ok () checked)
    (marker : optionalMetadataWith (source.calls.lookup (state.session.directory.file .walBoundary)) checked =
      .ok (some metadata) marked)
    (returned : source.openTable input entry = .ok table reached) :
    let directory := state.session.directory
    let keeper := source.keeperCallbacks.withFileReads source.fileCalls
    let readWal := fun watermark length => readSelectedWithCachedExtents directory watermark length
      source.directoryCalls.run (MarkedWalExtentReports.inspect source.fileCalls) source.fileCalls.seal
      (source.fileCalls.readKeeperWithRelease
        (fun path handle => keeper.modifyPending seed.pendingRef (SyncHandleRouting.pushPending path handle)))
    let cache := RawMarkedOpenInterpreter.makeCache directory seed.directoryRef seed.activeRef seed.pendingRef
    let writeStage := source.stage.stage seed.pendingRef keeper.modifyPending
    let syncPaths := keeper.syncPaths directory.path seed.directoryRef seed.activeRef seed.pendingRef
    ∃ (afterCheckpoint afterMarker : heap) (length : UInt64) (payloads : WalSegmentMarkerReads)
      (extent : Nat) (prepared repaired : heap) (patched : ByteArray) (logical : PackedTable)
      (first : Nat) (bytes : ByteArray) (phase : IO.Ref (Phase Installed)) (afterPhase : heap)
      (token : IO.Ref Unit),
      readIntegrityCheckpointSized directory (source.fileCalls.readOptional directory (directory.file .manifest))
        source.fileCalls.runSize source.fileCalls.runPrefix marked = .ok expected afterCheckpoint ∧
      source.fileCalls.readOptional directory (directory.file .walBoundary) afterCheckpoint =
        .ok (some chosenMarker) afterMarker ∧
      WAL.Boundary.decode chosenMarker = .ok length ∧
      readWal ((expected.getD (.empty, 0)).1.committed.toNat) length afterMarker = .ok (payloads, extent) prepared ∧
      (observedFiles names visible entry).Frames scope (observedFiles names visible afterMarker) ∧
      recoverMarkedWalSegments (expected.getD (.empty, 0)).1 length payloads.files = .ok (patched, logical) ∧
      payloads.files.getLast? = some (first, bytes) ∧
      finishBoundedMarkedOpen directory ⟨length.toNat / WAL.frameSize, first, payloads.newer, bytes⟩ extent
        source.remove writeStage syncPaths source.rename prepared = .ok () repaired ∧
      source.allocatePhase (.ready (Reopened.installed ⟨logical, (expected.getD (.empty, 0)).2, length, first⟩))
        repaired = .ok phase afterPhase ∧
      source.allocateToken () afterPhase = .ok token reached ∧
      table = RawMarkedOpenInterpreter.assemble directory raw.lock cache phase token := by
  intro directory keeper readWal cache writeStage syncPaths
  obtain ⟨checkpoint, afterCheckpoint, markerBytes, afterMarker, length, payloads, extent, prepared, repaired,
    patched, logical, first, bytes, phase, afterPhase, token, selected, markerRead, decoded, walRead,
    replayed, lastKeeper, repairedWal, allocated, tokenAllocated, exactTable⟩ :=
    raw.reachesMarkedReadsAndRepair source seed flat marker returned
  let frame (before after : heap) :=
    (observedFiles names visible before).Frames scope (observedFiles names visible after)
  have admissionFrame : frame entry seed.afterPending :=
    raw.framesThroughCache seed (frame := frame) CheckpointSurvivingFiles.Frames.trans admissionEffects
  have guardSteps := markedGuards_keepFrame (frame := frame) directory source.calls.lookup
    CheckpointSurvivingFiles.Frames.trans guardFrame flat marker
  have markedFrame := admissionFrame.trans guardSteps
  obtain ⟨actual, checkpointFrame⟩ := source.fileCalls.selectedCheckpointOfProtectedReturn state view names visible
    opens reads selection footprint scope (fun path member => includes path (.inr member)) markedFrame scopedReads statFrame statExtent statMissing selected
  obtain ⟨markerEq, finalFrame⟩ := source.fileCalls.acceptsMarkerFromProtectedFile view names visible opens reads
    directory scope (includes _ (.inl rfl)) storedMarker checkpointFrame scopedReads statFrame eof markerRead decoded
  have checkpointEq := actual.uniqueResult selection
  exact ⟨afterCheckpoint, afterMarker, length, payloads, extent, prepared, repaired, patched, logical, first,
    bytes, phase, afterPhase, token, by simpa only [checkpointEq] using selected, by simpa only [markerEq] using markerRead,
    by simpa only [markerEq] using decoded, by simpa only [checkpointEq] using walRead, finalFrame,
    by simpa only [checkpointEq] using replayed, lastKeeper, repairedWal,
    by simpa only [checkpointEq] using allocated, tokenAllocated, exactTable⟩

end ActualMarkedSelection

section ReachedSelectedFiles

variable {heap : Type} {input : FilePath} {directory : DiskDirectory} {inventory : DescriptorInventory}
  {retry : LockedFileState FileImage} {admission : CensusOpenAdmissionReports input directory inventory retry}
  {view : OpenCloseHeapView heap FileImage} {init : OpenSyncCacheCallbacks heap}
  {calls : RawOpenAdmissionCallbacks heap} {entry : heap}
  {admitted : RawOpenAdmissionReport admission view calls entry}
  {seed : OpenSyncCacheAllocations admission.opened view init admitted.afterFlock}
  {fileCalls : MarkedTemporaryReadCalls heap}
  {files : heap → CheckpointSurvivingFiles} {selectedPath : FilePath → Prop}

/-- Follow the manifest and each earlier bounded run read, including
their temporary releases. No raw namespace sample is reselected. -/
theorem RawCheckpointRunPrefix.preservesSelectedFiles {stop : Manifest.IntegrityCheckpoint → Nat}
    (seen : RawCheckpointRunPrefix (admitted := admitted) seed fileCalls stop)
    (laws : fileCalls.FileFrames files selectedPath)
    {index : Nat} (within : index ≤ stop seen.manifest) :
    (files seed.afterPending).Frames selectedPath (files (seen.atRun index)) := by
  induction index with
  | zero =>
    have frame := fileCalls.readWithFrames laws CheckpointSurvivingFiles.Frames.trans (directory.file .manifest)
      (fun file => readIntegrityManifestPrefixWith (fileCalls.readChunk file) seen.file.calls.metadata.byteSize.toNat)
      (fun temporary file chunks => manifestReadFrames (frame := GuardedReadFrame
        (fun before after => (files before).Frames selectedPath (files after)) temporary file)
        (GuardedReadFrame.refl (frame := fun before after => (files before).Frames selectedPath (files after))
          frameRefl file) (GuardedReadFrame.trans (frame := fun before after => (files before).Frames selectedPath (files after))
          CheckpointSurvivingFiles.Frames.trans)
        (fileCalls.readChunk file) chunks seen.file.calls.metadata.byteSize.toNat) seed.afterPending
    simpa only [seen.manifestRead.returns.1, reachedState] using frame
  | succ index prior =>
    have inside := Nat.lt_of_succ_le within
    let path := directory.file (.run seen.manifest.header.generation index)
    have kept := fileCalls.runPrefixFrames laws frameRefl CheckpointSurvivingFiles.Frames.trans
      path (seen.run index inside).stamp.byteCount.toNat (seen.atRun index)
    have read := (seen.readsRun inside).2.1
    rw [read] at kept
    exact (prior (Nat.le_of_lt inside)).trans kept

/-- A short chunk followed by the read error keeps the exact selected
objects through the temporary handle's scope drop. -/
theorem RawCheckpointChunkReadError.preservesSelectedFiles
    {selected : RawSelectedCheckpointRunStat (admitted := admitted) seed fileCalls}
    (seen : RawCheckpointChunkReadError selected) (laws : fileCalls.FileFrames files selectedPath) :
    (files seed.afterPending).Frames selectedPath (files seen.reached) := by
  have earlier := selected.reads.preservesSelectedFiles laws (Nat.le_refl selected.index)
  have later := fileCalls.runPrefixFrames laws frameRefl CheckpointSurvivingFiles.Frames.trans
    (directory.file (.run selected.reads.manifest.header.generation selected.index))
    selected.stamp.byteCount.toNat (selected.reads.atRun selected.index)
  rw [seen.releasesSelected.returned] at later
  exact earlier.trans later

end ReachedSelectedFiles

section

variable {heap : Type} {input : FilePath} {directory : DiskDirectory}
  {view : OpenCloseHeapView heap FileImage} {init : OpenSyncCacheCallbacks heap}
  {calls : RawOpenAdmissionCallbacks heap} {entry : heap}
  {admission : CensusOpenAdmissionReports input directory (view.descriptors entry) (view.files entry)}
  {admitted : RawOpenAdmissionReport admission view calls entry}
  {seed : OpenSyncCacheAllocations admission.opened view init admitted.afterFlock}
  {fileCalls : MarkedTemporaryReadCalls heap} {release : IO.FS.Handle → heap → heap}

variable {workerReached : heap}
variable (disposal : RawOpenCacheDisposal (admitted := admitted) seed workerReached)
    (finalized : RawOpenErrorLockFinalization view directory release admitted.lock admission.owner disposal.reached)

/-- Admission and cleanup frame any observation retained around the
held worker. The worker has its own effect law. -/
structure RawOpenCacheDisposal.ScopeFrames (frame : heap → heap → Prop) : Prop where
  admission : admitted.CacheFrames seed frame
  dispose : frame workerReached disposal.afterDisposal
  unlock : frame disposal.afterDisposal disposal.reached
  releaseLock : frame disposal.reached finalized.reached

variable {disposal finalized} {frame : heap → heap → Prop}

/-- Preserve the worker's reached bindings through both runtime drops
and the intervening unlock. These bindings can include a new keeper
that was published before the worker returned an error. -/
theorem RawOpenCacheDisposal.ScopeFrames.afterWorker
    (frames : disposal.ScopeFrames finalized frame)
    (trans : ∀ {before middle after}, frame before middle → frame middle after → frame before after) :
    frame workerReached finalized.reached :=
  trans (trans frames.dispose frames.unlock) frames.releaseLock

/-- Read-only and repair failures share admission and cleanup. -/
theorem RawOpenCacheDisposal.ScopeFrames.preserves
    (frames : disposal.ScopeFrames finalized frame)
    (trans : ∀ {before middle after}, frame before middle → frame middle after → frame before after)
    (worker : frame seed.afterPending workerReached) :
    frame entry finalized.reached :=
  trans (admitted.framesThroughCache seed trans frames.admission) (trans worker (frames.afterWorker trans))

variable (seen : RawManifestStatError (admitted := admitted) seed fileCalls)
    (disposal : RawOpenCacheDisposal (admitted := admitted) seed seen.reached)
    (finalized : RawOpenErrorLockFinalization view directory release admitted.lock admission.owner disposal.reached)
    (files : heap → CheckpointSurvivingFiles) (selectedPath : FilePath → Prop)

/-- The failed manifest stat lies between the same admission and drops. -/
structure RawManifestStatError.FileFrames extends
    disposal.ScopeFrames finalized (fun before after => (files before).Frames selectedPath (files after)) where
  stat : (files seed.afterPending).Frames selectedPath (files seen.reached)

variable {seen disposal finalized files selectedPath}

/-- Preserve the selected files through the caller-visible stat rejection. -/
theorem RawManifestStatError.FileFrames.preserves
    (frames : seen.FileFrames disposal finalized files selectedPath) :
    (files entry).Frames selectedPath (files finalized.reached) :=
  frames.toScopeFrames.preserves CheckpointSurvivingFiles.Frames.trans frames.stat

end

section FinalizedManifestLookup

variable {heap stream : Type} {input : FilePath} {directory : DiskDirectory}
  {view : OpenCloseHeapView heap FileImage} {entry : heap}
  {admission : CensusOpenAdmissionReports input directory (view.descriptors entry) (view.files entry)}
  {source : RawMarkedOpenInterpreter heap stream}
  {raw : RawOpenAdmissionReport admission view source.calls entry}
  {allocation : OpenSyncCacheAllocations admission.opened view source.init raw.afterFlock}

/-- Scoped laws at the actual primitive callbacks of a rejected MANIFEST lookup. -/
structure RawManifestStatError.CallbackFrames
    (seen : RawManifestStatError (admitted := raw) allocation source.fileCalls)
    (disposal : RawOpenCacheDisposal (admitted := raw) allocation seen.reached)
    (finalized : RawOpenErrorLockFinalization view directory source.release raw.lock admission.owner disposal.reached)
    (frame : heap → heap → Prop) : Prop where
  admission : raw.CacheFrames allocation frame
  stat : source.calls.lookup (directory.file .manifest) allocation.afterPending = .ok (.error seen.cause) seen.reached →
    frame allocation.afterPending seen.reached
  dispose : let cache :=
      RawMarkedOpenInterpreter.makeCache directory allocation.directoryRef allocation.activeRef allocation.pendingRef
    source.dispose cache seen.reached = .ok () disposal.afterDisposal → frame seen.reached disposal.afterDisposal
  unlock : source.calls.unlock raw.lock disposal.afterDisposal = (match disposal.unlockResult with
      | .ok () => .ok () disposal.reached
      | .error cause => .error cause disposal.reached) →
    frame disposal.afterDisposal disposal.reached
  release : source.release raw.lock disposal.reached = finalized.reached → frame disposal.reached finalized.reached

/-- Compose the same held lookup and cleanup receipts for any scoped
observation, including the live files and the parent crash maps. -/
theorem RawManifestStatError.finalizesWithFrames
    (seen : RawManifestStatError (admitted := raw) allocation source.fileCalls)
    (disposal : RawOpenCacheDisposal (admitted := raw) allocation seen.reached)
    (sameDisposal : source.dispose = disposal.dispose)
    (finalized : RawOpenErrorLockFinalization view directory source.release raw.lock admission.owner disposal.reached)
    {frame : heap → heap → Prop}
    (trans : ∀ {before middle after}, frame before middle → frame middle after → frame before after)
    (frames : seen.CallbackFrames disposal finalized frame) :
    ∃ failed : RawFinalizedOpenAttempt view directory source.calls source.init source.release input entry,
      source.openTable input entry = .error failed.diagnostic failed.reached ∧
      failed.diagnostic = disposal.diagnostic seen.cause ∧ failed.reached = finalized.reached ∧
      frame entry finalized.reached := by
  obtain ⟨failed, returned, cause, reached⟩ := seen.finalizesWithInterpreter source disposal sameDisposal finalized
  have uses := (RawMarkedOpenInterpreter.cacheReferences directory allocation.directoryRef allocation.activeRef
    allocation.pendingRef).1
  have dropped := frames.dispose (sameDisposal.symm ▸ disposal.disposed _ uses)
  have scope : disposal.ScopeFrames finalized frame :=
    ⟨frames.admission, dropped, frames.unlock disposal.unlocked, frames.release finalized.finalized⟩
  exact ⟨failed, returned, cause, reached, scope.preserves trans (frames.stat seen.stat)⟩

private theorem singletonFrame
    {atReturn : heap} {diagnostic : IO.Error} {frame : heap → heap → Prop}
    (returned : source.openTable input entry = .error diagnostic atReturn) (framed : frame entry atReturn)
    {earlier : List (FilePath × IO.Error)} {before after : heap} {path : FilePath} {error : IO.Error}
    (prior : source.FailedCalls entry earlier before)
    (inside : List.IsPrefix (earlier ++ [(path, error)]) [(input, diagnostic)])
    (ran : source.openTable path before = .error error after) :
    frame before after := by
  have earlierEmpty : earlier = [] := by
    apply List.eq_nil_of_length_eq_zero
    have bound := inside.length_le
    simp only [List.length_append, List.length_cons, List.length_nil] at bound
    omega
  have first : before = entry := by
    cases prior with
    | empty => rfl
    | next _ _ _ => simp at earlierEmpty
  subst earlier
  subst before
  have same : (path, error) = (input, diagnostic) := by
    simpa using inside.eq_of_length rfl
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj same
  obtain rfl := (EStateM.Result.error.inj (returned.symm.trans ran)).2
  exact framed

/-- A rejected MANIFEST lookup supplies the actual failed call and its
read-only frame for any selected manifest. The extra frame carries
other scoped effects, such as durable bytes and parent settlement. -/
theorem RawManifestStatError.finalizesSelectedCheckpoint
    (seen : RawManifestStatError (admitted := raw) allocation source.fileCalls)
    (disposal : RawOpenCacheDisposal (admitted := raw) allocation seen.reached)
    (sameDisposal : source.dispose = disposal.dispose)
    (finalized : RawOpenErrorLockFinalization view directory source.release raw.lock admission.owner disposal.reached)
    (files : heap → CheckpointSurvivingFiles) (scope : FilePath → Prop)
    {frame : heap → heap → Prop}
    (trans : ∀ {before middle after}, frame before middle → frame middle after → frame before after)
    (frames : seen.CallbackFrames disposal finalized (fun before after =>
      (files before).Frames scope (files after) ∧ frame before after)) :
    let errors := [(input, disposal.diagnostic seen.cause)]
    source.FailedCalls entry errors finalized.reached ∧
    (∀ {prior : List (FilePath × IO.Error)} {before after : heap} {path : FilePath} {cause : IO.Error},
      source.FailedCalls entry prior before → List.IsPrefix (prior ++ [(path, cause)]) errors →
      source.openTable path before = .error cause after →
      (files before).Frames scope (files after) ∧ (view.files after).image = (view.files before).image ∧
      frame before after) := by
  obtain ⟨failed, returned, diagnostic, reached, framed⟩ := seen.finalizesWithFrames disposal sameDisposal finalized
    (fun earlier later => ⟨earlier.1.trans later.1, trans earlier.2 later.2⟩) frames
  obtain ⟨_, _, _, _, _, _, sameImage, _⟩ := failed.returns
  have observed : source.openTable input entry = .error (disposal.diagnostic seen.cause) finalized.reached := by
    rw [← diagnostic, ← reached]
    exact returned
  have effect : (files entry).Frames scope (files finalized.reached) ∧
      (view.files finalized.reached).image = (view.files entry).image ∧ frame entry finalized.reached :=
    ⟨framed.1, reached ▸ sameImage, framed.2⟩
  exact ⟨.next .empty input observed, fun prior within ran => singletonFrame
    (frame := fun before after => (files before).Frames scope (files after) ∧
      (view.files after).image = (view.files before).image ∧ frame before after) observed effect prior within ran⟩

end FinalizedManifestLookup

section ManifestRetry

variable {heap stream : Type} {input : FilePath} {state : NativeReadyState} {target : Target}
  {view : OpenCloseHeapView heap FileImage} {entry : heap}
  {admission : CensusOpenAdmissionReports input state.session.directory (view.descriptors entry) (view.files entry)}
  {source : RawMarkedOpenInterpreter heap stream}
  {raw : RawOpenAdmissionReport admission view source.calls entry}
  {allocation : OpenSyncCacheAllocations admission.opened view source.init raw.afterFlock}
  {storage : heap → CheckpointStorageObservation} {names : heap → FilePath → Option Nat}
  {visible : heap → Nat → ByteArray}

local notation "dir" => state.session.directory
local notation "scope" => fun path =>
  state.selectedRetryPath path ∨ path = DiskDirectory.file dir (DiskFile.walSegment target.first)
local notation "durableFrames" => fun before after =>
  CheckpointSurvivingFiles.Frames state.selectedRetryPath (CheckpointStorageObservation.files (storage before))
    (CheckpointStorageObservation.files (storage after)) ∧
  CheckpointStorageObservation.Frames (· = DiskDirectory.path dir) (storage before) (storage after)

/-- A rejected held lookup supplies one actual failed retry. Live keeper
bytes and durable file and parent observations follow the same cleanup. -/
theorem RawManifestStatError.selectedRetry
    (seen : RawManifestStatError (admitted := raw) allocation source.fileCalls)
    (disposal : RawOpenCacheDisposal (admitted := raw) allocation seen.reached)
    (sameDisposal : source.dispose = disposal.dispose)
    (finalized : RawOpenErrorLockFinalization view dir source.release raw.lock admission.owner disposal.reached)
    (vacant : TryLockObserves (view.files entry).owners dir (.ok true))
    (frames : seen.CallbackFrames disposal finalized (fun before after =>
      (observedFiles names visible before).Frames scope (observedFiles names visible after) ∧ durableFrames before after)) :
    let calls := [(input, disposal.diagnostic seen.cause)]
    ∃ attempts : source.FailedCalls entry calls finalized.reached,
      calls ≠ [] ∧
      RawOpenRetryTrace.SelectedEffects view source entry target
        (fun heap => ⟨names heap, fun inode => [visible heap inode]⟩) state.selectedRetryPath
        (RawOpenRetryTrace.KeeperAt view dir target names visible) attempts ∧
      ∀ {earlier : List (FilePath × IO.Error)} {before after : heap} {path : FilePath} {error : IO.Error},
        source.FailedCalls entry earlier before → List.IsPrefix (earlier ++ [(path, error)]) calls →
        source.openTable path before = .error error after → durableFrames before after := by
  obtain ⟨failed, returned, diagnostic, reached, live, durable⟩ := seen.finalizesWithFrames disposal sameDisposal finalized
    (fun left right => ⟨left.1.trans right.1, left.2.1.trans right.2.1, left.2.2.trans right.2.2⟩) frames
  let block : RawFinalizedOpenAttempts view dir source.calls source.init source.release entry
      [(input, failed.diagnostic)] failed.reached := .attempt .empty vacant input failed
  let calls : source.FailedCalls entry [(input, failed.diagnostic)] failed.reached := .next .empty input returned
  rw [← reached] at live durable
  dsimp
  rw [← diagnostic, ← reached]
  exact ⟨calls, List.cons_ne_nil _ _, RawOpenRetryTrace.SelectedEffects.empty.readOnly block
    (fun path keeps => live path (.inl keeps)) (block.keepsVisibleKeeper (fun path keeper => live path (.inr keeper))) calls,
    fun prior inside ran => singletonFrame (frame := durableFrames) returned durable prior inside ran⟩

end ManifestRetry

section

variable {heap : Type} {state : NativeReadyState} {crash : NativeReadyQuietCrash state}
  {view : OpenCloseHeapView heap FileImage} {names : heap → FilePath → Option Nat} {bytes : heap → Nat → ByteArray}
  {before rebooted : heap} {beforeCensus : DescriptorInventory}
  {input : FilePath} {calls : RawOpenAdmissionCallbacks heap} {init : OpenSyncCacheCallbacks heap}
  {admission : CensusOpenAdmissionReports input state.session.directory
    (view.descriptors rebooted) (view.files rebooted)}
  {admitted : RawOpenAdmissionReport admission view calls rebooted}
  {seed : OpenSyncCacheAllocations admission.opened view init admitted.afterFlock}
  {fileCalls : MarkedTemporaryReadCalls heap} {release : IO.FS.Handle → heap → heap}

/-- A read-only attempt preserves the same selected survivor objects. -/
theorem RawQuietRebootEntry.readsAfterOpenFrame
    (entry : RawQuietRebootEntry crash view names bytes before rebooted beforeCensus)
    {reached : heap}
    (frame : (observedFiles names bytes rebooted).Frames
      (checkpointSurvivorPath state.session.directory state.writer state.writer.target.pair.manifest)
      (observedFiles names bytes reached))
    {retryInput : FilePath}
    {layout : CanonicalKeeperLayout crash.retry.image state.writer.history}
    {selected : SelectedIntegrityCheckpoint state.writer.published.durable
      crash.retry.image.directory.active.manifest state.writer.checkpoint}
    {reader : NativeReadyRestartReads crash retryInput layout selected} {path : FilePath} {payload : ByteArray}
    (selectedPath : checkpointSurvivorPath state.session.directory state.writer state.writer.target.pair.manifest path)
    (observed : reader.ReadsSurvivor path payload) :
    ∃ read : reader.opening.reads.reads.ObservesFile path payload,
      names reached path = some read.object ∧ bytes reached read.object = payload := by
  obtain ⟨read, object, contents⟩ := entry.readsSurvivingFile selectedPath observed
  obtain ⟨sameObject, sameBytes⟩ := frame path selectedPath
  exact ⟨read, sameObject.trans object, (List.cons.inj (sameBytes read.object object)).1.trans contents⟩

/-- A child's local name at the later admission identifies the same
survivor inode at the reboot, even if unrelated names have changed. -/
theorem RawQuietRebootEntry.childAfterOpenFrame
    (entry : RawQuietRebootEntry crash view names bytes before rebooted beforeCensus)
    {reached : heap}
    (frame : (observedFiles names bytes rebooted).Frames
      (checkpointSurvivorPath state.session.directory state.writer state.writer.target.pair.manifest)
      (observedFiles names bytes reached))
    {path : FilePath} {name : String}
    (selectedPath : checkpointSurvivorPath state.session.directory state.writer state.writer.target.pair.manifest path)
    (child : CheckpointCrashChild (names reached) admission path name) :
    CheckpointCrashChild crash.names admission path name :=
  child.trans ((frame path selectedPath).1.trans (entry.survivorNames path (.inr (.inr selectedPath))))

/-- The failed marked manifest stat leaves the selected reader's
exact survivor paths at the heap that the next open will use. -/
theorem RawQuietRebootEntry.readsAfterManifestRejection
    (entry : RawQuietRebootEntry crash view names bytes before rebooted beforeCensus)
    (seen : RawManifestStatError (admitted := admitted) seed fileCalls)
    (disposal : RawOpenCacheDisposal (admitted := admitted) seed seen.reached)
    (finalized : RawOpenErrorLockFinalization view state.session.directory release admitted.lock admission.owner disposal.reached)
    (frames : seen.FileFrames disposal finalized (observedFiles names bytes)
      (checkpointSurvivorPath state.session.directory state.writer state.writer.target.pair.manifest))
    {retryInput : FilePath}
    {layout : CanonicalKeeperLayout crash.retry.image state.writer.history}
    {selected : SelectedIntegrityCheckpoint state.writer.published.durable
      crash.retry.image.directory.active.manifest state.writer.checkpoint}
    {reader : NativeReadyRestartReads crash retryInput layout selected} {path : FilePath} {payload : ByteArray}
    (selectedPath : checkpointSurvivorPath state.session.directory state.writer state.writer.target.pair.manifest path)
    (observed : reader.ReadsSurvivor path payload) :
    ∃ read : reader.opening.reads.reads.ObservesFile path payload,
      names finalized.reached path = some read.object ∧ bytes finalized.reached read.object = payload :=
  entry.readsAfterOpenFrame frames.preserves selectedPath observed

end

section

variable {heap stream : Type} {history : List WAL.Write} {log : List DatabaseSubmissions}
  (current : NativeReadPosition history log)
  {crash : NativeReadyQuietCrash current.state}
  {input retryInput : FilePath} {view : OpenCloseHeapView heap FileImage}
  {names : heap → FilePath → Option Nat} {bytes : heap → Nat → ByteArray}
  {before rebooted retryHeap : heap} {beforeCensus : DescriptorInventory}
  {calls : RawOpenAdmissionCallbacks heap} {init : OpenSyncCacheCallbacks heap}
  {admission : CensusOpenAdmissionReports input current.state.session.directory
    (view.descriptors rebooted) (view.files rebooted)}
  {admitted : RawOpenAdmissionReport admission view calls rebooted}
  {seed : OpenSyncCacheAllocations admission.opened view init admitted.afterFlock}
  {release : IO.FS.Handle → heap → heap}
  {layout : CanonicalKeeperLayout crash.retry.image current.state.writer.history}
  {selected : SelectedIntegrityCheckpoint current.state.writer.published.durable
    crash.retry.image.directory.active.manifest current.state.writer.checkpoint}
  {reader : NativeReadyRestartReads crash retryInput layout selected}
  {phaseIdentity : IO.Ref (Phase Installed) → Nat} {tokenIdentity : IO.Ref Unit → Nat}
  {allocatePhase : Phase Installed → EStateM IO.Error heap (IO.Ref (Phase Installed))}
  {allocateToken : Unit → EStateM IO.Error heap (IO.Ref Unit)}

variable (remove : FilePath → EStateM IO.Error heap (Except IO.Error Unit))
    (write : FilePath → ByteArray → EStateM IO.Error heap Unit)
    (rename : FilePath → FilePath → EStateM IO.Error heap Unit)
    (bootstrap : DiskDirectory → DiskTable.OpenSyncFiles → EStateM IO.Error heap Reopened)
    (assemble : DiskDirectory → IO.FS.Handle → DiskTable.OpenSyncFiles → IO.Ref (Phase Installed) → IO.Ref Unit → DiskTable)
    {get : IO.Ref (Phase Installed) → EStateM IO.Error heap (Phase Installed)}
    {set : IO.Ref (Phase Installed) → Phase Installed → EStateM IO.Error heap Unit}
    (ptrEq : IO.Ref Unit → IO.Ref Unit → EStateM IO.Error heap Bool)

variable (target : layout.target = current.state.writer.target) (keeper : layout.keeper = current.state.writer.wal.active)
    (descriptors : layout.sealed ++ [layout.keeper] = current.state.writer.wal.readDescriptors layout.range.watermark)
    (offsets : selectWalSegmentReads (current.state.writer.wal.segments.map WalSegment.first) layout.range.watermark =
      some (layout.first, (current.state.writer.wal.readDescriptors layout.range.watermark).map WalSegment.first))
    (prepared : Prepared crash.retry.image layout.target layout.plan)
    (constructs : ∀ resolved lock files, DiskTable.OpenReferenceAssembly resolved lock files (assemble resolved lock files))
    (effects : OpenPhaseCellEffects view.phase get set)

include target keeper descriptors offsets prepared constructs effects

/-- Carry one reboot's selected names and payloads across the reported
read-only failures to the supplied aligned attempt. Each held failure
uses the worker in its report. Scratch paths stay outside the frame. -/
theorem RawQuietRebootEntry.reopensAfterReadOnlyAttempts
    (entry : RawQuietRebootEntry crash view names bytes before rebooted beforeCensus)
    (booted : (view.descriptors rebooted, view.files rebooted) = (crash.reboot, crash.retry))
    {errors : List (FilePath × IO.Error)}
    (attempts : RawFinalizedOpenAttempts view current.state.session.directory calls init release rebooted errors retryHeap)
    (beforeFlock : ∀ input entry (refused : RawBeforeFlockRejection view calls input entry),
      (observedFiles names bytes entry).Frames current.state.crashPath (observedFiles names bytes refused.reached))
    (flockError : ∀ input entry (refused : RawFlockRejection view calls current.state.session.directory release input entry),
      (observedFiles names bytes entry).Frames current.state.crashPath (observedFiles names bytes refused.reached))
    (held : ∀ input entry (failed : RawFinalizedOpenAttempt view current.state.session.directory calls init release input entry),
      (observedFiles names bytes entry).Frames current.state.crashPath (observedFiles names bytes failed.reached))
    (raw : RawAlignedCheckpointReopenEffects reader.opening reader.capturedChronology view calls init retryHeap
      phaseIdentity tokenIdentity allocatePhase allocateToken stream) :
    (view.descriptors retryHeap, view.files retryHeap) = (view.descriptors rebooted, view.files rebooted) ∧
    (∀ path, current.state.crashPath path → names retryHeap path = crash.names path) ∧
    (∀ path payload,
      checkpointSurvivorPath current.state.session.directory current.state.writer current.state.writer.target.pair.manifest path →
      reader.ReadsSurvivor path payload →
      ∃ read : reader.opening.reads.reads.ObservesFile path payload,
        names retryHeap path = some read.object ∧ bytes retryHeap read.object = payload) ∧
    (∃ next : NativeReadPosition history log, next.reads = current.reads ∧ next.opened = reader.run ∧
      reader.ReachedSession next.state history log current.reads ∧
      Nonempty (raw.ReturnedAt next remove write rename bootstrap assemble get set ptrEq)) := by
  have frame := attempts.frames (frame := fun first last =>
    (observedFiles names bytes first).Frames current.state.crashPath (observedFiles names bytes last))
    (fun _ _ _ => ⟨rfl, fun _ _ => rfl⟩) CheckpointSurvivingFiles.Frames.trans beforeFlock flockError held
  refine ⟨(Prod.ext raw.raw.entryCensus raw.raw.entryFiles).trans booted.symm,
    fun path selected => (frame path selected).1.trans (entry.survivorNames path selected), ?_,
    raw.reopensQuietSelection current remove write rename bootstrap assemble ptrEq target keeper
      descriptors offsets prepared constructs effects⟩
  intro path payload selectedPath observed
  exact entry.readsAfterOpenFrame (fun path selected => frame path (.inr (.inr selected))) selectedPath observed

/-- A finalized read-only failure and its successor use one native
program. Each attempt uses its own cache references. -/
theorem RawQuietRebootEntry.reopensAfterReadOnlyRejection
    (entry : RawQuietRebootEntry crash view names bytes before rebooted beforeCensus)
    (booted : (view.descriptors rebooted, view.files rebooted) = (crash.reboot, crash.retry))
    (raw : RawAlignedCheckpointReopenEffects reader.opening reader.capturedChronology view calls init retryHeap
      phaseIdentity tokenIdentity allocatePhase allocateToken stream)
    (failed : RawFinalizedOpenAttempt view current.state.session.directory calls init release input rebooted)
    (sameHeap : retryHeap = failed.reached)
    (frame : (observedFiles names bytes rebooted).Frames
      (checkpointSurvivorPath current.state.session.directory current.state.writer current.state.writer.target.pair.manifest)
      (observedFiles names bytes failed.reached))
    (sameWorker : failed.recover = fun resolved lock cache => do
      let state ← calls.recoverMarkedWithCacheRefs raw.fileCalls raw.directoryCalls raw.callbacks failed.seed.directoryRef
        failed.seed.activeRef failed.seed.pendingRef remove write rename bootstrap resolved cache
      installReady state.installed allocatePhase allocateToken
        (fun phase token => pure (assemble resolved lock cache phase token))) :
    let recover := fun resolved lock cache => do
      let state ← calls.recoverMarkedWithCacheRefs raw.fileCalls raw.directoryCalls raw.callbacks failed.seed.directoryRef
        failed.seed.activeRef failed.seed.pendingRef remove write rename bootstrap resolved cache
      installReady state.installed allocatePhase allocateToken
        (fun phase token => pure (assemble resolved lock cache phase token))
    failed.disposed.Finalized recover failed.cause failed.finalized ∧
    (view.descriptors retryHeap, view.files retryHeap) = (view.descriptors rebooted, view.files rebooted) ∧
    (∀ path payload,
      checkpointSurvivorPath current.state.session.directory current.state.writer current.state.writer.target.pair.manifest path →
      reader.ReadsSurvivor path payload →
      ∃ read : reader.opening.reads.reads.ObservesFile path payload,
        names retryHeap path = some read.object ∧ bytes retryHeap read.object = payload) ∧
    (∃ next : NativeReadPosition history log, next.reads = current.reads ∧ next.opened = reader.run ∧
      reader.ReachedSession next.state history log current.reads ∧
      Nonempty (raw.ReturnedAt next remove write rename bootstrap assemble get set ptrEq)) := by
  intro recover
  refine ⟨?_, (Prod.ext raw.raw.entryCensus raw.raw.entryFiles).trans booted.symm, ?_,
    raw.reopensQuietSelection current remove write rename bootstrap assemble ptrEq target keeper
      descriptors offsets prepared constructs effects⟩
  · rw [show recover = failed.recover from sameWorker.symm]
    exact failed.disposed.returnsAfterLockFinalization failed.recover failed.cause failed.rejected failed.finalized
  · intro path payload selectedPath observed
    rw [sameHeap]
    exact entry.readsAfterOpenFrame frame selectedPath observed

/-- Follow the same file, directory, repair and allocation callbacks
through a read-only manifest stat rejection and an aligned retry. Each
attempt allocates its own cache. The retry starts at the actual final
lock-drop heap and reads from the framed selected objects there. -/
theorem RawQuietRebootEntry.reopensAfterManifestRejection
    (entry : RawQuietRebootEntry crash view names bytes before rebooted beforeCensus)
    (booted : (view.descriptors rebooted, view.files rebooted) = (crash.reboot, crash.retry))
    (raw : RawAlignedCheckpointReopenEffects reader.opening reader.capturedChronology view calls init retryHeap
      phaseIdentity tokenIdentity allocatePhase allocateToken stream)
    (seen : RawManifestStatError (admitted := admitted) seed raw.fileCalls)
    (disposal : RawOpenCacheDisposal (admitted := admitted) seed seen.reached)
    (finalized : RawOpenErrorLockFinalization view current.state.session.directory release admitted.lock
      admission.owner disposal.reached)
    (sameHeap : retryHeap = finalized.reached)
    (frames : seen.FileFrames disposal finalized (observedFiles names bytes)
      (checkpointSurvivorPath current.state.session.directory current.state.writer current.state.writer.target.pair.manifest))
    :
    let install := fun resolved lock cache (opened : Reopened) =>
      installReady opened.installed allocatePhase allocateToken
        (fun phase token => pure (assemble resolved lock cache phase token))
    let failed := seen.finalizedAttempt disposal raw.directoryCalls raw.callbacks remove write rename bootstrap install finalized
    disposal.Finalized failed.recover failed.cause finalized ∧
    (view.descriptors retryHeap, view.files retryHeap) = (view.descriptors rebooted, view.files rebooted) ∧
    (∀ path payload,
      checkpointSurvivorPath current.state.session.directory current.state.writer current.state.writer.target.pair.manifest path →
      reader.ReadsSurvivor path payload →
      ∃ read : reader.opening.reads.reads.ObservesFile path payload,
        names retryHeap path = some read.object ∧ bytes retryHeap read.object = payload) ∧
    (∃ next : NativeReadPosition history log, next.reads = current.reads ∧ next.opened = reader.run ∧
      reader.ReachedSession next.state history log current.reads ∧
      Nonempty (raw.ReturnedAt next remove write rename bootstrap assemble get set ptrEq)) := by
  intro install failed
  exact entry.reopensAfterReadOnlyRejection current remove write rename bootstrap assemble ptrEq target keeper descriptors offsets prepared constructs effects
    booted raw failed sameHeap frames.preserves rfl

/-- Reopen after a positive short run chunk and a reached read error.
The issuing descriptor belongs to the selected run. Its scope drop,
cache disposal and lock drop all precede the same worker's next open. -/
theorem RawQuietRebootEntry.reopensAfterRunChunkRejection
    (entry : RawQuietRebootEntry crash view names bytes before rebooted beforeCensus)
    (booted : (view.descriptors rebooted, view.files rebooted) = (crash.reboot, crash.retry))
    (raw : RawAlignedCheckpointReopenEffects reader.opening reader.capturedChronology view calls init retryHeap
      phaseIdentity tokenIdentity allocatePhase allocateToken stream)
    {run : RawSelectedCheckpointRunStat (admitted := admitted) seed raw.fileCalls}
    (seen : RawCheckpointChunkReadError run)
    (disposal : RawOpenCacheDisposal (admitted := admitted) seed seen.reached)
    (finalized : RawOpenErrorLockFinalization view current.state.session.directory release admitted.lock
      admission.owner disposal.reached)
    (sameHeap : retryHeap = finalized.reached)
    (frames : disposal.ScopeFrames finalized (fun before after =>
      (observedFiles names bytes before).Frames
        (checkpointSurvivorPath current.state.session.directory current.state.writer current.state.writer.target.pair.manifest)
        (observedFiles names bytes after)))
    (readLaws : raw.fileCalls.FileFrames (observedFiles names bytes)
      (checkpointSurvivorPath current.state.session.directory current.state.writer current.state.writer.target.pair.manifest))
    (child : CheckpointCrashChild (names seed.afterPending) admission
      (current.state.session.directory.file (.run run.reads.manifest.header.generation run.index))
      (renderRunFileName run.reads.manifest.header.generation run.index))
    (issuedBytes : bytes seen.opened ((view.handle seen.opened seen.handle).1.inode
      (view.handle seen.opened seen.handle).2.1.description) = seen.bytes)
    :
    let install := fun resolved lock cache (opened : Reopened) =>
      installReady opened.installed allocatePhase allocateToken
        (fun phase token => pure (assemble resolved lock cache phase token))
    let failed := seen.finalizedAttempt disposal raw.directoryCalls raw.callbacks remove write rename bootstrap install finalized
    let inode := (view.handle seen.opened seen.handle).1.inode (view.handle seen.opened seen.handle).2.1.description
    let path := current.state.session.directory.file (.run run.reads.manifest.header.generation run.index)
    (view.descriptors retryHeap).references seen.slot.description = [] ∧
    crash.names path = some inode ∧ crash.contents inode = seen.bytes ∧
    names retryHeap path = some inode ∧ bytes retryHeap inode = seen.bytes ∧
    disposal.Finalized failed.recover failed.cause finalized ∧
    (view.descriptors retryHeap, view.files retryHeap) = (view.descriptors rebooted, view.files rebooted) ∧
    (∀ path payload,
      checkpointSurvivorPath current.state.session.directory current.state.writer current.state.writer.target.pair.manifest path →
      reader.ReadsSurvivor path payload →
      ∃ read : reader.opening.reads.reads.ObservesFile path payload,
        names retryHeap path = some read.object ∧ bytes retryHeap read.object = payload) ∧
    (∃ next : NativeReadPosition history log, next.reads = current.reads ∧ next.opened = reader.run ∧
      reader.ReachedSession next.state history log current.reads ∧
      Nonempty (raw.ReturnedAt next remove write rename bootstrap assemble get set ptrEq)) := by
  intro install failed inode path
  have admissionFrame := admitted.framesThroughCache seed
    (frame := fun before after => (observedFiles names bytes before).Frames
      (checkpointSurvivorPath current.state.session.directory current.state.writer current.state.writer.target.pair.manifest)
      (observedFiles names bytes after)) CheckpointSurvivingFiles.Frames.trans frames.admission
  have frame := frames.preserves CheckpointSurvivingFiles.Frames.trans (seen.preservesSelectedFiles readLaws)
  have selectedManifest : current.state.writer.target.pair.manifest = some run.reads.bytes := by
    have bound := run.reads.bound
    have sameFileState : view.files rebooted = crash.retry := congrArg Prod.snd booted
    exact (congrArg (fun state => state.image.directory.active.manifest) sameFileState).symm.trans bound
  have selectedPath : checkpointSurvivorPath current.state.session.directory current.state.writer
      current.state.writer.target.pair.manifest path :=
    .inr (.inr ⟨run.reads.bytes, run.reads.manifest, run.index, selectedManifest, run.reads.decoded, run.within, rfl⟩)
  have parentBinding := run.child.binds
  rw [run.child.atRoot, run.child.atName] at parentBinding
  have binding : crash.names path = some inode := by
    have sameChild := entry.childAfterOpenFrame admissionFrame selectedPath child
    unfold CheckpointCrashChild at sameChild
    rw [parentBinding, Option.map_some] at sameChild
    exact sameChild.symm.trans (congrArg some seen.releasesSelected.inode.symm)
  have survived : names rebooted path = some inode :=
    (entry.survivorNames path (.inr (.inr selectedPath))).trans binding
  have earlier := admissionFrame.trans (run.reads.preservesSelectedFiles readLaws (Nat.le_refl run.index))
  have opened := readLaws.openRead path (run.reads.atRun run.index)
  have actualOpen : raw.fileCalls.openRead path (run.reads.atRun run.index) = .ok seen.handle seen.opened := seen.openRaw
  rw [actualOpen] at opened
  have bytesOnIssue := ((earlier.trans opened) path selectedPath).2 inode survived
  have bytesAtReboot : bytes rebooted inode = seen.bytes :=
    (List.cons.inj bytesOnIssue).1.symm.trans issuedBytes
  have remains := frame path selectedPath
  have closed : (view.descriptors finalized.reached).references seen.slot.description = [] := by
    rw [finalized.census, disposal.returnedCensus, disposal.census, DescriptorInventory.afterDrops_append,
      DescriptorInventory.references_afterDrops, seen.releasesSelected.retired]
    rfl
  have durable := (entry.survivorBytes path selectedPath inode binding).symm.trans bytesAtReboot
  refine ⟨?_, binding, durable, ?_, ?_, entry.reopensAfterReadOnlyRejection current remove write rename bootstrap assemble ptrEq target keeper descriptors offsets prepared constructs effects
    booted raw failed sameHeap frame rfl⟩
  · simpa only [sameHeap] using closed
  · rw [sameHeap]
    exact remains.1.trans survived
  · exact (congrArg (fun atHeap => bytes atHeap inode) sameHeap).trans
      ((List.cons.inj (remains.2 inode survived)).1.trans bytesAtReboot)

end

end Alvoki.Storage.DiskSession
