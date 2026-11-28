import Alvoki.Experiments.SortedRun.Refinement

namespace SortedRun

open ImmutableSSTable ImmutableSSTable.Unified

abbrev NativeFrontier := Frontier Nat Nat Entry

/-- Evidence about a caller-owned checked table and the local size/read
effects of its immutable source. The acquisition itself remains outside
the merge. This packages primitive premises at use, not cursor results. -/
structure CheckedInput (table : Table (EIO String)) (observe : World → φ) (rows : List Entry) where
  source : Source (EIO String)
  layout : Layout
  crc : Checksum
  bytes : ByteArray
  image : Image crc layout rows bytes
  openedAt : World
  readyAt : World
  opened : openTableChecked source crc layout.tableId openedAt = .ok table readyAt
  reads : ∀ start, ScopedRead (fun t => observe t = observe start) source bytes

/-- Local native input observations for one held immutable descriptor.
The positional primitive is reached only after the source's count and
offset guards. Both outcomes preserve the chosen caller frame. -/
structure InputPrimitives (ops : ReadPrimitives (EIO String) handle) (held : handle)
    (frame : World → Prop) (bytes : ByteArray) : Prop where
  size : ReadPost frame (· = bytes.size) (ops.size held)
  pread : ∀ offset count : Nat, count ≤ maxRowSize → offset + count ≤ maxFileSize →
    ReadPost frame (· = bytes.extract offset (offset + count))
      (ops.pread held offset.toUInt64 count.toUSize)

theorem InputPrimitives.scopedSource
    (reads : InputPrimitives ops held frame bytes) :
    ScopedRead frame (ops.source held) bytes := by
  refine ⟨reads.size, ?_⟩
  intro offset count
  unfold ReadPrimitives.source
  by_cases countFits : count ≤ maxRowSize <;> by_cases offsetFits : offset + count ≤ maxFileSize
  · simpa [Nat.not_lt.mpr countFits, Nat.not_lt.mpr offsetFits, Bind.bind, instMonadEIO._aux_13, EST.bind]
      using reads.pread offset count countFits offsetFits
  all_goals
    have outside : maxRowSize < count ∨ maxFileSize < offset + count := by omega
    simp [outside, Bind.bind, instMonadEIO._aux_13, EST.bind, ReadPost]
    intro w kept
    exact kept

/-- Package the caller's actual checked open from the acquired description.
Acquisition and the authority to keep using this inode belong to the caller. -/
def CheckedInput.ofOpen {ops : ReadPrimitives (EIO String) handle} {held : handle}
    {path : System.FilePath} {layout : Layout} {rows : List Entry}
    {table : Table (EIO String)} {crc : Checksum} {bytes : ByteArray}
    {initial openedAt readyAt : World}
    (observe : World → φ) (image : Image crc layout rows bytes)
    (acquired : ops.openFile path .read initial = .ok held openedAt)
    (opened : openCheckedWith ops crc path layout.tableId initial = .ok table readyAt)
    (reads : ∀ start, InputPrimitives ops held (fun t => observe t = observe start) bytes) :
    CheckedInput table observe rows where
  source := ops.source held
  layout := layout
  crc := crc
  bytes := bytes
  image := image
  openedAt := openedAt
  readyAt := readyAt
  opened := by simpa [openCheckedWith, Bind.bind, instMonadEIO._aux_13, EST.bind, acquired] using opened
  reads start := (reads start).scopedSource

theorem CheckedInput.cursor (input : CheckedInput table observe rows) :
    CursorEffects table observe rows :=
  checkedCursorEffects observe input.image input.reads input.opened

def nativeWriterOps : OutputOps (EStateM IO.Error World) IO.FS.Handle :=
  effectOutput (nativeOutputOps syncFileHandle)

def nativeSupply (newer older : Table (EIO String)) (ref : IO.Ref NativeFrontier) :
    EStateM IO.Error World (Option Entry) :=
  effect (next Entry.key (tablePullIO newer) (tablePullIO older) (nativeSlot ref))

private theorem effect_encode (newer older : Table (EIO String)) (ref : IO.Ref NativeFrontier) :
    effect (Option.map id <$> next Entry.key (tablePullIO newer) (tablePullIO older) (nativeSlot ref)) =
      nativeSupply newer older ref := by
  rw [effect_map]
  funext w
  cases ran : effect (next Entry.key (tablePullIO newer) (tablePullIO older) (nativeSlot ref)) w <;>
    simp [Functor.map, EStateM.map, nativeSupply, ran]

/-- Output effects may change the owned output, but leave the two input
observations and the private cursor slot alone, also during cleanup. -/
structure OutputFrame (observe : World → φ) (path : System.FilePath) : Prop where
  create : Frames observe (nativeWriterOps.openFile path .writeNew)
  append : ∀ handle bytes, Frames observe (nativeWriterOps.append handle bytes)
  flush : ∀ handle, Frames observe (nativeWriterOps.flush handle)
  sync : ∀ handle, Frames observe (nativeWriterOps.sync handle)
  remove : Frames observe (nativeWriterOps.remove path)

private def observedWriter (writer : World → NativeWriteState IO.FS.Handle inode)
    (front : World → NativeFrontier) (newRows oldRows : List Entry) (w : World) :
    NativeWriteState IO.FS.Handle inode :=
  { writer w with rows := (front w).remaining Entry.key newRows.drop oldRows.drop }

private theorem supplierEffects {ref : IO.Ref NativeFrontier} {front : World → NativeFrontier}
    {writer : World → NativeWriteState IO.FS.Handle inode} {inputs : World → φ}
    {newer older : Table (EIO String)} {newRows oldRows : List Entry} {path : System.FilePath}
    (cell : RefEffects ref front (fun w => (inputs w, writer w)))
    (newRead : CursorEffects newer (fun w => (front w, inputs w, writer w)) newRows)
    (oldRead : CursorEffects older (fun w => (front w, inputs w, writer w)) oldRows)
    (output : NativeWritePrimitivesOn writer nativeWriterOps path)
    (kept : OutputFrame (fun w => (front w, inputs w)) path) :
    NativeWriteEffectsOn (observedWriter writer front newRows oldRows) nativeWriterOps path
      (nativeSupply newer older ref) := by
  constructor
  · constructor
    · intro before after handle ran
      have frame := kept.create before
      change nativeWriterOps.openFile path .writeNew before = _ at ran
      rw [ran] at frame
      have same : front after = front before := congrArg Prod.fst frame
      obtain ⟨fresh, identity, written⟩ := output.create before after handle ran
      exact ⟨fresh, identity, by simp [observedWriter, written, same]⟩
    · intro handle identity bytes before after bound ran
      have frame := kept.append handle bytes before
      change nativeWriterOps.append handle bytes before = _ at ran
      rw [ran] at frame
      have same : front after = front before := congrArg Prod.fst frame
      have written := output.append handle identity bytes before after bound ran
      simp [observedWriter, written, same]
    · intro handle identity before after bound ran
      have frame := kept.flush handle before
      change nativeWriterOps.flush handle before = _ at ran
      rw [ran] at frame
      have same : front after = front before := congrArg Prod.fst frame
      have written := output.flush handle identity before after bound ran
      simp [observedWriter, written, same]
    · intro handle identity before after bound flushed ran
      have frame := kept.sync handle before
      change nativeWriterOps.sync handle before = _ at ran
      rw [ran] at frame
      have same : front after = front before := congrArg Prod.fst frame
      have written := output.sync handle identity before after bound flushed ran
      simp [observedWriter, written, same]
  · intro handle identity before after row _ ran
    have nextStep := nativeNext_refines cell newRead oldRead before
    change nativeSupply newer older ref before = _ at ran
    rw [show effect (next Entry.key (tablePullIO newer) (tablePullIO older) (nativeSlot ref)) before =
      .ok row after from ran] at nextStep
    have physical : writer after = writer before := congrArg Prod.snd nextStep.1
    exact ⟨nextStep.2.1, by simp [observedWriter, physical, nextStep.2.2.1]⟩

private theorem effect_buildMergedOnRef (newer older : Table (EIO String))
    (ref : IO.Ref NativeFrontier) (path : System.FilePath) (layout : Layout)
    (options : BuildOptions) :
    effect (buildMergedOnRef newer older ref path layout options) =
      buildFileWith nativeWriterOps Alvoki.CRC32C.extend path layout
        (nativeSupply newer older ref) IO.userError options := by
  unfold buildMergedOnRef buildMergedWith
  rw [effect_buildFileWith, effect_encode]
  rfl

/-- The actual native build after allocation. The two read sources may
fail at any reached operation. A successful result carries the complete
image and identifies the callback at which the real builder saw EOF. -/
theorem buildMergedOnRef_success {ref : IO.Ref NativeFrontier} {front : World → NativeFrontier}
    {writer : World → NativeWriteState IO.FS.Handle inode} {inputs : World → φ}
    {newer older : Table (EIO String)} {newRows oldRows : List Entry}
    {path : System.FilePath} {layout : Layout} {options : BuildOptions}
    (cell : RefEffects ref front (fun w => (inputs w, writer w)))
    (newInput : CheckedInput newer (fun w => (front w, inputs w, writer w)) newRows)
    (oldInput : CheckedInput older (fun w => (front w, inputs w, writer w)) oldRows)
    (output : NativeWritePrimitivesOn writer nativeWriterOps path)
    (kept : OutputFrame (fun w => (front w, inputs w)) path)
    (built : buildMergedOnRef newer older ref path layout options before = .ok count after) :
    let rows := (front before).remaining Entry.key newRows.drop oldRows.drop
    count = rows.length ∧ Image Alvoki.CRC32C.extend layout rows (writer after).appended ∧
    (∃ handle identity, (writer after).BoundTo path handle identity ∧
      (writer after).durable = some (identity, (writer after).appended)) ∧
    ∃ atEOF consumed, nativeSupply newer older ref atEOF = .ok none consumed ∧
      (front atEOF).newer.remaining newRows.drop = [] ∧
      (front atEOF).older.remaining oldRows.drop = [] := by
  have run : effect (buildMergedOnRef newer older ref path layout options) before =
      .ok count after := by simp [effect, built]
  rw [effect_buildMergedOnRef] at run
  have effects := supplierEffects cell newInput.cursor oldInput.cursor output kept
  obtain ⟨_, countEq, image, handle, identity, bound, _, synced, _⟩ :=
    buildFileWith_refinesOn effects run
  obtain ⟨atEOF, consumed, eof⟩ := buildFileWith_eofWith run
  have step := nativeNext_refines cell newInput.cursor oldInput.cursor atEOF
  rw [show effect (next Entry.key (tablePullIO newer) (tablePullIO older) (nativeSlot ref)) atEOF =
    .ok none consumed from eof] at step
  exact ⟨countEq, image, ⟨handle, identity, bound, synced⟩, atEOF, consumed, eof, step.2.2.2 rfl⟩

private theorem afterAllocation {ref : IO.Ref NativeFrontier}
    {newer older : Table (EIO String)} {path : System.FilePath} {layout : Layout}
    {options : BuildOptions}
    (allocated : (show IO (IO.Ref NativeFrontier) from
      IO.mkRef (Frontier.start (row := Entry) 0 0)) before = .ok ref ready) :
    buildMergedFileSynced newer older path layout options before =
      buildMergedOnRef newer older ref path layout options ready := by
  simp [buildMergedFileSynced, Bind.bind, instMonadEIO._aux_13, EST.bind, allocated]

/-- The public entry point allocates its own reference. Only the initial
reference contents and the local IO primitives are inputs to the proof. -/
theorem buildMergedFileSynced_success {ref : IO.Ref NativeFrontier}
    {front : World → NativeFrontier} {writer : World → NativeWriteState IO.FS.Handle inode}
    {inputs : World → φ} {newer older : Table (EIO String)} {newRows oldRows : List Entry}
    {path : System.FilePath} {layout : Layout} {options : BuildOptions}
    (allocated : (show IO (IO.Ref NativeFrontier) from
      IO.mkRef (Frontier.start (row := Entry) 0 0)) before = .ok ref ready)
    (initialized : front ready = Frontier.start 0 0)
    (cell : RefEffects ref front (fun w => (inputs w, writer w)))
    (newInput : CheckedInput newer (fun w => (front w, inputs w, writer w)) newRows)
    (oldInput : CheckedInput older (fun w => (front w, inputs w, writer w)) oldRows)
    (output : NativeWritePrimitivesOn writer nativeWriterOps path)
    (kept : OutputFrame (fun w => (front w, inputs w)) path)
    (built : buildMergedFileSynced newer older path layout options before = .ok count after) :
    let rows := merge Entry.key newRows oldRows
    count = rows.length ∧ Image Alvoki.CRC32C.extend layout rows (writer after).appended ∧
    (∃ handle identity, (writer after).BoundTo path handle identity ∧
      (writer after).durable = some (identity, (writer after).appended)) ∧
    ∃ atEOF consumed, nativeSupply newer older ref atEOF = .ok none consumed ∧
      (front atEOF).newer.remaining newRows.drop = [] ∧
      (front atEOF).older.remaining oldRows.drop = [] := by
  rw [afterAllocation allocated] at built
  simpa [initialized, Frontier.remaining, Frontier.start, Front.remaining] using
    buildMergedOnRef_success cell newInput oldInput output kept built

/-- After any number of accepted rows, a required failure invokes only
cleanup at the reached world. The original IO.Error is preserved even
if removal reports another error. No successful EOF or image is reported. -/
private theorem buildMergedFileSynced_cleanup {ref : IO.Ref NativeFrontier}
    {newer older : Table (EIO String)} {path : System.FilePath} {layout : Layout}
    {options : BuildOptions} {handle : IO.FS.Handle} {observe : World → φ}
    (allocated : (show IO (IO.Ref NativeFrontier) from
      IO.mkRef (Frontier.start (row := Entry) 0 0)) before = .ok ref ready)
    (opened : nativeWriterOps.openFile path .writeNew ready = .ok handle created)
    (valid : layout.Valid)
    (targets : 0 < options.dataTarget ∧ options.dataTarget ≤ maxRowSize ∧
      0 < options.leafTarget ∧ options.leafTarget ≤ maxRowSize)
    (stages : (Writer.mk Alvoki.CRC32C.extend layout (nativeWriterOps.sink handle)
      IO.userError options).InputReached (nativeSupply newer older ref) atRead maxFileSize {} created)
    (failed : nativeSupply newer older ref atRead = .error error reached)
    (cleanupFrame : OutputFrame observe path) :
    ∃ after, buildMergedFileSynced newer older path layout options before = .error error after ∧
      observe after = observe reached ∧
      (nativeWriterOps.remove path reached = .ok () after ∨
        ∃ cleanupError, nativeWriterOps.remove path reached = .error cleanupError after) := by
  have run := buildFileWith_inputError opened valid targets stages failed
  rw [← effect_buildMergedOnRef] at run
  have frame := cleanupFrame.remove reached
  rw [afterAllocation allocated]
  cases cleaned : nativeWriterOps.remove path reached with
  | ok value after =>
    cases value
    rw [cleaned] at run frame
    exact ⟨after, by
      cases done : buildMergedOnRef newer older ref path layout options ready <;>
        simp [effect, done] at run ⊢
      exact run,
      frame, Or.inl rfl⟩
  | error cleanupError after =>
    rw [cleaned] at run frame
    exact ⟨after, by
      cases done : buildMergedOnRef newer older ref path layout options ready <;>
        simp [effect, done] at run ⊢
      exact run,
      frame, Or.inr ⟨cleanupError, rfl⟩⟩

/-- Join the reached-input failure with the actual native output cleanup.
The checked cursors frame both inputs and the writer up to the failing
read. Removal may change the output, while both inputs and the exact
post-failure frontier survive it. -/
theorem buildMergedFileSynced_inputError {ref : IO.Ref NativeFrontier}
    {front : World → NativeFrontier} {inputs : World → φ}
    {writer : World → NativeWriteState IO.FS.Handle inode}
    {newer older : Table (EIO String)} {newRows oldRows : List Entry}
    {path : System.FilePath} {layout : Layout} {options : BuildOptions} {handle : IO.FS.Handle}
    (allocated : (show IO (IO.Ref NativeFrontier) from
      IO.mkRef (Frontier.start (row := Entry) 0 0)) before = .ok ref ready)
    (cell : RefEffects ref front (fun w => (inputs w, writer w)))
    (newInput : CheckedInput newer (fun w => (front w, inputs w, writer w)) newRows)
    (oldInput : CheckedInput older (fun w => (front w, inputs w, writer w)) oldRows)
    (opened : nativeWriterOps.openFile path .writeNew ready = .ok handle created)
    (valid : layout.Valid)
    (targets : 0 < options.dataTarget ∧ options.dataTarget ≤ maxRowSize ∧
      0 < options.leafTarget ∧ options.leafTarget ≤ maxRowSize)
    (stages : (Writer.mk Alvoki.CRC32C.extend layout (nativeWriterOps.sink handle)
      IO.userError options).InputReached (nativeSupply newer older ref) atRead maxFileSize {} created)
    (failed : nativeSupply newer older ref atRead = .error error reached)
    (kept : OutputFrame (fun w => (front w, inputs w)) path) :
    writer reached = writer atRead ∧
    ∃ after, buildMergedFileSynced newer older path layout options before = .error error after ∧
      inputs after = inputs atRead ∧ front after = front reached ∧
      (nativeWriterOps.remove path reached = .ok () after ∨
        ∃ cleanupError, nativeWriterOps.remove path reached = .error cleanupError after) := by
  have step := nativeNext_refines cell newInput.cursor oldInput.cursor atRead
  rw [show effect (next Entry.key (tablePullIO newer) (tablePullIO older) (nativeSlot ref)) atRead =
    .error error reached from failed] at step
  obtain ⟨after, primary, frame, cleanup⟩ :=
    buildMergedFileSynced_cleanup allocated opened valid targets stages failed kept
  exact ⟨congrArg Prod.snd step.1, after, primary,
    (congrArg Prod.snd frame).trans (congrArg Prod.fst step.1), congrArg Prod.fst frame, cleanup⟩

end SortedRun
