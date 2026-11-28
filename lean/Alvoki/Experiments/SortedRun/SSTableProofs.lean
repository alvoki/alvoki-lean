import Alvoki.Experiments.SortedRun.Proofs
import Alvoki.Experiments.SortedRun.SSTable
import Alvoki.Experiments.SSTable.Proofs.UnifiedNativeEndToEnd
import Alvoki.Experiments.SSTable.Proofs.Typed
import Alvoki.Experiments.SSTable.Proofs.UnifiedReadErrors

namespace SortedRun

open ImmutableSSTable ImmutableSSTable.Unified

private theorem indexed_exact {indexed : Nat → EStateM String σ (Option (row × Nat))}
    {rows : List row}
    (observed : ∀ i, indexed i = pure
      (if h : i < rows.length then some (rows[i], i + 1) else none)) :
    Pull.Exact indexed rows.drop := by
  intro i start item reached ran
  rw [observed] at ran
  by_cases inside : i < rows.length
  · rw [dite_eq_left inside] at ran
    cases ran
    exact (List.drop_eq_getElem_cons inside).symm
  · rw [dite_eq_right inside] at ran
    cases ran
    exact (List.drop_eq_nil_of_le (Nat.le_of_not_gt inside)).symm

theorem table_next_exact {table : Table (EStateM String σ)} {rows : List Entry}
    (represented : table.Represents rows) : Pull.Exact table.next rows.drop :=
  indexed_exact represented.next

theorem typed_next_exact [DecidableEq key] {table : TypedTable (EStateM String σ) key value}
    {less : key → key → Prop} {rows : List (key × value)}
    (represented : table.Represents less rows) : Pull.Exact table.next rows.drop :=
  indexed_exact represented.next

/-- A decode error on the typed reader's required next row reaches the
same merge callback unchanged. The unread cursor stays at that row. -/
theorem next_typed_value_error [LT key] [DecidableLT key]
    {table : TypedTable (EStateM String σ) key value}
    {older : Pull (EStateM String σ) right (key × value)}
    {other : Front right (key × value)} {start reached : σ}
    (received : table.table.next index start = .ok (some (row, nextIndex)) reached)
    (decoded : table.keyCodec.decode row.key = .ok keyValue)
    (failed : table.valueCodec.decode row.value = .error message) :
    let front : Frontier Nat right (key × value) := ⟨.unread index, other⟩
    next Prod.fst (liftPull table.next) (liftPull older) effectSlot (front, start) =
      .error message (front, reached) := by
  dsimp only
  rw [next_effect]
  simp [Front.fill, TypedTable.next_value_decode_error received decoded failed]

/-- Output operations leave the merge frontier alone, including on error. -/
def liftOutput (ops : OutputOps (EStateM String σ) handle) :
    OutputOps (EStateM String (frontier × σ)) handle where
  openFile path mode := liftEffect (ops.openFile path mode)
  append held bytes := liftEffect (ops.append held bytes)
  flush held := liftEffect (ops.flush held)
  sync held := liftEffect (ops.sync held)
  remove path := liftEffect (ops.remove path)

private def observeWriter [LT key] [DecidableLT key] (keyOf : row → key)
    (encode : row → Entry) (newRows : left → List row) (oldRows : right → List row)
    (state : EffectState left right row (NativeWriteState handle inode)) :
    NativeWriteState handle inode :=
  { state.2 with rows := (state.1.remaining keyOf newRows oldRows).map encode }

private theorem mergeEffects [LT key] [DecidableLT key]
    (keyOf : row → key) (encode : row → Entry)
    {newer : Pull (NativeWriteM handle inode) left row}
    {older : Pull (NativeWriteM handle inode) right row}
    {newRows : left → List row} {oldRows : right → List row}
    {ops : OutputOps (NativeWriteM handle inode) handle} {path : System.FilePath}
    (output : NativeWritePrimitivesOn id ops path)
    (newExact : newer.Exact newRows) (oldExact : older.Exact oldRows)
    (newFrame : ∀ pos s item t, newer pos s = .ok item t → t = s)
    (oldFrame : ∀ pos s item t, older pos s = .ok item t → t = s) :
    NativeWriteEffectsOn (observeWriter keyOf encode newRows oldRows) (liftOutput ops) path
      (Option.map encode <$> next keyOf (liftPull newer) (liftPull older) effectSlot) := by
  constructor
  · constructor
    · intro before after held ran
      obtain ⟨front, act⟩ := liftEffect_ok ran
      obtain ⟨fresh, identity, updated⟩ := output.create before.2 after.2 held act
      change after.2 = _ at updated
      exact ⟨fresh, identity, by simp [observeWriter, front, updated]⟩
    · intro held identity bytes before after bound ran
      obtain ⟨front, act⟩ := liftEffect_ok ran
      have updated := output.append held identity bytes before.2 after.2 bound act
      change after.2 = _ at updated
      simp [observeWriter, front, updated]
    · intro held identity before after bound ran
      obtain ⟨front, act⟩ := liftEffect_ok ran
      have updated := output.flush held identity before.2 after.2 bound act
      change after.2 = _ at updated
      simp [observeWriter, front, updated]
    · intro held identity before after bound flushed ran
      obtain ⟨front, act⟩ := liftEffect_ok ran
      have updated := output.sync held identity before.2 after.2 bound flushed act
      change after.2 = _ at updated
      simp [observeWriter, front, updated]
  · intro held identity before after item _ ran
    cases before with
    | mk front start =>
      cases action : next keyOf (liftPull newer) (liftPull older) effectSlot (front, start) with
      | error =>
        simp [EStateM.run, Functor.map, EStateM.map, action] at ran
      | ok row reached =>
        simp [EStateM.run, Functor.map, EStateM.map, action] at ran
        obtain ⟨rfl, rfl⟩ := ran
        have facts := (next_exact keyOf newExact oldExact action).1
        have frame := next_preserves keyOf id newFrame oldFrame action
        change reached.2 = start at frame
        constructor
        · simp [observeWriter, facts.1, List.head?_map]
        · simp [observeWriter, frame, facts.2, List.map_tail]

/-- The real merge callback supplies one head and its tail to the existing
streaming writer model on every successful call. The synced image represents
the full merge, including opaque values. Each input ends at the actual EOF
callback of the successful builder. -/
theorem buildMergedWith_refines [LT key] [DecidableLT key]
    (keyOf : row → key) (encode : row → Entry)
    {newer : Pull (NativeWriteM handle inode) left row}
    {older : Pull (NativeWriteM handle inode) right row}
    {newRows : left → List row} {oldRows : right → List row}
    {ops : OutputOps (NativeWriteM handle inode) handle} {path : System.FilePath}
    {crc : Checksum} {layout : Layout} {options : BuildOptions}
    {before after : EffectState left right row (NativeWriteState handle inode)} {count : Nat}
    (output : NativeWritePrimitivesOn id ops path)
    (newExact : newer.Exact newRows) (oldExact : older.Exact oldRows)
    (newFrame : ∀ pos s item t, newer pos s = .ok item t → t = s)
    (oldFrame : ∀ pos s item t, older pos s = .ok item t → t = s)
    (built : buildMergedWith keyOf encode (liftPull newer) (liftPull older) effectSlot
      (liftOutput ops) crc path layout id options before = .ok count after) :
    let rows := (before.1.remaining keyOf newRows oldRows).map encode
    count = rows.length ∧ Image crc layout rows after.2.appended ∧
    (∃ held identity, after.2.BoundTo path held identity ∧
      after.2.durable = some (identity, after.2.appended)) ∧
    (∃ atEOF consumed : EffectState left right row (NativeWriteState handle inode),
      next keyOf (liftPull newer) (liftPull older) effectSlot atEOF = .ok none consumed ∧
      atEOF.1.newer.remaining newRows = [] ∧ atEOF.1.older.remaining oldRows = []) := by
  have effects := mergeEffects keyOf encode output newExact oldExact newFrame oldFrame
  obtain ⟨_, countEq, image, held, identity, bound, _, synced, _⟩ :=
    buildFileWith_refines_on effects built
  obtain ⟨atEOF, consumed, eof⟩ := buildFileWith_eof built
  have empty : next keyOf (liftPull newer) (liftPull older) effectSlot atEOF = .ok none consumed := by
    cases read : next keyOf (liftPull newer) (liftPull older) effectSlot atEOF <;>
      simp_all [Functor.map, EStateM.map, Option.map_eq_none_iff]
  have exhausted := (next_exact keyOf newExact oldExact empty).2.1 rfl
  exact ⟨countEq, image, ⟨held, identity, bound, synced⟩, atEOF, consumed, empty, exhausted⟩

private theorem table_frame {table : Table (NativeWriteM handle inode)} {rows : List Entry}
    (represented : table.Represents rows) :
    ∀ pos s item t, table.next pos s = .ok item t → t = s := by
  intro pos s item t ran
  rw [represented.next] at ran
  cases ran
  rfl

/-- An independent checked reopen of the descriptor selected by the caller
observes the exact rows supplied by the two checked input tables. The
primitive observations never assume a merge result or a completed write. -/
theorem buildMergedWith_open_represents [DecidableEq inode]
    {newer older : Table (NativeWriteM handle inode)} {newRows oldRows : List Entry}
    {ops : OutputOps (NativeWriteM handle inode) handle} {path readPath : System.FilePath}
    {crc : Checksum} {layout : Layout} {options : BuildOptions}
    {start : NativeWriteState handle inode}
    {written : EffectState Nat Nat Entry (NativeWriteState handle inode)} {count : Nat}
    {acquire : System.FilePath → IO.FS.Mode → EStateM String σ reader}
    {before opened : σ} {held : reader} {inodeAt : reader → Option inode}
    (newTable : newer.Represents newRows) (oldTable : older.Represents oldRows)
    (output : NativeWritePrimitivesOn id ops path)
    (built : buildMergedWith Entry.key id (liftPull newer.next) (liftPull older.next) effectSlot
      (liftOutput ops) crc path layout id options (Frontier.start 0 0, start) = .ok count written)
    (acquired : acquire readPath .read before = .ok held opened)
    (selected : ∀ output identity, written.2.BoundTo path output identity →
      inodeAt held = some identity) :
    count = (merge Entry.key newRows oldRows).length ∧
    ∃ table, openCheckedWith ((written.2.readSnapshot inodeAt).primitives acquire)
      crc readPath layout.tableId before = .ok table opened ∧
      table.Represents (merge Entry.key newRows oldRows) := by
  obtain ⟨countEq, image, ⟨outputHandle, identity, bound, durable⟩, _⟩ :=
    buildMergedWith_refines Entry.key id output
      (table_next_exact newTable) (table_next_exact oldTable)
      (table_frame newTable) (table_frame oldTable) built
  simp [Frontier.remaining, Frontier.start, Front.remaining] at countEq image
  have contents : (written.2.readSnapshot inodeAt).contents identity = some written.2.appended := by
    simp [NativeWriteState.readSnapshot, durable]
  have observed := (written.2.readSnapshot inodeAt).readsExactly acquire
    (selected outputHandle identity bound) contents image.extent
  obtain ⟨table, checked, represents⟩ := image.openCheckedWith_represents_at acquired observed
  exact ⟨countEq, table, checked, represents⟩

/-- Execute the checked-open schedule for each immutable input, then connect
those exact handles to the merge, synced write and checked reopen. The path
and descriptor premises are at acquisition, and the read and write premises
are at reached primitives. -/
theorem checkedInputs_merge_checkedOutput [DecidableEq inode]
    {input : ReadPrimitives (NativeWriteM handle inode) inputHandle}
    {newPath oldPath path readPath : System.FilePath}
    {newLayout oldLayout layout : Layout} {crc : Checksum} {options : BuildOptions}
    {newRows oldRows : List Entry} {newBytes oldBytes : ByteArray}
    {initial afterNew ready : NativeWriteState handle inode}
    {newHandle oldHandle : inputHandle}
    {ops : OutputOps (NativeWriteM handle inode) handle}
    {acquire : System.FilePath → IO.FS.Mode →
      EStateM String (EffectState Nat Nat Entry (NativeWriteState handle inode)) reader}
    {inodeAt : reader → Option inode}
    (newImage : Image crc newLayout newRows newBytes)
    (oldImage : Image crc oldLayout oldRows oldBytes)
    (newAcquired : input.openFile newPath .read initial = .ok newHandle afterNew)
    (oldAcquired : input.openFile oldPath .read afterNew = .ok oldHandle ready)
    (newRead : input.ReadsExactly newHandle newBytes)
    (oldRead : input.ReadsExactly oldHandle oldBytes)
    (output : NativeWritePrimitivesOn id ops path) :
    ∃ newer older, openCheckedWith input crc newPath newLayout.tableId initial = .ok newer afterNew ∧
      openCheckedWith input crc oldPath oldLayout.tableId afterNew = .ok older ready ∧
      ∀ written count reopened held,
        buildMergedWith Entry.key id (liftPull newer.next) (liftPull older.next) effectSlot
          (liftOutput ops) crc path layout id options (Frontier.start 0 0, ready) =
            .ok count written →
        acquire readPath .read written = .ok held reopened →
        (∀ output identity, written.2.BoundTo path output identity → inodeAt held = some identity) →
        count = (merge Entry.key newRows oldRows).length ∧
        ∃ table, openCheckedWith ((written.2.readSnapshot inodeAt).primitives acquire)
          crc readPath layout.tableId written = .ok table reopened ∧
          table.Represents (merge Entry.key newRows oldRows) := by
  obtain ⟨newer, checkedNew, newTable⟩ := newImage.openCheckedWith_represents_at newAcquired newRead
  obtain ⟨older, checkedOld, oldTable⟩ := oldImage.openCheckedWith_represents_at oldAcquired oldRead
  refine ⟨newer, older, checkedNew, checkedOld, ?_⟩
  intro written count reopened held built acquired selected
  exact buildMergedWith_open_represents newTable oldTable output built acquired selected

end SortedRun
