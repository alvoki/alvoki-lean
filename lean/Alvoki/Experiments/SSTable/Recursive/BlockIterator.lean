import Alvoki.Experiments.SSTable.Recursive.Image

namespace ImmutableSSTable.Recursive

open Unified (Ref Data findRef)

namespace BlockIterator

structure Frame where private mk ::
  ref : Ref
  childHeight : Nat
  children : Array Ref

structure Block where private mk ::
  ref : Ref
  data : Data

/-- A checked data packet and the checked index pages leading to it, nearest first.
The root is already retained by the handle. -/
structure Position where private mk ::
  block : Block
  path : List Frame

def contains (ref : Ref) (index : Nat) : Bool :=
  decide (ref.firstRow ≤ index ∧ index < ref.firstRow + ref.count)

def Position.read [Monad m] [MonadExceptOf String m] (position : Position)
    (index : Nat) : m Entry :=
  liftDecode (position.block.data.readRow (index - position.block.ref.firstRow))

def descend [Monad m] [MonadExceptOf String m] (handle : Handle m)
    (before : Ref → Bool) (ref : Ref) (parentOffset : Nat) (path : List Frame) :
    Nat → m Position
  | 0 => do
    let data ← handle.readData ref parentOffset
    return ⟨⟨ref, data⟩, path⟩
  | height + 1 => do
    let raw ← readIndexPacket handle.source handle.crc handle.layout.tableId
      (height + 1) ref parentOffset
    let children ← liftDecode (pageChildren raw ref true)
    let some child := findRef children before | throw "invalid SSTable child range"
    descend handle before child ref.offset (⟨ref, height, children⟩ :: path) height

def fromRoot [Monad m] [MonadExceptOf String m] (handle : Handle m)
    (before : Ref → Bool) (child : Ref) : m Position :=
  descend handle before child handle.rootOffset [] (handle.height - 1)

def atBoundary [Monad m] [MonadExceptOf String m] (handle : Handle m) (index : Nat) :
    List Frame → m Position
  | [] => do
    let before := fun ref : Ref => decide (ref.firstRow + ref.count ≤ index)
    let some child := findRef handle.root before | throw "invalid SSTable root row range"
    fromRoot handle before child
  | frame :: rest => do
    if contains frame.ref index then
      let before := fun ref : Ref => decide (ref.firstRow + ref.count ≤ index)
      let some child := findRef frame.children before | throw "invalid SSTable child range"
      descend handle before child frame.ref.offset (frame :: rest) frame.childHeight
    else
      atBoundary handle index rest

end BlockIterator

open BlockIterator (Position atBoundary contains fromRoot)

/-- A pull cursor binds the checked handle, next row ordinal, and optional cached packets. -/
structure BlockCursor (m : Type → Type) where private mk ::
  handle : Handle m
  index : Nat
  position : Option Position

def Handle.cursorAt (handle : Handle m) (index : Nat) : BlockCursor m :=
  ⟨handle, index, none⟩

/-- Start at the first row whose key is at least the target, retaining the path
and data block used by seek. -/
def Handle.seekCursor [Monad m] [MonadExceptOf String m] (handle : Handle m)
    (key : ByteArray) : m (BlockCursor m) := do
  let before := fun ref : Ref => decide (ref.lastKey < key)
  let some child := findRef handle.root before | return handle.cursorAt handle.rowCount
  let position ← fromRoot handle before child
  let block := position.block
  let index ← seekBetween (fun i => liftDecode (block.data.readRow i)) key 0 block.ref.count
  unless index < block.ref.count do throw "invalid SSTable data fence"
  return ⟨handle, block.ref.firstRow + index, some position⟩

def BlockCursor.prepare [Monad m] [MonadExceptOf String m] (cursor : BlockCursor m) :
    m Position :=
  match cursor.position with
  | none => atBoundary cursor.handle cursor.index []
  | some position =>
    if contains position.block.ref cursor.index then pure position
    else atBoundary cursor.handle cursor.index position.path

def BlockCursor.pull [Monad m] [MonadExceptOf String m] (cursor : BlockCursor m) :
    m (Option (Entry × BlockCursor m)) := do
  if cursor.handle.rowCount ≤ cursor.index then return none
  let position ← cursor.prepare
  let row ← position.read cursor.index
  return some (row, ⟨cursor.handle, cursor.index + 1, some position⟩)

open Unified (RefCovers)

namespace BlockIterator

structure Frame.Observes (frame : Frame) (handle : Handle m)
    (image : ByteArray) (rows : List Entry) : Prop where
  coverage : RefCovers rows frame.ref.firstRow frame.ref.count frame.children
  children : ∀ child ∈ frame.children.toList,
    TreeInImage handle.layout handle.crc image rows child frame.ref.offset true frame.childHeight

def PathObserves (path : List Frame) (handle : Handle m)
    (image : ByteArray) (rows : List Entry) : Prop :=
  ∀ frame ∈ path, Frame.Observes frame handle image rows

structure Position.Observes (position : Position) (handle : Handle m)
    (image : ByteArray) (rows : List Entry) : Prop where
  extent : position.block.ref.firstRow + position.block.ref.count ≤ rows.length
  exactRow : ∀ i, i < position.block.ref.count →
    position.block.data.readRow i = .ok (rowAt rows (position.block.ref.firstRow + i))
  path : PathObserves position.path handle image rows

theorem Position.Observes.read [Monad m] [MonadExceptOf String m] {handle : Handle m} {position : Position}
    (observed : position.Observes handle image rows)
    (inside : contains position.block.ref index = true) :
    position.read (m := m) index = pure (rowAt rows index) := by
  have ⟨lo, hi⟩ := of_decide_eq_true inside
  have localIndex := observed.exactRow (index - position.block.ref.firstRow) (by omega)
  rw [Nat.add_sub_of_le lo] at localIndex
  simp [Position.read, localIndex, liftDecode]

theorem descend_observes [Monad m] [LawfulMonad m] [MonadExceptOf String m] {handle : Handle m}
    (observed : handle.Observes image rows) (route : Routes rows index before)
    (tree : TreeInImage handle.layout handle.crc image rows ref parent true height)
    (pathOk : PathObserves path handle image rows)
    (lo : ref.firstRow ≤ index) (hi : index < ref.firstRow + ref.count) :
    ∃ position, descend handle before ref parent path height = pure position ∧
      contains position.block.ref index = true ∧ position.Observes handle image rows := by
  induction height generalizing ref parent path with
  | zero =>
    obtain ⟨block, read, exactRows⟩ := tree.read observed.serves observed.valid
    exact ⟨⟨⟨ref, block⟩, path⟩, by simp [descend, read],
      decide_eq_true ⟨lo, hi⟩, ⟨tree.rowExtent, exactRows, pathOk⟩⟩
  | succ depth ih =>
    obtain ⟨children, node, below⟩ := tree
    obtain ⟨child, member, picked, start, stop⟩ := route node.coverage lo hi
    have keep : PathObserves (⟨ref, depth, children⟩ :: path) handle image rows := by
      intro frame mem
      rcases List.mem_cons.mp mem with rfl | rest
      · exact ⟨node.coverage, below⟩
      · exact pathOk frame rest
    obtain ⟨position, ran, inside, sees⟩ := ih (below child member) keep start stop
    refine ⟨position, ?_, inside, sees⟩
    simp [descend, node.packet.read observed.serves, node.checked, liftDecode, picked, ran]

theorem fromRoot_observes [Monad m] [LawfulMonad m] [MonadExceptOf String m] {handle : Handle m}
    (observed : handle.Observes image rows) (route : Routes rows index before)
    (inside : index < rows.length) :
    ∃ child position, findRef handle.root before = some child ∧
      fromRoot handle before child = pure position ∧ contains position.block.ref index = true ∧
      position.Observes handle image rows := by
  obtain ⟨child, member, picked, lo, hi⟩ := route observed.root (Nat.zero_le _) (by simpa)
  obtain ⟨position, ran, within, sees⟩ := descend_observes observed route
    (observed.children child member) (path := []) (by simp [PathObserves]) lo hi
  exact ⟨child, position, picked, ran, within, sees⟩

theorem atBoundary_observes [Monad m] [LawfulMonad m] [MonadExceptOf String m] {handle : Handle m}
    (observed : handle.Observes image rows) (pathOk : PathObserves path handle image rows)
    (inside : index < rows.length) :
    ∃ position, atBoundary handle index path = pure position ∧
      contains position.block.ref index = true ∧ position.Observes handle image rows := by
  have route : Routes rows index (fun ref => decide (ref.firstRow + ref.count ≤ index)) :=
    Routes.cursor rows index
  induction path with
  | nil =>
    obtain ⟨child, position, picked, ran, within, sees⟩ := fromRoot_observes observed route inside
    exact ⟨position, by simp [atBoundary, picked, ran], within, sees⟩
  | cons frame rest ih =>
    cases within : contains frame.ref index with
    | false =>
      obtain ⟨position, ran, insideBlock, sees⟩ := ih (fun frame mem =>
        pathOk frame (List.mem_cons_of_mem _ mem))
      exact ⟨position, by simp [atBoundary, within, ran], insideBlock, sees⟩
    | true =>
      have frameOk := pathOk frame (by simp)
      obtain ⟨child, member, picked, start, stop⟩ :=
        route frameOk.coverage (of_decide_eq_true within).1 (of_decide_eq_true within).2
      obtain ⟨position, ran, insideBlock, sees⟩ := descend_observes observed route
        (frameOk.children child member) pathOk start stop
      exact ⟨position, by simp [atBoundary, within, picked, ran], insideBlock, sees⟩

end BlockIterator

open BlockIterator (contains)

/-- The cursor's remaining sequence is the logical suffix at its ordinal.
Cached packets refine the same exact image as its checked handle. -/
structure BlockCursor.Observes [Monad m] (cursor : BlockCursor m)
    (image : ByteArray) (rows : List Entry) : Prop where
  handle : cursor.handle.Observes image rows
  cache : ∀ position, cursor.position = some position →
    position.Observes cursor.handle image rows

theorem Handle.cursorAt_observes [Monad m] {handle : Handle m}
    (observed : handle.Observes image rows) (index : Nat) :
    (handle.cursorAt index).Observes image rows :=
  ⟨observed, by simp [Handle.cursorAt]⟩

theorem BlockCursor.Observes.prepare [Monad m] [LawfulMonad m] [MonadExceptOf String m]
    {cursor : BlockCursor m} (observed : cursor.Observes image rows)
    (inTable : cursor.index < rows.length) :
    ∃ position, cursor.prepare = pure position ∧ contains position.block.ref cursor.index = true ∧
      position.Observes cursor.handle image rows := by
  cases cached : cursor.position with
  | none =>
    simpa [BlockCursor.prepare, cached] using BlockIterator.atBoundary_observes observed.handle
      (path := []) (by simp [BlockIterator.PathObserves]) inTable
  | some position =>
    have exactPosition := observed.cache position cached
    cases inside : contains position.block.ref cursor.index with
    | false =>
      simpa [BlockCursor.prepare, cached, inside] using
        BlockIterator.atBoundary_observes observed.handle exactPosition.path inTable
    | true =>
      exact ⟨position, by simp [BlockCursor.prepare, cached, inside], inside, exactPosition⟩

/-- A healthy successful pull advances by exactly one row. EOF is a pure result,
including for a cursor started at an arbitrary ordinal beyond the table. -/
theorem BlockCursor.Observes.pull [Monad m] [LawfulMonad m] [MonadExceptOf String m]
    {cursor : BlockCursor m} (observed : cursor.Observes image rows) :
    match rows.drop cursor.index with
    | [] => cursor.pull = pure none
    | row :: rest => ∃ next, cursor.pull = pure (some (row, next)) ∧
        next.Observes image rows ∧ next.index = cursor.index + 1 ∧ rows.drop next.index = rest := by
  by_cases inTable : cursor.index < rows.length
  · obtain ⟨position, prepared, inside, exactPosition⟩ := observed.prepare inTable
    have row := exactPosition.read (m := m) inside
    have drop : rows.drop cursor.index =
        rowAt rows cursor.index :: rows.drop (cursor.index + 1) := by
      rw [rowAt_eq inTable, List.drop_eq_getElem_cons inTable]
    rw [drop]
    refine ⟨⟨cursor.handle, cursor.index + 1, some position⟩, ?_, ?_, rfl, rfl⟩
    · simp [BlockCursor.pull, observed.handle.count, Nat.not_le_of_gt inTable, prepared, row]
    · exact ⟨observed.handle, by simpa using exactPosition⟩
  · have endAt := Nat.le_of_not_gt inTable
    simp [List.drop_eq_nil_of_le endAt, BlockCursor.pull, observed.handle.count, endAt]

theorem BlockCursor.pull_cached [Monad m] [LawfulMonad m] [MonadExceptOf String m]
    {cursor : BlockCursor m} {position : BlockIterator.Position}
    (cached : cursor.position = some position)
    (inTable : cursor.index < cursor.handle.rowCount)
    (inside : contains position.block.ref cursor.index = true) :
    cursor.pull = (do
      let row ← position.read cursor.index
      pure (some (row, ⟨cursor.handle, cursor.index + 1, some position⟩))) := by
  simp [BlockCursor.pull, BlockCursor.prepare, cached, inside, Nat.not_le_of_gt inTable]

theorem Handle.Observes.seekCursor [Monad m] [LawfulMonad m] [MonadExceptOf String m]
    {handle : Handle m} (observed : handle.Observes image rows)
    (lower : LowerBound (fun i => (rowAt rows i).key) rows.length key index) :
    ∃ cursor, handle.seekCursor key = pure cursor ∧ cursor.index = index ∧
      cursor.Observes image rows := by
  by_cases inTable : index < rows.length
  · obtain ⟨child, position, picked, ready, within, positionOk⟩ :=
      BlockIterator.fromRoot_observes observed (Routes.key lower) inTable
    obtain ⟨lo, hi⟩ := of_decide_eq_true within
    have sought := Unified.seek_local (m := m) positionOk.exactRow lower lo hi positionOk.extent
    have valid : index - position.block.ref.firstRow < position.block.ref.count := by omega
    refine ⟨⟨handle, position.block.ref.firstRow + (index - position.block.ref.firstRow),
      some position⟩, ?_, Nat.add_sub_of_le lo, ⟨observed, by simpa using positionOk⟩⟩
    simp [Handle.seekCursor, picked, ready, sought, valid]
  · have atEnd : index = rows.length := by have := lower.1; omega
    subst index
    exact ⟨handle.cursorAt handle.rowCount, by simp [Handle.seekCursor, observed.root.noKey lower],
      observed.count, Handle.cursorAt_observes observed _⟩

end ImmutableSSTable.Recursive
