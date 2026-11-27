import Alvoki.Experiments.SSTable.UnifiedBuilder
import Alvoki.Experiments.SSTable.Proofs.UnifiedImage

namespace ImmutableSSTable.Unified

open Std

structure ModelFile where
  rows : List Entry
  bytes : ByteArray := .empty

abbrev ModelM := StateT ModelFile (Except String)

def modelSink : Sink ModelM where
  write bytes := fun file => .ok ((), { file with bytes := file.bytes ++ bytes })
  flush := pure ()

def modelNext : ModelM (Option Entry) := fun file =>
  match file.rows with
  | [] => .ok (none, file)
  | row :: rows => .ok (some row, { file with rows })

/-- Run the production streaming writer with an in-memory append sink and a
finite row supplier. Successful writes retain the exact bytes passed to the sink. -/
def modelBuild (crc : Checksum) (layout : Layout) (rows : List Entry)
    (options : BuildOptions := {}) : Except String (Nat × ByteArray) := do
  let (count, file) ← (buildStream crc layout modelSink modelNext id options).run { rows }
  return (count, file.bytes)

def modelWriter (crc : Checksum) (layout : Layout) (options : BuildOptions) :
    Writer ModelM String :=
  ⟨crc, layout, modelSink, id, options⟩

private theorem model_bind_ok {a : ModelM α} {b : α → ModelM β}
    {file out : ModelFile} {result : β}
    (run : (a >>= b).run file = .ok (result, out)) :
    ∃ value mid, a.run file = .ok (value, mid) ∧ (b value).run mid = .ok (result, out) := by
  cases step : a.run file with
  | error error =>
    change ((a.run file).bind _) = _ at run
    rw [step] at run
    cases run
  | ok value =>
    obtain ⟨value, mid⟩ := value
    exact ⟨value, mid, rfl, by
      change ((a.run file).bind _) = _ at run
      rw [step] at run
      exact run⟩

private theorem model_pure_ok {value result : α} {file out : ModelFile}
    (run : (pure value : ModelM α).run file = .ok (result, out)) :
    result = value ∧ out = file := by
  change Except.ok (value, file) = .ok (result, out) at run
  cases run
  exact ⟨rfl, rfl⟩

private theorem PacketAt.append {crc : Checksum} {id kind : UInt64} {image : ByteArray}
    {offset size : Nat} {body : ByteArray}
    (packet : PacketAt crc id kind image offset size body) (extra : ByteArray) :
    PacketAt crc id kind (image ++ extra) offset size body := by
  refine ⟨packet.size_eq, packet.bounded, ?_, ?_⟩
  · simpa using Nat.le_trans packet.extent (Nat.le_add_right image.size extra.size)
  · rw [ByteArray.extract_append]
    rw [Nat.sub_eq_zero_of_le packet.extent, packet.slice]
    have empty : extra.extract (offset - image.size) 0 = ByteArray.empty :=
      ByteArray.extract_eq_empty_iff.mpr (by simp)
    simp [empty]

private theorem LeafGroup.InImage.append {layout : Layout} {crc : Checksum} {image : ByteArray}
    {leaf : LeafGroup} (valid : leaf.InImage layout crc image) (extra : ByteArray) :
    leaf.InImage layout crc (image ++ extra) :=
  { valid with
    packet := valid.packet.append extra
    blocks := fun block member =>
      let existing := valid.blocks block member
      { existing with packet := existing.packet.append extra } }

private theorem PacketAt.atEnd (crc : Checksum) (id kind : UInt64) (image body : ByteArray)
    (bounded : body.size + checksumSize ≤ maxRowSize) :
    PacketAt crc id kind (image ++ encodePacket crc id kind image.size body)
      image.size (body.size + checksumSize) body := by
  refine ⟨rfl, bounded, by simp, ?_⟩
  exact ByteArray.extract_append_eq_right rfl (by rw [encodePacket_size])

private theorem writePacket_ok {crc : Checksum} {layout : Layout} {options : BuildOptions}
    {kind : UInt64} {body : ByteArray} {file out : ModelFile} {stop : Nat}
    (run : ((modelWriter crc layout options).writePacket kind file.bytes.size body).run file =
      .ok (stop, out)) :
    out = { file with
      bytes := file.bytes ++ encodePacket crc layout.tableId kind file.bytes.size body } ∧
    stop = file.bytes.size + (body.size + checksumSize) ∧
    body.size + checksumSize ≤ maxRowSize ∧ stop + footerPacketSize ≤ maxFileSize := by
  by_cases packet : body.size + checksumSize ≤ maxRowSize
  · by_cases extent : file.bytes.size + (body.size + checksumSize) + footerPacketSize ≤ maxFileSize
    · simp only [Writer.writePacket, packet, extent, ↓reduceIte] at run
      change Except.ok (file.bytes.size + (body.size + checksumSize), { file with
        bytes := file.bytes ++ encodePacket crc layout.tableId kind file.bytes.size body }) =
          .ok (stop, out) at run
      cases run
      exact ⟨rfl, rfl, packet, extent⟩
    · simp only [Writer.writePacket, packet, extent, ↓reduceIte] at run
      change Except.error "SSTable file exceeds signed offset limit" = .ok (stop, out) at run
      cases run
  · simp only [Writer.writePacket, packet, ↓reduceIte] at run
    change Except.error "SSTable packet exceeds size limit" = .ok (stop, out) at run
    cases run

private def blocksRows (blocks : Array DataGroup) : List Entry :=
  blocks.toList.flatMap (·.rows.toList)

private def leavesRows (leaves : Array LeafGroup) : List Entry :=
  leaves.toList.flatMap LeafGroup.rows

private theorem blocksRows_push (blocks : Array DataGroup) (group : DataGroup) :
    blocksRows (blocks.push group) = blocksRows blocks ++ group.rows.toList := by
  simp [blocksRows]

private theorem leavesRows_push (leaves : Array LeafGroup) (group : LeafGroup) :
    leavesRows (leaves.push group) = leavesRows leaves ++ LeafGroup.rows group := by
  simp [leavesRows]

private theorem Array.back_mem_list {xs : Array α} {x : α} (back : xs.back? = some x) :
    x ∈ xs.toList := by
  rw [← Array.getLast?_toList] at back
  obtain ⟨earlier, contents⟩ := List.getLast?_eq_some_iff.mp back
  simp [contents]

private theorem DataGroup.fence_mem {layout : Layout} {crc : Checksum} {image : ByteArray}
    {group : DataGroup} (inImage : group.InImage layout crc image) :
    ∃ row ∈ group.rows.toList, row.key = group.ref.lastKey := by
  cases back : group.rows.back? with
  | none =>
    have key := inImage.lastKey
    simp [back] at key
  | some row =>
    have key := inImage.lastKey
    rw [back] at key
    exact ⟨row, Array.back_mem_list back, Option.some.inj key⟩

private theorem DataGroup.fence_mem_in_blocks {layout : Layout} {crc : Checksum} {image : ByteArray}
    {blocks : Array DataGroup} (inImage : ∀ block ∈ blocks.toList, block.InImage layout crc image)
    {ref : Ref} (back : (blocks.map DataGroup.ref).back? = some ref) :
    ∃ row ∈ blocksRows blocks, row.key = ref.lastKey := by
  rw [Array.back?_map] at back
  cases block : blocks.back? with
  | none => simp [block] at back
  | some group =>
    rw [block] at back
    have same : group.ref = ref := Option.some.inj back
    subst ref
    have member := Array.back_mem_list block
    obtain ⟨row, found, key⟩ := DataGroup.fence_mem (inImage group member)
    exact ⟨row, List.mem_flatMap.mpr ⟨group, member, found⟩, key⟩

private theorem LeafGroup.fence_mem {layout : Layout} {crc : Checksum} {image : ByteArray}
    {group : LeafGroup} (inImage : group.InImage layout crc image) :
    ∃ row ∈ group.rows, row.key = group.ref.lastKey := by
  cases back : (group.blocks.map DataGroup.ref).back? with
  | none =>
    have key := inImage.lastKey
    simp [back] at key
  | some ref =>
    have key := inImage.lastKey
    rw [back] at key
    obtain ⟨row, member, same⟩ := DataGroup.fence_mem_in_blocks inImage.blocks back
    exact ⟨row, member, same.trans (Option.some.inj key)⟩

private theorem LeafGroup.fence_mem_in_leaves {layout : Layout} {crc : Checksum} {image : ByteArray}
    {leaves : Array LeafGroup} (inImage : ∀ leaf ∈ leaves.toList, leaf.InImage layout crc image)
    {ref : Ref} (back : (leaves.map LeafGroup.ref).back? = some ref) :
    ∃ row ∈ leavesRows leaves, row.key = ref.lastKey := by
  rw [Array.back?_map] at back
  cases leaf : leaves.back? with
  | none => simp [leaf] at back
  | some group =>
    rw [leaf] at back
    have same : group.ref = ref := Option.some.inj back
    subst ref
    have member := Array.back_mem_list leaf
    obtain ⟨row, found, key⟩ := LeafGroup.fence_mem (inImage group member)
    exact ⟨row, List.mem_flatMap.mpr ⟨group, member, found⟩, key⟩

private theorem refsAfter_push {refs : List Ref} {prev : Option Ref} {ref : Ref}
    (valid : ValidRefsAfter prev refs) (entry : ref.Valid)
    (follows : ∀ earlier ∈ refs.getLast?.or prev, earlier.Precedes ref) :
    ValidRefsAfter prev (refs ++ [ref]) := by
  induction refs generalizing prev with
  | nil => exact ⟨entry, follows, trivial⟩
  | cons first rest ih =>
    refine ⟨valid.1, valid.2.1, ih valid.2.2 ?_⟩
    cases rest with
    | nil => simpa using follows
    | cons head tail =>
      cases back : (head :: tail).getLast? with
      | none => simp at back
      | some last => simpa [back] using follows

private structure Directory (bytes first count : Nat) (refs : Array Ref) : Prop where
  adjacent : ValidRefsAfter none refs.toList
  start : ∀ head, refs[0]? = some head → head.firstRow = first
  stop : (refs.back?.map fun last => last.firstRow + last.count).getD first = first + count
  disk : ∀ ref ∈ refs.toList, ref.offset + ref.size ≤ bytes

private theorem Directory.empty (bytes first : Nat) : Directory bytes first 0 #[] := by
  exact ⟨trivial, by simp, by simp, by simp⟩

private theorem Directory.extend {bytes first count endAt : Nat} {refs : Array Ref}
    (dir : Directory bytes first count refs) (grows : bytes ≤ endAt) :
    Directory endAt first count refs :=
  { dir with disk := fun ref member => Nat.le_trans (dir.disk ref member) grows }

private theorem Directory.check {bytes first count : Nat} {refs : Array Ref}
    (dir : Directory bytes first count refs) (nonempty : refs ≠ #[]) :
    checkChildren refs first count bytes = .ok () := by
  have size : 0 < refs.size := Nat.pos_of_ne_zero (fun zero => nonempty (Array.size_eq_zero_iff.mp zero))
  cases start : refs[0]? with
  | none =>
    have atEnd := Array.getElem?_eq_none_iff.mp start
    omega
  | some head =>
    cases stop : refs.back? with
    | none => exact False.elim (nonempty (Array.back?_eq_none_iff.mp stop))
    | some last =>
      have rowStart := dir.start head start
      have rowStop : last.firstRow + last.count = first + count := by simpa [stop] using dir.stop
      have diskStop := dir.disk last (Array.back_mem_list stop)
      simp [checkChildren, start, stop, rowStart, rowStop, diskStop, Pure.pure, Except.pure]

private theorem Directory.push {bytes first count : Nat} {refs : Array Ref} {ref : Ref}
    (dir : Directory bytes first count refs) (valid : ref.Valid)
    (firstRow : ref.firstRow = first + count) (follows : ∀ prev, refs.back? = some prev →
      prev.lastKey < ref.lastKey) (physical : bytes ≤ ref.offset) :
    Directory (ref.offset + ref.size) first (count + ref.count) (refs.push ref) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Array.toList_push]
    apply refsAfter_push dir.adjacent valid
    intro prev present
    have back : refs.back? = some prev := by simpa using present
    have endRow : prev.firstRow + prev.count = first + count := by simpa [back] using dir.stop
    exact ⟨follows prev back, endRow.trans firstRow.symm,
      Nat.le_trans (dir.disk prev (Array.back_mem_list back)) physical⟩
  · intro head atHead
    rw [Array.getElem?_push] at atHead
    by_cases none : refs.size = 0
    · have same : ref = head := by simpa [none] using atHead
      subst head
      have zero : count = 0 := by
        have empty := Array.size_eq_zero_iff.mp none
        simpa [empty] using dir.stop.symm
      omega
    · exact dir.start head (by simpa [Ne.symm none] using atHead)
  · simp [firstRow, Nat.add_assoc]
  · intro entry member
    simp only [Array.toList_push, List.mem_append, List.mem_singleton] at member
    rcases member with inside | rfl
    · exact Nat.le_trans (dir.disk entry inside) (Nat.le_trans physical (Nat.le_add_right _ _))
    · exact Nat.le_refl _

private theorem ordered_across {earlierRows laterRows : List Entry}
    (ordered : Ordered (earlierRows ++ laterRows)) {left right : Entry}
    (earlier : left ∈ earlierRows) (later : right ∈ laterRows) : left.key < right.key :=
  (List.pairwise_append.mp ordered).2.2 left earlier right later

private structure BuilderPrefix (layout : Layout) (crc : Checksum) (rows : List Entry)
    (state : BuilderState) (image : ByteArray)
    (finished : Array LeafGroup) (pending : Array DataGroup) : Prop where
  flattened : leavesRows finished ++ blocksRows pending ++ state.data.toList = rows
  ordered : Ordered rows
  count : state.count = rows.length
  countLimit : state.count ≤ maxFileSize
  last : state.lastKey = rows.getLast?.map Entry.key
  dataFits : ∀ row ∈ state.data.toList, rowFits layout row = true
  offset : state.offset = image.size
  space : image.size + footerPacketSize ≤ maxFileSize
  emptyFile : rows = [] → image.size = 0
  rootRefs : finished.map LeafGroup.ref = state.root
  leafRefs : pending.map DataGroup.ref = state.leaf
  rootDir : Directory image.size 0 (leavesRows finished).length state.root
  leafDir : Directory image.size (leavesRows finished).length (blocksRows pending).length state.leaf
  leaves : ∀ leaf ∈ finished.toList, leaf.InImage layout crc image
  blocks : ∀ block ∈ pending.toList, block.InImage layout crc image

private theorem BuilderPrefix.empty (layout : Layout) (crc : Checksum) :
    BuilderPrefix layout crc [] {} .empty #[] #[] := by
  exact ⟨rfl, List.Pairwise.nil, rfl, by decide, rfl, by simp, rfl, by decide, fun _ => rfl, by simp, by simp,
    Directory.empty 0 0, Directory.empty 0 0, by simp, by simp⟩

private theorem array_head_none {xs : Array α} (none : xs[0]? = none) : xs = #[] := by
  have atEnd := Array.getElem?_eq_none_iff.mp none
  exact Array.size_eq_zero_iff.mp (by omega)

private theorem array_map_empty {f : α → β} {xs : Array α} (empty : xs.map f = #[]) : xs = #[] := by
  apply Array.size_eq_zero_iff.mp
  simpa using congrArg Array.size empty

private theorem array_nonempty_last {xs : Array α} {last : α} (back : xs.back? = some last) :
    0 < xs.size := by
  apply Nat.pos_of_ne_zero
  intro zero
  simp [Array.size_eq_zero_iff.mp zero] at back

private theorem BuilderPrefix.orderParts {layout : Layout} {crc : Checksum} {rows : List Entry}
    {state : BuilderState} {image : ByteArray}
    {finished : Array LeafGroup} {pending : Array DataGroup}
    (valid : BuilderPrefix layout crc rows state image finished pending) :
    Ordered (leavesRows finished ++ (blocksRows pending ++ state.data.toList)) := by
  rw [← List.append_assoc, valid.flattened]
  exact valid.ordered

private theorem flushLeaf_ok {layout : Layout} {crc : Checksum} {options : BuildOptions}
    {rows : List Entry} {state next : BuilderState} {file out : ModelFile}
    {finished : Array LeafGroup} {pending : Array DataGroup}
    (inv : BuilderPrefix layout crc rows state file.bytes finished pending)
    (run : ((modelWriter crc layout options).flushLeaf state).run file = .ok (next, out)) :
    out.rows = file.rows ∧ next.data = state.data ∧
      ∃ groups, BuilderPrefix layout crc rows next out.bytes groups #[] := by
  cases head : state.leaf[0]? with
  | none =>
    have empty := array_head_none head
    have pendingEmpty : pending = #[] := array_map_empty (inv.leafRefs.trans empty)
    subst pending
    simp only [Writer.flushLeaf, head] at run
    obtain ⟨rfl, rfl⟩ := model_pure_ok run
    exact ⟨rfl, rfl, finished, inv⟩
  | some first =>
    cases back : state.leaf.back? with
    | none =>
      have empty := Array.back?_eq_none_iff.mp back
      simp [empty] at head
    | some last =>
      by_cases room : state.rootBytes + indexEntrySize last.lastKey + checksumSize ≤ maxRowSize
      · simp only [Writer.flushLeaf, head, back, room, ↓reduceIte] at run
        obtain ⟨stop, mid, wrote, done⟩ := model_bind_ok run
        obtain ⟨rfl, rfl⟩ := model_pure_ok done
        rw [inv.offset] at wrote
        obtain ⟨rfl, stopSize, packetRoom, extent⟩ := writePacket_ok wrote
        let extra := encodePacket crc layout.tableId 2 file.bytes.size (encodeIndex state.leaf)
        let ref : Ref := ⟨last.lastKey, state.offset, stop - state.offset, first.firstRow,
          last.firstRow + last.count - first.firstRow⟩
        let group : LeafGroup := ⟨ref, pending⟩
        have start := inv.leafDir.start first head
        have endRow : last.firstRow + last.count =
            (leavesRows finished).length + (blocksRows pending).length := by
          simpa [back] using inv.leafDir.stop
        have rowCount : ref.count = (blocksRows pending).length := by
          dsimp [ref]
          omega
        have size : ref.size = (encodeIndex state.leaf).size + checksumSize := by
          dsimp [ref]
          rw [inv.offset, stopSize]
          omega
        have offset : ref.offset = file.bytes.size := inv.offset
        have refStop : ref.offset + ref.size = stop := by omega
        have packet : PacketAt crc layout.tableId 2 (file.bytes ++ extra) ref.offset ref.size
            (encodeIndex state.leaf) := by
          rw [offset, size]
          exact PacketAt.atEnd crc layout.tableId 2 file.bytes (encodeIndex state.leaf) packetRoom
        have directory : ValidRefs state.leaf :=
          ⟨array_nonempty_last back, by omega, inv.leafDir.adjacent⟩
        have children : checkChildren state.leaf ref.firstRow ref.count ref.offset = .ok () := by
          rw [show ref.firstRow = (leavesRows finished).length from start, rowCount, offset]
          exact inv.leafDir.check (by intro empty; simp [empty] at back)
        have leaf : group.InImage layout crc (file.bytes ++ extra) := by
          refine ⟨?_, ?_, ?_, ?_, ?_⟩
          · simpa only [group, inv.leafRefs] using directory
          · simpa only [group, inv.leafRefs] using children
          · simp [group, ref, inv.leafRefs, back]
          · simpa only [group, inv.leafRefs] using packet
          · intro block member
            have oldBlock := inv.blocks block member
            exact { oldBlock with packet := oldBlock.packet.append extra }
        obtain ⟨fenceRow, fenceMem, fenceKey⟩ :=
          DataGroup.fence_mem_in_blocks inv.blocks (by simpa only [inv.leafRefs] using back)
        have positiveRows : 0 < ref.count := by
          rw [rowCount]
          cases all : blocksRows pending with
          | nil => simp [all] at fenceMem
          | cons => simp
        have countValid : ref.firstRow + ref.count ≤ maxFileSize := by
          have total := congrArg List.length inv.flattened
          simp only [List.length_append] at total
          have countLimit := inv.countLimit
          rw [inv.count] at countLimit
          have firstRow : ref.firstRow = (leavesRows finished).length := start
          omega
        have refValid : ref.Valid := by
          unfold Ref.Valid
          refine ⟨?_, ?_, positiveRows, countValid⟩ <;> simp [checksumSize] at * <;> omega
        have precedes (earlier : Ref) (previous : state.root.back? = some earlier) :
            earlier.lastKey < ref.lastKey := by
          obtain ⟨row, member, key⟩ := LeafGroup.fence_mem_in_leaves inv.leaves
            (by simpa only [inv.rootRefs] using previous)
          rw [← key, show ref.lastKey = last.lastKey from rfl, ← fenceKey]
          exact ordered_across inv.orderParts member (List.mem_append_left _ fenceMem)
        have newRoot := inv.rootDir.push refValid (by simpa using start) precedes (by omega)
        have imageSize : (file.bytes ++ extra).size = stop := by
          simp only [extra, ByteArray.size_append, encodePacket_size]
          exact stopSize.symm
        refine ⟨rfl, rfl, finished.push group, ⟨?_, inv.ordered, inv.count, inv.countLimit,
          inv.last, inv.dataFits, imageSize.symm, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
        · change leavesRows (finished.push group) ++ [] ++ state.data.toList = rows
          rw [leavesRows_push, List.append_nil]
          exact inv.flattened
        · change (file.bytes ++ extra).size + footerPacketSize ≤ maxFileSize
          rw [imageSize]
          exact extent
        · intro empty
          have mem : fenceRow ∈ rows := by
            rw [← inv.flattened]
            exact List.mem_append_left _ (List.mem_append_right _ fenceMem)
          simp [empty] at mem
        · simp [Array.map_push, group, inv.rootRefs, ref]
        · simp
        · change Directory (file.bytes ++ extra).size 0 (leavesRows (finished.push group)).length
              (state.root.push ref)
          have addedRows : (leavesRows (finished.push group)).length =
              (leavesRows finished).length + ref.count := by
            rw [leavesRows_push, List.length_append]
            rw [rowCount]
            rfl
          rw [imageSize, addedRows]
          simpa only [refStop] using newRoot
        · exact Directory.empty _ _
        · intro old member
          simp only [Array.toList_push, List.mem_append, List.mem_singleton] at member
          rcases member with earlier | rfl
          · exact (inv.leaves old earlier).append extra
          · exact leaf
        · simp
      · simp only [Writer.flushLeaf, head, back, room, ↓reduceIte] at run
        change Except.error "SSTable root index exceeds size limit" = .ok (next, out) at run
        cases run

private theorem flushData_ok {layout : Layout} {crc : Checksum} {options : BuildOptions}
    {rows : List Entry} {state next : BuilderState} {file out : ModelFile}
    {finished : Array LeafGroup} {pending : Array DataGroup}
    (inv : BuilderPrefix layout crc rows state file.bytes finished pending)
    (run : ((modelWriter crc layout options).flushData state).run file = .ok (next, out)) :
    out.rows = file.rows ∧ next.data = #[] ∧
      ∃ groups blocks, BuilderPrefix layout crc rows next out.bytes groups blocks := by
  cases back : state.data.back? with
  | none =>
    have empty := Array.back?_eq_none_iff.mp back
    simp only [Writer.flushData, back] at run
    obtain ⟨rfl, rfl⟩ := model_pure_ok run
    exact ⟨rfl, empty, finished, pending, inv⟩
  | some last =>
    simp only [Writer.flushData, back] at run
    obtain ⟨staged, beforeData, prepare, write⟩ := model_bind_ok run
    have prepared : beforeData.rows = file.rows ∧ staged.data = state.data ∧
        ∃ groups blocks, BuilderPrefix layout crc rows staged beforeData.bytes groups blocks := by
      by_cases flush : (!state.leaf.isEmpty &&
          decide (state.leafBytes + indexEntrySize last.key + checksumSize >
            (modelWriter crc layout options).options.leafTarget)) = true
      · simp only [flush] at prepare
        obtain ⟨rowsEq, dataEq, groups, valid⟩ := flushLeaf_ok inv prepare
        exact ⟨rowsEq, dataEq, groups, #[], valid⟩
      · simp only [flush] at prepare
        obtain ⟨rfl, rfl⟩ := model_pure_ok prepare
        exact ⟨rfl, rfl, finished, pending, inv⟩
    obtain ⟨rowsEq, dataEq, groups, blocks, stagedInv⟩ := prepared
    obtain ⟨stop, mid, wrote, done⟩ := model_bind_ok write
    obtain ⟨stateEq, fileEq⟩ := model_pure_ok done
    subst next
    subst out
    rw [stagedInv.offset] at wrote
    change ((modelWriter crc layout options).writePacket 1 beforeData.bytes.size
      (encodeData layout staged.data)).run beforeData = .ok (stop, mid) at wrote
    obtain ⟨rfl, stopSize, packetRoom, extent⟩ := writePacket_ok wrote
    let extra := encodePacket crc layout.tableId 1 beforeData.bytes.size (encodeData layout staged.data)
    let ref : Ref := ⟨last.key, staged.offset, stop - staged.offset, staged.count - staged.data.size,
      staged.data.size⟩
    let group : DataGroup := ⟨ref, staged.data⟩
    have starts : ref.firstRow = (leavesRows groups).length + (blocksRows blocks).length := by
      have total := congrArg List.length stagedInv.flattened
      simp only [List.length_append, Array.length_toList] at total
      dsimp [ref]
      have count := stagedInv.count
      omega
    have size : ref.size = (encodeData layout staged.data).size + checksumSize := by
      dsimp [ref]
      rw [stagedInv.offset, stopSize]
      omega
    have offset : ref.offset = beforeData.bytes.size := stagedInv.offset
    have refStop : ref.offset + ref.size = stop := by omega
    have packet : PacketAt crc layout.tableId 1 (beforeData.bytes ++ extra) ref.offset ref.size
        (encodeData layout staged.data) := by
      rw [offset, size]
      exact PacketAt.atEnd crc layout.tableId 1 beforeData.bytes (encodeData layout staged.data) packetRoom
    have actualLast : staged.data.back? = some last := by rwa [dataEq]
    have block : group.InImage layout crc (beforeData.bytes ++ extra) :=
      ⟨rfl, array_nonempty_last actualLast, by simp [group, ref, actualLast], stagedInv.dataFits, packet⟩
    have refValid : ref.Valid := by
      have countLimit := stagedInv.countLimit
      have nonempty := block.nonempty
      unfold Ref.Valid
      refine ⟨?_, ?_, nonempty, ?_⟩
      · simp [checksumSize] at size
        omega
      · omega
      · have total := congrArg List.length stagedInv.flattened
        simp only [List.length_append, Array.length_toList] at total
        have count := stagedInv.count
        dsimp [ref]
        omega
    have afterBlock (prev : Ref) (previous : staged.leaf.back? = some prev) :
        prev.lastKey < ref.lastKey := by
      obtain ⟨row, member, key⟩ := DataGroup.fence_mem_in_blocks stagedInv.blocks
        (by simpa only [stagedInv.leafRefs] using previous)
      have order : Ordered (blocksRows blocks ++ staged.data.toList) :=
        (List.pairwise_append.mp stagedInv.orderParts).2.1
      rw [← key, show ref.lastKey = last.key from rfl]
      exact ordered_across order member (Array.back_mem_list actualLast)
    have leafDir := stagedInv.leafDir.push refValid starts afterBlock (by omega)
    have imageSize : (beforeData.bytes ++ extra).size = stop := by
      simp only [extra, ByteArray.size_append, encodePacket_size]
      exact stopSize.symm
    refine ⟨rowsEq, rfl, groups, blocks.push group, ⟨?_, stagedInv.ordered, stagedInv.count,
      stagedInv.countLimit, stagedInv.last, by simp, imageSize.symm, ?_, ?_, stagedInv.rootRefs, ?_,
      ?_, ?_, ?_, ?_⟩⟩
    · change leavesRows groups ++ blocksRows (blocks.push group) ++ [] = rows
      rw [blocksRows_push, List.append_nil, ← List.append_assoc]
      exact stagedInv.flattened
    · change (beforeData.bytes ++ extra).size + footerPacketSize ≤ maxFileSize
      rw [imageSize]
      exact extent
    · intro empty
      have member : last ∈ rows := by
        rw [← stagedInv.flattened]
        exact List.mem_append_right _ (Array.back_mem_list actualLast)
      simp [empty] at member
    · simp [Array.map_push, group, stagedInv.leafRefs, ref]
    · exact stagedInv.rootDir.extend (by simp)
    · change Directory (beforeData.bytes ++ extra).size (leavesRows groups).length
          (blocksRows (blocks.push group)).length (staged.leaf.push ref)
      rw [blocksRows_push, List.length_append, imageSize]
      simpa only [refStop, block.count_eq, Array.length_toList] using leafDir
    · intro old member
      exact (stagedInv.leaves old member).append extra
    · intro old member
      simp only [Array.toList_push, List.mem_append, List.mem_singleton] at member
      rcases member with earlier | rfl
      · have oldBlock := stagedInv.blocks old earlier
        exact { oldBlock with packet := oldBlock.packet.append extra }
      · exact block

private theorem checkRow_ok {state : BuilderState} {layout : Layout} {row : Entry}
    (checked : state.checkRow layout row = .ok ()) :
    rowFits layout row = true ∧ ∀ prev ∈ state.lastKey, prev < row.key := by
  have width : rowFits layout row = true := by
    by_cases width : rowFits layout row = true
    · exact width
    · have rejects : rowFits layout row = false := Bool.eq_false_of_ne_true width
      simp [BuilderState.checkRow, rejects] at checked
  have preceding : state.lastKey.all (fun prev => decide (prev < row.key)) = true := by
    by_cases preceding : state.lastKey.all (fun prev => decide (prev < row.key)) = true
    · exact preceding
    · have rejects : state.lastKey.all (fun prev => decide (prev < row.key)) = false :=
        Bool.eq_false_of_ne_true preceding
      simp [BuilderState.checkRow, width, rejects] at checked
  exact ⟨width, by simpa [Option.all_eq_true] using preceding⟩

private theorem ordered_append_row {rows : List Entry} {row : Entry} (ordered : Ordered rows)
    (last : ∀ old ∈ rows.getLast?, old.key < row.key) : Ordered (rows ++ [row]) := by
  apply List.pairwise_append.mpr
  refine ⟨ordered, by simp, ?_⟩
  intro entry member tail one
  have same : tail = row := by simpa using one
  subst tail
  cases back : rows.getLast? with
  | none => simp [List.getLast?_eq_none_iff.mp back] at member
  | some old =>
    have next := last old back
    obtain ⟨earlier, eq⟩ := List.getLast?_eq_some_iff.mp back
    rw [eq, List.mem_append, List.mem_singleton] at member
    rcases member with first | rfl
    · exact Std.lt_trans
        (ordered_across (by simpa only [eq] using ordered) first (by simp)) next
    · exact next

private theorem BuilderPrefix.addRow {layout : Layout} {crc : Checksum} {rows : List Entry}
    {state : BuilderState} {image : ByteArray}
    {finished : Array LeafGroup} {pending : Array DataGroup}
    (inv : BuilderPrefix layout crc rows state image finished pending) (row : Entry)
    (fits : rowFits layout row = true) (ordered : ∀ prev ∈ state.lastKey, prev < row.key)
    (room : state.count + 1 ≤ maxFileSize) :
    BuilderPrefix layout crc (rows ++ [row]) (state.addRow layout row) image finished pending := by
  refine ⟨?_, ?_, ?_, room, ?_, ?_, inv.offset, inv.space, by simp, inv.rootRefs, inv.leafRefs,
    inv.rootDir, inv.leafDir, inv.leaves, inv.blocks⟩
  · simp only [BuilderState.addRow, Array.toList_push, ← List.append_assoc, inv.flattened]
  · apply ordered_append_row inv.ordered
    intro old member
    apply ordered old.key
    rw [inv.last, show rows.getLast? = some old from member]
    rfl
  · simp [BuilderState.addRow, inv.count]
  · simp [BuilderState.addRow]
  · intro r member
    simp only [BuilderState.addRow, Array.toList_push, List.mem_append, List.mem_singleton] at member
    rcases member with earlier | rfl
    · exact inv.dataFits r earlier
    · exact fits

private theorem accept_ok {layout : Layout} {crc : Checksum} {options : BuildOptions}
    {rows : List Entry} {state next : BuilderState} {file out : ModelFile}
    {finished : Array LeafGroup} {pending : Array DataGroup} {row : Entry}
    (inv : BuilderPrefix layout crc rows state file.bytes finished pending)
    (room : state.count + 1 ≤ maxFileSize)
    (run : ((modelWriter crc layout options).accept state row).run file = .ok (next, out)) :
    out.rows = file.rows ∧
      ∃ groups blocks, BuilderPrefix layout crc (rows ++ [row]) next out.bytes groups blocks := by
  have checkedResult : state.checkRow layout row = .ok () := by
    cases result : state.checkRow layout row with
    | error error =>
      simp only [Writer.accept, show (modelWriter crc layout options).layout = layout from rfl, result] at run
      change Except.error error = .ok (next, out) at run
      cases run
    | ok accepted =>
      cases accepted
      rfl
  obtain ⟨width, ordered⟩ := checkRow_ok checkedResult
  simp only [Writer.accept, show (modelWriter crc layout options).layout = layout from rfl,
    checkedResult] at run
  obtain ⟨staged, mid, stage, accepted⟩ := model_bind_ok run
  obtain ⟨stateEq, fileEq⟩ := model_pure_ok accepted
  subst next
  subst out
  have prefixResult : mid.rows = file.rows ∧
      ∃ groups blocks, BuilderPrefix layout crc rows staged mid.bytes groups blocks := by
    by_cases flush : (!state.data.isEmpty &&
        decide (dataSize layout (state.data.size + 1) (state.payloadBytes + entrySize layout row) >
          (modelWriter crc layout options).options.dataTarget)) = true
    · simp only [flush] at stage
      obtain ⟨same, _, groups, blocks, valid⟩ := flushData_ok inv stage
      exact ⟨same, groups, blocks, valid⟩
    · simp only [flush] at stage
      obtain ⟨rfl, rfl⟩ := model_pure_ok stage
      exact ⟨rfl, finished, pending, inv⟩
  obtain ⟨same, groups, blocks, stagedInv⟩ := prefixResult
  refine ⟨same, groups, blocks, stagedInv.addRow row width ?_ ?_⟩
  · simpa only [stagedInv.last, inv.last] using ordered
  · simpa only [stagedInv.count, inv.count] using room

private theorem streamRows_ok {layout : Layout} {crc : Checksum} {options : BuildOptions}
    (remaining accepted : List Entry) (state : BuilderState) (bytes : ByteArray)
    (finished : Array LeafGroup) (pending : Array DataGroup)
    (inv : BuilderPrefix layout crc accepted state bytes finished pending)
    (room : Nat) (limit : state.count + room ≤ maxFileSize) {last : BuilderState} {out : ModelFile}
    (run : ((modelWriter crc layout options).streamRows modelNext state room).run
      ⟨remaining, bytes⟩ = .ok (last, out)) :
    ∃ groups blocks, BuilderPrefix layout crc (accepted ++ remaining) last out.bytes groups blocks := by
  induction remaining generalizing accepted state bytes finished pending room with
  | nil =>
    have eq : (state, (⟨[], bytes⟩ : ModelFile)) = (last, out) := by
      cases room <;> exact Except.ok.inj run
    cases eq
    exact ⟨finished, pending, by simpa using inv⟩
  | cons row rest ih =>
    cases room with
    | zero => cases run
    | succ room =>
      simp only [Writer.streamRows] at run
      obtain ⟨item, file, read, continuation⟩ := model_bind_ok run
      change Except.ok (some row, (⟨rest, bytes⟩ : ModelFile)) = .ok (item, file) at read
      cases read
      obtain ⟨next, mid, acceptedRow, loop⟩ := model_bind_ok continuation
      obtain ⟨same, groups, blocks, new⟩ := accept_ok inv (by omega) acceptedRow
      have modelEq : mid = ⟨rest, mid.bytes⟩ := by
        cases mid
        simp only [ModelFile.mk.injEq, and_true]
        exact same
      have nextLimit : next.count + room ≤ maxFileSize := by
        have previous := inv.count
        have current := new.count
        simp only [List.length_append, List.length_singleton] at current
        omega
      rw [modelEq] at loop
      obtain ⟨moreGroups, moreBlocks, complete⟩ :=
        ih (accepted ++ [row]) next mid.bytes groups blocks new room nextLimit loop
      exact ⟨moreGroups, moreBlocks, by simpa only [List.append_assoc, List.singleton_append] using complete⟩

private theorem finish_ok {layout : Layout} {crc : Checksum} {options : BuildOptions}
    {rows : List Entry} {state : BuilderState} {file out : ModelFile} {count : Nat}
    {finished : Array LeafGroup} {pending : Array DataGroup}
    (validLayout : layout.Valid) (inv : BuilderPrefix layout crc rows state file.bytes finished pending)
    (run : ((modelWriter crc layout options).finish state).run file = .ok (count, out)) :
    count = rows.length ∧ Image crc layout rows out.bytes := by
  simp only [Writer.finish] at run
  obtain ⟨afterData, dataFile, wroteData, continuation⟩ := model_bind_ok run
  obtain ⟨_, noData, groups, blocks, dataInv⟩ := flushData_ok inv wroteData
  obtain ⟨afterLeaf, leafFile, wroteLeaf, continuation⟩ := model_bind_ok continuation
  obtain ⟨_, dataKept, groups, leafInv⟩ := flushLeaf_ok dataInv wroteLeaf
  have grouped : leavesRows groups = rows := by simpa [dataKept, noData, blocksRows] using leafInv.flattened
  obtain ⟨root, beforeFooter, wroteRoot, wroteFooter⟩ := model_bind_ok continuation
  let footer : Footer := ⟨layout, afterLeaf.count, root.1, root.2⟩
  let trailer := encodePacket crc 0 4 0 (encodeFooterBody footer)
  have finalWrite : count = afterLeaf.count ∧ out.bytes = beforeFooter.bytes ++ trailer := by
    cases root with
    | mk rootOffset rootSize =>
      change Except.ok (afterLeaf.count, { beforeFooter with bytes := beforeFooter.bytes ++ trailer }) =
        .ok (count, out) at wroteFooter
      cases wroteFooter
      exact ⟨rfl, rfl⟩
  have footerCount : footer.count = rows.length := leafInv.count
  have trailerSize : trailer.size = footerPacketSize := by simp [trailer, footerPacketSize]
  have fileSize : out.bytes.size = beforeFooter.bytes.size + footerPacketSize := by
    rw [finalWrite.2, ByteArray.size_append, trailerSize]
  have footerStart : out.bytes.size - footerPacketSize = beforeFooter.bytes.size := by omega
  have footerSlice : out.bytes.extract (out.bytes.size - footerPacketSize) out.bytes.size = trailer := by
    rw [footerStart, finalWrite.2]
    exact ByteArray.extract_append_eq_right rfl (by simp)
  refine ⟨finalWrite.1.trans leafInv.count, ?_⟩
  by_cases empty : afterLeaf.root = #[]
  · have groupsEmpty : groups = #[] := array_map_empty (leafInv.rootRefs.trans empty)
    have noRows : rows = [] := by simpa [groupsEmpty, leavesRows] using grouped.symm
    have noRoot : afterLeaf.root.isEmpty = true := Array.isEmpty_iff.mpr empty
    simp only [noRoot, ↓reduceIte] at wroteRoot
    obtain ⟨rootEq, retained⟩ := model_pure_ok wroteRoot
    have onlyFooter : out.bytes.size = footerPacketSize := by
      rw [fileSize, retained, leafInv.emptyFile noRows, Nat.zero_add]
    have validFooter : footer.Valid := by
      refine ⟨validLayout, leafInv.countLimit, ?_, ?_⟩
      · simp [footer, rootEq, footerBodySize]
        decide
      · simp [footer, rootEq, leafInv.count, noRows]
    refine ⟨leafInv.ordered, by rw [onlyFooter]; decide, footer, groups, rfl, footerCount, grouped, validFooter,
      footerSlice, by change footerPacketSize ≤ out.bytes.size; omega, ?_, ?_⟩
    · simp [groupsEmpty]
    · simpa [noRows, groupsEmpty, footerPacketSize] using onlyFooter
  · have present : afterLeaf.root.isEmpty = false :=
      Bool.eq_false_of_ne_true (fun absent => empty (Array.isEmpty_iff.mp absent))
    have countPositive : footer.count ≠ 0 := by
      intro zero
      have noRows : rows = [] := List.length_eq_zero_iff.mp (footerCount.symm.trans zero)
      have emptyFile := leafInv.emptyFile noRows
      cases last : afterLeaf.root.back? with
      | none => exact empty (Array.back?_eq_none_iff.mp last)
      | some ref =>
        have member := Array.back_mem_list last
        have within := leafInv.rootDir.disk ref member
        have refFits := leafInv.rootDir.adjacent.ref_valid member
        unfold Ref.Valid at refFits
        omega
    have rowsPresent : rows.isEmpty = false := by
      apply Bool.eq_false_of_ne_true
      intro absent
      have noRows : rows = [] := List.isEmpty_iff.mp absent
      exact countPositive (by simp [footerCount, noRows])
    simp only [present, Bool.false_eq_true, ↓reduceIte] at wroteRoot
    obtain ⟨stop, mid, wrote, done⟩ := model_bind_ok wroteRoot
    obtain ⟨rootEq, retained⟩ := model_pure_ok done
    rw [leafInv.offset] at wrote
    obtain ⟨midFile, stopSize, packetRoom, space⟩ := writePacket_ok wrote
    have footerOffset : footer.rootOffset = leafFile.bytes.size := by
      simp [footer, rootEq, leafInv.offset]
    have footerRootSize : footer.rootSize = (encodeIndex afterLeaf.root).size + checksumSize := by
      simp only [footer, rootEq, leafInv.offset, stopSize, Nat.add_sub_cancel_left]
    have rootByteSize : beforeFooter.bytes.size = stop := by
      rw [retained, midFile, ByteArray.size_append, encodePacket_size, ← stopSize]
    have validFooter : footer.Valid := by
      refine ⟨validLayout, leafInv.countLimit, ?_, ?_⟩
      · rw [footerOffset, footerRootSize]
        rw [stopSize, footerPacketSize] at space
        omega
      · simp [countPositive, footerRootSize, checksumSize]
    refine ⟨leafInv.ordered, by simpa only [fileSize, rootByteSize] using space, footer, groups, rfl, footerCount,
      grouped, validFooter, footerSlice, by change footerPacketSize ≤ out.bytes.size; omega, ?_, ?_⟩
    · intro leaf member
      rw [finalWrite.2, retained, midFile]
      exact ((leafInv.leaves leaf member).append _).append trailer
    · simp only [rowsPresent, Bool.false_eq_true, ↓reduceIte]
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [leafInv.rootRefs]
        exact ⟨Nat.pos_of_ne_zero (fun zero => empty (Array.size_eq_zero_iff.mp zero)), by omega,
          leafInv.rootDir.adjacent⟩
      · rw [leafInv.rootRefs, footerOffset, ← grouped]
        exact leafInv.rootDir.check empty
      · rw [footerOffset, footerRootSize]
        change leafFile.bytes.size + ((encodeIndex afterLeaf.root).size + checksumSize) =
          out.bytes.size - footerPacketSize
        rw [← stopSize, footerStart, rootByteSize]
      · rw [leafInv.rootRefs, footerOffset, footerRootSize, finalWrite.2, retained, midFile]
        exact (PacketAt.atEnd crc layout.tableId 3 leafFile.bytes (encodeIndex afterLeaf.root)
          packetRoom).append trailer

/-- The successful append interpretation of the production writer establishes
the packet image, including both index levels, and the original row sequence. -/
theorem modelBuild_ok {crc : Checksum} {layout : Layout} {options : BuildOptions}
    {rows : List Entry} {count : Nat} {bytes : ByteArray}
    (built : modelBuild crc layout rows options = .ok (count, bytes)) :
    count = rows.length ∧ Image crc layout rows bytes := by
  unfold modelBuild at built
  cases run : (buildStream crc layout modelSink modelNext id options).run { rows } with
  | error error =>
    simp [run, Bind.bind, Except.bind] at built
  | ok result =>
    obtain ⟨n, out⟩ := result
    have resultEq : (n, out.bytes) = (count, bytes) := by
      simpa [run, Bind.bind, Except.bind, Pure.pure, Except.pure] using built
    cases resultEq
    by_cases layoutValid : layout.Valid
    · by_cases targets : 0 < options.dataTarget ∧ options.dataTarget ≤ maxRowSize ∧
          0 < options.leafTarget ∧ options.leafTarget ≤ maxRowSize
      · simp only [buildStream, layoutValid, targets, ↓reduceIte] at run
        obtain ⟨last, file, body, done⟩ := model_bind_ok run
        change ((modelWriter crc layout options).streamRows modelNext {} maxFileSize).run
          ⟨rows, .empty⟩ = .ok (last, file) at body
        obtain ⟨groups, blocks, image⟩ := streamRows_ok rows [] {} .empty #[] #[]
          (BuilderPrefix.empty layout crc) maxFileSize (by simp) body
        exact finish_ok layoutValid (by simpa using image) done
      · simp only [buildStream, layoutValid, targets, ↓reduceIte] at run
        change Except.error "invalid SSTable packet targets" = .ok (count, out) at run
        cases run
    · simp only [buildStream, layoutValid, ↓reduceIte] at run
      change Except.error "invalid SSTable layout" = .ok (count, out) at run
      cases run

end ImmutableSSTable.Unified
