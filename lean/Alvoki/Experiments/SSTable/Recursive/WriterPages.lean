import Alvoki.Experiments.SSTable.Recursive.Builder
import Alvoki.Experiments.SSTable.Recursive.Image

namespace ImmutableSSTable.Recursive

open Unified (Layout Checksum Ref RefCovers ValidRefsAfter encodeIndex checksumSize indexEntrySize)

theorem slice_append (bytes extra : ByteArray) (within : offset + size ≤ bytes.size) :
    (bytes ++ extra).extract offset (offset + size) = bytes.extract offset (offset + size) := by
  rw [ByteArray.extract_append, Nat.sub_eq_zero_of_le within]
  have empty : extra.extract (offset - bytes.size) 0 = ByteArray.empty :=
    ByteArray.extract_eq_empty_iff.mpr (by simp)
  simp [empty]

private theorem packet_append {id : UInt64}
    (p : Unified.PacketAt crc id kind bytes offset size body) (extra : ByteArray) :
    Unified.PacketAt crc id kind (bytes ++ extra) offset size body := by
  refine ⟨p.size_eq, p.bounded, ?_, (slice_append bytes extra p.extent).trans p.slice⟩
  have := p.extent
  simp
  omega

theorem TreeInImage.extend (p : TreeInImage layout crc bytes rows ref endAt fence height)
    (extra : ByteArray) (grows : endAt ≤ extended) (within : extended ≤ (bytes ++ extra).size) :
    TreeInImage layout crc (bytes ++ extra) rows ref extended fence height := by
  induction height generalizing ref endAt fence extended with
  | zero =>
    obtain ⟨ends, positive, range, key, block, count, limit, rowMatches, fits, packet⟩ := p
    exact ⟨Nat.le_trans ends grows, positive, range, key,
      block, count, limit, rowMatches, fits, packet_append packet extra⟩
  | succ h ih =>
    obtain ⟨children, node, below⟩ := p
    have disk := node.packet
    have oldEnd := Nat.le_trans disk.extent disk.within
    refine ⟨children, { node with packet := ⟨disk.shape, Nat.le_trans disk.extent grows,
      within, disk.length, (slice_append bytes extra oldEnd).trans disk.slice⟩ }, ?_⟩
    intro child member
    exact ih (below child member) (Nat.le_refl _) (by
      rw [ByteArray.size_append]
      omega)

structure WrittenChild (layout : Layout) (crc : Checksum) (bytes : ByteArray)
    (rows : List Entry) (endAt height : Nat) (ref : Ref) : Prop where
  tree : TreeInImage layout crc bytes rows ref endAt true height
  valid : ref.Valid
  ends : ref.offset + ref.size ≤ endAt
  range : ref.firstRow + ref.count ≤ rows.length
  fence : ref.lastKey = (rowAt rows (ref.firstRow + ref.count - 1)).key
  keyFits : indexEntrySize ref.lastKey + checksumSize ≤ maxRowSize

theorem WrittenChild.extend (p : WrittenChild layout crc bytes rows endAt height ref)
    (extra : ByteArray) (grows : endAt ≤ extended) (within : extended ≤ (bytes ++ extra).size) :
    WrittenChild layout crc (bytes ++ extra) rows extended height ref :=
  { p with tree := p.tree.extend extra grows within, ends := Nat.le_trans p.ends grows }

theorem WrittenChild.restrict (p : WrittenChild layout crc bytes rows endAt height ref)
    (extent : ref.offset + ref.size ≤ before) (within : before ≤ bytes.size) :
    WrittenChild layout crc bytes rows before height ref := by
  refine { p with ends := extent, tree := ?_ }
  cases height
  · exact { (p.tree : DataAt layout crc bytes rows ref endAt) with within := extent }
  · obtain ⟨children, node, below⟩ := p.tree
    exact ⟨children, { node with packet := { node.packet with extent, within } }, below⟩

structure PendingPage (layout : Layout) (crc : Checksum) (bytes : ByteArray)
    (rows : List Entry) (endAt childHeight first stop : Nat) (page : Page) : Prop where
  first_le : first ≤ stop
  nonempty : 0 < page.refs.size
  length : page.bytes = (encodeIndex page.refs).size
  packetBound : page.bytes + checksumSize ≤ maxIndexSize
  overflow : page.bytes + checksumSize ≤ maxRowSize || page.refs.size == 2
  adjacent : ValidRefsAfter none page.refs.toList
  start : ∀ head, page.refs[0]? = some head → head.firstRow = first
  finish : ∀ last, page.refs.back? = some last → last.firstRow + last.count = stop
  coverage : RefCovers rows first (stop - first) page.refs
  children : ∀ ref ∈ page.refs.toList, WrittenChild layout crc bytes rows endAt childHeight ref

inductive PendingPages (layout : Layout) (crc : Checksum) (bytes : ByteArray)
    (rows : List Entry) (endAt : Nat) : Nat → Nat → List Page → Prop where
  | nil : PendingPages layout crc bytes rows endAt height 0 []
  | cons (upper : PendingPages layout crc bytes rows endAt (height + 1) first pages)
      (current : PendingPage layout crc bytes rows endAt height first stop page) :
      PendingPages layout crc bytes rows endAt height stop (page :: pages)

theorem PendingPage.extend (p : PendingPage layout crc bytes rows endAt h first stop page)
    (extra : ByteArray) (grows : endAt ≤ extended) (within : extended ≤ (bytes ++ extra).size) :
    PendingPage layout crc (bytes ++ extra) rows extended h first stop page :=
  { p with children := fun ref member => (p.children ref member).extend extra grows within }

theorem PendingPages.extend (p : PendingPages layout crc bytes rows endAt h stop pages)
    (extra : ByteArray) (grows : endAt ≤ extended) (within : extended ≤ (bytes ++ extra).size) :
    PendingPages layout crc (bytes ++ extra) rows extended h stop pages := by
  induction p with
  | nil => exact .nil
  | cons _ current ih => exact .cons ih (current.extend extra grows within)

theorem array_back_mem {xs : Array α} {x : α} (back : xs.back? = some x) :
    x ∈ xs.toList := by
  rw [← Array.getLast?_toList] at back
  obtain ⟨earlier, eq⟩ := List.getLast?_eq_some_iff.mp back
  rw [eq]
  simp

private theorem adjacent_push {refs : List Ref} {prev : Option Ref} {ref : Ref}
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

private theorem key_lt_of_ordered_take
    (ordered : Ordered (rows.take n)) (hi : j < n) (inside : j < rows.length) (before : i < j) :
    (rowAt rows i).key < (rowAt rows j).key := by
  have left : i < (rows.take n).length := by simp; omega
  have right : j < (rows.take n).length := by simp; omega
  simpa only [List.getElem_take, rowAt_eq (Nat.lt_trans before inside), rowAt_eq inside] using
    ordered.rel_getElem_of_lt left right before

private theorem covers_push (corr : RefCovers rows first (stop - first) refs) (lo : first ≤ stop)
    (starts : ref.firstRow = stop) (positive : 0 < ref.count)
    (rowEnd : ref.firstRow + ref.count ≤ rows.length)
    (fence : ref.lastKey = (rowAt rows (ref.firstRow + ref.count - 1)).key) :
    RefCovers rows first (stop + ref.count - first) (refs.push ref) := by
  have base : first + (stop - first) = stop := by omega
  have extended : first + (stop + ref.count - first) = stop + ref.count := by omega
  refine ⟨by omega, ?_, ?_, ?_⟩
  · intro i hi
    by_cases earlier : i < refs.size
    · obtain ⟨pos, start, finish, key⟩ := corr.span i earlier
      simp only [Array.getElem_push_lt earlier]
      exact ⟨pos, start, by omega, key⟩
    · have atLast : i = refs.size := by simp at hi; omega
      subst i
      simp only [Array.getElem_push_eq]
      exact ⟨positive, by omega, by omega, fence⟩
  · intro i j hi hj less
    have earlier : i < refs.size := by simp at hj; omega
    rw [Array.getElem_push_lt earlier]
    by_cases prev : j < refs.size
    · rw [Array.getElem_push_lt prev]
      exact corr.separated i j earlier prev less
    · have atLast : j = refs.size := by simp at hj; omega
      subst j
      rw [Array.getElem_push_eq]
      exact Nat.le_trans (corr.span i earlier).2.2.1 (Nat.le_of_eq (base.trans starts.symm))
  · intro index start finish
    by_cases earlier : index < stop
    · obtain ⟨i, hi, lower, before⟩ := corr.covers index start (by omega)
      exact ⟨i, by simp; omega, by simpa only [Array.getElem_push_lt hi] using And.intro lower before⟩
    · exact ⟨refs.size, by simp, by simp only [Array.getElem_push_eq]; omega⟩

theorem PendingPage.singleton (r : WrittenChild layout crc bytes rows endAt h ref) :
    PendingPage layout crc bytes rows endAt h ref.firstRow (ref.firstRow + ref.count)
      (({} : Page).add ref) := by
  have upper : maxRowSize ≤ maxIndexSize := by unfold maxIndexSize; omega
  have count := r.valid.2.2.1
  have range := r.range
  refine ⟨by omega, by simp [Page.add], ?_, Nat.le_trans (by simpa [Page.add] using r.keyFits) upper, ?_,
    ?_, ?_, ?_, ?_, ?_⟩
  · simp [Page.add, Unified.encodeIndex_size]
  · simp [Page.add, r.keyFits]
  · exact ⟨r.valid, by simp, trivial⟩
  · intro head headEq
    have same : ref = head := by simpa [Page.add] using headEq
    rw [← same]
  · intro last lastEq
    have same : ref = last := by simpa [Page.add] using lastEq
    rw [← same]
  · have empty : RefCovers rows ref.firstRow (ref.firstRow - ref.firstRow) #[] := by
      refine ⟨by omega, ?_, ?_, ?_⟩
      · intro i hi; simp at hi
      · intro i j hi; simp at hi
      · intro i lo hi; omega
    simpa [Page.add] using covers_push empty (Nat.le_refl _) rfl count range r.fence
  · intro entry member
    have same : entry = ref := by simpa [Page.add] using member
    rwa [same]

theorem PendingPage.add (p : PendingPage layout crc bytes rows oldEnd h first stop page)
    (r : WrittenChild layout crc bytes rows endAt h ref)
    (disjoint : oldEnd ≤ ref.offset) (grows : oldEnd ≤ endAt) (within : endAt ≤ bytes.size)
    (starts : ref.firstRow = stop) (targetFits : target ≤ maxRowSize)
    (fits : page.shouldFlush ref target = false) (ordered : Ordered (rows.take (stop + ref.count))) :
    PendingPage layout crc bytes rows endAt h first (stop + ref.count) (page.add ref) := by
  have pos := r.valid.2.2.1
  have keyFits := r.keyFits
  have pagePos := p.nonempty
  have len : (page.add ref).bytes = (encodeIndex (page.add ref).refs).size := by
    simp [Page.add, Unified.encodeIndex_size, p.length]
  have smallOrPair : (page.add ref).bytes + checksumSize ≤ maxRowSize ∨
      (page.refs.size = 1 ∧ page.bytes + checksumSize ≤ maxRowSize) := by
    by_cases two : 2 ≤ page.refs.size
    · left
      simp [Page.shouldFlush, two] at fits
      exact Nat.le_trans fits targetFits
    · right
      have one : page.refs.size = 1 := by omega
      obtain ⟨child, contents⟩ := List.length_eq_one_iff.mp (by simpa using one : page.refs.toList.length = 1)
      have childFits := (p.children child (by simp [contents])).keyFits
      refine ⟨one, ?_⟩
      simpa [p.length, Unified.encodeIndex_size, contents] using childFits
  have large : (page.add ref).bytes + checksumSize ≤ maxIndexSize := by
    unfold maxIndexSize
    rcases smallOrPair with small | ⟨_, small⟩
    · omega
    · change page.bytes + indexEntrySize ref.lastKey + checksumSize ≤ 2 * maxRowSize
      omega
  refine ⟨by have := p.first_le; omega, by simp [Page.add], len, large, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rcases smallOrPair with small | ⟨one, _⟩
    · simp [small]
    · simp [Page.add, one]
  · rw [Page.add, Array.toList_push]
    apply adjacent_push p.adjacent r.valid
    intro prev member
    have back : page.refs.back? = some prev := by simpa using member
    have finish := p.finish prev back
    have prevChild := p.children prev (array_back_mem back)
    have earlier := prevChild.fence
    have later := r.fence
    have lt := key_lt_of_ordered_take ordered
      (j := ref.firstRow + ref.count - 1) (i := prev.firstRow + prev.count - 1)
      (by omega) (by have := r.range; omega) (by have := prevChild.valid.2.2.1; omega)
    exact ⟨by simpa [← earlier, ← later] using lt, by omega,
      Nat.le_trans prevChild.ends disjoint⟩
  · intro head headEq
    apply p.start head
    rw [Page.add, Array.getElem?_push] at headEq
    simpa only [show 0 ≠ page.refs.size by omega, ↓reduceIte] using headEq
  · intro last lastEq
    have same : ref = last := by simpa [Page.add] using lastEq
    rw [← same, starts]
  · exact covers_push p.coverage p.first_le starts pos r.range r.fence
  · intro child member
    simp only [Page.add, Array.toList_push, List.mem_append, List.mem_singleton] at member
    rcases member with old | rfl
    · have prior := p.children child old
      exact prior.restrict (Nat.le_trans prior.ends grows) within
    · exact r

theorem PendingPage.pageValid (p : PendingPage layout crc bytes rows endAt h first stop page) :
    PageValid page.refs := by
  refine ⟨p.nonempty, p.length ▸ p.packetBound, ?_, ?_, p.adjacent⟩
  · rw [← p.length]
    exact p.overflow
  · apply Array.all_eq_true.mpr
    intro i inside
    exact decide_eq_true (p.children _ (by simp)).keyFits

end ImmutableSSTable.Recursive
