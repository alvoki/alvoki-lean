import Alvoki.Experiments.SSTable.Proofs.UnifiedBuilder
import Alvoki.Experiments.SSTable.Recursive.Invariants

namespace ImmutableSSTable.Recursive

open Unified (Checksum Layout ModelM ModelFile Ref modelSink checksumSize)

private def modelWriter (crc : Checksum) (layout : Layout) (options : BuildOptions) :
    Writer ModelM String :=
  ⟨crc, layout, modelSink, id, options⟩

/-- A page covers a contiguous interval of the consumed supplier. -/
def Tiles : Nat → Nat → List Ref → Prop
  | start, stop, [] => start = stop
  | start, stop, ref :: rest =>
    ref.firstRow = start ∧ Tiles (ref.firstRow + ref.count) stop rest

private theorem Tiles.lower {start stop : Nat} {refs : List Ref}
    (tiles : Tiles start stop refs) : start ≤ stop := by
  induction refs generalizing start with
  | nil => exact Nat.le_of_eq tiles
  | cons first rest ih =>
    obtain ⟨rfl, next⟩ := tiles
    exact Nat.le_trans (Nat.le_add_right _ _) (ih next)

private theorem Tiles.append {start mid stop : Nat} {left right : List Ref}
    (before : Tiles start mid left) (after : Tiles mid stop right) :
    Tiles start stop (left ++ right) := by
  induction left generalizing start with
  | nil =>
    change start = mid at before
    subst start
    exact after
  | cons first rest ih => exact ⟨before.1, ih before.2⟩

private theorem Tiles.head {start stop : Nat} {refs : List Ref} {first : Ref}
    (tiles : Tiles start stop refs) (head : refs.head? = some first) :
    first.firstRow = start := by
  cases refs with
  | nil => simp at head
  | cons ref rest =>
    have same : ref = first := by simpa using head
    simpa only [← same] using tiles.1

private theorem Tiles.last {start stop : Nat} {refs : List Ref} {last : Ref}
    (tiles : Tiles start stop refs) (back : refs.getLast? = some last) :
    last.firstRow + last.count = stop := by
  induction refs generalizing start with
  | nil => simp at back
  | cons ref rest ih =>
    cases rest with
    | nil =>
      have same : ref = last := by simpa using back
      simpa only [← same, Tiles] using tiles.2
    | cons next tail => exact ih tiles.2 (by simpa using back)

private theorem Tiles.floorSum {start stop : Nat} {refs : List Ref}
    (tiles : Tiles start stop refs) (floor : Nat) (mass : ∀ ref ∈ refs, floor ≤ ref.count) :
    start + floor * refs.length ≤ stop := by
  induction refs generalizing start with
  | nil =>
    simp only [List.length_nil, Nat.mul_zero, Nat.add_zero]
    exact Nat.le_of_eq tiles
  | cons first rest ih =>
    have endBound := ih tiles.2 fun ref mem => mass ref (List.mem_cons_of_mem _ mem)
    have firstBound := mass first (by simp)
    have atStart := tiles.1
    simp only [List.length_cons, Nat.mul_succ]
    omega

structure PageRows (start stop : Nat) (page : Page) : Prop where
  nonempty : 0 < page.refs.size
  tiles : Tiles start stop page.refs.toList
  positive : ∀ ref ∈ page.refs.toList, 0 < ref.count

private theorem PageRows.strict {start stop : Nat} {page : Page} (pageRows : PageRows start stop page) :
    start < stop := by
  have mass := pageRows.tiles.floorSum 1 pageRows.positive
  simp only [Nat.one_mul, Array.length_toList] at mass
  have nonempty := pageRows.nonempty
  omega

/-- Every reference delivered by a regular promotion has at least
`2^rank` rows. Leaves of this argument are actual nonempty data packets. -/
def Regular (rank : Nat) (page : Page) : Prop :=
  ∀ ref ∈ page.refs.toList, 2 ^ rank ≤ ref.count

/-- Finalization is allowed to carry one short reference at the right edge. -/
def Fringe (rank : Nat) (page : Page) : Prop :=
  ∀ ref ∈ page.refs.toList.dropLast, 2 ^ rank ≤ ref.count

/-- Pending pages start at the bottom rank, while upper pages cover the
earlier row intervals. Every occupied upper page is nonempty. -/
inductive RankedPages : Nat → Nat → Nat → List Page → Prop where
  | nil : RankedPages rank row row []
  | cons : PageRows mid stop page → Regular rank page →
    RankedPages (rank + 1) start mid upper → RankedPages rank start stop (page :: upper)

/-- The currently draining page may include the rightmost short reference.
Higher pending pages still consist entirely of regular references. -/
inductive FringePages (rank start stop : Nat) : List Page → Prop where
  | cons : PageRows mid stop page → Fringe rank page →
    RankedPages (rank + 1) start mid upper → FringePages rank start stop (page :: upper)

private theorem RankedPages.upper_empty
    (pending : RankedPages rank start stop pages)
    (small : stop < 2 ^ rank) : pages = [] := by
  cases pending with
  | nil => rfl
  | cons page regular above =>
    have total := page.tiles.floorSum (2 ^ rank) regular
    simp only [Array.length_toList] at total
    have nonempty : 1 ≤ _ := page.nonempty
    have mul : 2 ^ rank ≤ 2 ^ rank * _ :=
      Nat.le_trans (by simp) (Nat.mul_le_mul_left _ (show 1 ≤ _ from by
        simpa only [Array.length_toList] using nonempty))
    omega

private theorem page_append {first stop rank : Nat} {page : Page} {ref : Ref}
    (rows : PageRows first stop page) (regular : Regular rank page)
    (follows : ref.firstRow = stop) (positive : 0 < ref.count) :
    PageRows first (ref.firstRow + ref.count) (page.add ref) ∧
      Fringe rank (page.add ref) ∧ (2 ^ rank ≤ ref.count → Regular rank (page.add ref)) := by
  have tileRef : Tiles stop (ref.firstRow + ref.count) [ref] := ⟨follows, rfl⟩
  refine ⟨⟨by simp [Page.add], ?_, ?_⟩, ?_, ?_⟩
  · simpa [Page.add] using rows.tiles.append tileRef
  · intro seen has
    simp [Page.add] at has
    rcases has with old | rfl
    · exact rows.positive seen (by simpa using old)
    · exact positive
  · intro seen has
    have old : seen ∈ page.refs.toList := by simpa [Page.add] using has
    exact regular seen old
  · intro amount seen has
    simp [Page.add] at has
    rcases has with old | rfl
    · exact regular seen (by simpa using old)
    · exact amount

/-- With at least two regular children, promotion doubles the guaranteed
minimum row span, including when the preferred target is smaller. -/
theorem promotion_rank {rank first stop : Nat} {page : Page} {ref : Ref} {target : Nat}
    (rows : PageRows first stop page) (regular : Regular rank page)
    (flush : page.shouldFlush ref target = true) :
    2 ^ (rank + 1) ≤ stop - first := by
  have mass := rows.tiles.floorSum (2 ^ rank) regular
  have two := Page.flush_has_two _ _ _ flush
  have mul := Nat.mul_le_mul_left (2 ^ rank) (show 2 ≤ page.refs.toList.length by simpa using two)
  rw [Nat.pow_succ]
  omega

private def heightError : String := "SSTable index height exceeds format limit"

/-- The pure reference interpreter leaves other failures available. This
predicate excludes a height failure and characterizes a returned result. -/
private def Post (action : ModelM α) (result : α → Prop) : Prop :=
  ∀ file, match action.run file with
  | .error message => message ≠ heightError
  | .ok (value, _) => result value

private theorem Post.pure {value : α} {result : α → Prop}
    (valid : result value) : Post (pure value : ModelM α) result :=
  fun _ => valid

private theorem Post.throw {result : α → Prop} (message : String)
    (different : message ≠ heightError) : Post (throw message : ModelM α) result :=
  fun _ => different

private theorem Post.bind {action : ModelM α} {next : α → ModelM β}
    {before : α → Prop} {after : β → Prop} (first : Post action before)
    (rest : ∀ value, before value → Post (next value) after) : Post (action >>= next) after := by
  intro file
  have step := first file
  cases observed : action.run file with
  | error message =>
    change match (action.run file).bind (fun (value, mid) => (next value).run mid) with
      | .error message => message ≠ heightError
      | .ok (value, _) => after value
    simpa only [observed, Except.bind] using step
  | ok outcome =>
    obtain ⟨value, mid⟩ := outcome
    change match (action.run file).bind (fun (value, mid) => (next value).run mid) with
      | .error message => message ≠ heightError
      | .ok (value, _) => after value
    rw [observed] at step
    simpa only [observed, Except.bind] using rest value step mid

private theorem writePacket_post (crc : Checksum) (layout : Layout) (options : BuildOptions)
    (kind : UInt64) (limit offset : Nat) (body : ByteArray) :
    Post ((modelWriter crc layout options).writePacket kind limit offset body)
      (· = offset + (body.size + checksumSize)) := by
  by_cases packet : body.size + checksumSize ≤ limit
  · by_cases file : offset + (body.size + checksumSize) + footerPacketSize ≤ maxFileSize
    · simp only [Writer.writePacket, packet, file, ↓reduceIte, modelWriter]
      refine Post.bind (before := fun _ => True) ?_ fun _ _ => .pure rfl
      exact fun _ => True.intro
    · simp only [Writer.writePacket, packet, file, ↓reduceIte, modelWriter]
      intro state
      change "SSTable file exceeds signed offset limit" ≠ heightError
      decide
  · simp only [Writer.writePacket, packet, ↓reduceIte, modelWriter]
    intro state
    change "SSTable packet exceeds size limit" ≠ heightError
    decide

private theorem writePage_post (crc : Checksum) (layout : Layout) (options : BuildOptions)
    (height offset first stop : Nat) (page : Page) (rows : PageRows first stop page) :
    Post ((modelWriter crc layout options).writePage height offset page)
      (fun result => result.1.firstRow = first ∧ result.1.count = stop - first) := by
  cases head : page.refs[0]? with
  | none =>
    simp only [Writer.writePage, head, modelWriter]
    exact .throw _ (by decide)
  | some firstRef =>
    cases back : page.refs.back? with
    | none =>
      simp only [Writer.writePage, head, back, modelWriter]
      exact .throw _ (by decide)
    | some lastRef =>
      simp only [Writer.writePage, head, back]
      have firstRow : firstRef.firstRow = first :=
        rows.tiles.head (by simpa [List.head?_eq_getElem?] using head)
      have lastRow : lastRef.firstRow + lastRef.count = stop :=
        rows.tiles.last (by simpa only [Array.getLast?_toList] using back)
      exact (writePacket_post crc layout options _ _ _ _).bind
        (fun _ _ => .pure ⟨firstRow, by rw [lastRow, firstRow]⟩)

private theorem single_page {ref : Ref} (positive : 0 < ref.count) (rank : Nat) :
    PageRows ref.firstRow (ref.firstRow + ref.count) (({} : Page).add ref) ∧
      Fringe rank (({} : Page).add ref) ∧
      (2 ^ rank ≤ ref.count → Regular rank (({} : Page).add ref)) := by
  refine ⟨⟨by simp [Page.add], ⟨rfl, rfl⟩, ?_⟩, ?_, ?_⟩
  · intro child member
    simp [Page.add] at member
    simpa only [member] using positive
  · simp [Fringe, Page.add]
  · intro minimum child member
    simp [Page.add] at member
    simpa only [member] using minimum

private theorem proper_rank (rank : Nat) (ranked : 2 ^ rank ≤ maxFileSize) :
    rank < maxHeight := by
  by_cases fits : rank < maxHeight
  · exact fits
  have full : 2 ^ maxHeight = maxFileSize + 1 := by decide
  have grows : 2 ^ maxHeight ≤ 2 ^ rank := Nat.pow_le_pow_right (by decide) (by omega)
  omega

private theorem push_post (crc : Checksum) (layout : Layout) (options : BuildOptions)
    (rank height offset start middle fuel : Nat) (pageList : List Page) (ref : Ref)
    (pending : RankedPages rank start middle pageList) (arrives : ref.firstRow = middle)
    (positive : 0 < ref.count) (cap : ref.firstRow + ref.count ≤ maxFileSize)
    (reserve : 0 < fuel) (span : rank + fuel = maxHeight) :
    Post ((modelWriter crc layout options).push height offset ref pageList fuel)
      (fun result => FringePages rank start (ref.firstRow + ref.count) result.2 ∧
        (2 ^ rank ≤ ref.count → RankedPages rank start (ref.firstRow + ref.count) result.2)) := by
  induction fuel generalizing rank height offset start middle pageList ref with
  | zero => omega
  | succ fuel ih =>
    obtain ⟨single, oneFringe, oneRegular⟩ := single_page positive rank
    cases pending with
    | nil =>
      simp only [Writer.push]
      exact .pure ⟨.cons single oneFringe (arrives ▸ RankedPages.nil),
        fun minimum => .cons single (oneRegular minimum) (arrives ▸ RankedPages.nil)⟩
    | cons rows regular above =>
      rename_i mid page upper
      by_cases flush : page.shouldFlush ref options.indexTarget = true
      · simp only [Writer.push, show (modelWriter crc layout options).options = options by rfl,
          flush, ↓reduceIte]
        apply (writePage_post crc layout options height offset mid middle page rows).bind
        rintro ⟨promoted, next⟩ ⟨starts, counts⟩
        have promotedMass := promotion_rank rows regular flush
        have enough : 2 ^ (rank + 1) ≤ promoted.count := by
          change promoted.count = middle - mid at counts
          rw [counts]
          exact promotedMass
        change promoted.firstRow = mid at starts
        change promoted.count = middle - mid at counts
        have originalLow := rows.tiles.lower
        have endEq : promoted.firstRow + promoted.count = middle := by
          rw [starts, counts]
          omega
        have promotedCap : promoted.firstRow + promoted.count ≤ maxFileSize := by omega
        have rankBelow := proper_rank (rank + 1) (by omega)
        have keepGoing : 0 < fuel := by omega
        have right := ih (rank + 1) (height + 1) next start mid upper promoted
          above starts (by have pow := Nat.two_pow_pos (rank + 1); omega) promotedCap keepGoing (by omega)
        apply right.bind
        rintro ⟨stop, pages⟩ ⟨_, normal⟩
        have installed := normal enough
        change RankedPages (rank + 1) start (promoted.firstRow + promoted.count) pages at installed
        rw [endEq, ← arrives] at installed
        exact .pure ⟨.cons single oneFringe installed,
          fun minimum => .cons single (oneRegular minimum) installed⟩
      · simp only [Writer.push, show (modelWriter crc layout options).options = options by rfl,
          flush, Bool.false_eq_true, ↓reduceIte]
        obtain ⟨grown, fringe, normal⟩ := page_append rows regular arrives positive
        exact .pure ⟨.cons grown fringe above, fun minimum => .cons grown (normal minimum) above⟩

private theorem finish_post (crc : Checksum) (layout : Layout) (options : BuildOptions)
    (rank height offset start stop fuel : Nat) (pageList : List Page)
    (pending : pageList = [] ∨ FringePages rank start stop pageList)
    (cap : stop ≤ maxFileSize) (reserve : 0 < fuel) (span : rank + fuel = maxHeight) :
    Post ((modelWriter crc layout options).finishPages height offset pageList fuel)
      (fun result => result.1 < height + fuel) := by
  induction fuel generalizing rank height offset start stop pageList with
  | zero => omega
  | succ fuel ih =>
    rcases pending with rfl | pending
    · simp only [Writer.finishPages]
      exact .pure (by dsimp; omega)
    cases pending with
    | cons rows fringe above =>
      rename_i mid page upper
      simp only [Writer.finishPages]
      apply (writePage_post crc layout options height offset mid stop page rows).bind
      rintro ⟨promoted, next⟩ ⟨starts, counts⟩
      by_cases top : upper.isEmpty = true
      · simp only [top, ↓reduceIte]
        exact .pure (by dsimp; omega)
      · simp only [top]
        change promoted.firstRow = mid at starts
        change promoted.count = stop - mid at counts
        have scope := rows.tiles.lower
        have promotedEnd : promoted.firstRow + promoted.count = stop := by
          rw [starts, counts]
          omega
        have nextFuel : 0 < fuel := by
          by_cases zero : fuel = 0
          · have rankTop : rank + 1 = maxHeight := by omega
            have exceeds : mid < 2 ^ (rank + 1) := by
              rw [rankTop, show 2 ^ maxHeight = maxFileSize + 1 by decide]
              omega
            exact False.elim (top (by simp [above.upper_empty exceeds]))
          · omega
        apply (push_post crc layout options (rank + 1) (height + 1) next start mid fuel upper promoted
          above starts (by have := rows.strict; omega) (promotedEnd ▸ cap) nextFuel (by omega)).bind
        rintro ⟨offset, rest⟩ ⟨prepared, _⟩
        change FringePages (rank + 1) start (promoted.firstRow + promoted.count) rest at prepared
        rw [promotedEnd] at prepared
        have progressed := ih (rank + 1) (height + 1) offset start stop rest (.inr prepared)
          cap nextFuel (by omega)
        intro file
        have observed := progressed file
        cases ran : ((modelWriter crc layout options).finishPages (height + 1) offset rest fuel).run file with
        | error msg => simpa only [ran] using observed
        | ok result =>
          obtain ⟨observedHeight, after⟩ := result
          rw [ran] at observed
          have bound : observedHeight.1 < height + 1 + fuel := observed
          change observedHeight.1 < height + (fuel + 1)
          omega

private theorem RankedPages.fringe {rank start stop : Nat} {pageList : List Page}
    (pending : RankedPages rank start stop pageList) :
    pageList = [] ∨ FringePages rank start stop pageList := by
  cases pending with
  | nil => exact .inl rfl
  | cons rows regular above =>
    exact .inr (.cons rows (fun ref mem => regular ref (List.dropLast_subset _ mem)) above)

/-- A regular append keeps the pending rank invariant on the actual writer
state. The supplier cap leaves room for every resulting promotion. -/
theorem Writer.push_ranked (crc : Checksum) (layout : Layout) (options : BuildOptions)
    (offset : Nat) (pageList : List Page) (ref : Ref) (file : ModelFile)
    (pending : RankedPages 0 0 ref.firstRow pageList) (positive : 0 < ref.count)
    (cap : ref.firstRow + ref.count ≤ maxFileSize) :
    match ((⟨crc, layout, modelSink, id, options⟩ : Writer ModelM String).push
      1 offset ref pageList maxHeight).run file with
    | .error message => message ≠ "SSTable index height exceeds format limit"
    | .ok ((_, pages), _) => RankedPages 0 0 (ref.firstRow + ref.count) pages := by
  have checked := push_post crc layout options 0 1 offset 0 ref.firstRow maxHeight pageList ref
    pending rfl positive cap (by decide) rfl file
  change match ((modelWriter crc layout options).push 1 offset ref pageList maxHeight).run file with
    | .error msg => msg ≠ _
    | .ok ((_, pages), _) => RankedPages 0 0 (ref.firstRow + ref.count) pages
  cases ran : ((modelWriter crc layout options).push 1 offset ref pageList maxHeight).run file with
  | error error => simpa only [ran, heightError] using checked
  | ok result =>
    obtain ⟨⟨next, pages⟩, after⟩ := result
    rw [ran] at checked
    exact checked.2 (by simpa using Nat.succ_le_of_lt positive)

/-- A bounded regular supplier cannot exhaust the promotion height budget.
Packet and file extent failures remain independent of this result. -/
theorem Writer.push_height (crc : Checksum) (layout : Layout) (options : BuildOptions)
    (offset : Nat) (pageList : List Page) (ref : Ref) (file : ModelFile)
    (pending : RankedPages 0 0 ref.firstRow pageList) (positive : 0 < ref.count)
    (cap : ref.firstRow + ref.count ≤ maxFileSize) :
    ((⟨crc, layout, modelSink, id, options⟩ : Writer ModelM String).push
      1 offset ref pageList maxHeight).run file ≠
      .error "SSTable index height exceeds format limit" := by
  intro failed
  have executed := Writer.push_ranked crc layout options offset pageList ref file pending positive cap
  rw [failed] at executed
  exact executed rfl

/-- The executable finalization has enough height even when its rightmost
reference is short. It either fails at an independent format limit or returns
a root height representable in the footer. -/
theorem Writer.finishPages_height (crc : Checksum) (layout : Layout) (options : BuildOptions)
    (offset count : Nat) (pageList : List Page) (file : ModelFile)
    (pending : RankedPages 0 0 count pageList) (cap : count ≤ maxFileSize) :
    match ((⟨crc, layout, modelSink, id, options⟩ : Writer ModelM String).finishPages
      1 offset pageList maxHeight).run file with
    | .error message => message ≠ "SSTable index height exceeds format limit"
    | .ok ((height, _, _), _) => height ≤ maxHeight := by
  have checked := finish_post crc layout options 0 1 offset 0 count maxHeight pageList
    pending.fringe cap (by decide) rfl file
  cases ran : ((modelWriter crc layout options).finishPages 1 offset pageList maxHeight).run file with
  | error error =>
    change match ((modelWriter crc layout options).finishPages 1 offset pageList maxHeight).run file with
      | .error msg => msg ≠ _
      | .ok ((height, _, _), _) => height ≤ maxHeight
    rw [ran]
    simpa only [ran, heightError] using checked
  | ok result =>
    obtain ⟨⟨height, rootOffset, rootSize⟩, after⟩ := result
    change match ((modelWriter crc layout options).finishPages 1 offset pageList maxHeight).run file with
      | .error msg => msg ≠ _
      | .ok ((height, _, _), _) => height ≤ maxHeight
    rw [ran] at checked ⊢
    have bound : height < 1 + maxHeight := checked
    omega

end ImmutableSSTable.Recursive
