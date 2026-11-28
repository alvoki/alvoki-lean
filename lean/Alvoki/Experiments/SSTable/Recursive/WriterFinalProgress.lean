import Alvoki.Experiments.SSTable.Recursive.WriterProgress
import Alvoki.Experiments.SSTable.Recursive.WriterProofs

namespace ImmutableSSTable.Recursive

open Unified (Layout Checksum Ref ModelM ModelFile modelSink checksumSize encodeIndex
  encodePacket encodePacket_size)

/-- A finalization step writes its own page and can displace each pending
page above it. With `fuel` slots this reserves one triangular sum of
maximum-sized logical index packets. -/
def finalizationReserve : Nat → Nat
  | 0 => 0
  | fuel + 1 => maxIndexSize * (fuel + 1) + finalizationReserve fuel

private theorem tiles_start_le {first stop : Nat} {refs : List Ref}
    (tiles : Tiles first stop refs) : first ≤ stop := by
  induction refs generalizing first with
  | nil => exact Nat.le_of_eq tiles
  | cons ref tail ih =>
    obtain ⟨rfl, tiled⟩ := tiles
    exact Nat.le_trans (Nat.le_add_right _ _) (ih tiled)

private theorem tiled_head_count {first stop : Nat} {refs : List Ref} {ref : Ref}
    (tiles : Tiles first stop refs) (head : refs.head? = some ref) :
    ref.firstRow = first ∧ ref.count ≤ stop := by
  cases refs with
  | nil => simp at head
  | cons r tail =>
    have same : r = ref := by simpa using head
    subst r
    have ends := tiles_start_le tiles.2
    exact ⟨tiles.1, by omega⟩

private theorem page_head_exists {page : Page} (nonempty : 0 < page.refs.size) :
    ∃ head, page.refs[0]? = some head := by
  cases atHead : page.refs[0]? with
  | none =>
    have emptySize := Array.getElem?_eq_none_iff.mp atHead
    omega
  | some ref => exact ⟨ref, rfl⟩

private theorem pendingBytes_le {layout crc bytes rows endAt height stop pages}
    (pending : PendingPages layout crc bytes rows endAt height stop pages) :
    pendingPacketBytes pages ≤ maxIndexSize * pages.length := by
  induction pending with
  | nil => simp [pendingPacketBytes]
  | cons upper current ih =>
    simp only [pendingPacketBytes, List.length_cons, Nat.mul_succ]
    have size := current.packetBound
    omega

private theorem finishPages_progressFrom (crc : Checksum) (layout : Layout)
    (options : BuildOptions) (file : ModelFile) (rows : List Entry) (height stop fuel : Nat)
    (pages : List Page)
    (pending : PendingPages layout crc file.bytes rows file.bytes.size height stop pages)
    (ranks : pages = [] ∨ FringePages height 0 stop pages)
    (ordered : Ordered (rows.take stop)) (rowLimit : stop ≤ maxFileSize)
    (target : options.indexTarget ≤ maxRowSize) (levels : 0 < fuel)
    (heightFuel : height + fuel = maxHeight)
    (spare : stop < 2 ^ (height + fuel - 1))
    (room : file.bytes.size + finalizationReserve fuel + footerPacketSize ≤ maxFileSize) :
    ∃ rootHeight rootOffset rootSize after,
      ((modelWriter crc layout options).finishPages (height + 1) file.bytes.size pages fuel).run
        file = .ok ((rootHeight, rootOffset, rootSize), after) ∧
      Appended file after after.bytes.size := by
  induction fuel generalizing file height stop pages with
  | zero => omega
  | succ fuel ih =>
    cases pending with
    | nil =>
      exact ⟨0, 0, 0, file, rfl, Appended.same file (by omega)⟩
    | @cons height first upper stop page higher current =>
      rcases ranks with empty | fringe
      · cases empty
      cases fringe with
      | @cons mid page upper rowShape lower regular =>
        have sameMid : mid = first := by
          obtain ⟨head, found⟩ := page_head_exists current.nonempty
          have listHead : page.refs.toList.head? = some head := by
            simpa [List.head?_eq_getElem?] using found
          exact (tiled_head_count rowShape.tiles listHead).1.symm.trans (current.start head found)
        subst mid
        have packetBound := current.packetBound
        have localRoom : file.bytes.size + (page.bytes + checksumSize) + footerPacketSize ≤
            maxFileSize := by
          simp only [finalizationReserve, Nat.mul_succ] at room
          omega
        by_cases top : upper.isEmpty = true
        · have empty := List.isEmpty_iff.mp top
          subst upper
          let payload := encodePacket crc layout.tableId (indexKind (height + 1))
            file.bytes.size (encodeIndex page.refs)
          let after : ModelFile := { file with bytes := file.bytes ++ payload }
          have appendSize : after.bytes.size = file.bytes.size + (page.bytes + checksumSize) := by
            simp [after, payload, ← current.length]
          exact ⟨height + 1, file.bytes.size, page.bytes + checksumSize, after,
            Writer.finishRoot_progress crc layout options current fuel localRoom,
            ⟨rfl, rfl, ⟨payload, rfl⟩, by rw [appendSize]; exact localRoom⟩⟩
        · have firstScope := current.first_le
          have hasFuel : 0 < fuel := by
            by_cases zero : fuel = 0
            · have upperSmall : first < 2 ^ (height + 1) := by
                have same : height + (fuel + 1) - 1 ≤ height + 1 := by omega
                have up := Nat.pow_le_pow_right (by decide : 0 < (2 : Nat)) same
                omega
              exact False.elim (top (by simp [regular.upper_empty upperSmall]))
            · omega
          have nextUpper : first < 2 ^ (height + 1 + fuel - 1) := by
            simpa only [Nat.add_assoc, Nat.add_comm 1 fuel] using Nat.lt_of_le_of_lt firstScope spare
          have slots := regular.length_lt fuel hasFuel nextUpper
          let payload := encodePacket crc layout.tableId (indexKind (height + 1))
            file.bytes.size (encodeIndex page.refs)
          let beforePush : ModelFile := { file with bytes := file.bytes ++ payload }
          have cursor : beforePush.bytes.size = file.bytes.size + (page.bytes + checksumSize) := by
            simp [beforePush, payload, ← current.length]
          obtain ⟨promoted, wrote, _, _, _, _, _⟩ :=
            Writer.writePage_progress crc layout options file current localRoom
          have exactWrite : ((modelWriter crc layout options).writePage (height + 1)
              file.bytes.size page).run file =
              .ok ((promoted, file.bytes.size + (page.bytes + checksumSize)), beforePush) := wrote
          obtain ⟨appended, atOffset, _, firstEq, countEq, child⟩ :=
            writePage_ok current (Nat.le_refl _) rowLimit exactWrite
          have newer : PendingPages layout crc beforePush.bytes rows beforePush.bytes.size
              (height + 1) first upper := higher.extend payload (by rw [cursor]; omega) (Nat.le_refl _)
          have upperBudget := Nat.le_trans (pendingBytes_le higher)
            (Nat.mul_le_mul_left maxIndexSize (Nat.le_of_lt slots))
          have pushRoom : beforePush.bytes.size + pendingPacketBytes upper + footerPacketSize ≤ maxFileSize :=
            by
              simp only [finalizationReserve, Nat.mul_succ] at room
              omega
          obtain ⟨position, placed, afterPush, pushed, positionEq, positionBound, _⟩ :=
            Writer.push_progress crc layout options newer promoted fuel slots pushRoom
          have rowEnd : first + promoted.count = stop := by omega
          have atPrevious : file.bytes.size ≤ promoted.offset := Nat.le_of_eq atOffset.symm
          have prevFits : beforePush.bytes.size + footerPacketSize ≤ maxFileSize := by omega
          have orderedPush : Ordered (rows.take (first + promoted.count)) := by rwa [rowEnd]
          have exactPush : ((modelWriter crc layout options).push (height + 1 + 1)
              beforePush.bytes.size promoted upper fuel).run beforePush =
              .ok ((position, placed), afterPush) := pushed
          have extended : PendingPages layout crc beforePush.bytes rows file.bytes.size
              (height + 1) first upper := higher.extend payload (Nat.le_refl _) (by rw [cursor]; omega)
          obtain ⟨pushedFile, newPages⟩ := push_ok extended child atPrevious firstEq orderedPush
            target prevFits exactPush
          rw [rowEnd] at newPages
          have exactEnd : promoted.firstRow + promoted.count = stop := by omega
          have roomForFringe : promoted.firstRow + promoted.count ≤ maxFileSize :=
            exactEnd.symm ▸ rowLimit
          have newHeightFuel : height + 1 + fuel = maxHeight := by omega
          have rankedPush : FringePages (height + 1) 0 stop placed := by
            have ran := push_post crc layout options (height + 1) (height + 1 + 1)
              beforePush.bytes.size 0 first fuel upper promoted regular firstEq child.valid.2.2.1
              roomForFringe hasFuel newHeightFuel
            change Post ((modelWriter crc layout options).push (height + 1 + 1)
              beforePush.bytes.size promoted upper fuel)
              (fun value => FringePages (height + 1) 0
                (promoted.firstRow + promoted.count) value.2 ∧
                  (2 ^ (height + 1) ≤ promoted.count →
                    RankedPages (height + 1) 0 (promoted.firstRow + promoted.count) value.2)) at ran
            have ran := ran beforePush
            rw [exactPush] at ran
            have fringeAt : FringePages (height + 1) 0 (promoted.firstRow + promoted.count) placed := ran.1
            rw [exactEnd] at fringeAt
            exact fringeAt
          have nextSpare : stop < 2 ^ (height + 1 + fuel - 1) := by
            rw [newHeightFuel]
            rwa [heightFuel] at spare
          have depthRoom : afterPush.bytes.size + finalizationReserve fuel + footerPacketSize ≤
              maxFileSize := by
            simp only [finalizationReserve, Nat.mul_succ] at room
            omega
          obtain ⟨rootHeight, rootOffset, rootSize, after, finished, reached⟩ :=
            ih afterPush (height + 1) stop placed newPages (.inr rankedPush) ordered rowLimit hasFuel
              newHeightFuel nextSpare depthRoom
          refine ⟨rootHeight, rootOffset, rootSize, after, ?_,
            appended.trans (pushedFile.trans reached)⟩
          simp only [Writer.finishPages]
          change (((modelWriter crc layout options).writePage (height + 1) file.bytes.size page).run
            file).bind _ = _
          rw [exactWrite]
          simp only [Except.bind, top, Bool.false_eq_true, ↓reduceIte]
          rw [← cursor]
          change (((modelWriter crc layout options).push (height + 1 + 1) beforePush.bytes.size
            promoted upper fuel).run beforePush).bind _ = _
          rw [exactPush]
          simp only [Except.bind, positionEq]
          exact finished

/-- In the append-only interpreter every remaining index level finalizes
with a spare rank and the stated conservative disk reserve. The returned
append witness carries the exact byte cursor and the room for the footer. -/
theorem Writer.finishPages_progress (crc : Checksum) (layout : Layout) (options : BuildOptions)
    {file : ModelFile} {rows : List Entry} {stop : Nat} {pages : List Page}
    (pending : PendingPages layout crc file.bytes rows file.bytes.size 0 stop pages)
    (ranked : RankedPages 0 0 stop pages)
    (ordered : Ordered (rows.take stop)) (rowLimit : stop ≤ maxFileSize)
    (target : options.indexTarget ≤ maxRowSize)
    (spare : stop < 2 ^ (maxHeight - 1))
    (room : file.bytes.size + finalizationReserve maxHeight + footerPacketSize ≤ maxFileSize) :
    ∃ rootHeight rootOffset rootSize after,
      ((⟨crc, layout, modelSink, id, options⟩ : Writer ModelM String).finishPages
        1 file.bytes.size pages maxHeight).run file = .ok ((rootHeight, rootOffset, rootSize), after) ∧
      Appended file after after.bytes.size :=
  finishPages_progressFrom crc layout options file rows 0 stop maxHeight pages pending
    ranked.fringe ordered rowLimit target (by decide) rfl spare room

end ImmutableSSTable.Recursive
