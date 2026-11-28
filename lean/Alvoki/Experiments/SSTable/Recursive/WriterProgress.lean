import Alvoki.Experiments.SSTable.Recursive.WriterPages
import Alvoki.Experiments.SSTable.Proofs.UnifiedBuilder

namespace ImmutableSSTable.Recursive

open Unified (Layout Checksum Ref checksumSize encodeData encodeIndex encodePacket encodePacket_size
  ModelM ModelFile modelSink)

/-- The local extent check leaves one append when the packet and footer
fit. A caller can supply successful append effects under its own I/O contract. -/
theorem Writer.writePacket_of_room [Monad m] [MonadExceptOf ε m]
    (writer : Writer m ε) (kind : UInt64) (limit offset : Nat) (body : ByteArray)
    (packet : body.size + checksumSize ≤ limit)
    (room : offset + (body.size + checksumSize) + footerPacketSize ≤ maxFileSize) :
    writer.writePacket kind limit offset body = (do
      writer.sink.write (encodePacket writer.crc writer.layout.tableId kind offset body)
      return offset + (body.size + checksumSize)) := by
  simp only [Writer.writePacket, packet, room, ↓reduceIte]

/-- A pending page has both endpoints and a representable packet. The
remaining file extent suffices for the page's only append and the future
footer. The returned reference covers the exact pending row range. -/
theorem Writer.writePage_of_room [Monad m] [LawfulMonad m] [MonadExceptOf ε m]
    (writer : Writer m ε)
    (pending : PendingPage writer.layout writer.crc bytes rows offset height first stop page)
    (room : offset + (page.bytes + checksumSize) + footerPacketSize ≤ maxFileSize) :
    ∃ fence, page.refs.back?.map Ref.lastKey = some fence ∧
      writer.writePage (height + 1) offset page = (do
        writer.sink.write (encodePacket writer.crc writer.layout.tableId
          (indexKind (height + 1)) offset (encodeIndex page.refs))
        return (⟨fence, offset, page.bytes + checksumSize, first, stop - first⟩,
          offset + (page.bytes + checksumSize))) := by
  cases head : page.refs[0]? with
  | none =>
    have out := Array.getElem?_eq_none_iff.mp head
    have nonempty := pending.nonempty
    omega
  | some lead =>
    cases back : page.refs.back? with
    | none =>
      have empty := Array.back?_eq_none_iff.mp back
      have nonempty := pending.nonempty
      simp [empty] at nonempty
    | some last =>
      have firstEq := pending.start lead head
      have stopEq := pending.finish last back
      have packet : (encodeIndex page.refs).size + checksumSize ≤ maxIndexSize := pending.pageValid.bounded
      have exactRoom : offset + ((encodeIndex page.refs).size + checksumSize) + footerPacketSize ≤ maxFileSize :=
        pending.length ▸ room
      have subtract : offset + (page.bytes + checksumSize) - offset = page.bytes + checksumSize :=
        Nat.add_sub_cancel_left _ _
      refine ⟨last.lastKey, rfl, ?_⟩
      simp only [Writer.writePage, head, back, writer.writePacket_of_room _ _ _ _ packet exactRoom,
        ← pending.length, bind_assoc, pure_bind, subtract, firstEq, stopEq]

/-- Concrete success in the append-only model, including its exact new byte
stream. Only the current page append is covered by this physical budget. -/
theorem Writer.writePage_progress (crc : Checksum) (layout : Layout) (options : BuildOptions)
    (file : ModelFile)
    (pending : PendingPage layout crc file.bytes rows file.bytes.size height first stop page)
    (room : file.bytes.size + (page.bytes + checksumSize) + footerPacketSize ≤ maxFileSize) :
    ∃ ref, ((⟨crc, layout, modelSink, id, options⟩ : Writer ModelM String).writePage
      (height + 1) file.bytes.size page).run file =
        .ok ((ref, file.bytes.size + (page.bytes + checksumSize)),
          { file with bytes := file.bytes ++ (encodePacket crc layout.tableId
            (indexKind (height + 1)) file.bytes.size (encodeIndex page.refs)) }) ∧
      ref.offset = file.bytes.size ∧ ref.size = page.bytes + checksumSize ∧
      ref.firstRow = first ∧ ref.count = stop - first ∧
      page.refs.back?.map Ref.lastKey = some ref.lastKey := by
  let writer : Writer ModelM String := ⟨crc, layout, modelSink, id, options⟩
  obtain ⟨fence, back, write⟩ := writer.writePage_of_room pending room
  refine ⟨⟨fence, file.bytes.size, page.bytes + checksumSize, first, stop - first⟩,
    ?_, rfl, rfl, rfl, rfl, back⟩
  change (writer.writePage (height + 1) file.bytes.size page).run file = _
  rw [write]
  rfl

/-- A push can flush each previously pending page once. This sum reserves
all such appends independently of the target or incoming reference. -/
def pendingPacketBytes : List Page → Nat
  | [] => 0
  | page :: upper => page.bytes + checksumSize + pendingPacketBytes upper

private def modelWriter (crc : Checksum) (layout : Layout) (options : BuildOptions) :
    Writer ModelM String :=
  ⟨crc, layout, modelSink, id, options⟩

/-- A push terminates successfully in the append-only model when one extra
level is available and the extent reserves all currently pending pages.
The row supplier is unchanged and the returned position is the exact new
byte length. -/
theorem Writer.push_progress (crc : Checksum) (layout : Layout) (options : BuildOptions)
    {file : ModelFile} {rows : List Entry} {height stop : Nat} {pages : List Page}
    (pending : PendingPages layout crc file.bytes rows file.bytes.size height stop pages)
    (ref : Ref) (fuel : Nat) (levels : pages.length < fuel)
    (room : file.bytes.size + pendingPacketBytes pages + footerPacketSize ≤ maxFileSize) :
    ∃ position placed written,
      ((⟨crc, layout, modelSink, id, options⟩ : Writer ModelM String).push
        (height + 1) file.bytes.size ref pages fuel).run file = .ok ((position, placed), written) ∧
      position = written.bytes.size ∧
      position ≤ file.bytes.size + pendingPacketBytes pages ∧ written.rows = file.rows := by
  induction fuel generalizing file height stop pages ref with
  | zero => omega
  | succ fuel ih =>
    cases pending with
    | nil =>
      exact ⟨_, _, file, rfl, rfl, by simp [pendingPacketBytes], rfl⟩
    | @cons height first upper stop page higher current =>
      by_cases flush : page.shouldFlush ref options.indexTarget = true
      · let packet := encodePacket crc layout.tableId (indexKind (height + 1))
          file.bytes.size (encodeIndex page.refs)
        have exactSize : packet.size = page.bytes + checksumSize := by
          simp [packet, ← current.length]
        let mid : ModelFile := { file with bytes := file.bytes ++ packet }
        have cursor : mid.bytes.size = file.bytes.size + (page.bytes + checksumSize) := by
          simp [mid, exactSize]
        have localRoom : file.bytes.size + (page.bytes + checksumSize) + footerPacketSize ≤ maxFileSize := by
          simp only [pendingPacketBytes] at room
          omega
        obtain ⟨promoted, write, _, _, _, _, _⟩ := Writer.writePage_progress crc layout options file
          current localRoom
        have lifted : PendingPages layout crc mid.bytes rows mid.bytes.size (height + 1) first upper :=
          higher.extend packet (by rw [cursor]; omega) (Nat.le_refl _)
        have reserve : mid.bytes.size + pendingPacketBytes upper + footerPacketSize ≤ maxFileSize := by
          simp only [pendingPacketBytes] at room
          omega
        have slots : upper.length < fuel := by simpa using levels
        obtain ⟨position, placed, written, proceeded, reached, bound, supplied⟩ :=
          ih lifted promoted slots reserve
        refine ⟨position, ({} : Page).add ref :: placed, written, ?_, reached, ?_, supplied⟩
        · change ((modelWriter crc layout options).push (height + 1) file.bytes.size ref
            (page :: upper) (fuel + 1)).run file = _
          simp only [Writer.push, show (modelWriter crc layout options).options = options from rfl,
            flush, ↓reduceIte]
          change (((modelWriter crc layout options).writePage (height + 1) file.bytes.size page).run file).bind _ = _
          rw [show ((modelWriter crc layout options).writePage (height + 1) file.bytes.size page).run file =
            .ok ((promoted, file.bytes.size + (page.bytes + checksumSize)), mid) from write]
          simp only [Except.bind]
          rw [← cursor]
          change (((modelWriter crc layout options).push (height + 1 + 1) mid.bytes.size promoted upper
            fuel).run mid).bind _ = _
          rw [show ((modelWriter crc layout options).push (height + 1 + 1) mid.bytes.size promoted
            upper fuel).run mid = .ok ((position, placed), written) from proceeded]
          rfl
        · simp only [pendingPacketBytes]
          omega
      · refine ⟨file.bytes.size, page.add ref :: upper, file, ?_, rfl, by omega, rfl⟩
        change ((modelWriter crc layout options).push (height + 1) file.bytes.size ref
          (page :: upper) (fuel + 1)).run file = _
        simp only [Writer.push, show (modelWriter crc layout options).options = options from rfl,
          flush, Bool.false_eq_true, ↓reduceIte]
        rfl

/-- A data flush succeeds when the encoded data packet fits, the current
pending stack has space for a promotion, and the exact packet plus the
pending-page reserve fit the file. The supplier state remains unchanged. -/
theorem Writer.flushData_progress (crc : Checksum) (layout : Layout) (options : BuildOptions)
    {file : ModelFile} {rows : List Entry} {state : BuilderState}
    (position : state.offset = file.bytes.size)
    (pending : PendingPages layout crc file.bytes rows file.bytes.size 0
      (state.count - state.data.size) state.pages)
    (packet : (encodeData layout state.data).size + checksumSize ≤ maxRowSize)
    (levels : state.pages.length < maxHeight)
    (room : file.bytes.size + ((encodeData layout state.data).size + checksumSize) +
      pendingPacketBytes state.pages + footerPacketSize ≤ maxFileSize) :
    ∃ next out, ((⟨crc, layout, modelSink, id, options⟩ : Writer ModelM String).flushData state).run
      file = .ok (next, out) ∧ next.offset = out.bytes.size ∧ next.count = state.count ∧
      next.data = #[] ∧ out.rows = file.rows := by
  let writer := modelWriter crc layout options
  cases back : state.data.back? with
  | none =>
    refine ⟨state, file, ?_, position, rfl, Array.back?_eq_none_iff.mp back, rfl⟩
    simp only [Writer.flushData, back]
    rfl
  | some last =>
    let body := encodeData layout state.data
    let payload := encodePacket crc layout.tableId dataKind file.bytes.size body
    let size := body.size + checksumSize
    let mid : ModelFile := { file with bytes := file.bytes ++ payload }
    have cursor : mid.bytes.size = file.bytes.size + size := by simp [mid, payload, size]
    have writeRoom : file.bytes.size + size + footerPacketSize ≤ maxFileSize := by
      change file.bytes.size + size + pendingPacketBytes state.pages + footerPacketSize ≤ maxFileSize at room
      omega
    have write : (writer.writePacket dataKind maxRowSize file.bytes.size body).run file =
        .ok (file.bytes.size + size, mid) := by
      rw [writer.writePacket_of_room _ _ _ _ packet writeRoom]
      rfl
    let ref : Ref := ⟨last.key, file.bytes.size, mid.bytes.size - file.bytes.size,
      state.count - state.data.size, state.data.size⟩
    have above : PendingPages layout crc mid.bytes rows mid.bytes.size 0
        (state.count - state.data.size) state.pages :=
      pending.extend payload (by rw [cursor]; omega) (Nat.le_refl _)
    have addRoom : mid.bytes.size + pendingPacketBytes state.pages + footerPacketSize ≤ maxFileSize :=
      cursor.symm ▸ room
    obtain ⟨stop, pages, out, pushed, endEq, _, preserves⟩ :=
      Writer.push_progress crc layout options above ref maxHeight levels addRoom
    refine ⟨{ state with offset := stop, data := #[], payloadBytes := 0, pages := pages },
      out, ?_, endEq, rfl, rfl, preserves⟩
    change (writer.flushData state).run file = _
    simp only [Writer.flushData, back, position]
    change ((writer.writePacket dataKind maxRowSize file.bytes.size body).run file).bind _ = _
    rw [write]
    simp only [Except.bind]
    rw [← cursor]
    change ((writer.push 1 mid.bytes.size ref state.pages maxHeight).run mid).bind _ = _
    rw [show (writer.push 1 mid.bytes.size ref state.pages maxHeight).run mid =
      .ok ((stop, pages), out) from pushed]
    rfl

/-- When finalization has reached a single root page, the exact page budget
suffices for the actual finalization step. -/
theorem Writer.finishRoot_progress (crc : Checksum) (layout : Layout) (options : BuildOptions)
    {file : ModelFile} {rows : List Entry} {height first stop : Nat} {page : Page}
    (pending : PendingPage layout crc file.bytes rows file.bytes.size height first stop page)
    (fuel : Nat)
    (room : file.bytes.size + (page.bytes + checksumSize) + footerPacketSize ≤ maxFileSize) :
    ((⟨crc, layout, modelSink, id, options⟩ : Writer ModelM String).finishPages
      (height + 1) file.bytes.size [page] (fuel + 1)).run file =
      .ok ((height + 1, file.bytes.size, page.bytes + checksumSize),
        { file with bytes := file.bytes ++ (encodePacket crc layout.tableId
          (indexKind (height + 1)) file.bytes.size (encodeIndex page.refs)) }) := by
  let writer := modelWriter crc layout options
  obtain ⟨ref, write, atOffset, size, _, _, _⟩ :=
    Writer.writePage_progress crc layout options file pending room
  change (writer.finishPages (height + 1) file.bytes.size [page] (fuel + 1)).run file = _
  simp only [Writer.finishPages]
  change ((writer.writePage (height + 1) file.bytes.size page).run file).bind _ = _
  rw [show (writer.writePage (height + 1) file.bytes.size page).run file = _ from write]
  simp only [Except.bind, atOffset, size]
  rfl

end ImmutableSSTable.Recursive
