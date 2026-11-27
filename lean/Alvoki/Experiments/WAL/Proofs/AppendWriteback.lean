import Alvoki.Experiments.WAL.Writeback

namespace WalRecoverySlice.Persistence

private def WalFile.marker (slot : Nat) : WalFile := if slot = 0 then .slot0 else .slot1

/-- When background writeback has already settled the target, a failing fsync
can report the same error at the already-settled image. -/
private def barrierAfterWriteback (p : Primitive) (files : List WalFile) (file : WalFile) : Primitive :=
  match p with
  | .before a => if file ∈ files then .after (some a) else .before a
  | .after abort => .after abort

def appendEffects (effects : Effects) (s : WritebackSchedule) : Effects :=
  { effects with
    dataSync := barrierAfterWriteback effects.dataSync s.dataSync .data
    markerSync := fun slot => barrierAfterWriteback (effects.markerSync slot) (s.markerSync slot) (.marker slot) }

private def WalFile.get (file : WalFile) (b : Image) : FileImage :=
  match file with
  | .data => b.data
  | .slot0 => b.slot0
  | .slot1 => b.slot1

private def WalFile.put (file : WalFile) (b : Image) (v : FileImage) : Image :=
  match file with
  | .data => {b with data := v}
  | .slot0 => {b with slot0 := v}
  | .slot1 => {b with slot1 := v}

private theorem settle_put_clean (file : WalFile) (b : Image) (v : FileImage) (clean : b.powerLoss = b) :
    (file.settle (file.put b v)).powerLoss = file.settle (file.put b v) := by
  obtain ⟨⟨dl, dd⟩, ⟨al, ad⟩, ⟨bl, bd⟩⟩ := b
  simp [Image.powerLoss, FileImage.powerLoss] at clean
  obtain ⟨rfl, rfl, rfl⟩ := clean
  cases file <;> rfl

private theorem settleFiles_written (files : List WalFile) (file : WalFile) (b : Image) (v : FileImage)
    (clean : b.powerLoss = b) :
    settleFiles files (file.put b v) =
      if file ∈ files then file.settle (file.put b v) else file.put b v := by
  induction files with
  | nil => simp [settleFiles]
  | cons current rest ih =>
    change settleFiles rest (current.settle (file.put b v)) = _
    by_cases same : file = current
    · subst current
      simp [settleFiles_clean _ _ (settle_put_clean file b v clean)]
    · have frame : current.settle (file.put b v) = file.put b v := by
        have base := current.settle_clean b clean
        cases file <;> cases current <;> simp_all [WalFile.settle, WalFile.put]
        all_goals first | exact congrArg Image.data base | exact congrArg Image.slot0 base | exact congrArg Image.slot1 base
      rw [frame, ih]
      simp [same]

private def fileSync (p : Primitive) (file : WalFile) : M Unit :=
  fun image => p.syncResult image (file.get image) (file.put image)

private theorem sync_written (p : Primitive) (files : List WalFile) (file : WalFile) (b : Image)
    (v : FileImage) (clean : b.powerLoss = b) :
    (withWritebacks files (fileSync p file)).run (file.put b v) =
    (fileSync (barrierAfterWriteback p files file) file).run (file.put b v) := by
  change p.syncResult (settleFiles files (file.put b v)) _ _ = _
  rw [settleFiles_written _ _ _ _ clean]
  by_cases hit : file ∈ files <;> cases p <;> cases file <;>
    simp only [fileSync, ExceptT.run, barrierAfterWriteback, hit, ↓reduceIte,
      Primitive.syncResult, WalFile.get, WalFile.put, WalFile.settle]
  all_goals first | rfl | rename_i a; cases a <;> rfl

private theorem bind_eq_on_return {left right : M α} {k k' : α → M β} {b : Image}
    (act : left.run b = right.run b)
    (cont : ∀ a post, right.run b = .ok (.ok a) post → (k a).run post = (k' a).run post) :
    (left >>= k).run b = (right >>= k').run b := by
  change left b = right b at act
  simp only [Bind.bind, ExceptT.run, ExceptT.bind, ExceptT.mk, EStateM.bind, act]
  cases h : right b with
  | error => rfl
  | ok val post =>
    cases val with
    | error => rfl
    | ok a => exact cont a post h

private theorem written_return (outcome : Write) (modify : Bytes → Bytes → Bytes) (bytes : Bytes)
    (file : WalFile) (b after : Image) (a : Unit)
    (h : outcome.result modify bytes b (file.get b) (file.put b) = .ok (.ok a) after) :
    ∃ v, after = file.put b v := by
  cases outcome with
  | before abort | torn _ _ abort => cases abort <;> cases h
  | full _ cont =>
    cases cont with
    | some abort => cases abort <;> cases h
    | none => cases h; exact ⟨_, rfl⟩

private theorem sync_return (p : Primitive) (file : WalFile) (b after : Image) (a : Unit)
    (h : (fileSync p file).run b = .ok (.ok a) after) : after = file.settle b := by
  cases p with
  | before abort => cases abort <;> cases h
  | after cont =>
    cases cont with
    | some abort => cases abort <;> cases h
    | none => cases h; cases file <;> rfl

/-- While a newly written file is awaiting its barrier, every other file is
already settled. Successful synchronization reestablishes a clean entry. -/
private theorem write_then_sync {f : WalFile} (p : Primitive) (writeSchedule syncSchedule : List WalFile)
    (write : M Unit) {b : Image} (clean : b.powerLoss = b)
    (wrote : ∀ a after, write.run b = .ok (.ok a) after → ∃ v, after = f.put b v)
    {k k' : Unit → M α}
    (tail : ∀ a after, after.powerLoss = after → (k a).run after = (k' a).run after) :
    (withWritebacks writeSchedule write >>= fun _ =>
      withWritebacks syncSchedule (fileSync p f) >>= k).run b =
    (write >>= fun _ => fileSync (barrierAfterWriteback p syncSchedule f) f >>= k').run b := by
  apply bind_eq_on_return
  · change write (settleFiles writeSchedule b) = write b
    rw [settleFiles_clean _ _ clean]
  · intro a written obs
    obtain ⟨v, rfl⟩ := wrote a written obs
    apply bind_eq_on_return (sync_written p syncSchedule f b v clean)
    intro u after synced
    rw [sync_return _ _ _ _ _ synced]
    exact tail _ _ (settle_put_clean _ _ _ clean)

private theorem marker_get (b : Image) (slot : Nat) : (WalFile.marker slot).get b = b.marker slot := by
  by_cases zero : slot = 0 <;> simp [WalFile.marker, WalFile.get, Image.marker, zero]

private theorem marker_put (b : Image) (slot : Nat) : (WalFile.marker slot).put b = b.withMarker slot := by
  funext v
  by_cases zero : slot = 0 <;> simp [WalFile.marker, WalFile.put, Image.withMarker, zero]

private theorem sync_marker (effects : Effects) (slot : Nat) :
    (ops effects).syncMarker slot = fileSync (effects.markerSync slot) (.marker slot) := by
  funext b
  change _ = (effects.markerSync slot).syncResult b _ _
  rw [marker_get, marker_put]
  rfl

/-- Every append from a fully settled image has exactly the same API outcome
and reached image as a plain execution. The only effect adjustment concerns
whether a reported barrier error occurred before or after persistence. -/
theorem appendBatch_withWritebacks (effects : Effects) (schedule : WritebackSchedule)
    (policy : Policy) (cursor : Cursor) (payload : Bytes) (before : Image)
    (clean : before.powerLoss = before) :
    (appendBatch (scheduledOps (ops effects) schedule) policy cursor payload).run before =
      (appendBatch (ops (appendEffects effects schedule)) policy cursor payload).run before := by
  unfold appendBatch
  dsimp only
  split <;> first | rfl | skip
  split <;> first | rfl | skip
  apply write_then_sync (f := .data) effects.dataSync schedule.appendData schedule.dataSync
    ((ops effects).append (frame cursor.nextSeq payload)) clean
  · intro a after observed
    exact written_return effects.appendData List.append _ .data before after a observed
  · intro u after synced
    split <;> first | rfl | skip
    let slot := cursor.nextSeq % 2
    rw [show (scheduledOps (ops effects) schedule).syncMarker slot = withWritebacks (schedule.markerSync slot)
      (fileSync (effects.markerSync slot) (.marker slot)) by
        exact congrArg (withWritebacks (schedule.markerSync slot)) (sync_marker effects slot)]
    rw [sync_marker]
    apply write_then_sync (f := .marker slot) (effects.markerSync slot) (schedule.writeMarker slot)
      (schedule.markerSync slot) ((ops effects).writeMarker slot _) synced
    · intro value next observed
      apply written_return effects.writeMarker (markerFragment effects.tornSlot)
        (encodeMarker (cursor.endPos + (frame cursor.nextSeq payload).length) cursor.nextSeq) _ after next value
      rw [marker_get, marker_put]
      exact observed
    · intros; rfl

end WalRecoverySlice.Persistence
