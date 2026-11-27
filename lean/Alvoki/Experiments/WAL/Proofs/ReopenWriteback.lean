import Alvoki.Experiments.WAL.Writeback

namespace WalRecoverySlice.Persistence

/-- Apply writeback to a reached image without changing the result or interruption. -/
def Result.writeback (files : List WalFile) (result : Result α) : Result α :=
  match result with
  | .ok value image => .ok value (settleFiles files image)
  | .error token image => .error token (settleFiles files image)

@[simp] private theorem settleFiles_nil (image : Image) : settleFiles [] image = image := rfl

private theorem settleFiles_append (one two : List WalFile) (before : Image) :
    settleFiles (one ++ two) before = settleFiles two (settleFiles one before) :=
  List.foldl_append ..

@[simp] private theorem Result.writeback_nil (r : Result α) : r.writeback [] = r := by
  cases r <;> rfl

private theorem Result.writeback_append (one two : List WalFile) (r : Result α) :
    r.writeback (one ++ two) = (r.writeback one).writeback two := by
  cases r <;> simp [Result.writeback, settleFiles_append]

private def Commutes (action : M α) : Prop :=
  ∀ files before, action.run (settleFiles files before) = Result.writeback files (action.run before)

private theorem commutes_of_single {action : M α}
    (one : ∀ file image, action.run (file.settle image) = Result.writeback [file] (action.run image)) :
    Commutes action := by
  intro files before
  induction files generalizing before with
  | nil => simp
  | cons file rest ih =>
    change action.run (settleFiles rest (file.settle before)) = _
    rw [ih, one, ← Result.writeback_append]
    rfl

private theorem commutes_readData (effects : Effects) : Commutes (ops effects).readData := by
  apply commutes_of_single
  intro file image
  cases file <;> rfl

private theorem commutes_readMarker (effects : Effects) (slot : Nat) : Commutes ((ops effects).readMarker slot) := by
  apply commutes_of_single
  intro file image
  by_cases zero : slot = 0 <;> cases file <;>
    simp [ops, ExceptT.run, Image.marker, zero, WalFile.settle, Result.writeback, settleFiles]

private theorem commutes_syncData (effects : Effects) : Commutes (ops effects).syncData := by
  apply commutes_of_single
  intro file image
  cases h : effects.dataSync with
  | before a => cases a <;> cases file <;> simp [ops, ExceptT.run, h, Primitive.syncResult, Abort.result] <;> rfl
  | after a =>
    cases a with
    | none => cases file <;> simp [ops, ExceptT.run, h, Primitive.syncResult] <;> rfl
    | some a => cases a <;> cases file <;> simp [ops, ExceptT.run, h, Primitive.syncResult, Abort.result] <;> rfl

private theorem commutes_syncMarker (effects : Effects) (slot : Nat) :
    Commutes ((ops effects).syncMarker slot) := by
  apply commutes_of_single
  intro file image
  cases h : effects.markerSync slot with
  | before a => cases a <;> cases file <;>
      simp [ops, ExceptT.run, h, Primitive.syncResult, Abort.result] <;> rfl
  | after a =>
    simp only [ops, ExceptT.run, h, Primitive.syncResult]
    cases a with
    | none => by_cases zero : slot = 0 <;> cases file <;>
        simp [Image.marker, Image.withMarker, zero, WalFile.settle, Result.writeback, settleFiles]
    | some a => cases a <;> by_cases zero : slot = 0 <;> cases file <;>
        simp [Abort.result, Image.marker, Image.withMarker, zero, WalFile.settle, Result.writeback,
          settleFiles]

private theorem commutes_pure (value : α) : Commutes (pure value : M α) := by
  intro files before
  rfl

private def Normalizes (plain decorated : M α) : Prop :=
  ∀ image, ∃ first last : List WalFile,
    decorated.run image = Result.writeback last (plain.run (settleFiles first image))

private def PostNormalizes (plain decorated : M α) : Prop :=
  ∀ image, ∃ last : List WalFile,
    decorated.run image = Result.writeback last (plain.run image)

private theorem normalizes_throw (error : String) {a b : α → M β} :
    Normalizes ((throw error : M α) >>= a) ((throw error : M α) >>= b) := by
  intro image
  exact ⟨[], [], rfl⟩

-- Move the part of the continuation's plan that can cross this callback
-- to its input, keeping the remaining writebacks after the plain run.
private theorem normalizes_bind_of
    (files : List WalFile) (plain : M α) {next actual : α → M β}
    (rest : ∀ value image, ∃ more last : List WalFile,
      (∀ before, plain.run (settleFiles more before) = Result.writeback more (plain.run before)) ∧
        (actual value).run image =
          Result.writeback last ((next value).run (settleFiles more image))) :
    Normalizes (plain >>= next) (withWritebacks files plain >>= actual) := by
  intro image
  cases first : plain.run (settleFiles files image) with
  | error token reached =>
    refine ⟨files, [], ?_⟩
    simp only [Bind.bind, ExceptT.bind, ExceptT.run, ExceptT.mk, EStateM.bind, withWritebacks] at first ⊢
    rw [first] <;> rfl
  | ok returned reached =>
    cases returned with
    | error error =>
      refine ⟨files, [], ?_⟩
      simp only [Bind.bind, ExceptT.bind, ExceptT.run, ExceptT.mk, EStateM.bind, withWritebacks] at first ⊢
      rw [first] <;> rfl
    | ok value =>
      obtain ⟨more, last, commutes, final⟩ := rest value reached
      have moved := commutes (settleFiles files image)
      rw [first] at moved
      refine ⟨files ++ more, last, ?_⟩
      simp only [settleFiles_append, Bind.bind, ExceptT.bind, ExceptT.run, ExceptT.mk,
        EStateM.bind, withWritebacks] at first final moved ⊢
      rw [first, moved]
      exact final

private theorem normalizes_bind (files : List WalFile) (plain : M α)
    {next actual : α → M β} (commutes : Commutes plain)
    (rest : ∀ value, Normalizes (next value) (actual value)) :
    Normalizes (plain >>= next) (withWritebacks files plain >>= actual) := by
  apply normalizes_bind_of
  intro value image
  obtain ⟨more, last, final⟩ := rest value image
  exact ⟨more, last, commutes more, final⟩

private theorem normalizes_bind_post (files : List WalFile) (plain : M α)
    {next actual : α → M β}
    (rest : ∀ value, PostNormalizes (next value) (actual value)) :
    Normalizes (plain >>= next) (withWritebacks files plain >>= actual) := by
  apply normalizes_bind_of
  intro value image
  obtain ⟨last, final⟩ := rest value image
  exact ⟨[], last, by simp, final⟩

private theorem post_pure_after (files : List WalFile) (plain : M α)
    (commutes : Commutes plain) (value : β) :
    PostNormalizes (plain >>= fun _ => pure value)
      (withWritebacks files plain >>= fun _ => pure value) := by
  intro image
  refine ⟨files, ?_⟩
  have moved := commutes files image
  simp only [Bind.bind, ExceptT.bind, ExceptT.run, ExceptT.mk, EStateM.bind, withWritebacks] at moved ⊢
  rw [moved]
  cases plain image with
  | error => rfl
  | ok returned _ => cases returned <;> rfl

/-- Whole-file writebacks before the reached recovery callbacks have exactly the same
response (or interruption) and reached image as a plain recovery bracketed by
writebacks. Writes on opposite sides of truncation are kept separate. -/
theorem reopen_writeback_normalizes (effects : Effects) (schedule : WritebackSchedule)
    (policy : Policy) (before : Image) :
    ∃ first last : List WalFile,
      (reopen (scheduledOps (ops effects) schedule) policy).run before =
        Result.writeback last ((reopen (ops effects) policy).run (settleFiles first before)) := by
  suffices law : Normalizes (reopen (ops effects) policy) (reopen (scheduledOps (ops effects) schedule) policy)
    from law before
  have finish (bytes : Bytes) (decoded : Decoded) :
      Normalizes
        (do
          if decoded.cursor.endPos < bytes.length then (ops effects).truncate decoded.cursor.endPos
          (ops effects).syncData
          pure decoded)
        (do
          if decoded.cursor.endPos < bytes.length then
            (scheduledOps (ops effects) schedule).truncate decoded.cursor.endPos
          (scheduledOps (ops effects) schedule).syncData
          pure decoded) := by
    have syncTail : PostNormalizes
        ((ops effects).syncData >>= fun _ => pure decoded)
        ((scheduledOps (ops effects) schedule).syncData >>= fun _ => pure decoded) :=
      post_pure_after schedule.dataSync (ops effects).syncData (commutes_syncData effects) decoded
    split
    · exact normalizes_bind_post schedule.truncate ((ops effects).truncate _) (fun _ => syncTail)
    · intro image
      obtain ⟨last, equal⟩ := syncTail image
      exact ⟨[], last, equal⟩
  unfold reopen
  split <;> first
    | apply normalizes_bind (schedule.markerRead 0) ((ops effects).readMarker 0)
        (commutes_readMarker effects 0)
      intro a
      apply normalizes_bind (schedule.markerRead 1) ((ops effects).readMarker 1)
        (commutes_readMarker effects 1)
      intro b
      cases selectMarker a b <;> first
        | exact normalizes_throw _
        | apply normalizes_bind [] (pure _) (commutes_pure _)
          intro selected
    | apply normalizes_bind [] (pure none) (commutes_pure none)
      intro selected
  all_goals
    dsimp only
    apply normalizes_bind schedule.dataRead (ops effects).readData (commutes_readData effects)
    intro bytes
    cases scan bytes (selected.map Marker.endPos |>.getD bytes.length) policy with
    | error e => exact normalizes_throw e
    | ok d =>
      apply normalizes_bind [] (pure d) (commutes_pure d)
      intro decoded
      cases selected with
      | none => exact finish bytes decoded
      | some marker =>
        by_cases ordinal : (decoded.cursor.nextSeq != marker.lastSeq + 1) = true
        · simp only [ordinal, ite_true]
          exact normalizes_throw _
        · simp only [ordinal]
          apply normalizes_bind (schedule.markerSync _) ((ops effects).syncMarker _)
            (commutes_syncMarker effects _)
          intro _
          apply normalizes_bind (schedule.markerSync _) ((ops effects).syncMarker _)
            (commutes_syncMarker effects _)
          intro _
          exact finish bytes decoded

end WalRecoverySlice.Persistence
