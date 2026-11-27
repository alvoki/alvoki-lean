import Alvoki.Storage.Disk.NativeOpenCacheReferences
import Alvoki.Storage.Disk.CapturedAlignedInstallation
import Alvoki.Storage.Disk.NativeRawSync
import Alvoki.Storage.Disk.NativeFileEffectProjection

namespace Alvoki.Storage.DiskSession

open System SyncHandleRouting WalSegmentRepair

/-- The successful finisher has one authorization barrier. It reaches
the shared checked unlink pass except on the empty aligned fast path.
The measured size then determines the tail of that same execution. -/
theorem _root_.Alvoki.Storage.WalSegmentRepair.finishBoundedMarkedOpen_reachedSuccess {heap : Type}
    (directory : DiskDirectory) (plan : Plan) (physicalSize : Nat)
    (remove : FilePath → EStateM IO.Error heap (Except IO.Error Unit))
    (write : FilePath → ByteArray → EStateM IO.Error heap Unit)
    (sync : Array FilePath → EStateM IO.Error heap Unit)
    (rename : FilePath → FilePath → EStateM IO.Error heap Unit) {entry reached : heap}
    (returned : finishBoundedMarkedOpen directory plan physicalSize remove write sync rename entry = .ok () reached) :
    let run := performPaths directory plan remove throw write sync rename
    plan.valid = true ∧ plan.keeperBytes.size = plan.keeperSize ∧ plan.keeperSize ≤ physicalSize ∧
    ∃ authorized, sync #[directory.path] entry = .ok () authorized ∧
      if plan.newer.isEmpty && physicalSize == plan.keeperSize then
        sync #[directory.file (.walSegment plan.keeper)] authorized = .ok () reached
      else
        ∃ pruned, ((plan.newer.map Step.unlink ++ [Step.syncPruned]).forM run) authorized = .ok () pruned ∧
          (if plan.keeperSize < physicalSize then (Publication.steps.map Step.replace).forM run
            else sync #[directory.file (.walSegment plan.keeper)]) pruned = .ok () reached := by
  intro run
  have guarded :
      (plan.valid && (plan.keeperBytes.size == plan.keeperSize) && decide (plan.keeperSize ≤ physicalSize)) = true := by
    cases guard : plan.valid && (plan.keeperBytes.size == plan.keeperSize) && decide (plan.keeperSize ≤ physicalSize)
    · simp [finishBoundedMarkedOpen, guard, throw, throwThe, MonadExceptOf.throw, EStateM.throw, Bind.bind, EStateM.bind] at returned
    · rfl
  obtain ⟨valid, size, bounded⟩ : plan.valid = true ∧ plan.keeperBytes.size = plan.keeperSize ∧ plan.keeperSize ≤ physicalSize := by
    simpa only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, and_assoc] using guarded
  refine ⟨valid, size, bounded, ?_⟩
  let fast := plan.newer.isEmpty && physicalSize == plan.keeperSize
  change ∃ authorized, sync #[directory.path] entry = .ok () authorized ∧ (if fast then _ else _)
  simp only [finishBoundedMarkedOpen, guarded, ite_true, Bind.bind] at returned
  change ((if fast then _ else _) : EStateM IO.Error heap Unit) entry = _ at returned
  by_cases short : fast = true
  · simp only [short, ite_true] at returned ⊢
    cases root : sync #[directory.path] entry with
    | error cause failed => simp [root, EStateM.bind] at returned
    | ok result authorized =>
      cases result
      exact ⟨authorized, rfl, by simpa only [Bind.bind, EStateM.bind, root] using returned⟩
  · have notFast : fast = false := Bool.eq_false_iff.mpr short
    simp only [notFast, Bool.false_eq_true, ite_false, runRepairPlan, Bind.bind, EStateM.bind] at returned ⊢
    cases root : sync #[directory.path] entry with
    | error cause failed => simp [root] at returned
    | ok result authorized =>
      cases result
      have schedule : ((steps plan.newer (decide (plan.keeperSize < physicalSize))).forM run) authorized =
          .ok () reached := by simpa only [root] using returned
      unfold steps at schedule
      rw [List.forM_eq_forM, List.forM_append, ← List.forM_eq_forM] at schedule
      cases pruneReturn : ((plan.newer.map Step.unlink ++ [Step.syncPruned]).forM run) authorized with
      | error cause after => simp [Bind.bind, EStateM.bind, pruneReturn] at schedule
      | ok result pruned =>
        cases result
        refine ⟨authorized, rfl, pruned, pruneReturn, ?_⟩
        by_cases longer : plan.keeperSize < physicalSize
        · simp only [longer, ite_true]
          simpa only [Bind.bind, EStateM.bind, pruneReturn, decide_eq_true longer, ite_true] using schedule
        · simp only [longer, ite_false]
          simp [Bind.bind, EStateM.bind, pruneReturn, longer, run, performPaths, List.forM_eq_forM,
            List.forM_cons, List.forM_nil, Pure.pure, EStateM.pure] at schedule
          cases kept : sync #[directory.file (.walSegment plan.keeper)] pruned with
          | error cause failed => simp [kept] at schedule
          | ok result after =>
            cases result
            simpa only [kept] using schedule

/-- The aligned empty-suffix route has just the authorization and keeper
barriers. Their adjacent returns determine the whole finisher result. -/
theorem _root_.Alvoki.Storage.WalSegmentRepair.finishBoundedMarkedOpen_alignedEmpty {heap : Type}
    (directory : DiskDirectory) (plan : Plan) (physicalSize : Nat)
    (remove : FilePath → EStateM IO.Error heap (Except IO.Error Unit))
    (write : FilePath → ByteArray → EStateM IO.Error heap Unit)
    (sync : Array FilePath → EStateM IO.Error heap Unit)
    (rename : FilePath → FilePath → EStateM IO.Error heap Unit)
    (valid : plan.valid = true) (size : plan.keeperBytes.size = plan.keeperSize)
    (aligned : physicalSize = plan.keeperSize) (noLater : plan.newer = [])
    {entry authorized reached : heap}
    (root : sync #[directory.path] entry = .ok () authorized)
    (keeper : sync #[directory.file (.walSegment plan.keeper)] authorized = .ok () reached) :
    finishBoundedMarkedOpen directory plan physicalSize remove write sync rename entry = .ok () reached := by
  simpa only [finishBoundedMarkedOpen, aligned, valid, size, Bind.bind, EStateM.bind,
    beq_self_eq_true, decide_eq_true (Nat.le_refl _), Bool.and_self, ↓reduceIte, noLater,
    List.isEmpty_nil, root] using keeper

/-- Fold the literal unlink loop. An error identifies the accepted prefix
and the exact reached removal that ended that loop. -/
theorem foldWalUnlinksWithPrefix {heap model : Type}
    (directory : DiskDirectory) (plan : Plan)
    (remove : FilePath → EStateM IO.Error heap (Except IO.Error Unit))
    (write : FilePath → ByteArray → EStateM IO.Error heap Unit)
    (sync : Array FilePath → EStateM IO.Error heap Unit)
    (rename : FilePath → FilePath → EStateM IO.Error heap Unit)
    (invariant : model → heap → Prop) (applyUnlink : model → Nat → model)
    {initial : model} {first : heap} (entered : invariant initial first)
    (unlink : ∀ {ordinal start finish result before}, ordinal ∈ plan.newer →
      remove (directory.file (.walSegment ordinal)) start = .ok result finish →
      RunCollection.ownedUnlinkResult result = .ok () →
      invariant before start → invariant (applyUnlink before ordinal) finish) :
    let run := performPaths directory plan remove throw write sync rename
    match ((plan.newer.map Step.unlink).forM run) first with
    | .ok () last => invariant (plan.newer.foldl applyUnlink initial) last
    | .error cause last =>
      ∃ (earlier : List Nat) (victim : Nat) (suffix : List Nat) (atVictim : heap),
        plan.newer = earlier ++ victim :: suffix ∧
        ((earlier.map Step.unlink).forM run) first = .ok () atVictim ∧
        invariant (earlier.foldl applyUnlink initial) atVictim ∧
        (remove (directory.file (.walSegment victim)) atVictim = .error cause last ∨
          ∃ result, remove (directory.file (.walSegment victim)) atVictim = .ok result last ∧
            RunCollection.ownedUnlinkResult result = .error cause) := by
  intro run
  have preserve {ordinals : List Nat} (included : ∀ ordinal ∈ ordinals, ordinal ∈ plan.newer)
      {start : heap} {before : model} (known : invariant before start) :
      match ((ordinals.map Step.unlink).forM run) start with
      | .ok () last => invariant (ordinals.foldl applyUnlink before) last
      | .error cause last =>
        ∃ (earlier : List Nat) (victim : Nat) (suffix : List Nat) (atVictim : heap),
          ordinals = earlier ++ victim :: suffix ∧
          ((earlier.map Step.unlink).forM run) start = .ok () atVictim ∧
          invariant (earlier.foldl applyUnlink before) atVictim ∧
          (remove (directory.file (.walSegment victim)) atVictim = .error cause last ∨
            ∃ result, remove (directory.file (.walSegment victim)) atVictim = .ok result last ∧
              RunCollection.ownedUnlinkResult result = .error cause) := by
    induction ordinals generalizing start before with
    | nil => exact known
    | cons ordinal rest ih =>
      simp only [List.map_cons, List.forM_eq_forM, List.forM_cons, run, performPaths,
        RunCollection.performPaths, Bind.bind, EStateM.bind]
      cases removed : remove (directory.file (.walSegment ordinal)) start with
      | error cause reached =>
        exact ⟨[], ordinal, rest, start, rfl, rfl, known, .inl removed⟩
      | ok result reached =>
        cases accepted : RunCollection.ownedUnlinkResult result with
        | error cause =>
          simp only [accepted, throw, throwThe, MonadExceptOf.throw, EStateM.throw]
          exact ⟨[], ordinal, rest, start, rfl, rfl, known, .inr ⟨result, removed, accepted⟩⟩
        | ok value =>
          cases value
          simp only [accepted, Pure.pure, EStateM.pure]
          have next := ih (fun other member => included other (List.mem_cons_of_mem _ member))
            (unlink (included _ List.mem_cons_self) removed accepted known)
          simp only [List.forM_eq_forM, run] at next
          cases remaining : forM (rest.map Step.unlink) (performPaths directory plan remove throw write sync rename) reached with
          | ok value last =>
            cases value
            simpa only [remaining, List.foldl_cons] using next
          | error cause last =>
            simp only [remaining] at next
            obtain ⟨earlier, victim, suffix, atVictim, split, ran, prior, rejected⟩ := next
            refine ⟨ordinal :: earlier, victim, suffix, atVictim, ?_, ?_, prior, rejected⟩
            · simpa only [List.cons_append] using congrArg (ordinal :: ·) split
            · simpa only [List.map_cons, List.forM_eq_forM, List.forM_cons, run, performPaths,
                RunCollection.performPaths, Bind.bind, EStateM.bind, removed, accepted, Pure.pure, EStateM.pure]
                using ran
  exact preserve (fun _ member => member) entered

/-- Fold the accepted removes of the actual WAL unlink loop in call order. -/
theorem foldReturnedWalUnlinks {heap model : Type}
    (directory : DiskDirectory) (plan : Plan)
    (remove : FilePath → EStateM IO.Error heap (Except IO.Error Unit))
    (write : FilePath → ByteArray → EStateM IO.Error heap Unit)
    (sync : Array FilePath → EStateM IO.Error heap Unit)
    (rename : FilePath → FilePath → EStateM IO.Error heap Unit)
    (invariant : model → heap → Prop) (applyUnlink : model → Nat → model)
    {initial : model} {first last : heap} (entered : invariant initial first)
    (unlink : ∀ {ordinal start finish result before}, ordinal ∈ plan.newer →
      remove (directory.file (.walSegment ordinal)) start = .ok result finish →
      RunCollection.ownedUnlinkResult result = .ok () →
      invariant before start → invariant (applyUnlink before ordinal) finish)
    (returned : ((plan.newer.map Step.unlink).forM
      (performPaths directory plan remove throw write sync rename)) first = .ok () last) :
    invariant (plan.newer.foldl applyUnlink initial) last := by
  simpa only [returned] using
    foldWalUnlinksWithPrefix directory plan remove write sync rename invariant applyUnlink entered unlink

/-- Carry a frame across every reached remove, including the one whose
outer failure or rejected unlink result ends the loop. -/
theorem framesWalUnlinks {heap : Type}
    {directory : DiskDirectory} {plan : Plan}
    {remove : FilePath → EStateM IO.Error heap (Except IO.Error Unit)}
    {write : FilePath → ByteArray → EStateM IO.Error heap Unit}
    {sync : Array FilePath → EStateM IO.Error heap Unit}
    {rename : FilePath → FilePath → EStateM IO.Error heap Unit}
    (frame : heap → heap → Prop) (refl : ∀ atHeap, frame atHeap atHeap)
    (trans : ∀ {first middle last}, frame first middle → frame middle last → frame first last)
    (unlink : ∀ ordinal ∈ plan.newer, ∀ before,
      frame before (NativeFileEffectProjection.reached (remove (directory.file (.walSegment ordinal)) before)))
    (first : heap) :
    frame first (NativeFileEffectProjection.reached (((plan.newer.map Step.unlink).forM
      (performPaths directory plan remove throw write sync rename)) first)) := by
  have called {ordinal : Nat} {before after : heap} {result : EStateM.Result IO.Error heap (Except IO.Error Unit)}
      (member : ordinal ∈ plan.newer)
      (returns : remove (directory.file (.walSegment ordinal)) before = result)
      (reached : NativeFileEffectProjection.reached result = after) :
      frame before after := by simpa only [returns, reached] using unlink ordinal member before
  have framed := foldWalUnlinksWithPrefix directory plan remove write sync rename (fun (_ : Unit) => frame first)
    (fun _ _ => ()) (initial := ()) (refl first)
    (fun member returns _ prior => trans prior (called member returns rfl))
  dsimp only at framed
  cases result : ((plan.newer.map Step.unlink).forM
    (performPaths directory plan remove throw write sync rename)) first with
  | error cause last =>
    simp only [result] at framed
    obtain ⟨_, victim, _, _, split, _, prior, stopped⟩ := framed
    have member : victim ∈ plan.newer := by
      rw [split]
      exact List.mem_append_right _ List.mem_cons_self
    change frame first last
    rcases stopped with outer | ⟨_, inner, _⟩
    · exact trans prior (called member outer rfl)
    · exact trans prior (called member inner rfl)
  | ok value => cases value; simpa only [result, NativeFileEffectProjection.reached] using framed

/-- Only a longer keeper or a nonempty suffix reaches the prune block.
Its returned error stops before either the keeper sync or replacement. -/
theorem _root_.Alvoki.Storage.WalSegmentRepair.finishBoundedMarkedOpen_errorDuringPrune {heap : Type}
    {directory : DiskDirectory} {plan : Plan} {physicalSize : Nat}
    {remove : FilePath → EStateM IO.Error heap (Except IO.Error Unit)}
    {write : FilePath → ByteArray → EStateM IO.Error heap Unit}
    {sync : Array FilePath → EStateM IO.Error heap Unit}
    {rename : FilePath → FilePath → EStateM IO.Error heap Unit}
    (valid : plan.valid = true) (bytes : plan.keeperBytes.size = plan.keeperSize)
    (bounded : plan.keeperSize ≤ physicalSize)
    (needsPrune : plan.newer ≠ [] ∨ plan.keeperSize < physicalSize)
    {first authorized last : heap} {cause : IO.Error}
    (authorization : sync #[directory.path] first = .ok () authorized)
    (failed : ((plan.newer.map Step.unlink ++ [Step.syncPruned]).forM
      (performPaths directory plan remove throw write sync rename)) authorized = .error cause last) :
    finishBoundedMarkedOpen directory plan physicalSize remove write sync rename first = .error cause last := by
  have notFast : (plan.newer.isEmpty && physicalSize == plan.keeperSize) = false := by
    cases needsPrune with
    | inl listed => simp [List.isEmpty_eq_false_iff.mpr listed]
    | inr longer => simp [Nat.ne_of_gt longer]
  have guarded : (plan.valid && plan.keeperBytes.size == plan.keeperSize &&
      decide (plan.keeperSize ≤ physicalSize)) = true := by simp [valid, bytes, bounded]
  simp only [finishBoundedMarkedOpen, guarded, ite_true, notFast, Bool.false_eq_true, ite_false,
    runRepairPlan, Bind.bind, EStateM.bind, authorization]
  unfold steps
  rw [List.forM_eq_forM, List.forM_append, ← List.forM_eq_forM]
  simp only [Bind.bind, EStateM.bind, failed]

/-- A reported unlink error ends the literal bounded repair at the unlink's
reached heap. Both keeper sizes share this authorization and unlink prefix. -/
theorem _root_.Alvoki.Storage.WalSegmentRepair.finishBoundedMarkedOpen_errorDuringUnlinks {heap : Type}
    {directory : DiskDirectory} {plan : Plan} {physicalSize : Nat}
    {remove : FilePath → EStateM IO.Error heap (Except IO.Error Unit)}
    {write : FilePath → ByteArray → EStateM IO.Error heap Unit}
    {sync : Array FilePath → EStateM IO.Error heap Unit}
    {rename : FilePath → FilePath → EStateM IO.Error heap Unit}
    (valid : plan.valid = true) (bytes : plan.keeperBytes.size = plan.keeperSize)
    (bounded : plan.keeperSize ≤ physicalSize) {first authorized last : heap} {cause : IO.Error}
    (authorization : sync #[directory.path] first = .ok () authorized)
    (failed : ((plan.newer.map Step.unlink).forM
      (performPaths directory plan remove throw write sync rename)) authorized = .error cause last) :
    finishBoundedMarkedOpen directory plan physicalSize remove write sync rename first = .error cause last := by
  have nonempty : plan.newer ≠ [] := by
    intro names
    simp [names, List.forM_eq_forM, List.forM_nil, Pure.pure, EStateM.pure] at failed
  apply finishBoundedMarkedOpen_errorDuringPrune valid bytes bounded (.inl nonempty) authorization
  rw [List.forM_eq_forM, List.forM_append, ← List.forM_eq_forM]
  simp only [Bind.bind, EStateM.bind, failed]

/-- An accepted unlink changes its logical suffix entry while preserving
an independently chosen frame, such as held lock authority. -/
theorem filesAndFrameOfReturnedWalUnlinks {heap : Type}
    (directory : DiskDirectory) (plan : Plan)
    (remove : FilePath → EStateM IO.Error heap (Except IO.Error Unit))
    (write : FilePath → ByteArray → EStateM IO.Error heap Unit)
    (sync : Array FilePath → EStateM IO.Error heap Unit)
    (rename : FilePath → FilePath → EStateM IO.Error heap Unit)
    (files : heap → FileImage) (keeps : heap → heap → Prop)
    (trans : ∀ {before middle after}, keeps before middle → keeps middle after → keeps before after)
    {origin first last : heap} (entered : keeps origin first)
    (unlink : ∀ {ordinal before after result}, ordinal ∈ plan.newer →
      remove (directory.file (.walSegment ordinal)) before = .ok result after →
      RunCollection.ownedUnlinkResult result = .ok () →
      files after = (files before).unlinkLater ordinal ∧ keeps before after)
    (returned : ((plan.newer.map Step.unlink).forM
      (performPaths directory plan remove throw write sync rename)) first = .ok () last) :
    files last = plan.newer.foldl FileImage.unlinkLater (files first) ∧ keeps origin last := by
  let invariant (image : FileImage) (atHeap : heap) := files atHeap = image ∧ keeps origin atHeap
  have step {ordinal before after result image} (member : ordinal ∈ plan.newer)
      (called : remove (directory.file (.walSegment ordinal)) before = .ok result after)
      (accepted : RunCollection.ownedUnlinkResult result = .ok ()) (known : invariant image before) :
      invariant (image.unlinkLater ordinal) after := by
    obtain ⟨same, framed⟩ := unlink member called accepted
    exact ⟨same.trans (congrArg (fun image => image.unlinkLater ordinal) known.1), trans known.2 framed⟩
  exact foldReturnedWalUnlinks directory plan remove write sync rename invariant FileImage.unlinkLater
    ⟨rfl, entered⟩ step returned

/-- Split the reached prune block into the ordered unlink pass and the
directory barrier that follows it. -/
theorem returnedWalUnlinksAndBarrier {heap : Type}
    (directory : DiskDirectory) (plan : Plan)
    (remove : FilePath → EStateM IO.Error heap (Except IO.Error Unit))
    (write : FilePath → ByteArray → EStateM IO.Error heap Unit)
    (sync : Array FilePath → EStateM IO.Error heap Unit)
    (rename : FilePath → FilePath → EStateM IO.Error heap Unit)
    {first last : heap}
    (returned : ((plan.newer.map Step.unlink ++ [Step.syncPruned]).forM
      (performPaths directory plan remove throw write sync rename)) first = .ok () last) :
    ∃ unlinked, ((plan.newer.map Step.unlink).forM
      (performPaths directory plan remove throw write sync rename)) first = .ok () unlinked ∧
      sync #[directory.path] unlinked = .ok () last := by
  let run := performPaths directory plan remove throw write sync rename
  change ((plan.newer.map Step.unlink ++ [Step.syncPruned]).forM run) first = _ at returned
  rw [List.forM_eq_forM, List.forM_append, ← List.forM_eq_forM] at returned
  cases passed : ((plan.newer.map Step.unlink).forM run) first with
  | error cause reached => simp [Bind.bind, EStateM.bind, passed] at returned
  | ok value unlinked =>
    cases value
    refine ⟨unlinked, rfl, ?_⟩
    simp only [Bind.bind, EStateM.bind, passed, List.forM_eq_forM, List.forM_cons, List.forM_nil,
      Pure.pure, EStateM.pure, run, performPaths] at returned
    cases status : sync #[directory.path] unlinked with
    | error cause stopped => simp [status] at returned
    | ok value stopped =>
      cases value
      simpa only [status] using returned

/-- A longer keeper reaches the common prune pass and then replaces the
old keeper with exactly its selected prefix. These are issue and return
heaps of the literal successful schedule. -/
theorem _root_.Alvoki.Storage.WalSegmentRepair.finishBoundedMarkedOpen_replacementReached {heap : Type}
    (directory : DiskDirectory) (plan : Plan) (physicalSize : Nat)
    (remove : FilePath → EStateM IO.Error heap (Except IO.Error Unit))
    (write : FilePath → ByteArray → EStateM IO.Error heap Unit)
    (sync : Array FilePath → EStateM IO.Error heap Unit)
    (rename : FilePath → FilePath → EStateM IO.Error heap Unit) {entry reached : heap}
    (longer : plan.keeperSize < physicalSize)
    (returned : finishBoundedMarkedOpen directory plan physicalSize remove write sync rename entry = .ok () reached) :
    ∃ authorized unlinked pruned staged synced renamed,
      sync #[directory.path] entry = .ok () authorized ∧
      ((plan.newer.map Step.unlink).forM (performPaths directory plan remove throw write sync rename)) authorized =
        .ok () unlinked ∧
      sync #[directory.path] unlinked = .ok () pruned ∧
      write (directory.file .stagedWal) (plan.keeperBytes.extract 0 plan.keeperSize) pruned = .ok () staged ∧
      sync #[directory.file .stagedWal] staged = .ok () synced ∧
      rename (directory.file .stagedWal) (directory.file (.walSegment plan.keeper)) synced = .ok () renamed ∧
      sync #[directory.path] renamed = .ok () reached := by
  obtain ⟨_, _, _, authorized, authorizedRoot, tail⟩ :=
    finishBoundedMarkedOpen_reachedSuccess directory plan physicalSize remove write sync rename returned
  have different : physicalSize ≠ plan.keeperSize := fun same => Nat.lt_irrefl _ (same ▸ longer)
  have slow : (plan.newer.isEmpty && (physicalSize == plan.keeperSize)) = false := by
    simp [different]
  simp only [slow, Bool.false_eq_true, ite_false, ite_eq_left longer] at tail
  obtain ⟨pruned, prune, replaced⟩ := tail
  obtain ⟨unlinked, unlinks, pruneBarrier⟩ :=
    returnedWalUnlinksAndBarrier directory plan remove write sync rename prune
  simp only [Publication.steps, List.map_cons, List.map_nil, List.forM_eq_forM, List.forM_cons,
    List.forM_nil, performPaths, Publication.performReplacement] at replaced
  change (do
    write (directory.file .stagedWal) (plan.keeperBytes.extract 0 plan.keeperSize)
    sync #[directory.file .stagedWal]
    rename (directory.file .stagedWal) (directory.file (.walSegment plan.keeper))
    sync #[directory.path]
    pure () : EStateM IO.Error heap Unit) pruned = .ok () reached at replaced
  cases stagedCall : write (directory.file .stagedWal) (plan.keeperBytes.extract 0 plan.keeperSize) pruned with
  | error cause failed => simp [Bind.bind, EStateM.bind, stagedCall] at replaced
  | ok value staged =>
    cases value
    cases stageBarrier : sync #[directory.file .stagedWal] staged with
    | error cause failed => simp [Bind.bind, EStateM.bind, stagedCall, stageBarrier] at replaced
    | ok value synced =>
      cases value
      cases renameCall : rename (directory.file .stagedWal) (directory.file (.walSegment plan.keeper)) synced with
      | error cause failed => simp [Bind.bind, EStateM.bind, stagedCall, stageBarrier, renameCall] at replaced
      | ok value renamed =>
        cases value
        refine ⟨authorized, unlinked, pruned, staged, synced, renamed, authorizedRoot, unlinks, pruneBarrier,
          stagedCall, stageBarrier, renameCall, ?_⟩
        simp only [Bind.bind, EStateM.bind, stagedCall, stageBarrier, renameCall, Pure.pure, EStateM.pure] at replaced
        cases final : sync #[directory.path] renamed with
        | error cause failed => simp [final] at replaced
        | ok value after =>
          cases value
          simpa only [final] using replaced

/-- Each selected name is absent after the actual checked unlink pass.
Only paths in the caller's canonical scope need the off-target frame. -/
theorem namesOfReturnedWalUnlinks {heap : Type}
    (directory : DiskDirectory) (plan : Plan)
    (remove : FilePath → EStateM IO.Error heap (Except IO.Error Unit))
    (write : FilePath → ByteArray → EStateM IO.Error heap Unit)
    (sync : Array FilePath → EStateM IO.Error heap Unit)
    (rename : FilePath → FilePath → EStateM IO.Error heap Unit)
    (names : heap → FilePath → Option Nat) (scope : FilePath → Prop)
    (inScope : ∀ ordinal ∈ plan.newer, scope (directory.file (.walSegment ordinal)))
    (unlink : ∀ {ordinal start finish result}, ordinal ∈ plan.newer →
      remove (directory.file (.walSegment ordinal)) start = .ok result finish →
      RunCollection.ownedUnlinkResult result = .ok () →
      names finish (directory.file (.walSegment ordinal)) = none ∧
      ∀ path, scope path → path ≠ directory.file (.walSegment ordinal) → names finish path = names start path)
    {first last : heap}
    (returned : ((plan.newer.map Step.unlink).forM
      (performPaths directory plan remove throw write sync rename)) first = .ok () last) :
    (∀ ordinal ∈ plan.newer, names last (directory.file (.walSegment ordinal)) = none) ∧
    ∀ path, scope path → (∀ ordinal ∈ plan.newer, path ≠ directory.file (.walSegment ordinal)) →
      names last path = names first path := by
  let invariant (removed : List Nat) (atHeap : heap) :=
    (∀ ordinal ∈ plan.newer, ordinal ∈ removed → names atHeap (directory.file (.walSegment ordinal)) = none) ∧
    ∀ path, scope path → (∀ ordinal ∈ removed, path ≠ directory.file (.walSegment ordinal)) →
      names atHeap path = names first path
  have start : invariant [] first := ⟨by simp, fun _ _ _ => rfl⟩
  have step {ordinal : Nat} {before after : heap} {result : Except IO.Error Unit} {removed : List Nat}
      (selected : ordinal ∈ plan.newer) (called : remove (directory.file (.walSegment ordinal)) before = .ok result after)
      (accepted : RunCollection.ownedUnlinkResult result = .ok ()) (prior : invariant removed before) :
      invariant (removed ++ [ordinal]) after := by
    obtain ⟨gone, unchanged⟩ := prior
    obtain ⟨absent, keeps⟩ := unlink selected called accepted
    constructor
    · intro other eligible member
      by_cases same : other = ordinal
      · simpa only [same] using absent
      · have earlier : other ∈ removed := by simpa only [List.mem_append, List.mem_singleton, same, or_false] using member
        have apart : directory.file (.walSegment other) ≠ directory.file (.walSegment ordinal) :=
          fun collision => same (directory.walSegment_path_injective collision)
        exact (keeps _ (inScope other eligible) apart).trans (gone other eligible earlier)
    · intro path inside outside
      exact (keeps path inside (outside ordinal (List.mem_append_right _ (List.mem_singleton_self _)))).trans
        (unchanged path inside (fun other member => outside other (List.mem_append_left _ member)))
  have complete : invariant plan.newer last := by
    simpa [← List.flatMap_def] using
      foldReturnedWalUnlinks directory plan remove write sync rename invariant
        (fun done ordinal => done ++ [ordinal]) start step returned
  exact ⟨fun ordinal member => complete.1 ordinal member member, complete.2⟩

structure AlignedKeeperCacheCallbacks (heap : Type) where
  openRead : FilePath → EStateM IO.Error heap IO.FS.Handle
  readChunk : IO.FS.Handle → USize → EStateM IO.Error heap ByteArray
  modifyPending : IO.Ref (List (FilePath × IO.FS.Handle)) →
    (List (FilePath × IO.FS.Handle) → List (FilePath × IO.FS.Handle)) → EStateM IO.Error heap Unit
  getDirectory : IO.Ref (Option IO.FS.Handle) → EStateM IO.Error heap (Option IO.FS.Handle)
  getPending : IO.Ref (List (FilePath × IO.FS.Handle)) → EStateM IO.Error heap (List (FilePath × IO.FS.Handle))
  setPending : IO.Ref (List (FilePath × IO.FS.Handle)) → List (FilePath × IO.FS.Handle) → EStateM IO.Error heap Unit
  getActive : IO.Ref (Option (FilePath × IO.FS.Handle)) → EStateM IO.Error heap (Option (FilePath × IO.FS.Handle))
  sync : IO.FS.Handle → EStateM IO.Error heap Unit

namespace AlignedKeeperCacheCallbacks

variable {heap : Type} (calls : AlignedKeeperCacheCallbacks heap)

/-- Interpret the native keeper reader with a pending cell allocated by
the same opener. -/
def readKeeper (pending : IO.Ref (List (FilePath × IO.FS.Handle))) (path : FilePath)
    (count size : Nat) : EStateM IO.Error heap ByteArray :=
  readKeeperWith calls.openRead
    (fun handle size => readExactPrefixWith (IO.userError "short or oversized WAL keeper read")
      (calls.readChunk handle) size ByteArray.empty)
    (fun name handle => calls.modifyPending pending (pushPending name handle)) path count size

def syncPaths (directory : FilePath) (cached : IO.Ref (Option IO.FS.Handle))
    (active : IO.Ref (Option (FilePath × IO.FS.Handle)))
    (pending : IO.Ref (List (FilePath × IO.FS.Handle))) (paths : Array FilePath) : EStateM IO.Error heap Unit :=
  SyncPathGroup.run (fun path => syncWithHandles directory path (calls.getDirectory cached)
    (calls.getPending pending) (calls.setPending pending) (calls.getActive active) calls.openRead calls.sync) paths

theorem readsAligned {pending path count before opened read remembered keeper bytes}
    (fits : count < USize.size)
    (openedKeeper : calls.openRead path before = .ok keeper opened)
    (readKeeper : readExactPrefixWith (IO.userError "short or oversized WAL keeper read") (calls.readChunk keeper)
      count ByteArray.empty opened = .ok bytes read)
    (rememberedKeeper : calls.modifyPending pending (pushPending path keeper) read = .ok () remembered) :
    calls.readKeeper pending path count count before = .ok bytes remembered := by
  simp [AlignedKeeperCacheCallbacks.readKeeper, readKeeperWith, Bind.bind, EStateM.bind, fits, openedKeeper,
    readKeeper, rememberedKeeper, Pure.pure, EStateM.pure]

theorem syncsDirectory {dir cached active pending before issued after handle}
    (loaded : calls.getDirectory cached before = .ok (some handle) issued)
    (synced : calls.sync handle issued = .ok () after) :
    calls.syncPaths dir cached active pending #[dir] before = .ok () after := by
  rw [syncPaths, SyncPathGroup.run_single]
  simp [syncWithHandles, Bind.bind, EStateM.bind, loaded, synced, Pure.pure, EStateM.pure]

/-- A pending keeper bypasses the active cell and any fallback open.
The removal from the pending cell precedes fsync. -/
theorem syncsSelectedPending {dir path cached active pending before read consumed after handle entries}
    (separate : path ≠ dir)
    (loaded : calls.getPending pending before = .ok entries read)
    (selected : entries.find? (fun item => item.1 == path) = some (path, handle))
    (cleared : calls.setPending pending (entries.filter (fun item => item.1 != path)) read = .ok () consumed)
    (synced : calls.sync handle consumed = .ok () after) :
    calls.syncPaths dir cached active pending #[path] before = .ok () after := by
  rw [syncPaths, SyncPathGroup.run_single]
  simp [syncWithHandles, Bind.bind, EStateM.bind, separate, loaded, selected, cleared, synced, Pure.pure, EStateM.pure]

theorem syncsPendingKeeper {dir path cached active pending before consumed after handle}
    (separate : path ≠ dir)
    (loaded : calls.getPending pending before = .ok [(path, handle)] before)
    (cleared : calls.setPending pending [] before = .ok () consumed)
    (synced : calls.sync handle consumed = .ok () after) :
    calls.syncPaths dir cached active pending #[path] before = .ok () after :=
  calls.syncsSelectedPending separate loaded (by simp) (by simpa using cleared) synced

/-- A pending insertion selects the same handle even with other entries
in the cell. The actual singleton sync consumes all matches before fsync. -/
theorem rememberedPendingReturned {image : Type} (view : OpenCloseHeapView heap image)
    {directory path : FilePath}
    {cached : IO.Ref (Option IO.FS.Handle)} {active : IO.Ref (Option (FilePath × IO.FS.Handle))}
    {pending : IO.Ref (List (FilePath × IO.FS.Handle))} {before reached : heap}
    {handle : IO.FS.Handle} {previous : List (FilePath × IO.FS.Handle)}
    (separate : path ≠ directory)
    (remembered : view.pending before pending = pushPending path handle previous)
    (readsPending : ∀ {entries loaded}, calls.getPending pending before = .ok entries loaded →
      entries = view.pending before pending)
    (returned : calls.syncPaths directory cached active pending #[path] before = .ok () reached) :
    ∃ (entries : List (FilePath × IO.FS.Handle)) (loaded consumed : heap),
      calls.getPending pending before = .ok entries loaded ∧
      entries.find? (fun item => item.1 == path) = some (path, handle) ∧
      calls.setPending pending (entries.filter (fun item => item.1 != path)) loaded = .ok () consumed ∧
      calls.sync handle consumed = .ok () reached := by
  let syncer : RawSyncCalls heap :=
    ⟨⟨calls.getDirectory, calls.getPending, calls.setPending, calls.getActive, calls.openRead⟩, calls.sync⟩
  have selects {entries loaded} (read : syncer.readPending pending before = .ok entries loaded) :
      entries.find? (fun item => item.1 == path) = some (path, handle) := by
    rw [readsPending read, remembered]
    simp [pushPending]
  exact syncer.pendingGroupReturned separate selects returned

/-- Local cache effects needed to carry the original keeper through
the reached unlink pass and its directory barrier. -/
structure SuffixCacheEffects {image : Type} (view : OpenCloseHeapView heap image)
    (directory : DiskDirectory) (plan : Plan)
    (cached : IO.Ref (Option IO.FS.Handle)) (pending : IO.Ref (List (FilePath × IO.FS.Handle)))
    (root : IO.FS.Handle) (remove : FilePath → EStateM IO.Error heap (Except IO.Error Unit)) : Prop where
  readsDirectory : ∀ {before result issued}, calls.getDirectory cached before = .ok result issued →
    result = view.directory before cached ∧ view.directory issued cached = view.directory before cached ∧
    view.pending issued pending = view.pending before pending
  syncKeepsDirectory : ∀ {issued after}, calls.sync root issued = .ok () after →
    view.directory after cached = view.directory issued cached
  removesKeepCache : ∀ {ordinal before after result}, ordinal ∈ plan.newer →
    remove (directory.file (.walSegment ordinal)) before = .ok result after →
    RunCollection.ownedUnlinkResult result = .ok () →
    view.directory after cached = view.directory before cached ∧ view.pending after pending = view.pending before pending

/-- Both aligned routes sync the remembered keeper. The longer schedule
additionally records the checked removals and the second root barrier,
all on the same cache and the exact reached heaps. -/
theorem alignedRepairSyncsWithSuffix {image : Type} (view : OpenCloseHeapView heap image)
    (directory : DiskDirectory) (plan : Plan) (physicalSize : Nat)
    (cached : IO.Ref (Option IO.FS.Handle)) (active : IO.Ref (Option (FilePath × IO.FS.Handle)))
    (pending : IO.Ref (List (FilePath × IO.FS.Handle)))
    (remove : FilePath → EStateM IO.Error heap (Except IO.Error Unit))
    (write : FilePath → ByteArray → EStateM IO.Error heap Unit)
    (rename : FilePath → FilePath → EStateM IO.Error heap Unit)
    {readHeap entry reached : heap} {root keeper : IO.FS.Handle}
    (aligned : physicalSize = plan.keeperSize)
    (cachedRoot : view.directory entry cached = some root)
    (remembered : calls.modifyPending pending (pushPending (directory.file (.walSegment plan.keeper)) keeper)
      readHeap = .ok () entry)
    (recordsKeeper : calls.modifyPending pending (pushPending (directory.file (.walSegment plan.keeper)) keeper)
      readHeap = .ok () entry →
      view.pending entry pending = pushPending (directory.file (.walSegment plan.keeper)) keeper (view.pending readHeap pending))
    (readsDirectory : ∀ {result issued}, calls.getDirectory cached entry = .ok result issued →
      result = view.directory entry cached ∧ view.pending issued pending = view.pending entry pending)
    (syncKeepsPending : ∀ {issued after}, calls.sync root issued = .ok () after →
      view.pending after pending = view.pending issued pending)
    (readsPending : ∀ {before entries loaded}, calls.getPending pending before = .ok entries loaded →
      entries = view.pending before pending)
    (suffix : plan.newer ≠ [] → calls.SuffixCacheEffects view directory plan cached pending root remove)
    (returned : finishBoundedMarkedOpen directory plan physicalSize remove write
      (calls.syncPaths directory.path cached active pending) rename entry = .ok () reached) :
    let path := directory.file (.walSegment plan.keeper)
    let sync := calls.syncPaths directory.path cached active pending
    ∃ (rootIssued authorized keeperEntry : heap) (entries : List (FilePath × IO.FS.Handle)) (loaded consumed : heap),
      calls.getDirectory cached entry = .ok (some root) rootIssued ∧
      calls.sync root rootIssued = .ok () authorized ∧
      (if plan.newer = [] then keeperEntry = authorized
        else ∃ (unlinked suffixIssued : heap),
          ((plan.newer.map Step.unlink).forM (performPaths directory plan remove throw write sync rename))
            authorized = .ok () unlinked ∧
          calls.getDirectory cached unlinked = .ok (some root) suffixIssued ∧
          calls.sync root suffixIssued = .ok () keeperEntry) ∧
      calls.getPending pending keeperEntry = .ok entries loaded ∧
      entries.find? (fun item => item.1 == path) = some (path, keeper) ∧
      calls.setPending pending (entries.filter (fun item => item.1 != path)) loaded = .ok () consumed ∧
      calls.sync keeper consumed = .ok () reached := by
  intro path sync
  obtain ⟨_, _, _, authorized, rootBarrier, finish⟩ :=
    finishBoundedMarkedOpen_reachedSuccess directory plan physicalSize remove write sync rename returned
  let syncer : RawSyncCalls heap :=
    ⟨⟨calls.getDirectory, calls.getPending, calls.setPending, calls.getActive, calls.openRead⟩, calls.sync⟩
  change syncer.group directory.path cached active pending #[directory.path] entry = .ok () authorized at rootBarrier
  obtain ⟨directoryHandle, rootIssued, loadedRoot, syncedRoot⟩ := syncer.rootGroupReturned rootBarrier
  obtain ⟨sameRoot, pendingFromRead⟩ := readsDirectory loadedRoot
  have sameHandle := Option.some.inj (sameRoot.trans cachedRoot)
  subst directoryHandle
  have authorizedPending := (syncKeepsPending syncedRoot).trans pendingFromRead
  have tail :
      ∃ keeperEntry,
        (if plan.newer = [] then keeperEntry = authorized
          else ∃ (unlinked suffixIssued : heap),
            ((plan.newer.map Step.unlink).forM (performPaths directory plan remove throw write sync rename))
              authorized = .ok () unlinked ∧
            calls.getDirectory cached unlinked = .ok (some root) suffixIssued ∧
            calls.sync root suffixIssued = .ok () keeperEntry) ∧
        view.pending keeperEntry pending = view.pending entry pending ∧ sync #[path] keeperEntry = .ok () reached := by
    by_cases empty : plan.newer = []
    · have keeperBarrier : sync #[path] authorized = .ok () reached := by
        simpa [aligned, empty, path] using finish
      exact ⟨authorized, by simp [empty], authorizedPending, keeperBarrier⟩
    · have nonempty : plan.newer.isEmpty = false := by
        cases names : plan.newer with
        | nil => exact (empty names).elim
        | cons => rfl
      simp only [aligned, nonempty, Bool.false_and, Bool.false_eq_true, ite_false, Nat.lt_irrefl] at finish
      obtain ⟨keeperEntry, prune, keeperBarrier⟩ := finish
      obtain ⟨unlinked, removed, suffixBarrier⟩ :=
        returnedWalUnlinksAndBarrier directory plan remove write sync rename prune
      have effects := suffix empty
      have rootAuthorized := (effects.syncKeepsDirectory syncedRoot).trans
        ((effects.readsDirectory loadedRoot).2.1.trans cachedRoot)
      let invariant (_ : Unit) (atHeap : heap) :=
        view.directory atHeap cached = some root ∧ view.pending atHeap pending = view.pending entry pending
      have keeps {ordinal before after result} (member : ordinal ∈ plan.newer)
          (ran : remove (directory.file (.walSegment ordinal)) before = .ok result after)
          (accepted : RunCollection.ownedUnlinkResult result = .ok ()) (known : invariant () before) :
          invariant () after :=
        let framed := effects.removesKeepCache member ran accepted
        ⟨framed.1.trans known.1, framed.2.trans known.2⟩
      have unlinkedCache := foldReturnedWalUnlinks directory plan remove write sync rename invariant (fun _ _ => ())
        (initial := ()) ⟨rootAuthorized, authorizedPending⟩ (fun member ran accepted known => keeps member ran accepted known)
        removed
      change syncer.group directory.path cached active pending #[directory.path] unlinked = .ok () keeperEntry at suffixBarrier
      obtain ⟨suffixHandle, suffixIssued, loadedSuffix, syncedSuffix⟩ := syncer.rootGroupReturned suffixBarrier
      obtain ⟨readRoot, _, readPending⟩ := effects.readsDirectory loadedSuffix
      have sameRoot := Option.some.inj (readRoot.trans unlinkedCache.1)
      subst suffixHandle
      have pendingAtKeeper := (syncKeepsPending syncedSuffix).trans (readPending.trans unlinkedCache.2)
      refine ⟨keeperEntry, ?_, pendingAtKeeper, keeperBarrier⟩
      rw [ite_eq_right empty]
      exact ⟨unlinked, suffixIssued, removed, loadedSuffix, syncedSuffix⟩
  obtain ⟨keeperEntry, pruned, pendingAtKeeper, keeperBarrier⟩ := tail
  obtain ⟨entries, loaded, consumed, got, chosen, cleared, synced⟩ :=
    calls.rememberedPendingReturned view (file_ne_directory directory (.walSegment plan.keeper))
      (pendingAtKeeper.trans (recordsKeeper remembered)) readsPending keeperBarrier
  exact ⟨rootIssued, authorized, keeperEntry, entries, loaded, consumed, loadedRoot, syncedRoot, pruned, got, chosen,
    cleared, synced⟩

end AlignedKeeperCacheCallbacks

variable {input : FilePath} {directory : DiskDirectory} {inventory : DescriptorInventory}
  {retry : LockedFileState FileImage} {history : List WAL.Write}
  {layout : CanonicalKeeperLayout retry.image history} {published : CheckpointPublication.Image}
  {checkpoint : Option (PackedTable × UInt64)}
  {admission : CensusOpenAdmissionReports input directory inventory retry}
  {vacant : TryLockObserves retry.owners directory (.ok true)}
  {selected : SelectedIntegrityCheckpoint published.durable retry.image.directory.active.manifest checkpoint}
  {calls : CapturedAlignedCallbacks admission} {reads : CapturedMarkedReadReports admission layout published}
  {heap : Type}

private def keeperPath (directory : DiskDirectory) (first : Nat) : FilePath :=
  directory.file (.walSegment first)

/-- The raw keeper callbacks use the cells from the preceding cache
allocation. Earlier checkpoint and WAL reads reach the given entry
census. The directory and keeper fsyncs carry their own file and slot
effects, including the keeper's observed drops after the second fsync. -/
structure AlignedKeeperCacheReport
    (finish : CapturedAlignedFinish calls reads vacant selected)
    (view : OpenCloseHeapView heap FileImage) (init : OpenSyncCacheCallbacks heap) (cacheEntry : heap)
    (seed : OpenSyncCacheAllocations admission.opened view init cacheEntry)
    (callbacks : AlignedKeeperCacheCallbacks heap) (entry : heap) where
  keeper : IO.FS.Handle
  opened : heap
  read : heap
  remembered : heap
  authorized : heap
  consumed : heap
  reached : heap
  entryDirectory : view.directory entry seed.directoryRef = view.directory seed.afterPending seed.directoryRef
  entryActive : view.active entry seed.activeRef = view.active seed.afterPending seed.activeRef
  entryPending : view.pending entry seed.pendingRef = view.pending seed.afterPending seed.pendingRef
  entryFiles : view.files entry = admission.held
  entryCensus : view.descriptors entry = finish.readCustody.atOpen
  rawOpen : callbacks.openRead (keeperPath directory layout.keeper.first) entry = .ok keeper opened
  rawKeeper : view.handle opened keeper = (reads.wal.keeper.calls.inventory, reads.wal.keeper.calls.slot, 0)
  openedCensus : view.descriptors opened = reads.wal.keeper.calls.inventory
  rawRead : readExactPrefixWith (IO.userError "short or oversized WAL keeper read") (callbacks.readChunk keeper)
    layout.keeper.bytes.size ByteArray.empty opened = .ok layout.keeper.bytes read
  readFiles : view.files read = admission.held
  readCensus : view.descriptors read = finish.readCustody.afterRead
  rawRemember : callbacks.modifyPending seed.pendingRef (pushPending (keeperPath directory layout.keeper.first) keeper)
    read = .ok () remembered
  rememberFrame : view.files remembered = view.files read ∧ view.descriptors remembered = view.descriptors read
  directoryLoad : callbacks.getDirectory seed.directoryRef remembered = .ok (some seed.handle) remembered
  sameDirectory : view.handle remembered seed.handle = (admission.reached, admission.cached, 0)
  directorySync : callbacks.sync seed.handle remembered = .ok () authorized
  authorizedFiles : view.files authorized = { admission.held with image := retry.image.syncDirectory }
  authorizedCensus : view.descriptors authorized = finish.readCustody.afterRead.afterDrops finish.repair.afterAuthorization
  pendingLoad : callbacks.getPending seed.pendingRef authorized =
    .ok [(keeperPath directory layout.keeper.first, keeper)] authorized
  consume : callbacks.setPending seed.pendingRef [] authorized = .ok () consumed
  consumeFrame : view.files consumed = view.files authorized ∧ view.descriptors consumed = view.descriptors authorized
  sameKeeper : view.handle consumed keeper = view.handle opened keeper
  keeperSync : callbacks.sync keeper consumed = .ok () reached
  reachedFiles : view.files reached = { admission.held with image := retry.image.syncDirectory.syncKeeper }
  reachedCensus : view.descriptors reached = finish.census
  directoryKept : view.directory reached seed.directoryRef = view.directory entry seed.directoryRef
  activeKept : view.active reached seed.activeRef = view.active entry seed.activeRef
  pendingConsumed : view.pending reached seed.pendingRef = []
  directoryHandleKept : view.handle reached seed.handle = view.handle remembered seed.handle

variable {finish : CapturedAlignedFinish calls reads vacant selected}
  {view : OpenCloseHeapView heap FileImage} {init : OpenSyncCacheCallbacks heap} {cacheEntry entry : heap}
  {seed : OpenSyncCacheAllocations admission.opened view init cacheEntry} {callbacks : AlignedKeeperCacheCallbacks heap}

def AlignedKeeperCacheReport.schedule
    (_seen : AlignedKeeperCacheReport finish view init cacheEntry seed callbacks entry)
    (remove : FilePath → EStateM IO.Error heap (Except IO.Error Unit))
    (write : FilePath → ByteArray → EStateM IO.Error heap Unit)
    (rename : FilePath → FilePath → EStateM IO.Error heap Unit) : EStateM IO.Error heap Unit :=
    let path := keeperPath directory layout.keeper.first
    let size := reads.wal.keeper.calls.metadata.byteSize.toNat
    let sync := callbacks.syncPaths directory.path seed.directoryRef seed.activeRef seed.pendingRef
    do
      let _ ← callbacks.readKeeper seed.pendingRef path layout.keeper.bytes.size size
      finishBoundedMarkedOpen directory layout.boundedPlan size remove write sync rename

private theorem alignedExtent (finish : CapturedAlignedFinish calls reads vacant selected) :
    layout.keeper.bytes.size = reads.wal.keeper.calls.metadata.byteSize.toNat := by
  have exactSize := finish.repair.aligned
  rw [finish.sameKeeper] at exactSize
  exact exactSize

/-- The actual keeper reader returns the selected bytes at the heap
where it has just remembered the original read handle. -/
theorem AlignedKeeperCacheReport.readsKeeper
    (seen : AlignedKeeperCacheReport finish view init cacheEntry seed callbacks entry) :
    callbacks.readKeeper seed.pendingRef (directory.file (.walSegment layout.keeper.first))
      layout.keeper.bytes.size reads.wal.keeper.calls.metadata.byteSize.toNat entry =
      .ok layout.keeper.bytes seen.remembered := by
  rw [← alignedExtent finish]
  exact callbacks.readsAligned reads.wal.keeperFits seen.rawOpen seen.rawRead seen.rawRemember

/-- Both barriers start at the heap returned by the keeper reader.
The bounded finisher uses the pending handle already held there. -/
theorem AlignedKeeperCacheReport.repairsAfterRead
    (seen : AlignedKeeperCacheReport finish view init cacheEntry seed callbacks entry)
    (remove : FilePath → EStateM IO.Error heap (Except IO.Error Unit))
    (write : FilePath → ByteArray → EStateM IO.Error heap Unit)
    (rename : FilePath → FilePath → EStateM IO.Error heap Unit) :
    finishBoundedMarkedOpen directory layout.boundedPlan reads.wal.keeper.calls.metadata.byteSize.toNat
      remove write (callbacks.syncPaths directory.path seed.directoryRef seed.activeRef seed.pendingRef) rename
      seen.remembered = .ok () seen.reached := by
  let sync := callbacks.syncPaths directory.path seed.directoryRef seed.activeRef seed.pendingRef
  have bytes : layout.boundedPlan.keeperBytes.size = layout.boundedPlan.keeperSize := layout.target.trimmedSize
  have sizeEq := (alignedExtent finish).symm.trans bytes
  have noLater : layout.boundedPlan.newer = [] := finish.repair.noLater
  have valid := layout.boundedPlan_valid (by simp [noLater])
  have separate := file_ne_directory directory (.walSegment layout.keeper.first)
  have directorySelected : sync #[directory.path] seen.remembered = .ok () seen.authorized :=
    callbacks.syncsDirectory seen.directoryLoad seen.directorySync
  have selectedKeeper : sync #[directory.file (.walSegment layout.keeper.first)] seen.authorized = .ok () seen.reached :=
    callbacks.syncsPendingKeeper separate seen.pendingLoad seen.consume seen.keeperSync
  exact finishBoundedMarkedOpen_alignedEmpty directory layout.boundedPlan
    reads.wal.keeper.calls.metadata.byteSize.toNat remove write sync rename valid bytes sizeEq noLater
    directorySelected selectedKeeper

/-- Read the marked prefix and execute the two actual aligned barriers.
The sync of the original keeper consumes its remembered reference before
issuing fsync on that same handle. -/
theorem AlignedKeeperCacheReport.returns
    (seen : AlignedKeeperCacheReport finish view init cacheEntry seed callbacks entry)
    (remove : FilePath → EStateM IO.Error heap (Except IO.Error Unit))
    (write : FilePath → ByteArray → EStateM IO.Error heap Unit)
    (rename : FilePath → FilePath → EStateM IO.Error heap Unit) :
    seen.schedule remove write rename entry = .ok () seen.reached ∧
    view.handle seen.consumed seen.keeper = (reads.wal.keeper.calls.inventory, reads.wal.keeper.calls.slot, 0) ∧
    view.files seen.consumed = { admission.held with image := retry.image.syncDirectory } ∧
    view.descriptors seen.consumed = finish.readCustody.afterRead.afterDrops finish.repair.afterAuthorization ∧
    (view.cacheAt seen.reached seed.directoryRef seed.activeRef seed.pendingRef,
      view.descriptors seen.reached, view.files seen.reached) =
      (admission.cache, finish.census, { admission.held with image := retry.image.syncDirectory.syncKeeper }) := by
  refine ⟨?_, seen.sameKeeper.trans seen.rawKeeper, seen.consumeFrame.1.trans seen.authorizedFiles,
    seen.consumeFrame.2.trans seen.authorizedCensus, ?_⟩
  · simpa only [schedule, keeperPath, Bind.bind, EStateM.bind, seen.readsKeeper] using
      seen.repairsAfterRead remove write rename
  · simp only [OpenCloseHeapView.cacheAt, seen.directoryKept, seen.entryDirectory,
      seed.directoryKept, seed.directorySet, seen.activeKept, seen.entryActive, seed.activeKept, seed.activeSet,
      seen.pendingConsumed, Option.map_some, Option.map_none, List.map_nil, seen.directoryHandleKept, seen.sameDirectory,
      seen.reachedFiles, seen.reachedCensus, CensusOpenAdmissionReports.cache]

end Alvoki.Storage.DiskSession
