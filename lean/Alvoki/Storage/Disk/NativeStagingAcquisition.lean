import Alvoki.Storage.Disk.StagingFile
import Alvoki.Storage.Disk.NativeFileEffectProjection

namespace Alvoki.Storage

open System
open DiskSession.NativeFileEffectProjection (reached)

variable {heap : Type}

private theorem keepsAfterBind {α β : Type} (frame : heap → heap → Prop)
    (compose : ∀ {a b c}, frame a b → frame b c → frame a c)
    (first : EStateM IO.Error heap α) (next : α → EStateM IO.Error heap β) (entry : heap)
    (firstKeeps : frame entry (reached (first entry)))
    (nextKeeps : ∀ {value after}, first entry = .ok value after → frame after (reached (next value after))) :
    frame entry (reached ((first >>= next) entry)) := by
  cases returned : first entry with
  | error cause after => simpa [Bind.bind, EStateM.bind, returned, reached] using firstKeeps
  | ok value after =>
    have kept := nextKeeps returned
    rw [returned] at firstKeeps
    simpa [Bind.bind, EStateM.bind, returned] using compose firstKeeps kept

/-- The no-follow stat frames the reached state. It can trigger an
unlink only when it returned a regular file. -/
theorem removeStaleStagingWith_keeps
    (stat : FilePath → EStateM IO.Error heap (Except IO.Error IO.FS.Metadata))
    (unlink : FilePath → EStateM IO.Error heap (Except IO.Error Unit)) (path : FilePath)
    (frame : heap → heap → Prop) (identity : ∀ atHeap, frame atHeap atHeap)
    (compose : ∀ {a b c}, frame a b → frame b c → frame a c) (entry : heap)
    (statKeeps : frame entry (reached (stat path entry)))
    (unlinkKeeps : ∀ {info before}, stat path entry = .ok (.ok info) before →
      (info.type == .file) = true → frame before (reached (unlink path before))) :
    frame entry (reached (removeStaleStagingWith stat unlink path entry)) := by
  unfold removeStaleStagingWith
  refine keepsAfterBind frame compose _ _ entry statKeeps ?_
  intro metadata after returned
  split
  · rename_i info
    by_cases regular : info.type == .file
    · simp only [regular, ite_true]
      refine keepsAfterBind frame compose _ _ after (unlinkKeeps returned regular) ?_
      intro result final _
      cases RunCollection.ownedUnlinkResult result <;> exact identity final
    · simpa [regular, Bind.bind, EStateM.bind, throw, throwThe, MonadExceptOf.throw, EStateM.throw, reached]
        using identity after
  next => exact identity after
  next => exact identity after

/-- The frame tracks the actual acquisition. Only the reached EEXIST
branch uses the detach and retry frames. -/
theorem withFreshStaging_acquireKeeps {handle : Type}
    (tryCreate : FilePath → EStateM IO.Error heap (Except IO.Error handle))
    (detach : FilePath → EStateM IO.Error heap Unit) (create : FilePath → EStateM IO.Error heap handle)
    (path : FilePath) (frame : heap → heap → Prop) (identity : ∀ atHeap, frame atHeap atHeap)
    (compose : ∀ {a b c}, frame a b → frame b c → frame a c) (entry : heap)
    (tryKeeps : frame entry (reached (tryCreate path entry)))
    (detachKeeps : ∀ {name details conflict}, tryCreate path entry = .ok (.error (.alreadyExists name 17 details)) conflict →
      frame conflict (reached (detach path conflict)))
    (createKeeps : ∀ {name details conflict before}, tryCreate path entry = .ok (.error (.alreadyExists name 17 details)) conflict →
      detach path conflict = .ok () before → frame before (reached (create path before))) :
    frame entry (reached (withFreshStaging tryCreate detach create path pure entry)) := by
  unfold withFreshStaging
  refine keepsAfterBind frame compose _ _ entry tryKeeps ?_
  intro result after returned
  split
  next => exact identity after
  next =>
    refine keepsAfterBind frame compose _ _ after (detachKeeps returned) ?_
    intro value before detached
    cases value
    exact keepsAfterBind frame compose _ _ before (createKeeps returned detached) (fun {_ final} _ => identity final)
  next => exact identity after

/-- Invert a successful acquisition to the exclusive create that
returned that handle. Only an EEXIST result can reach the retry. -/
theorem withFreshStaging_acquireProvides {handle : Type}
    (tryCreate : FilePath → EStateM IO.Error heap (Except IO.Error handle))
    (detach : FilePath → EStateM IO.Error heap Unit) (create : FilePath → EStateM IO.Error heap handle)
    (path : FilePath)
    (observes : handle → heap → Prop)
    {entry opened : heap} {file : handle}
    (acquired : withFreshStaging tryCreate detach create path pure entry = .ok file opened)
    (first : ∀ {file reached}, tryCreate path entry = .ok (.ok file) reached →
      observes file reached)
    (retry : ∀ {file before reached}, create path before = .ok file reached →
      observes file reached) : observes file opened := by
  unfold withFreshStaging at acquired
  cases tried : tryCreate path entry with
  | error => simp [Bind.bind, EStateM.bind, tried] at acquired
  | ok initial reached =>
    simp only [Bind.bind, EStateM.bind, tried] at acquired
    split at acquired
    next selected =>
      simp [Pure.pure] at acquired
      obtain ⟨rfl, rfl⟩ := acquired
      exact first tried
    next =>
      cases detached : detach path reached with
      | error => simp [EStateM.bind, detached] at acquired
      | ok value atRetry =>
        cases value
        cases created : create path atRetry with
        | error => simp [EStateM.bind, detached, created] at acquired
        | ok selected atOpen =>
          simp [EStateM.bind, detached, created, Pure.pure] at acquired
          obtain ⟨rfl, rfl⟩ := acquired
          exact retry created
    next => simp [EStateM.bind, throw, throwThe, MonadExceptOf.throw, EStateM.throw] at acquired

/-- Use the acquired description in the supplied continuation. -/
theorem withFreshStaging_bind {handle α : Type}
    (tryCreate : FilePath → EStateM IO.Error heap (Except IO.Error handle))
    (detach : FilePath → EStateM IO.Error heap Unit) (create : FilePath → EStateM IO.Error heap handle)
    (path : FilePath) (use : handle → EStateM IO.Error heap α) :
    withFreshStaging tryCreate detach create path use =
      (withFreshStaging tryCreate detach create path pure >>= use) := by
  simp only [withFreshStaging, bind_assoc, pure_bind]
  congr 1
  funext outcome
  split <;> simp [bind_assoc]

/-- Compose the write, flush and next action at the description that
acquisition actually returned. The frame includes a reached error. -/
theorem writeFreshStagedWith_keeps {handle α : Type}
    (tryCreate : FilePath → EStateM IO.Error heap (Except IO.Error handle))
    (detach : FilePath → EStateM IO.Error heap Unit) (create : FilePath → EStateM IO.Error heap handle)
    (write : handle → ByteArray → EStateM IO.Error heap Unit) (flush : handle → EStateM IO.Error heap Unit)
    (path : FilePath) (bytes : ByteArray) (next : handle → EStateM IO.Error heap α)
    (frame : heap → heap → Prop) (compose : ∀ {a b c}, frame a b → frame b c → frame a c) (entry : heap)
    (opened : frame entry (reached (withFreshStaging tryCreate detach create path pure entry)))
    (written : ∀ {file atOpen}, withFreshStaging tryCreate detach create path pure entry = .ok file atOpen →
      frame atOpen (reached (write file bytes atOpen)))
    (flushed : ∀ {file atOpen atWrite}, withFreshStaging tryCreate detach create path pure entry = .ok file atOpen →
      write file bytes atOpen = .ok () atWrite → frame atWrite (reached (flush file atWrite)))
    (continued : ∀ {file atOpen atWrite atFlush}, withFreshStaging tryCreate detach create path pure entry = .ok file atOpen →
      write file bytes atOpen = .ok () atWrite → flush file atWrite = .ok () atFlush →
      frame atFlush (reached (next file atFlush))) :
    frame entry (reached ((writeFreshStagedWith tryCreate detach create write flush path bytes >>= next) entry)) := by
  unfold writeFreshStagedWith
  rw [withFreshStaging_bind]
  simp only [bind_assoc, pure_bind]
  refine keepsAfterBind frame compose _ _ entry opened ?_
  intro file atOpen acquired
  refine keepsAfterBind frame compose _ _ atOpen (written acquired) ?_
  intro value atWrite wrote
  cases value
  refine keepsAfterBind frame compose _ _ atWrite (flushed acquired wrote) ?_
  intro value atFlush didFlush
  cases value
  exact continued acquired wrote didFlush

end Alvoki.Storage
