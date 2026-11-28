import Alvoki.Experiments.WAL.Segmented.Native
import Alvoki.Experiments.WAL.Segmented.Proofs.Reopen
import Alvoki.Experiments.WAL.Segmented.Proofs.ControlCodec
import Alvoki.Experiments.WAL.Segmented.Proofs.Discard
import Std.Data.String.ToNat
import Init.Data.String.Lemmas.TakeDrop

namespace WalRecoverySlice.Segmented.Native

open System

/-- With metadata and bytes from the bound CONTROL file, the actual native
read selects its canonical control, including the metadata size check. -/
theorem readControl_canonical (root : FilePath) (c : Control)
    (capacity : c.capacity ≤ 255) (active : c.active ≤ ControlCodec.wordMax)
    (discarded : c.discarded ≤ ControlCodec.wordMax) :
    readControlWith (m := Except String)
      (fun path => if path = root / "CONTROL" then .ok (true, (ControlCodec.encode c).size)
        else .error "unexpected metadata path")
      (fun path => if path = root / "CONTROL" then .ok (ControlCodec.encode c)
        else .error "unexpected read path") root = .ok c := by
  have fits := ControlCodec.encoded_size c capacity active discarded
  simp [readControlWith, show ¬ 80 < (ControlCodec.encode c).size from Nat.not_lt.mpr fits,
    ControlCodec.decode_encode c active discarded, Bind.bind, Pure.pure, Except.bind, Except.pure]

/-- Root acquisition opens only the protected lock name, and a denied
lock returns no owned descriptor. A missing lock can be created by open. -/
theorem acquireRoot_selects (root : FilePath) (metadata : Option Bool)
    (valid : metadata ≠ some false) (granted : Bool) :
    acquireRootWith (m := Except String)
      (fun path => if path = root / "lock" then .ok metadata else .error "unexpected metadata path")
      (fun path mode => match mode with
        | .append => if path = root / "lock" then .ok path else .error "unexpected lock path"
        | _ => .error "unexpected lock mode")
      (fun reached => if reached = root / "lock" then .ok granted else .error "unexpected lock")
      root =
    if granted then .ok (root / "lock") else .error "segmented WAL already open" := by
  cases metadata with
  | none => cases granted <;> simp [acquireRootWith, Bind.bind, Pure.pure, Except.bind, Except.pure] <;> rfl
  | some regular =>
    cases regular
    · exact (valid rfl).elim
    · cases granted <;> simp [acquireRootWith, Bind.bind, Pure.pure, Except.bind, Except.pure] <;> rfl

/-- The ready phase stores exactly the session produced by the shared
reopen protocol. The public scan uses that phase's cached view. -/
theorem scan_ready (owned : store) (session : Session) :
    scanWith (m := Except String) (.ready owned session) = .ok session.view := rfl

theorem close_ready (owned : store) (session : Session) (release : store → Except String Unit) :
    closeWith (fun _ => .ok (.ready owned session)) release = release owned := rfl

theorem close_alreadyClosed (release : store → Except String Unit) :
    closeWith (fun _ => .ok .closed) release = .ok () := rfl

/-- The child reference is emptied before calling close. If close fails the
old child cannot be taken a second time by root cleanup. -/
theorem closeChild_reached (close : child → EStateM error (Option (Nat × child)) Unit)
    (held : Option (Nat × child)) :
    (closeChildWith
      (fun current => EStateM.Result.ok current none)
      close).run held =
      match held with
      | none => .ok () none
      | some (_, child) => (close child).run none := by
  cases held with
  | none => rfl
  | some pair => cases pair; rfl

/-- The public phase is set to closed before release. Repeat close has no
release call, including after a reported first release error. -/
theorem closePhase_reached (release : store → EStateM error (Phase store) Unit)
    (held : Phase store) :
    (closeWith (fun phase old => .ok old phase) release).run held =
      match held with
      | .ready owned _ | .poisoned owned => (release owned).run .closed
      | .closed => .ok () .closed := by
  cases held <;> rfl

/-- Root unlock receives the state reached by child close on either outcome. -/
theorem release_reached (close unlock : EStateM error state Unit) (before : state) :
    (releaseWith (error := error) close unlock).run before =
      match close.run before with
      | .ok () after => unlock.run after
      | .error childError after =>
        match unlock.run after with
        | .ok () released => .error childError released
        | .error _ reached => .error childError reached := by
  simp only [releaseWith, cleanupOnError, EStateM.run, Bind.bind, EStateM.bind, tryCatchThe]
  cases closed : close before with
  | ok value after => cases value; simp [MonadExceptOf.tryCatch, EStateM.tryCatch, closed]
  | error err after =>
    cases unlocked : unlock after with
    | ok value _ => cases value; simp [MonadExceptOf.tryCatch, EStateM.tryCatch, closed, unlocked, EStateM.bind, EStateM.Backtrackable.restore, EStateM.dummyRestore] <;> rfl
    | error => simp [MonadExceptOf.tryCatch, EStateM.tryCatch, closed, unlocked, EStateM.bind, EStateM.Backtrackable.restore, EStateM.dummyRestore, EStateM.pure, Pure.pure] <;> rfl

/-- Only canonical segment names can supply a reclamation ID. -/
theorem segmentId_sound {name : String} {id : Nat} (parsed : segmentId name = .ok (some id)) :
    name = segmentName id := by
  unfold segmentId at parsed
  split at parsed
  · cases parsed
  · split at parsed
    · contradiction
    · split at parsed
      · rename_i same
        cases parsed
        exact beq_iff_eq.mp same
      · contradiction

theorem segmentId_canonical (id : Nat) : segmentId (segmentName id) = .ok (some id) := by
  have suffix : ((segmentName id).drop "segment-".length).toString = id.repr := by
    apply String.toList_inj.mp
    rw [String.Slice.toString_eq, String.toList_copy_drop]
    simp [segmentName, String.toList_append] <;> rfl
  have read := Nat.toNat?_repr id
  have ordinary : ["lock", "CONTROL", "CONTROL.next"].contains (segmentName id) = false := by
    simp only [List.contains_cons, List.contains_nil, Bool.or_false, Bool.or_eq_false_iff]
    refine ⟨?_, ?_, ?_⟩ <;> apply beq_eq_false_iff_ne.mpr <;> intro eq <;>
      have wrong := congrArg (fun name : String => name.toList.head?) eq <;>
      simp [segmentName, String.toList_append] at wrong
  unfold segmentId
  rw [ordinary]
  simp only [Bool.false_eq_true, ↓reduceIte, suffix, read, beq_self_eq_true]

/-- The pure part of native enumeration recovers exactly the represented
IDs from one listing. Reserved root entries are ignored. -/
theorem listedIds_exact (name : entry → String) (items : Array entry)
    (contents : List (Option Nat))
    (parsed : items.toList.map (segmentId ∘ name) = contents.map Except.ok) :
    listedIds name items = .ok (contents.filterMap id).reverse := by
  have fold (entries : List entry) (contents : List (Option Nat))
      (parsed : entries.map (segmentId ∘ name) = contents.map Except.ok)
      (acc : List Nat) :
      entries.foldlM (fun ids item => collectId ids (name item)) acc =
        .ok ((contents.filterMap id).reverse ++ acc) := by
    induction entries generalizing contents acc with
    | nil => cases contents with
      | nil => rfl
      | cons => cases parsed
    | cons item rest ih =>
      cases contents with
      | nil => cases parsed
      | cons value contents =>
        obtain ⟨head, tail⟩ := List.cons.inj parsed
        change segmentId (name item) = .ok value at head
        cases value <;> simp [List.foldlM, collectId, head, Except.map, Bind.bind, Except.bind,
          List.reverse_cons, List.append_assoc] <;> exact ih contents tail _
  unfold listedIds
  rw [← Array.foldlM_toList, fold _ _ parsed]
  simp

/-- The retained descriptor is opened read-only on the resolved root. -/
theorem openRootDirectory_usesCanonicalPath (dir root : FilePath) (held : descriptor)
    (resolve : FilePath → Except String FilePath)
    (openFile : FilePath → IO.FS.Mode → Except String descriptor)
    (resolved : resolve dir = .ok root) (opened : openFile root .read = .ok held) :
    openRootDirectoryWith resolve openFile dir = .ok (root, held) := by
  simp [openRootDirectoryWith, Bind.bind, Pure.pure, Except.bind, Except.pure, resolved, opened]

/-- A successful acquisition passes the held directory and lock descriptions
and their common canonical path to allocation. A failed lock never allocates. -/
theorem acquireStore_bind [Monad m] [LawfulMonad m]
    (resolve : FilePath → m FilePath) (openDirectory : FilePath → IO.FS.Mode → m directory)
    (lockRoot : FilePath → m lock) (allocate : FilePath → directory → lock → m store)
    (dir : FilePath) :
    acquireStoreWith resolve openDirectory lockRoot allocate dir = (do
      let root ← resolve dir
      let directory ← openDirectory root .read
      let lock ← lockRoot root
      allocate root directory lock) := by
  simp [acquireStoreWith, openRootDirectoryWith, bind_assoc]

/-- Installation and failure cleanup receive the same acquired store. -/
theorem openWithStore_reached (acquire : EStateM abort state (Except String store))
    (load : store → ExceptT String (EStateM abort state) phase)
    (newRef : phase → ExceptT String (EStateM abort state) cell)
    (newMutex : ExceptT String (EStateM abort state) mutex)
    (release : store → ExceptT String (EStateM abort state) Unit) (before : state) :
    (openWithStore (error := String) (ExceptT.mk acquire) load newRef newMutex release).run before =
      match acquire before with
      | .ok (.ok owned) reached =>
        (installPhaseWith (error := String) (load owned) newRef newMutex (release owned)).run reached
      | .ok (.error error) reached => .ok (.error error) reached
      | .error token reached => .error token reached := by
  simp only [openWithStore, ExceptT.run, ExceptT.mk, Bind.bind, ExceptT.bind,
    EStateM.bind, ExceptT.bindCont]
  cases acquire before with
  | error => rfl
  | ok value _ => cases value <;> rfl

/-- Interpret cleanup against the same reached state as installation, even
when phase installation failed after the root protocol changed the disk. -/
theorem installPhase_reached (load : EStateM abort state (Except String phase))
    (newRef : phase → EStateM abort state (Except String cell))
    (newMutex : EStateM abort state (Except String mutex))
    (release : EStateM abort state (Except String Unit)) (before : state) :
    let action : ExceptT String (EStateM abort state) (cell × mutex) := do
      let phase ← (ExceptT.mk load : ExceptT String (EStateM abort state) phase)
      let cell ← (ExceptT.mk (newRef phase) : ExceptT String (EStateM abort state) cell)
      let mutex ← (ExceptT.mk newMutex : ExceptT String (EStateM abort state) mutex)
      return (cell, mutex)
    (installPhaseWith (error := String) (ExceptT.mk load)
      (fun phase => ExceptT.mk (newRef phase)) (ExceptT.mk newMutex)
      (ExceptT.mk release)).run before =
      match action.run before with
      | .ok (.error err) reached =>
        match release reached with
        | .ok (.ok ()) after => .ok (.error err) after
        | .ok (.error _) after => .ok (.error err) after
        | .error stopped after => .error stopped after
      | other => other := by
  dsimp only
  simp only [installPhaseWith, cleanupOnError, tryCatchThe, MonadExceptOf.tryCatch, ExceptT.tryCatch,
    ExceptT.run, ExceptT.mk, Bind.bind, EStateM.bind]
  split
  · rename_i response reached ran
    rw [ran]
    cases response with
    | ok => rfl
    | error =>
      simp only [ExceptT.bind, ExceptT.bindCont, ExceptT.mk, Bind.bind, EStateM.bind]
      cases release reached with
      | error => rfl
      | ok response _ => cases response with
        | error => rfl
        | ok value => cases value; rfl
  · rename_i _ _ ran
    rw [ran]

/-- On a reported continuation error, close receives the acquired child
and the exact reached state. An acquisition error has nothing to close. -/
theorem withActiveChild_reached
    (acquire : EStateM abort state (Except String child))
    (close : child → ExceptT String (EStateM abort state) Unit)
    (resume : child → ExceptT String (EStateM abort state) result) (before : state) :
    (withActiveChild (error := String) (ExceptT.mk acquire) close resume).run before =
      match acquire before with
      | .ok (.ok child) opened =>
        match (resume child).run opened with
        | .ok (.error err) reached =>
          match (close child).run reached with
          | .ok (.ok ()) after => .ok (.error err) after
          | .ok (.error _) after => .ok (.error err) after
          | .error token after => .error token after
        | other => other
      | .ok (.error err) reached => .ok (.error err) reached
      | .error token reached => .error token reached := by
  simp only [withActiveChild, cleanupOnError, Bind.bind, ExceptT.bind, ExceptT.run, ExceptT.mk,
    EStateM.bind, ExceptT.bindCont, tryCatchThe, MonadExceptOf.tryCatch, ExceptT.tryCatch]
  cases acquired : acquire before with
  | error => rfl
  | ok value reached =>
    cases value with
    | error => rfl
    | ok child =>
      simp only [EStateM.bind]
      cases ran : (resume child).run reached with
      | error =>
        simp only [ExceptT.run] at ran
        rw [ran]
      | ok result after =>
        simp only [ExceptT.run] at ran
        rw [ran]
        cases result with
        | ok => rfl
        | error =>
          simp only [EStateM.bind]
          cases closed : (close child).run after with
          | error => simp only [ExceptT.run] at closed; rw [closed]
          | ok result _ =>
            simp only [ExceptT.run] at closed
            rw [closed]
            cases result with
            | error => rfl
            | ok closedValue => cases closedValue; rfl

end WalRecoverySlice.Segmented.Native

namespace WalRecoverySlice.Segmented.Model
open System
open Persistence

private abbrev ReadyChild :=
  SingleFile.Opened SingleFile.OpenTarget (SingleFile.AppendFiles SingleFile.OpenTarget)

/-- Embed the exact public child recovery result in a disk slot. A reported
failure or interruption still carries the reached image and preserves the
previous cursor. Root namespace and other slots are framed by `child`. -/
def nativeChildWorker (dir : System.FilePath) (policy : Policy)
    (reports : SingleFile.OpenReports) : Persistence.M ReadyChild := fun image =>
  match SingleFile.openExistingModel dir policy reports {image} with
  | .ok (.ok ready) after => .ok (.ok ready) after.image
  | .ok (.error err) after => .ok (.error err) after.image
  | .error token after => .error token after.image

theorem nativeChild_recoverable {id : Nat} {s : State} (dir : System.FilePath)
    (reports : SingleFile.OpenReports) (named : id ∈ s.disk.liveNames)
    (prior : Child.Recoverable policy known pending (s.disk.segment id)) :
    let result := child s id (nativeChildWorker dir policy reports) (fun ready => ready.recovered.cursor) (fun ready => ready.recovered.batches)
    let disk := (reached result).disk
    Child.Recoverable policy known pending (disk.segment id) ∧
    ∀ batches, returned result = some batches →
      WalRecoverySlice.Contract.Permitted known pending batches ∧
      Child.Installed policy (disk.segment id) (disk.cursor id) batches := by
  let run := nativeChildWorker dir policy reports
  have frame := child_reached named run (fun ready => ready.recovered.cursor) (fun ready => ready.recovered.batches)
  have observed := child_returned named run (fun ready => ready.recovered.cursor) (fun ready => ready.recovered.batches)
  have facts := prior.nativeOpen dir reports {image := s.disk.segment id} rfl
  dsimp only
  rw [frame, Disk.setSegment_here]
  have report : (run.run (s.disk.segment id)) =
      match SingleFile.openExistingModel dir policy reports {image := s.disk.segment id} with
      | .ok (.ok ready) after => .ok (.ok ready) after.image
      | .ok (.error err) after => .ok (.error err) after.image
      | .error token after => .error token after.image := rfl
  cases issued : SingleFile.openExistingModel dir policy reports {image := s.disk.segment id} with
  | error =>
    rw [issued] at facts report
    rw [report]
    refine ⟨facts.1, ?_⟩
    intro batches returned
    rw [observed, report] at returned
    cases returned
  | ok response after =>
    cases response with
    | error =>
      rw [issued] at facts report
      rw [report]
      refine ⟨facts.1, ?_⟩
      intro batches returned
      rw [observed, report] at returned
      cases returned
    | ok ready =>
      rw [issued] at facts report
      rw [report]
      refine ⟨facts.1, ?_⟩
      intro batches returned
      rw [observed, report] at returned
      obtain rfl := Option.some.inj returned
      obtain ⟨_, _, _, permitted, installed, _⟩ := facts.2
      rw [Disk.setCursor_here]
      exact ⟨permitted, installed⟩

/-- The public child path keeps an already settled sealed segment's exact
bytes, even if a later namespace action fails. -/
theorem nativeChild_sealed (dir : System.FilePath) (r : SingleFile.OpenReports)
    (entry : Child.Settled policy image history)
    (bounded : ∀ b ∈ history, b.length ≤ 32) (fits : history.length ≤ 255) :
    Persistence.reached ((nativeChildWorker dir policy r).run image) = image := by
  have physical := SingleFile.openExisting_worker dir policy r {image} rfl
    (entry.recoverable bounded fits).dirty (entry.recoverable bounded fits).markers
  have worker := (reopensSettledSegmentScheduled entry.ready entry.clean bounded fits r.worker r.writebacks).1
  rw [← SingleFile.recoverScheduled_eq] at worker
  dsimp only at physical
  rw [settleFiles_clean _ _ entry.clean, worker, settleFiles_clean _ _ entry.clean] at physical
  have same := physical.1.elim id id
  unfold nativeChildWorker
  cases ran : SingleFile.openExistingModel dir policy r {image} with
  | error => simpa [ExceptT.run, ran, Persistence.reached, SingleFile.postState] using same
  | ok value _ => cases value <;>
      simpa [ExceptT.run, ran, Persistence.reached, SingleFile.postState] using same

/-- A successful public child open returns the value selected from the
live child bytes. Whole-file writeback outside the worker keeps that view. -/
theorem nativeChild_selected (dir : System.FilePath) (r : SingleFile.OpenReports)
    (entry : Child.Recoverable policy known pending image)
    (selected : Child.Selects policy image batches)
    (opened : SingleFile.openExistingModel dir policy r {image} = .ok (.ok ready) after) :
    ready.recovered.batches = batches := by
  have physical := SingleFile.openExisting_worker dir policy r {image} rfl entry.dirty entry.markers
  rw [opened] at physical
  obtain ⟨marker, decoded, selected, rfl⟩ := selected
  have preserved : ReopenSelection policy (settleFiles r.beforeWorker image) marker decoded := by
    apply writebacks_keep (P := fun state => ReopenSelection policy state marker decoded) _ _ selected
    intro state file prior
    cases policy <;> cases marker <;> cases file <;> exact prior
  have exact := scheduledReopen_selected preserved r.worker r.writebacks ready.recovered
  rw [← SingleFile.recoverScheduled_eq] at exact
  exact congrArg Decoded.batches (exact physical.2)

/-- Interpret the public single-file producer at the selected segment path. -/
def nativeOpenChild (root : FilePath) (reports : Nat → Nat → SingleFile.OpenReports)
    (policy : Policy) (id : Nat) : M (List Bytes) := fun s =>
  child s id (nativeChildWorker (Native.segmentPath root id) policy (reports s.step id))
    (fun ready => ready.recovered.cursor) (fun ready => ready.recovered.batches)

def HealthyChildren (reports : Nat → Nat → SingleFile.OpenReports) : Prop :=
  ∀ step id, reports step id = {}

theorem nativeOpenChild_effects (root : FilePath) (reports : Nat → Nat → SingleFile.OpenReports) :
    OpenChildEffects (nativeOpenChild root reports) (HealthyChildren reports) where
  frame _ _ _ named := child_frame named _ _ _
  settled {policy id s history} named entry bounded fits := by
    have frame := child_reached named
      (nativeChildWorker (Native.segmentPath root id) policy (reports s.step id))
      (fun ready => ready.recovered.cursor) (fun ready => ready.recovered.batches)
    have facts := nativeChild_recoverable (Native.segmentPath root id) (reports s.step id)
      named (entry.recoverable bounded fits)
    refine ⟨?_, fun batches observed => ?_⟩
    · change (reached (child s id _ (fun (ready : ReadyChild) => ready.recovered.cursor) (fun (ready : ReadyChild) => ready.recovered.batches))).disk.segment id = _
      rw [frame, Disk.setSegment_here]
      exact nativeChild_sealed _ _ entry bounded fits
    · have permitted := (facts.2 batches observed).1
      cases permitted with
      | inl same => exact same
      | inr same => simpa using same
  dirty {policy id s known pending} named entry :=
    nativeChild_recoverable (Native.segmentPath root id) (reports s.step id) named entry
  selected {policy id s batches known pending} named entry chosen observed ack := by
    let dir := Native.segmentPath root id
    let r := reports s.step id
    change returned (child s id (nativeChildWorker dir policy r) (fun ready => ready.recovered.cursor) (fun ready => ready.recovered.batches)) = _ at ack
    rw [child_returned named] at ack
    cases opened : SingleFile.openExistingModel dir policy r {image := s.disk.segment id} with
    | error => simp [nativeChildWorker, ExceptT.run, opened, Persistence.acknowledged] at ack
    | ok response after =>
      cases response with
      | error => simp [nativeChildWorker, ExceptT.run, opened, Persistence.acknowledged] at ack
      | ok ready =>
        have eq : ready.recovered.batches = observed := by
          simpa [nativeChildWorker, ExceptT.run, opened, Persistence.acknowledged] using ack
        exact eq.symm.trans (nativeChild_selected dir r entry chosen opened)
  healthy {policy id s known pending} named entry healthy := by
    let dir := Native.segmentPath root id
    obtain ⟨ready, after, opened⟩ :=
      SingleFile.openExisting_healthy dir policy (s.disk.segment id) entry.dirty
    refine ⟨ready.recovered.batches, ?_⟩
    change returned (child s id (nativeChildWorker dir policy (reports s.step id))
      (fun ready => ready.recovered.cursor) (fun ready => ready.recovered.batches)) = _
    rw [child_returned named, healthy s.step id]
    simp [nativeChildWorker, ExceptT.run, opened, Persistence.acknowledged]

/-- Both barriers use the already opened root directory. One filesystem
effect settles CONTROL and child directory names together. -/
theorem nativeRootBarrier (directory : System.FilePath) (effect : Primitive) (s : State) :
    let result := (Native.syncRootWith (m := M)
      (fun path state => if path = directory then barrier effect Disk.syncRoot state
        else .ok (.error "wrong directory description") state) directory).run s
    result = barrier effect Disk.syncRoot s ∧
      ((reached result).disk = s.disk ∨
        ((reached result).disk.durableControl = s.disk.liveControl ∧
         (reached result).disk.durableNames = s.disk.liveNames)) := by
  simp only [Native.syncRootWith, ExceptT.run]
  cases effect with
  | before fault =>
    cases fault <;> exact ⟨rfl, .inl rfl⟩
  | after fault =>
    cases fault with
    | none => exact ⟨rfl, .inr ⟨rfl, rfl⟩⟩
    | some fault => cases fault <;> exact ⟨rfl, .inr ⟨rfl, rfl⟩⟩

/-- Member unlinks stay inside the retired directory. In the root projection
these files are private artifacts, so only rmdir changes the root binding. -/
theorem nativeRemoveSegment (root : FilePath) (id : Nat)
    (present : Except String Bool) (members : Except String (Array String))
    (unlinkFailure : FilePath → Option Abort)
    (removeEffect : NamespaceEffect) (s : State)
    (missing : present = .ok false → id ∉ s.disk.liveNames) :
    let observe : {α : Type} → Except String α → M α := fun {_} value t => read none value t
    let dir := Native.segmentPath root id
    DiskPost (fun _ after => ∃ persist, after = s.disk.remove id persist)
      (fun after => after = s.disk ∨ ∃ persist, after = s.disk.remove id persist)
      ((Native.removeSegmentWith (m := M)
        (fun path => observe (if path = dir then present else .error "wrong metadata path"))
        (fun path => observe (if path = dir then members else .error "wrong listing path")) _root_.id
        (fun path t => read (unlinkFailure path) (.ok ()) t)
        (fun path t => if path = dir then namespaceChange removeEffect (fun d p => d.remove id p) t
          else .ok (.error "wrong rmdir path") t) root id).run s) := by
  dsimp only [Native.removeSegmentWith]
  apply bindPost (P := fun found d => d = s.disk ∧ present = .ok found)
  · change DiskPost _ _ (read none (if Native.segmentPath root id = Native.segmentPath root id
      then present else .error "wrong metadata path") s)
    rw [ite_eq_left rfl]
    cases present with
    | error => exact .inl rfl
    | ok => exact ⟨rfl, rfl⟩
  intro found t ⟨same, readPresent⟩
  cases found with
  | false =>
    refine ⟨false, ?_⟩
    rw [same]
    have filtered : s.disk.liveNames.filter (· != id) = s.disk.liveNames :=
      List.filter_eq_self.mpr (fun n hn => by
        simp only [bne_iff_ne]
        intro eq
        exact missing readPresent (eq ▸ hn))
    simp [Disk.remove, filtered]
  | true =>
    apply bindPost (P := fun _ d => d = s.disk)
    · change DiskPost _ _ (read none (if Native.segmentPath root id = Native.segmentPath root id
        then members else .error "wrong listing path") t)
      rw [ite_eq_left rfl]
      cases members with
      | error => exact .inl same
      | ok => exact same
    intro names t inspected
    apply bindPost (P := fun _ d => d = s.disk)
    · have loop (names : List String) (state : State) (same : state.disk = s.disk) :
          DiskPost (fun _ d => d = s.disk)
            (fun d => d = s.disk ∨ ∃ p, d = s.disk.remove id p)
            ((names.foldlM (m := M) (fun (_ : Unit) (name : String) state =>
              read (unlinkFailure (Native.segmentPath root id / name)) (.ok ()) state) ()).run state) := by
        induction names generalizing state with
        | nil => exact same
        | cons name tail ih =>
          apply bindPost (P := fun _ d => d = s.disk)
          · change DiskPost _ _ (read (unlinkFailure (Native.segmentPath root id / name)) (.ok ()) state)
            cases h : unlinkFailure (Native.segmentPath root id / name) with
            | none => exact same
            | some fault => cases fault <;> exact .inl same
          · intro _ next frame
            exact ih next frame
      change DiskPost _ _ ((names.foldlM (m := M) (fun (_ : Unit) (name : String) state =>
        read (unlinkFailure (Native.segmentPath root id / name)) (.ok ()) state) ()).run t)
      have eq := Array.foldlM_toList (m := M) (xs := names) (init := ()) (f := fun _ (name : String) state =>
        read (unlinkFailure (Native.segmentPath root id / name)) (.ok ()) state)
      have post := loop names.toList t inspected
      rw [eq] at post
      exact post
    intro _ last frame
    change DiskPost _ _ (if Native.segmentPath root id = Native.segmentPath root id then
      namespaceChange removeEffect (fun d p => d.remove id p) last else .ok (.error "wrong rmdir path") last)
    rw [ite_eq_left rfl]
    apply namespacePost
    · exact .inl frame
    · intro persist; exact .inr ⟨persist, by rw [frame]⟩
    · intro persist; exact ⟨persist, by rw [frame]⟩

/-- Observations by the protected child listing and the two policy reads. -/
structure ChildValidationReports where
  names : Except String (Array String)
  policySize : Except String Nat
  policyText : Except String String

def ChildValidationReports.canonical (p : Policy) : ChildValidationReports :=
  ⟨.ok #["policy", "segment", "commit.0", "commit.1"],
    .ok (Native.policyStamp p).utf8ByteSize, .ok (Native.policyStamp p)⟩

private def validateChildModel (root : FilePath) (p : Policy) (index : Nat)
    (r : ChildValidationReports) : Except String Unit :=
  let dir := Native.segmentPath root index
  Native.validateChildWith
    (fun path => if path = dir then r.names else .error "unexpected child listing path")
    (fun path => if path = dir / "policy" then r.policySize else .error "unexpected policy metadata path")
    (fun path => if path = dir / "policy" then r.policyText else .error "unexpected policy read path")
    dir p index

/-- Enumeration order and extra recognized files do not affect a healthy
validation. Both policy reads are of the selected child's policy file. -/
def ChildValidationReports.Healthy (p : Policy) (r : ChildValidationReports) : Prop :=
  (∃ names, r.names = .ok names ∧ (Native.requiredChildNames p).all names.contains = true) ∧
  r.policySize = .ok (Native.policyStamp p).utf8ByteSize ∧ r.policyText = .ok (Native.policyStamp p)

private theorem validateChildModel_healthy (root : FilePath) (p : Policy) (index : Nat)
    (r : ChildValidationReports) (healthy : r.Healthy p) :
    validateChildModel root p index r = .ok () := by
  obtain ⟨⟨names, listed, complete⟩, size, text⟩ := healthy
  simp only [validateChildModel, Native.validateChildWith, listed, size, text, complete,
    ↓reduceIte, Bind.bind, Except.bind, Pure.pure, Except.pure,
    beq_self_eq_true, Bool.and_self]

private def validatedChild {α : Type} (guard : State → Except String Unit) (action : M α) : M α :=
  fun s => match guard s with
    | .ok () => action.run s
    | .error err => .ok (.error err) s

private theorem validatedChildEffects
    (guard : Policy → Nat → State → Except String Unit) {call : Policy → Nat → M (List Bytes)}
    {healthy : Prop} (effects : OpenChildEffects call healthy) :
    OpenChildEffects (fun policy index => validatedChild (guard policy index) (call policy index))
      (healthy ∧ ∀ p i s, guard p i s = .ok ()) where
  frame p i s named := by
    cases cut : guard p i s with
    | ok value => cases value; simpa only [validatedChild, ExceptT.run, cut] using effects.frame p i s named
    | error =>
      refine ⟨s.disk.segment i, s.disk.cursor i, ?_⟩
      simp only [validatedChild, ExceptT.run, cut]
      have same : s.disk.setSegment i (s.disk.segment i) (s.disk.cursor i) = s.disk := by
        cases s.disk
        simp [Disk.setSegment]
        constructor <;> funext j <;> by_cases equal : j = i <;> simp_all
      exact same.symm
  settled {policy index s history} named entry bounded fits := by
    cases cut : guard policy index s with
    | ok value =>
      cases value
      simpa only [validatedChild, ExceptT.run, cut] using effects.settled named entry bounded fits
    | error =>
      simp only [validatedChild, ExceptT.run, cut]
      exact ⟨rfl, fun _ impossible => by cases impossible⟩
  dirty {policy index s known pending} named entry := by
    cases cut : guard policy index s with
    | ok value => cases value; simpa only [validatedChild, ExceptT.run, cut] using effects.dirty named entry
    | error =>
      simp only [validatedChild, ExceptT.run, cut]
      exact ⟨entry, fun _ impossible => by cases impossible⟩
  selected {policy index s batches known pending} named entry selected observed ack := by
    cases cut : guard policy index s with
    | ok value =>
      cases value
      exact effects.selected named entry selected observed (by simpa only [validatedChild, ExceptT.run, cut] using ack)
    | error =>
      simp only [validatedChild, ExceptT.run, cut] at ack
      cases ack
  healthy {policy index s known pending} named entry h := by
    simpa only [validatedChild, ExceptT.run, h.2 policy index s] using effects.healthy named entry h.1

/-- The sealed callback's two observations come from the handle that was
actually opened. Even a reported close error clears its held description
and leaves its reached bytes alone. -/
theorem sealedChildReport
    (ready : ReadyChild) (after : SingleFile.OpenImage)
    (lock : ready.lock = .lock)
    (phase : ready.phase = .active ready.lock (SingleFile.appendFiles ready.writer ready.reader ready.markers)
      ready.recovered.cursor ready.recovered.batches)
    (unlockError : Bool) :
    (Native.readSealedChildWith (m := SingleFile.OpenM) (error := String) (pure ready)
      (fun child => SingleFile.scanWith (SingleFile.storedPhase child))
      (fun child => ExceptT.mk (SingleFile.closeModel child.policy {unlockError}
        (SingleFile.storedPhase child)))).run after =
      .ok (if unlockError then .error "primitive error" else .ok ready.recovered.batches)
        {after with closed := true, held := false} := by
  have scan := SingleFile.scan_opened ready after phase
  have close := SingleFile.close_opened_report ready {unlockError} after lock phase
  simp only [Native.readSealedChildWith, Native.cleanupOnError, Bind.bind, ExceptT.bind,
    ExceptT.run, ExceptT.mk, EStateM.bind, ExceptT.bindCont, Pure.pure, ExceptT.pure,
    EStateM.pure, tryCatchThe, MonadExceptOf.tryCatch, ExceptT.tryCatch]
  simp only [ExceptT.run] at scan
  rw [scan]
  simp only [EStateM.pure, EStateM.bind]
  rw [close]
  cases unlockError <;> rfl

/-- A returned close error suppresses the scan result but carries the same
reached state. The single-file close changes only resource ownership. -/
private def sealedCloseResult (fault : State → Bool) (action : M (List Bytes)) : M (List Bytes) := fun s =>
  match action.run s with
  | .ok (.ok batches) t =>
    (Native.readSealedChildWith (m := M) (error := String) (pure batches) pure
      (fun _ state => .ok (if fault s then .error "primitive error" else .ok ()) state)).run t
  | .ok (.error err) t => .ok (.error err) t
  | .error token t => .error token t

private theorem sealedCloseResult_frame (fault : State → Bool) (action : M (List Bytes)) (s : State) :
    reached ((sealedCloseResult fault action).run s) = reached (action.run s) := by
  simp only [sealedCloseResult, ExceptT.run]
  cases action s with
  | error => rfl
  | ok response _ => cases response with
    | error => rfl
    | ok _ => cases fault s <;> rfl

private theorem sealedCloseResult_returned (fault : State → Bool) (action : M (List Bytes)) (s : State) :
    returned ((sealedCloseResult fault action).run s) =
      if fault s then none else returned (action.run s) := by
  simp only [sealedCloseResult, ExceptT.run]
  cases action s with
  | error => cases fault s <;> rfl
  | ok response _ => cases response <;> cases fault s <;> rfl

private theorem sealedCloseEffects
    (fault : Nat → State → Bool) {call : Policy → Nat → M (List Bytes)}
    {healthy : Prop} (effects : OpenChildEffects call healthy) :
    OpenChildEffects (fun p i => sealedCloseResult (fault i) (call p i))
      (healthy ∧ ∀ i s, fault i s = false) where
  frame p i s named := by
    rw [sealedCloseResult_frame]
    exact effects.frame p i s named
  settled {policy id s history} named entry bounded fits := by
    dsimp only
    rw [sealedCloseResult_frame, sealedCloseResult_returned]
    have facts := effects.settled named entry bounded fits
    refine ⟨facts.1, ?_⟩
    cases fault id s <;> intro _ received
    · exact facts.2 _ received
    · cases received
  dirty {policy id s known pending} named entry := by
    dsimp only
    rw [sealedCloseResult_frame, sealedCloseResult_returned]
    have facts := effects.dirty named entry
    refine ⟨facts.1, ?_⟩
    cases fault id s <;> intro _ received
    · exact facts.2 _ received
    · cases received
  selected {policy id s batches known pending} named entry selected observed ack := by
    rw [sealedCloseResult_returned] at ack
    cases cut : fault id s <;> simp only [cut, Bool.false_eq_true, ↓reduceIte] at ack
    · exact effects.selected named entry selected observed ack
    · cases ack
  healthy {policy id s known pending} named entry h := by
    simpa only [sealedCloseResult_returned, h.2 id s, Bool.false_eq_true, ↓reduceIte]
      using effects.healthy named entry h.1

/-- Reached Linux effects for the root operations. Child file unlinks are
projected out after retirement. Directory fsync and rmdir retain their
effects even when an error is reported. -/
structure RootReports where
  sealedUnlockError : Nat → Nat → Bool := fun _ _ => false
  childValidation : Nat → Nat → Policy → ChildValidationReports :=
    fun _ _ policy => .canonical policy
  controlRead : Nat → Option Abort := fun _ => none
  listFault : Nat → Option Abort := fun _ => none
  sync : Nat → Primitive := fun _ => .after none
  presenceFault : Nat → Nat → Option String := fun _ _ => none
  members : Nat → Nat → Except String (Array String) := fun _ _ => .ok #[]
  unlinkFault : Nat → FilePath → Option Abort := fun _ _ => none
  rmdir : Nat → Nat → NamespaceEffect := fun _ _ => .after false none

private def rootControl (root : FilePath) (disk : Disk) : Except String Control :=
  match disk.liveControl with
  | none => .error "missing CONTROL"
  | some c =>
    if c.capacity ≤ 255 ∧ c.active ≤ ControlCodec.wordMax ∧ c.discarded ≤ ControlCodec.wordMax then
      Native.readControlWith
        (fun path => if path = root / "CONTROL" then .ok (true, (ControlCodec.encode c).size)
          else .error "unexpected metadata path")
        (fun path => if path = root / "CONTROL" then .ok (ControlCodec.encode c)
          else .error "unexpected read path") root
    else .error "unrepresentable CONTROL"

private def rootListing (ids : List Nat) : Except String (List Nat) :=
  Native.listedIds id (ids.reverse.map Native.segmentName).toArray

private theorem rootListing_eq (ids : List Nat) : rootListing ids = .ok ids := by
  unfold rootListing
  have parsed : ((ids.reverse.map Native.segmentName).toArray).toList.map
      (Native.segmentId ∘ id) = (ids.reverse.map some).map Except.ok := by
    simp [List.map_map, Function.comp_def, Native.segmentId_canonical]
  rw [Native.listedIds_exact id _ _ parsed]
  simp [List.filterMap_map, Function.comp_def]

private def rootPresent (r : RootReports) (s : State) (id : Nat) : Except String Bool :=
  match r.presenceFault s.step id with
  | some cause => .error cause
  | none => .ok (decide (id ∈ s.disk.liveNames))

private def rootRemove (root : FilePath) (r : RootReports) (id : Nat) : M Unit := fun s =>
  let dir := Native.segmentPath root id
  (Native.removeSegmentWith (m := M)
    (fun path t => read none (if path = dir then rootPresent r s id else .error "wrong metadata path") t)
    (fun path t => read none (if path = dir then r.members s.step id else .error "wrong listing path") t) _root_.id
    (fun path t => read (r.unlinkFault s.step path) (.ok ()) t)
    (fun path t => if path = dir then namespaceChange (r.rmdir s.step id) (fun d p => d.remove id p) t
      else .ok (.error "wrong rmdir path") t) root id).run s

private def rootSync (root : FilePath) (r : RootReports) : M Unit := fun s =>
  (Native.syncRootWith (m := M)
    (fun path t => if path = root then barrier (r.sync s.step) Disk.syncRoot t
      else .ok (.error "wrong directory description") t) root).run s

private def childValidation (root : FilePath) (r : RootReports)
    (policy : Policy) (index : Nat) (s : State) : Except String Unit :=
  validateChildModel root policy index (r.childValidation s.step index policy)

private def sealedSelection (index : Nat) (s : State) : Bool :=
  match s.disk.liveControl with
  | some c => index < c.active
  | none => false

private def sealedFault (r : RootReports) (index : Nat) (s : State) : Bool :=
  sealedSelection index s && r.sealedUnlockError s.step index

/-- Return the exact single-file handle and retain its reached disk. -/
private def acquireChildModel (root : FilePath) (r : RootReports) (reports : Nat → Nat → SingleFile.OpenReports)
    (policy : Policy) (id : Nat) : M ReadyChild :=
  validatedChild (childValidation root r policy id) fun s =>
  child s id (nativeChildWorker (Native.segmentPath root id) policy (reports s.step id))
    (fun ready => ready.recovered.cursor) _root_.id

private theorem acquireChildModel_project (root : FilePath) (r : RootReports)
    (reports : Nat → Nat → SingleFile.OpenReports) (policy : Policy) (index : Nat) :
    (acquireChildModel root r reports policy index >>= fun ready => pure ready.recovered.batches) =
      validatedChild (childValidation root r policy index) (nativeOpenChild root reports policy index) := by
  funext s
  unfold acquireChildModel validatedChild nativeOpenChild
  simp only [ExceptT.run, Bind.bind, ExceptT.bind, ExceptT.bindCont, ExceptT.mk, EStateM.bind]
  cases childValidation root r policy index s with
  | error => rfl
  | ok value =>
    cases value
    by_cases named : index ∈ s.disk.liveNames
    · simp only [child, named, ↓reduceIte]
      cases (nativeChildWorker (Native.segmentPath root index) policy (reports s.step index)).run
          (s.disk.segment index) with
      | error => rfl
      | ok response _ => cases response <;> rfl
    · simp only [child, named, ↓reduceIte]
      rfl

private def nativeChildRead (root : FilePath) (r : RootReports)
    (reports : Nat → Nat → SingleFile.OpenReports) (policy : Policy) (index : Nat) : M (List Bytes) :=
  fun s =>
    match acquireChildModel root r reports policy index s with
    | .ok (.ok ready) reached =>
      if sealedSelection index s then
        match (Native.readSealedChildWith (m := SingleFile.OpenM) (error := String) (pure ready)
          (fun child => SingleFile.scanWith (SingleFile.storedPhase child))
          (fun child => ExceptT.mk (SingleFile.closeModel child.policy
            {unlockError := r.sealedUnlockError s.step index} (SingleFile.storedPhase child)))).run
              {image := reached.disk.segment index, held := true} with
        | .ok response _ => .ok response reached
        | .error token _ => .error token reached
      else .ok (.ok ready.recovered.batches) reached
    | .ok (.error err) reached => .ok (.error err) reached
    | .error token reached => .error token reached

private theorem nativeChildRead_eq (root : FilePath) (r : RootReports)
    (reports : Nat → Nat → SingleFile.OpenReports) (policy : Policy) (index : Nat) :
    nativeChildRead root r reports policy index =
      sealedCloseResult (sealedFault r index)
        (validatedChild (childValidation root r policy index) (nativeOpenChild root reports policy index)) := by
  funext s
  simp only [nativeChildRead, acquireChildModel, sealedCloseResult, validatedChild, ExceptT.run]
  cases checked : childValidation root r policy index s with
  | error => rfl
  | ok result =>
    cases result
    simp only [nativeOpenChild]
    by_cases named : index ∈ s.disk.liveNames
    · simp only [child, named, ↓reduceIte, nativeChildWorker, ExceptT.run]
      cases opened : SingleFile.openExistingModel (Native.segmentPath root index) policy (reports s.step index)
          {image := s.disk.segment index} with
      | error => rfl
      | ok response after =>
        cases response with
        | error => rfl
        | ok ready =>
          dsimp only
          cases selected : sealedSelection index s with
          | false => simp [sealedFault, selected]; rfl
          | true =>
            simp only [selected, sealedFault, Bool.true_and, ↓reduceIte]
            have ⟨lock, phase⟩ := SingleFile.openExisting_scanPhase _ _ _ _ rfl opened
            have effect := sealedChildReport ready {image := after.image, held := true} lock phase (r.sealedUnlockError s.step index)
            simp only [id_eq, Disk.setSegment_here]
            simp only [ExceptT.run] at effect
            rw [effect]
            cases r.sealedUnlockError s.step index <;> rfl
    · simp only [child, named, ↓reduceIte]

/-- The unused write callbacks retain their model implementations. Reopen
uses only the filesystem schedules in these five fields. -/
def nativeReopenOps (root : FilePath) (r : RootReports)
    (childReports : Nat → Nat → SingleFile.OpenReports) : Ops M :=
  { ops healthy with
    readControl := fun s => read (r.controlRead s.step) (rootControl root s.disk) s
    syncRoot := rootSync root r
    listSegments := fun s => read (r.listFault s.step) (rootListing s.disk.liveNames) s
    removeSegment := rootRemove root r
    openSegment := nativeChildRead root r childReports }

theorem nativeRemove_framesEntry (root : FilePath) (r : RootReports) (id : Nat) :
    FramesEntry ((nativeReopenOps root r (fun _ _ => {})).removeSegment id) := by
  intro s
  change (reached (rootRemove root r id s)).activeEntry = s.activeEntry
  unfold rootRemove Native.removeSegmentWith
  apply framesEntry_bind
  · intro t
    simp only [↓reduceIte, ExceptT.run]
    cases rootPresent r s id <;> rfl
  · intro found
    simp only
    cases found
    · intro _; rfl
    · apply framesEntry_bind
      · intro t
        simp only [↓reduceIte, ExceptT.run]
        cases r.members s.step id <;> rfl
      · intro names
        apply framesEntry_bind
        · have loop (items : List String) :
              FramesEntry (items.foldlM (m := M) (fun (_ : Unit) (name : String) state =>
                read (r.unlinkFault s.step (Native.segmentPath root id / name)) (.ok ()) state) ()) := by
            induction items with
            | nil => intro _; rfl
            | cons item tail ih =>
              apply framesEntry_bind
              · intro t
                change (reached (read (r.unlinkFault s.step (Native.segmentPath root id / item)) (.ok ()) t)).activeEntry = t.activeEntry
                cases r.unlinkFault s.step (Native.segmentPath root id / item) with
                | none => rfl
                | some fault => cases fault <;> rfl
              · intro done
                cases done
                exact ih
          intro t
          have framed := loop names.toList t
          have eq := Array.foldlM_toList (m := M) (xs := names) (init := ())
            (f := fun _ (name : String) state =>
              read (r.unlinkFault s.step (Native.segmentPath root id / name)) (.ok ()) state)
          rw [eq] at framed
          exact framed
        · intro _ t
          simp only [↓reduceIte, ExceptT.run]
          exact namespace_framesEntry _ _ _

/-- A fault-free root does not require an empty retired directory. The
checked listing may contain any number of members. -/
structure HealthyRoot (r : RootReports) : Prop where
  sealedUnlock : ∀ step index, r.sealedUnlockError step index = false
  child : ∀ step index policy, (r.childValidation step index policy).Healthy policy
  read : ∀ step, r.controlRead step = none
  listing : ∀ step, r.listFault step = none
  barrier : ∀ step, r.sync step = .after none
  present : ∀ step id, r.presenceFault step id = none
  inspect : ∀ step id, ∃ names, r.members step id = .ok names
  unlink : ∀ step path, r.unlinkFault step path = none
  rmdir : ∀ step id, ∃ persist, r.rmdir step id = .after persist none

private theorem rootBind_ok {a : M α} {b : α → M β} {s t : State} {value : α}
    (ran : a.run s = .ok (.ok value) t) : (a >>= b).run s = (b value).run t := by
  simp only [ExceptT.run, Bind.bind, ExceptT.bind, ExceptT.mk, EStateM.bind] at ran ⊢
  rw [ran]
  rfl

private theorem rootRemove_healthy (root : FilePath) (r : RootReports)
    (healthy : HealthyRoot r) (id : Nat) (s : State) :
    ∃ t, (rootRemove root r id).run s = .ok (.ok ()) t := by
  obtain ⟨members, inspected⟩ := healthy.inspect s.step id
  obtain ⟨persist, removed⟩ := healthy.rmdir s.step id
  unfold rootRemove Native.removeSegmentWith rootPresent
  by_cases named : id ∈ s.disk.liveNames
  · simp only [ExceptT.run, Bind.bind, ExceptT.bind, ExceptT.bindCont, ExceptT.mk, EStateM.bind,
      healthy.present, healthy.unlink, inspected, removed, read, named, decide_true, ↓reduceIte]
    have loop (names : List String) (t : State) : ∃ after,
        (names.foldlM (m := M) (fun (_ : Unit) _ u => read none (.ok ()) u) ()).run t =
          .ok (.ok ()) after := by
      induction names generalizing t with
      | nil => exact ⟨t, rfl⟩
      | cons name tail ih =>
        change ∃ after, ((show M Unit from fun u => read none (.ok ()) u) >>= _).run t = _
        rw [rootBind_ok (show (ExceptT.run (show M Unit from fun u => read none (.ok ()) u) t) = _ from rfl)]
        exact ih t.tick
    have folded := Array.foldlM_toList (m := M) (xs := members) (init := ())
      (f := fun (_ : Unit) (_ : String) t => read none (.ok ()) t)
    obtain ⟨after, done⟩ := loop members.toList s.tick.tick
    rw [folded] at done
    simp only [ExceptT.run, read] at done
    unfold Array.forM
    rw [done]
    exact ⟨_, rfl⟩
  · simp only [ExceptT.run, Bind.bind, ExceptT.bind, ExceptT.bindCont, ExceptT.mk, EStateM.bind,
      healthy.present, read, named, decide_false, Bool.false_eq_true, ↓reduceIte]
    exact ⟨_, rfl⟩

theorem nativeRemove_healthy (root : FilePath) (r : RootReports)
    (reports : Nat → Nat → SingleFile.OpenReports) (healthy : HealthyRoot r) (id : Nat) (s : State) :
    ∃ after, ((nativeReopenOps root r reports).removeSegment id).run s = .ok (.ok ()) after :=
  rootRemove_healthy root r healthy id s

private theorem rootSync_healthy (root : FilePath) (r : RootReports)
    (healthy : HealthyRoot r) (s : State) :
    (rootSync root r).run s = .ok (.ok ()) {s.tick with disk := s.disk.syncRoot} := by
  change rootSync root r s = _
  unfold rootSync
  rw [(nativeRootBarrier root (r.sync s.step) s).1, healthy.barrier]
  rfl

private theorem collectNative_healthy (root : FilePath) (r : RootReports)
    (reports : Nat → Nat → SingleFile.OpenReports) (healthy : HealthyRoot r) (c : Control) (s : State) :
    ∃ t, (Segmented.collect (nativeReopenOps root r reports) c).run s = .ok (.ok ()) t := by
  let callbacks := nativeReopenOps root r reports
  have listed : callbacks.listSegments.run s = .ok (.ok s.disk.liveNames) s.tick := by
    change read (r.listFault s.step) (rootListing s.disk.liveNames) s = _
    rw [healthy.listing, rootListing_eq]
    rfl
  have remove (ids : List Nat) (t : State) :
      ∃ u, (Segmented.removeRetired callbacks c.firstNeeded ids).run t = .ok (.ok ()) u := by
    induction ids generalizing t with
    | nil => exact ⟨t, rfl⟩
    | cons id tail ih =>
      by_cases retired : id < c.firstNeeded
      · simp only [Segmented.removeRetired, retired, ↓reduceIte]
        obtain ⟨u, done⟩ := rootRemove_healthy root r healthy id t
        change (callbacks.removeSegment id).run t = _ at done
        rw [rootBind_ok done]
        exact ih u
      · simpa only [Segmented.removeRetired, retired, ↓reduceIte] using ih t
  unfold Segmented.collect
  rw [rootBind_ok listed]
  obtain ⟨u, done⟩ := remove s.disk.liveNames s.tick
  rw [rootBind_ok done]
  exact ⟨_, rootSync_healthy root r healthy u⟩

theorem nativeRootEffects (root : FilePath) (r : RootReports) (reports : Nat → Nat → SingleFile.OpenReports) :
    OpenRootEffects (nativeReopenOps root r reports) (HealthyRoot r) where
  collection := {
    list s := by
      change DiskPost _ _ (read (r.listFault s.step) (rootListing s.disk.liveNames) s)
      rw [rootListing_eq]
      cases r.listFault s.step with
      | none => exact ⟨fun _ h => h, rfl⟩
      | some fault => cases fault <;> rfl
    remove i s := nativeRemoveSegment root i (rootPresent r s i) (r.members s.step i)
      (r.unlinkFault s.step) (r.rmdir s.step i) s (by
        unfold rootPresent
        split <;> simp)
    sync s := by
      change DiskPost _ _ (rootSync root r s)
      unfold rootSync
      rw [(nativeRootBarrier root (r.sync s.step) s).1]
      apply barrierPost
      · exact .inl rfl
      · exact .inr rfl
      · rfl }
  control s c found := by
    change DiskPost _ _ (read (r.controlRead s.step) (rootControl root s.disk) s)
    cases cut : r.controlRead s.step with
    | none =>
      unfold rootControl
      simp only [found]
      split
      · rename_i fits
        rw [Native.readControl_canonical root c fits.1 fits.2.1 fits.2.2]
        exact ⟨rfl, rfl⟩
      · rfl
    | some fault => cases fault <;> rfl
  syncHealthy s healthy := ⟨_, rootSync_healthy root r healthy s⟩
  collectHealthy c s healthy := collectNative_healthy root r reports healthy c s

private theorem nativeValidatedChildEffects (root : FilePath) (r : RootReports)
    (reports : Nat → Nat → SingleFile.OpenReports) :
    OpenChildEffects (nativeReopenOps root r reports).openSegment
      ((HealthyChildren reports ∧ ∀ p i s, childValidation root r p i s = .ok ()) ∧
        ∀ index s, sealedFault r index s = false) :=
  by
    have eq : (nativeReopenOps root r reports).openSegment =
        fun policy index => sealedCloseResult (sealedFault r index)
          (validatedChild (childValidation root r policy index) (nativeOpenChild root reports policy index)) := by
      funext policy index
      exact nativeChildRead_eq root r reports policy index
    rw [eq]
    exact sealedCloseEffects (sealedFault r)
      (validatedChildEffects (childValidation root r) (nativeOpenChild_effects root reports))

theorem reopen_nativeRoot {known request} (root : FilePath) (r : RootReports)
    (reports : Nat → Nat → SingleFile.OpenReports) (s : State) (prior : Recoverable known request s.disk) :
    DiskPost (fun session after => Installed session after ∧ PermittedView known request session.view)
      (Recoverable known request) ((Segmented.reopen (nativeReopenOps root r reports)).run s) := by
  exact reopenWithEffects_refines (nativeRootEffects root r reports)
    (nativeValidatedChildEffects root r reports) s prior

/-- Progress assumes the actual primitive reports are healthy and the
protected CONTROL binding is representable in its on-disk codec. -/
theorem reopen_nativeHealthy (root : FilePath) (r : RootReports)
    (reports : Nat → Nat → SingleFile.OpenReports) (s : State)
    (prior : Recoverable known request s.disk) (rootOK : HealthyRoot r)
    (childrenOK : HealthyChildren reports)
    (representable : ∀ c, s.disk.liveControl = some c →
      c.capacity ≤ 255 ∧ c.active ≤ ControlCodec.wordMax ∧ c.discarded ≤ ControlCodec.wordMax) :
    ∃ next after, (Segmented.reopen (nativeReopenOps root r reports)).run s = .ok (.ok next) after := by
  apply reopenWithEffects_healthy (nativeRootEffects root r reports)
    (nativeValidatedChildEffects root r reports) s prior rootOK
      ⟨⟨childrenOK, fun p i t => validateChildModel_healthy root p i _ (rootOK.child t.step i p)⟩,
        fun i t => by simp [sealedFault, rootOK.sealedUnlock]⟩
  obtain ⟨c, found, _⟩ := prior.live
  refine ⟨c, ?_⟩
  change returned (read (r.controlRead s.step) (rootControl root s.disk) s) = _
  rw [rootOK.read]
  have fits := representable c found
  simp only [rootControl, found, fits]
  rw [Native.readControl_canonical root c fits.1 fits.2.1 fits.2.2]
  rfl

/-- Directory and lock identities are separate open descriptions under the
same resolved root. Their binding is supplied by the Linux primitives. -/
structure RootBinding (directory lock : Type) where
  root : FilePath
  directoryHandle : directory
  lockHandle : lock

/-- Model the acquisition primitives by their results. Reference allocation
is BaseIO and the installed value carries the exact acquired binding. -/
def nativeAcquireBinding
    (resolve : FilePath → Except String FilePath)
    (openDirectory : FilePath → IO.FS.Mode → Except String directory)
    (lockRoot : FilePath → Except String lock) (dir : FilePath) :
    Except String (RootBinding directory lock) :=
  Native.acquireStoreWith resolve openDirectory lockRoot
    (fun root directoryHandle lockHandle => .ok ⟨root, directoryHandle, lockHandle⟩) dir

theorem nativeAcquireBinding_ok
    (resolve : FilePath → Except String FilePath)
    (openDirectory : FilePath → IO.FS.Mode → Except String directory)
    (lockRoot : FilePath → Except String lock) (dir root : FilePath)
    (resolved : resolve dir = .ok root)
    (opened : openDirectory root .read = .ok directoryHandle)
    (locked : lockRoot root = .ok lockHandle) :
    nativeAcquireBinding resolve openDirectory lockRoot dir =
      .ok ⟨root, directoryHandle, lockHandle⟩ := by
  unfold nativeAcquireBinding
  rw [Native.acquireStore_bind]
  simp [Bind.bind, Except.bind, resolved, opened, locked]

private def scanActiveModel (index : Nat) (ready : ReadyChild) : M (List Bytes) := fun s =>
  match (SingleFile.scanWith (SingleFile.storedPhase ready) : SingleFile.OpenM _).run
      {image := s.disk.segment index, held := true} with
  | .ok response _ => .ok response s
  | .error token _ => .error token s

private theorem scanActiveModel_eq (index : Nat) (ready : ReadyChild)
    (phase : ready.phase = .active ready.lock (SingleFile.appendFiles ready.writer ready.reader ready.markers)
      ready.recovered.cursor ready.recovered.batches) :
    scanActiveModel index ready = pure ready.recovered.batches := by
  funext s
  unfold scanActiveModel
  rw [SingleFile.scan_opened ready _ phase]
  rfl

private theorem acquireActive_scanPhase (root : FilePath) (r : RootReports)
    (reports : Nat → Nat → SingleFile.OpenReports) (policy : Policy) (index : Nat)
    (s : State) (opened : acquireChildModel root r reports policy index s = .ok (.ok ready) after) :
    ready.lock = .lock ∧
    ready.phase = .active ready.lock (SingleFile.appendFiles ready.writer ready.reader ready.markers)
      ready.recovered.cursor ready.recovered.batches := by
  unfold acquireChildModel validatedChild at opened
  cases validation : childValidation root r policy index s with
  | error => rw [validation] at opened; cases opened
  | ok value =>
    cases value
    rw [validation] at opened
    simp only [ExceptT.run] at opened
    unfold child at opened
    split at opened
    · simp only [ExceptT.run, nativeChildWorker] at opened
      cases ran : SingleFile.openExistingModel (Native.segmentPath root index) policy (reports s.step index)
          {image := s.disk.segment index} with
      | error => rw [ran] at opened; cases opened
      | ok response _ =>
        rw [ran] at opened
        cases response with
        | error => cases opened
        | ok child =>
          cases opened
          exact SingleFile.openExisting_scanPhase _ _ _ _ rfl ran
    · cases opened

/-- The disk projection of releasing a single-file handle keeps its reached
image. The report records a returned close error, if any. -/
private def closeChildResult (index : Nat) (err : Option String) (ready : ReadyChild) (s : State) :=
  SingleFile.closeModel ready.policy {unlockError := err.isSome}
    (SingleFile.storedPhase ready) {image := s.disk.segment index, held := true}

private def projectedChildClose (index : Nat) (err : Option String) (ready : ReadyChild) :
    M Unit := fun s =>
  match closeChildResult index err ready s with
  | .ok response _ => .ok response s
  | .error token _ => .error token s

private theorem projectedChildClose_frame (index : Nat) (err : Option String)
    (ready : ReadyChild) (s : State) :
    ∃ response, projectedChildClose index err ready s = .ok response s := by
  obtain ⟨response, after, close, _⟩ :=
    SingleFile.closeModel_frames ready.policy {unlockError := err.isSome}
      (SingleFile.storedPhase ready) {image := s.disk.segment index, held := true}
  unfold projectedChildClose closeChildResult
  rw [close]
  exact ⟨response, rfl⟩

/-- For an acquired child, the projected close has no residual lock or
file effect, including when unlock reports an error. -/
private theorem projectedChildClose_acquired (index : Nat) (err : Option String)
    (ready : ReadyChild) (s : State) (lock : ready.lock = .lock)
    (phase : ready.phase = .active ready.lock (SingleFile.appendFiles ready.writer ready.reader ready.markers)
      ready.recovered.cursor ready.recovered.batches) :
    let closed := closeChildResult index err ready s
    (SingleFile.postState closed).held = false ∧ (SingleFile.postState closed).closed = true ∧
      projectedChildClose index err ready s =
      .ok (if err.isSome then .error "primitive error" else .ok ()) s := by
  have closed := SingleFile.close_opened ready.policy {unlockError := err.isSome} ready lock
    {image := s.disk.segment index, held := true} phase
  have report := SingleFile.close_opened_report ready {unlockError := err.isSome}
    {image := s.disk.segment index, held := true} lock phase
  refine ⟨closed.2.1, closed.1, ?_⟩
  unfold projectedChildClose closeChildResult
  rw [report]

private def resumeActive (ops : Ops M) (c : Control) (sealed : Array Bytes)
    (ready : ReadyChild) : M (Session × ReadyChild) := do
  let batches ← scanActiveModel c.active ready
  let session ← Segmented.finishReopen ops c sealed batches
  pure (session, ready)

private def reopenScopedModel (root : FilePath) (r : RootReports)
    (reports : Nat → Nat → SingleFile.OpenReports) (closeError : Option String) :
    M (Session × ReadyChild) :=
  Segmented.reopenWith (nativeReopenOps root r reports)
    (fun policy index resume =>
      Native.withActiveChild (error := String) (acquireChildModel root r reports policy index)
        (projectedChildClose index closeError) fun ready => do resume ready (← scanActiveModel index ready))
    (fun session ready => pure (session, ready))

/-- If the scoped continuation reports failure after acquisition, it returns
that error at the close's reached state with the acquired handle closed and
its lock released. Prefix failure issues no active child. A failed single-file
open releases its own lock, and process stop drops process-owned resources. -/
def ScopedFailureReleased (root : FilePath) (r : RootReports)
    (reports : Nat → Nat → SingleFile.OpenReports) (closeError : Option String)
    (start after : State) (err : String) : Prop :=
  let ops := nativeReopenOps root r reports
  match (Segmented.reopenPrefix ops).run start with
  | .ok (.ok (c, sealed)) before =>
    ∀ ready acquired,
      acquireChildModel root r reports c.policy c.active before = .ok (.ok ready) acquired →
      (resumeActive ops c sealed ready).run acquired = .ok (.error err) after ∧
      (SingleFile.postState (closeChildResult c.active closeError ready after)).held = false ∧
      (SingleFile.postState (closeChildResult c.active closeError ready after)).closed = true
  | _ => True

private theorem reopenScoped_failureReleased (root : FilePath) (r : RootReports)
    (reports : Nat → Nat → SingleFile.OpenReports) (closeError : Option String)
    {start after : State} {err : String}
    (failed : (reopenScopedModel root r reports closeError).run start = .ok (.error err) after) :
    ScopedFailureReleased root r reports closeError start after err := by
  unfold ScopedFailureReleased
  let ops := nativeReopenOps root r reports
  change (match (Segmented.reopenPrefix ops).run start with
    | .ok (.ok (c, sealed)) before => _
    | _ => _)
  unfold reopenScopedModel Segmented.reopenWith at failed
  simp only [Bind.bind, ExceptT.bind, ExceptT.mk, ExceptT.run, EStateM.bind] at failed
  simp only [ExceptT.run]
  cases prefixed : (Segmented.reopenPrefix ops) start with
  | error => trivial
  | ok selection before =>
    cases selection with
    | error => trivial
    | ok pair =>
      obtain ⟨c, sealed⟩ := pair
      intro ready acquired opened
      rw [prefixed] at failed
      change (Native.withActiveChild (error := String)
        (ExceptT.mk (acquireChildModel root r reports c.policy c.active).run)
        (projectedChildClose c.active closeError) (resumeActive ops c sealed)).run before =
          .ok (.error err) after at failed
      rw [Native.withActiveChild_reached] at failed
      simp only [ExceptT.run] at failed
      rw [opened] at failed
      dsimp only at failed
      cases resumed : (resumeActive ops c sealed ready) acquired with
      | error => rw [resumed] at failed; cases failed
      | ok response reached =>
        rw [resumed] at failed
        cases response with
        | ok => cases failed
        | error primary =>
          have ⟨lock, phase⟩ := acquireActive_scanPhase root r reports c.policy c.active before opened
          obtain ⟨unlocked, shut, closed⟩ :=
            projectedChildClose_acquired c.active closeError ready reached lock phase
          simp only [closed] at failed
          cases closeError <;> cases failed <;> exact ⟨rfl, unlocked, shut⟩

/-- Erasing the returned child gives exactly the original disk run. A
reported close failure retains both the reached disk and the primary error. -/
private theorem reopenScopedModel_project (root : FilePath) (r : RootReports)
    (reports : Nat → Nat → SingleFile.OpenReports) (closeError : Option String)
    (start : State) (prior : Recoverable known request start.disk) :
    ((reopenScopedModel root r reports closeError >>= fun value => pure value.1).run start) =
      (Segmented.reopen (nativeReopenOps root r reports)).run start := by
  let ops := nativeReopenOps root r reports
  have afterPrefix (c : Control) (sealed : Array Bytes) (s : State)
      (live : s.disk.liveControl = some c) :
      ((Native.withActiveChild (error := String) (acquireChildModel root r reports c.policy c.active)
        (projectedChildClose c.active closeError) (fun ready => do
          let batches ← scanActiveModel c.active ready
          let session ← Segmented.finishReopen ops c sealed batches
          pure (session, ready)) >>= fun value => pure value.1).run s) =
        ((ops.openSegment c.policy c.active >>= Segmented.finishReopen ops c sealed).run s) := by
    let acquire := acquireChildModel root r reports c.policy c.active
    have project := acquireChildModel_project root r reports c.policy c.active
    have same :
        ((ops.openSegment c.policy c.active >>= Segmented.finishReopen ops c sealed).run s) =
          (((acquire >>= fun ready => pure ready.recovered.batches) >>=
            Segmented.finishReopen ops c sealed).run s) := by
      simp only [Bind.bind, ExceptT.bind, ExceptT.run, ExceptT.mk, EStateM.bind]
      have openEq : ops.openSegment c.policy c.active s =
          (acquire >>= fun ready => pure ready.recovered.batches) s := by
        rw [project]
        simp only [ops, nativeReopenOps, nativeChildRead_eq, sealedCloseResult, sealedFault, sealedSelection, live, Nat.lt_irrefl,
          ExceptT.run]
        cases validatedChild (childValidation root r c.policy c.active)
            (nativeOpenChild root reports c.policy c.active) s with
        | error => rfl
        | ok response _ => cases response <;> rfl
      rw [openEq]; rfl
    rw [same]
    let finish := Segmented.finishReopen (nativeReopenOps root r reports) c sealed
    let resume (ready : ReadyChild) : M (Session × ReadyChild) := do
      let batches ← scanActiveModel c.active ready
      let session ← finish batches
      pure (session, ready)
    change ((Native.withActiveChild (error := String) acquire (projectedChildClose c.active closeError) resume >>=
      fun value => pure value.1).run s) = ((acquire >>= fun ready => pure ready.recovered.batches) >>= finish).run s
    have scopeResult := Native.withActiveChild_reached acquire.run (projectedChildClose c.active closeError) resume s
    simp only [Bind.bind, ExceptT.run, ExceptT.bind, ExceptT.mk, EStateM.bind] at scopeResult ⊢
    rw [scopeResult]
    cases opened : acquire s with
    | error => rfl
    | ok response afterOpen =>
      cases response with
      | error => rfl
      | ok ready =>
        have resumed :
            resume ready afterOpen =
              match finish ready.recovered.batches afterOpen with
              | .ok (.ok session) t => .ok (.ok (session, ready)) t
              | .ok (.error err) t => .ok (.error err) t
              | .error token t => .error token t := by
          have phase := (acquireActive_scanPhase root r reports c.policy c.active s opened).2
          simp only [resume, scanActiveModel_eq c.active ready phase, pure_bind]
          simp only [Bind.bind, ExceptT.bind, ExceptT.mk, EStateM.bind]
          cases finish ready.recovered.batches afterOpen with
          | error => rfl
          | ok result _ => cases result <;> rfl
        dsimp only
        rw [resumed]
        simp only [ExceptT.bindCont, Pure.pure, ExceptT.pure, ExceptT.mk, EStateM.pure]
        cases finish ready.recovered.batches afterOpen with
        | error => rfl
        | ok result reached =>
          cases result with
          | ok => rfl
          | error =>
            obtain ⟨response, closed⟩ := projectedChildClose_frame c.active closeError ready reached
            dsimp only
            rw [closed]
            cases response with
            | error => rfl
            | ok value => cases value; rfl

  simp only [reopenScopedModel, Segmented.reopenWith, Segmented.reopen, bind_assoc, bind_pure]
  simp only [Bind.bind, ExceptT.bind, ExceptT.run, ExceptT.mk, EStateM.bind]
  cases selected : Segmented.reopenPrefix ops start with
  | error => rfl
  | ok selection before =>
    cases selection with
    | error => rfl
    | ok pair =>
      obtain ⟨c, sealed⟩ := pair
      have prefixResult : (Segmented.reopenPrefix ops).run start = .ok (.ok (c, sealed)) before := selected
      have live := (reopenPrefix_active (nativeRootEffects root r reports)
        (nativeValidatedChildEffects root r reports) prior prefixResult).1
      have eq := afterPrefix c sealed before live
      simp only [Bind.bind, ExceptT.bind, ExceptT.run, ExceptT.mk, EStateM.bind] at eq
      exact eq

/-- Disk correctness of the complete schedule with the retained child.
The postcondition uses the state of that run, including its cleanup branch. -/
theorem reopenScopedModel_refines (root : FilePath) (r : RootReports)
    (reports : Nat → Nat → SingleFile.OpenReports) (closeError : Option String)
    (s : State) (prior : Recoverable known request s.disk) :
    DiskPost (fun result disk => Installed result.1 disk ∧ PermittedView known request result.1.view)
      (Recoverable known request) ((reopenScopedModel root r reports closeError).run s) := by
  have facts := reopen_nativeRoot root r reports s prior
  rw [← reopenScopedModel_project root r reports closeError s prior] at facts
  simp only [Bind.bind, ExceptT.bind, ExceptT.run, ExceptT.mk, EStateM.bind] at facts
  cases ran : (reopenScopedModel root r reports closeError).run s with
  | error =>
    simp only [ExceptT.run] at ran
    rw [ran] at facts
    exact facts
  | ok result after =>
    simp only [ExceptT.run] at ran
    rw [ran] at facts
    cases result <;> exact facts

theorem reopenScopedModel_healthy (root : FilePath) (r : RootReports)
    (reports : Nat → Nat → SingleFile.OpenReports) (closeError : Option String)
    (s : State) (prior : Recoverable known request s.disk)
    (rootOK : HealthyRoot r) (childrenOK : HealthyChildren reports)
    (representable : ∀ c, s.disk.liveControl = some c →
      c.capacity ≤ 255 ∧ c.active ≤ ControlCodec.wordMax ∧ c.discarded ≤ ControlCodec.wordMax) :
    ∃ session ready after, (reopenScopedModel root r reports closeError).run s =
      .ok (.ok (session, ready)) after := by
  obtain ⟨next, after, result⟩ := reopen_nativeHealthy root r reports s prior rootOK childrenOK representable
  rw [← reopenScopedModel_project root r reports closeError s prior] at result
  simp only [Bind.bind, ExceptT.bind, ExceptT.run, ExceptT.mk, EStateM.bind] at result
  cases ran : (reopenScopedModel root r reports closeError).run s with
  | error => simp only [ExceptT.run] at ran; rw [ran] at result; cases result
  | ok response _ =>
    simp only [ExceptT.run] at ran
    rw [ran] at result
    cases response with
    | error => cases result
    | ok pair => exact ⟨pair.1, pair.2, _, rfl⟩

private theorem finishReopen_frame {callbacks : Ops M} (effects : CollectionEffects callbacks)
    {c : Control} {sealed : Array Bytes} {active : List Bytes}
    {s t : State} {session : Session}
    (ran : (Segmented.finishReopen callbacks c sealed active).run s = .ok (.ok session) t) :
    session.control = c ∧ t.disk.segment = s.disk.segment := by
  unfold Segmented.finishReopen at ran
  by_cases oversized : active.length > c.capacity
  · simp only [oversized, ↓reduceIte] at ran
    cases ran
  by_cases release : c.discarded > c.active * c.capacity + active.length
  · simp only [oversized, release, ↓reduceIte] at ran
    cases ran
  · simp only [oversized, release, ↓reduceIte, Bind.bind, ExceptT.bind, ExceptT.run,
      ExceptT.mk, EStateM.bind] at ran
    have facts := collectWith_cases effects c s
    simp only [ExceptT.run] at facts
    cases collected : (Segmented.collect callbacks c) s with
    | error => rw [collected] at ran; cases ran
    | ok response reached =>
      rw [collected] at facts ran
      cases response with
      | error => cases ran
      | ok unitValue =>
        cases unitValue
        cases ran
        exact ⟨rfl, facts.1.segment⟩

private theorem reopenScopedModel_delivered (root : FilePath) (r : RootReports)
    (reports : Nat → Nat → SingleFile.OpenReports) (closeError : Option String)
    {s t : State} {session : Session} {ready : ReadyChild}
    (ran : (reopenScopedModel root r reports closeError).run s = .ok (.ok (session, ready)) t) :
    ∃ before sealed childAfter,
      (Segmented.reopenPrefix (nativeReopenOps root r reports)).run s =
        .ok (.ok (session.control, sealed)) before ∧
      SingleFile.openExistingModel (Native.segmentPath root session.control.active) session.control.policy
        (reports before.step session.control.active) {image := before.disk.segment session.control.active} =
          .ok (.ok ready) childAfter ∧
      t.disk.segment session.control.active = childAfter.image := by
  let callbacks := nativeReopenOps root r reports
  unfold reopenScopedModel Segmented.reopenWith at ran
  simp only [Bind.bind, ExceptT.bind, ExceptT.mk, ExceptT.run, EStateM.bind] at ran
  cases selected : (Segmented.reopenPrefix callbacks) s with
  | error => rw [selected] at ran; cases ran
  | ok selection before =>
    rw [selected] at ran
    cases selection with
    | error => cases ran
    | ok selection =>
      obtain ⟨c, sealed⟩ := selection
      let acquire := acquireChildModel root r reports c.policy c.active
      let resume (handle : ReadyChild) : M (Session × ReadyChild) := do
        let batches ← scanActiveModel c.active handle
        let session ← Segmented.finishReopen callbacks c sealed batches
        pure (session, handle)
      change (Native.withActiveChild (error := String) (ExceptT.mk acquire.run) (projectedChildClose c.active closeError) resume).run before =
        .ok (.ok (session, ready)) t at ran
      have scopedResult := Native.withActiveChild_reached acquire.run (projectedChildClose c.active closeError) resume before
      rw [scopedResult] at ran
      simp only [ExceptT.run] at ran
      cases validation : childValidation root r c.policy c.active before with
      | error => simp [acquire, acquireChildModel, validatedChild, validation] at ran
      | ok value =>
        cases value
        by_cases named : c.active ∈ before.disk.liveNames
        · simp only [acquire, acquireChildModel, validatedChild, validation, child, named, ↓reduceIte, ExceptT.run, nativeChildWorker] at ran
          cases single : SingleFile.openExistingModel (Native.segmentPath root c.active) c.policy
              (reports before.step c.active) {image := before.disk.segment c.active} with
          | error => rw [single] at ran; cases ran
          | ok response childAfter =>
            rw [single] at ran
            cases response with
            | error => cases ran
            | ok handle =>
              let opened : State := {before.tick with
                disk := before.disk.setSegment c.active childAfter.image handle.recovered.cursor}
              dsimp only at ran
              have phase := (SingleFile.openExisting_scanPhase _ _ _ _ rfl single).2
              simp only [resume, id_eq, scanActiveModel_eq c.active handle phase, pure_bind] at ran
              simp only [Bind.bind, ExceptT.bind, ExceptT.mk, EStateM.bind] at ran
              cases finished : (Segmented.finishReopen callbacks c sealed handle.recovered.batches) opened with
              | error => simp only [opened] at finished; rw [finished] at ran; cases ran
              | ok response reached =>
                simp only [opened] at finished
                rw [finished] at ran
                cases response with
                | error =>
                  obtain ⟨response, closed⟩ := projectedChildClose_frame c.active closeError handle reached
                  simp only [ExceptT.bindCont, Pure.pure, EStateM.pure] at ran
                  rw [closed] at ran
                  cases response with
                  | error => cases ran
                  | ok value => cases value; cases ran
                | ok next =>
                  cases ran
                  obtain ⟨control, frame⟩ := finishReopen_frame (nativeRootEffects root r reports).collection finished
                  rw [control]
                  exact ⟨before, sealed, childAfter, selected, single,
                    (congrFun frame c.active).trans (Disk.setSegment_here ..)⟩
        · simp only [acquire, acquireChildModel, validatedChild, validation, ExceptT.run, child, named, ↓reduceIte] at ran
          cases ran

/-- Append consumes the returned child phase and the segment image on the
same disk that the complete reopen schedule left after collection. -/
private theorem appendAfterScopedReopen (root : FilePath) (r : RootReports)
    (openReports : Nat → Nat → SingleFile.OpenReports) (closeError : Option String)
    {s t : State} (prior : Recoverable known request s.disk) {session : Session} {ready : ReadyChild}
    (transferred : (reopenScopedModel root r openReports closeError).run s =
      .ok (.ok (session, ready)) t)
    (reports : ∀ cursor, SingleFile.AppendReports session.control.policy cursor batch)
    (room : ready.recovered.batches.length < 255) (size : batch.length ≤ 32) :
    let old := ready.recovered.batches
    let result := SingleFile.appendModel reports
      ⟨t.disk.segment session.control.active, SingleFile.storedPhase ready⟩
    Installed session t.disk ∧ PermittedView known request session.view ∧
    Child.Recoverable session.control.policy old (some batch) (SingleFile.appendReached result).image ∧
    SingleFile.AppendGuarantee session.control.policy old batch result := by
  obtain ⟨before, sealed, childAfter, prefixResult, opened, image⟩ :=
    reopenScopedModel_delivered root r openReports closeError transferred
  obtain ⟨_, _, _, _, childPrior⟩ := reopenPrefix_active (nativeRootEffects root r openReports)
    (nativeValidatedChildEffects root r openReports) prior prefixResult
  have disk := reopenScopedModel_refines root r openReports closeError s prior
  rw [transferred] at disk
  have append := childPrior.nativeAppendAfterOpen _ _ _ rfl opened reports room size
  dsimp only
  rw [image]
  exact ⟨disk.1, disk.2, append.1, append.2.1⟩

/-- Projection of the acquired root and the active reference in its store.
The reference setter is BaseIO in the native adapter. -/
structure ReopenedStore (directory lock : Type) where
  binding : RootBinding directory lock
  activeId : Nat
  activeChild : ReadyChild

def installScopedModel (owned : RootBinding directory lock) (r : RootReports)
    (reports : Nat → Nat → SingleFile.OpenReports) (closeError : Option String) :
    M (Native.Phase (ReopenedStore directory lock)) :=
  Native.installReopenedWith (reopenScopedModel owned.root r reports closeError)
    (fun entry => match entry with
      | some (index, ready) => fun s => .ok (.ok ⟨owned, index, ready⟩) {s with activeEntry := some index}
      | none => throw "missing active child")

private theorem installScopedModel_run (owned : RootBinding directory lock) (r : RootReports)
    (reports : Nat → Nat → SingleFile.OpenReports) (closeError : Option String) (s : State) :
    (installScopedModel owned r reports closeError).run s =
      match (reopenScopedModel owned.root r reports closeError).run s with
      | .ok (.ok (session, ready)) after =>
        .ok (.ok (.ready ⟨owned, session.control.active, ready⟩ session))
          {after with activeEntry := some session.control.active}
      | .ok (.error err) after => .ok (.error err) after
      | .error token after => .error token after := by
  simp only [installScopedModel, Native.installReopenedWith, Bind.bind, ExceptT.bind,
    ExceptT.run, ExceptT.mk, EStateM.bind]
  cases (reopenScopedModel owned.root r reports closeError) s with
  | error => rfl
  | ok response _ =>
    cases response with
    | error => rfl
    | ok pair => cases pair; rfl

theorem installScopedModel_registered
    (ran : (installScopedModel owned r reports closeError).run before =
      .ok (.ok (.ready store session)) after) :
    after.activeEntry = some store.activeId := by
  rw [installScopedModel_run] at ran
  split at ran <;> cases ran
  rfl

/-- The exact phase issued by the child producer is positioned after the
active suffix of the installed segmented history. -/
theorem installScopedModel_appendPhase (owned : RootBinding directory lock) (r : RootReports)
    (openReports : Nat → Nat → SingleFile.OpenReports) (closeError : Option String)
    {s t : State} (prior : Recoverable known request s.disk) {session : Session}
    {store : ReopenedStore directory lock}
    (installed : (installScopedModel owned r openReports closeError).run s =
      .ok (.ok (.ready store session)) t) :
    ∃ history, session = sessionOf session.control history ∧
      ReadyLayout session.control history t.disk ∧ t.disk.liveControl = some session.control ∧
      t.disk.durableControl = some session.control ∧ store.binding = owned ∧
      store.activeId = session.control.active ∧
      SingleFile.storedPhase store.activeChild =
        .active .lock (SingleFile.appendBindings session.control.policy)
          (t.disk.cursor store.activeId) (segmentHistory session.control.capacity store.activeId history) ∧
      store.activeChild.recovered.batches = segmentHistory session.control.capacity store.activeId history := by
  rw [installScopedModel_run] at installed
  cases ran : (reopenScopedModel owned.root r openReports closeError).run s with
  | error => rw [ran] at installed; cases installed
  | ok response after =>
    rw [ran] at installed
    cases response with
    | error => cases installed
    | ok pair =>
      obtain ⟨next, ready⟩ := pair
      cases installed
      obtain ⟨before, sealed, childAfter, prefixResult, opened, image⟩ :=
        reopenScopedModel_delivered owned.root r openReports closeError ran
      obtain ⟨_, _, _, _, childPrior⟩ := reopenPrefix_active (nativeRootEffects owned.root r openReports)
        (nativeValidatedChildEffects owned.root r openReports) prior prefixResult
      have child := SingleFile.openExisting_refines (Native.segmentPath owned.root session.control.active) session.control.policy (openReports before.step session.control.active)
        {image := before.disk.segment session.control.active} rfl childPrior.dirty childPrior.markers
      rw [opened] at child
      have phase := SingleFile.openedAppendPhase child
      obtain ⟨_, _, _, _, _, _, _, _, permitted, _, childReady, _, _⟩ := child.2.2
      have bounds : ∀ b ∈ ready.recovered.batches, b.length ≤ 32 := by
        intro b mem
        apply childPrior.dirty.bounded b
        rcases permitted with same | same
        · exact List.mem_append_left _ (same ▸ mem)
        · exact same ▸ mem
      have fits : ready.recovered.batches.length ≤ 255 := by
        rcases permitted with same | same
        · rw [same]
          have := childPrior.dirty.fits
          simp only [List.length_append] at this
          omega
        · rw [same]
          exact childPrior.dirty.fits
      have disk := reopenScopedModel_refines owned.root r openReports closeError s prior
      rw [ran] at disk
      obtain ⟨history, shape, layout, live, durable⟩ := disk.1
      let suffix := segmentHistory session.control.capacity session.control.active history
      have suffixFits : suffix.length ≤ 255 := by
        dsimp only [suffix]
        rw [segmentHistory_active_length layout.layout.upper]
        have high := layout.layout.upper
        have cap := layout.layout.capacityFits
        rw [Nat.add_mul, Nat.one_mul] at high
        omega
      have other := (Persistence.ready_powerLoss_reopen layout.active.ready
        (segmentHistory_bounded layout.layout session.control.active) suffixFits).1
      have issued := (Persistence.ready_powerLoss_reopen childReady bounds fits).1
      dsimp only at other issued
      rw [image, issued] at other
      have same : ready.recovered.batches = suffix := by
        injection other with result
        exact congrArg Decoded.batches (Except.ok.inj result)
      refine ⟨history, shape, layout, live, durable, rfl, rfl, ?_, same⟩
      simp only [phase, same, layout.active.position, suffix]

/-- The append consumer uses the active reference installed by the same
schedule that produced the public session. -/
theorem nativeAppendAfterTransfer (owned : RootBinding directory lock) (r : RootReports)
    (openReports : Nat → Nat → SingleFile.OpenReports) (closeError : Option String)
    {s t : State} (prior : Recoverable known request s.disk) {session : Session}
    {store : ReopenedStore directory lock}
    (installed : (installScopedModel owned r openReports closeError).run s =
      .ok (.ok (.ready store session)) t)
    (reports : ∀ cursor, SingleFile.AppendReports session.control.policy cursor batch)
    (room : store.activeChild.recovered.batches.length < 255) (size : batch.length ≤ 32) :
    let old := store.activeChild.recovered.batches
    let result := SingleFile.appendModel reports
      ⟨t.disk.segment store.activeId, SingleFile.storedPhase store.activeChild⟩
    store.binding = owned ∧ store.activeId = session.control.active ∧
    Installed session t.disk ∧ PermittedView known request session.view ∧
    Child.Recoverable session.control.policy old (some batch) (SingleFile.appendReached result).image ∧
    SingleFile.AppendGuarantee session.control.policy old batch result := by
  rw [installScopedModel_run] at installed
  cases ran : (reopenScopedModel owned.root r openReports closeError).run s with
  | error => rw [ran] at installed; cases installed
  | ok response after =>
    rw [ran] at installed
    cases response with
    | error => cases installed
    | ok pair =>
      obtain ⟨next, ready⟩ := pair
      cases installed
      exact ⟨rfl, rfl, appendAfterScopedReopen owned.root r openReports closeError prior ran reports room size⟩

theorem installScopedModel_healthy (owned : RootBinding directory lock) (r : RootReports)
    (reports : Nat → Nat → SingleFile.OpenReports) (closeError : Option String)
    (s : State) (prior : Recoverable known request s.disk)
    (rootOK : HealthyRoot r) (childrenOK : HealthyChildren reports)
    (representable : ∀ c, s.disk.liveControl = some c →
      c.capacity ≤ 255 ∧ c.active ≤ ControlCodec.wordMax ∧ c.discarded ≤ ControlCodec.wordMax) :
    ∃ session ready after, (installScopedModel owned r reports closeError).run s =
      .ok (.ok (.ready ⟨owned, session.control.active, ready⟩ session)) after := by
  obtain ⟨session, ready, after, ran⟩ :=
    reopenScopedModel_healthy owned.root r reports closeError s prior rootOK childrenOK representable
  exact ⟨session, ready, _, by rw [installScopedModel_run, ran]⟩

/-- Only the root lock is live outside the scoped recovery. On success the
active child moves into the ready store. On failure the child scope has
already released it before the outer store tries root unlock. -/
def publicOpenModel (binding : Except String (RootBinding directory lock)) (r : RootReports)
    (reports : Nat → Nat → SingleFile.OpenReports) (childCloseError rootUnlockError : Option String) :
    ExceptT String (EStateM Unit (State × Bool)) (Native.Phase (ReopenedStore directory lock) × Unit) :=
  Native.openWithStore (error := String)
    (fun state => .ok binding (state.1, binding.isOk))
    (fun owned state =>
      match (installScopedModel owned r reports childCloseError).run state.1 with
      | .ok response after => .ok response (after, state.2)
      | .error token after => .error token (after, false))
    pure (pure ())
    (fun _ => Native.releaseWith (error := String) (pure ())
      (fun state => .ok (rootUnlockError.elim (.ok ()) .error) (state.1, false)))

/-- Acquisition, installation and outer release use the same reached disk.
The last reference to the root descriptor drops on a reported unlock error.
An interruption drops process-owned resources. -/
theorem publicOpenModel_run (binding : Except String (RootBinding directory lock)) (r : RootReports)
    (reports : Nat → Nat → SingleFile.OpenReports) (childCloseError rootUnlockError : Option String)
    (s : State) :
    (publicOpenModel binding r reports childCloseError rootUnlockError).run (s, false) =
      match binding with
      | .error err => .ok (.error err) (s, false)
      | .ok owned =>
        match (installScopedModel owned r reports childCloseError).run s with
        | .ok (.ok phase) after => .ok (.ok (phase, ())) (after, true)
        | .ok (.error err) after => .ok (.error err) (after, false)
        | .error token after => .error token (after, false) := by
  unfold publicOpenModel
  simp only [Native.openWithStore, Native.installPhaseWith, Native.cleanupOnError, Native.releaseWith,
    tryCatchThe, MonadExceptOf.tryCatch, ExceptT.tryCatch, Bind.bind, ExceptT.bind, ExceptT.mk,
    ExceptT.run, EStateM.bind]
  cases binding with
  | error => rfl
  | ok owned =>
    simp only [ExceptT.bindCont, EStateM.bind, Except.isOk]
    cases ran : (installScopedModel owned r reports childCloseError).run s with
    | error => simp only [ExceptT.run] at ran; rw [ran]
    | ok response _ =>
      simp only [ExceptT.run] at ran
      rw [ran]
      cases response with
      | ok => rfl
      | error => cases rootUnlockError <;> rfl

theorem publicOpenModel_refines (binding : Except String (RootBinding directory lock)) (r : RootReports)
    (reports : Nat → Nat → SingleFile.OpenReports) (childCloseError rootUnlockError : Option String)
    (s : State) (prior : Recoverable known request s.disk) :
    match (publicOpenModel binding r reports childCloseError rootUnlockError).run (s, false) with
    | .ok (.ok (.ready store session, ())) (after, held) =>
      binding = .ok store.binding ∧ held = true ∧ store.activeId = session.control.active ∧
      Installed session after.disk ∧ PermittedView known request session.view ∧
      Native.scanWith (m := Except String) (.ready store session) = .ok session.view
    | .ok (.ok _) _ => False
    | .ok (.error err) (after, held) =>
      held = false ∧ Recoverable known request after.disk ∧
      ∀ owned, binding = .ok owned →
        ScopedFailureReleased owned.root r reports childCloseError s after err
    | .error _ (after, held) => held = false ∧ Recoverable known request after.disk := by
  rw [publicOpenModel_run]
  cases binding with
  | error => exact ⟨rfl, prior, fun _ same => by cases same⟩
  | ok owned =>
    dsimp only
    rw [installScopedModel_run]
    have disk := reopenScopedModel_refines owned.root r reports childCloseError s prior
    cases ran : (reopenScopedModel owned.root r reports childCloseError).run s with
    | error => rw [ran] at disk; exact ⟨rfl, disk⟩
    | ok response after =>
      rw [ran] at disk
      cases response with
      | error =>
        refine ⟨rfl, disk, ?_⟩
        intro acquired same
        cases same
        exact reopenScoped_failureReleased _ _ _ _ ran
      | ok pair => exact ⟨rfl, rfl, rfl, disk.1, disk.2, rfl⟩

theorem publicOpenModel_append (owned : RootBinding directory lock) (r : RootReports)
    (openReports : Nat → Nat → SingleFile.OpenReports) (childCloseError rootUnlockError : Option String)
    {s t : State} (prior : Recoverable known request s.disk) {session : Session}
    {store : ReopenedStore directory lock}
    (opened : (publicOpenModel (.ok owned) r openReports childCloseError rootUnlockError).run (s, false) =
      .ok (.ok (.ready store session, ())) (t, true))
    (reports : ∀ cursor, SingleFile.AppendReports session.control.policy cursor batch)
    (room : store.activeChild.recovered.batches.length < 255) (size : batch.length ≤ 32) :
    let old := store.activeChild.recovered.batches
    let result := SingleFile.appendModel reports
      ⟨t.disk.segment store.activeId, SingleFile.storedPhase store.activeChild⟩
    store.binding = owned ∧ store.activeId = session.control.active ∧
    Installed session t.disk ∧ PermittedView known request session.view ∧
    Child.Recoverable session.control.policy old (some batch) (SingleFile.appendReached result).image ∧
    SingleFile.AppendGuarantee session.control.policy old batch result := by
  rw [publicOpenModel_run] at opened
  dsimp only at opened
  have installed : (installScopedModel owned r openReports childCloseError).run s =
      .ok (.ok (.ready store session)) t := by
    cases ran : (installScopedModel owned r openReports childCloseError).run s with
    | error => rw [ran] at opened; cases opened
    | ok response _ =>
      rw [ran] at opened
      cases response with
      | error => cases opened
      | ok phase => cases opened; rfl
  exact nativeAppendAfterTransfer owned r openReports childCloseError prior installed reports room size

theorem publicOpenModel_healthy (owned : RootBinding directory lock) (r : RootReports)
    (reports : Nat → Nat → SingleFile.OpenReports) (s : State) (prior : Recoverable known request s.disk)
    (rootOK : HealthyRoot r) (childrenOK : HealthyChildren reports)
    (representable : ∀ c, s.disk.liveControl = some c →
      c.capacity ≤ 255 ∧ c.active ≤ ControlCodec.wordMax ∧ c.discarded ≤ ControlCodec.wordMax) :
    ∃ session ready after, (publicOpenModel (.ok owned) r reports none none).run (s, false) =
      .ok (.ok (.ready ⟨owned, session.control.active, ready⟩ session, ())) (after, true) := by
  obtain ⟨session, ready, after, installed⟩ :=
    installScopedModel_healthy owned r reports none s prior rootOK childrenOK representable
  refine ⟨session, ready, after, ?_⟩
  rw [publicOpenModel_run]
  dsimp only
  rw [installed]

/-- The same continuation applies to every publication cut that reports an
error. The interpreted native reopen runs on each reached disk. -/
theorem repeatOpenAfterFailedDiscard (root : FilePath) (publish : Effects)
    (interruptedOpen first second : RootReports)
    (reports : Nat → Nat → SingleFile.OpenReports)
    (session : Session) (position : Nat) (before failed retried opened done : State)
    (selected repeated : Session) (installed : Installed session before.disk)
    (discardError : (Segmented.discardThrough (ops publish) session position).run before =
      .ok (.error publicationError) failed)
    (openError : (Segmented.reopen (nativeReopenOps root interruptedOpen reports)).run failed =
      .ok (.error recoveryError) retried)
    (openFirst : (Segmented.reopen (nativeReopenOps root first reports)).run retried =
      .ok (.ok selected) opened)
    (openSecond : (Segmented.reopen (nativeReopenOps root second reports)).run opened =
      .ok (.ok repeated) done) :
    PermittedView session.view (some (.discardThrough position)) selected.view ∧
      repeated.view = selected.view := by
  have discard := discard_refines publish session position before installed
  rw [discardError] at discard
  have retry := reopen_nativeRoot root interruptedOpen reports failed discard
  rw [openError] at retry
  have chosen := reopen_nativeRoot root first reports retried retry
  rw [openFirst] at chosen
  have settled := chosen.1.offline (request := none) (.inl rfl)
  have again := reopen_nativeRoot root second reports opened settled
  rw [openSecond] at again
  exact ⟨chosen.2, again.2.elim id (fun impossible => by cases impossible)⟩

end WalRecoverySlice.Segmented.Model
