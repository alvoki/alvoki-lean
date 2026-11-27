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
    (releaseWith close unlock).run before =
      match close.run before with
      | .ok () after => unlock.run after
      | .error childError after =>
        match unlock.run after with
        | .ok () released => .error childError released
        | .error unlockError reached => .error unlockError reached := by
  simp only [releaseWith, tryFinally, EStateM.run]
  change (EStateM.map Prod.fst (tryFinally' close (fun _ => unlock))) before = _
  cases closed : close before with
  | ok value after =>
    cases value
    simp [EStateM.map, tryFinally', closed]
    cases unlock after with
    | ok value _ => cases value; rfl
    | error => rfl
  | error err after =>
    simp [EStateM.map, tryFinally', closed]
    cases unlock after with
    | ok value _ => cases value; rfl
    | error => rfl

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
        | .ok (.error cleanup) after => .ok (.error cleanup) after
        | .error stopped after => .error stopped after
      | other => other := by
  dsimp only
  simp only [installPhaseWith, tryCatchThe, MonadExceptOf.tryCatch, ExceptT.tryCatch,
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
          | .ok (.error cleanup) after => .ok (.error cleanup) after
          | .error token after => .error token after
        | other => other
      | .ok (.error err) reached => .ok (.error err) reached
      | .error token reached => .error token reached := by
  simp only [withActiveChild, Bind.bind, ExceptT.bind, ExceptT.run, ExceptT.mk,
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

/-- Embed the exact public child recovery result in a disk slot. A reported
failure or interruption still carries the reached image and preserves the
previous cursor. Root namespace and other slots are framed by `child`. -/
def nativeChildWorker (dir : System.FilePath) (policy : Policy)
    (reports : SingleFile.OpenReports) : Persistence.M Decoded := fun image =>
  match SingleFile.openExistingModel dir policy reports {image} with
  | .ok (.ok ready) after => .ok (.ok ready.recovered) after.image
  | .ok (.error err) after => .ok (.error err) after.image
  | .error token after => .error token after.image

theorem nativeChild_recoverable {id : Nat} {s : State} (dir : System.FilePath)
    (reports : SingleFile.OpenReports) (named : id ∈ s.disk.liveNames)
    (prior : Child.Recoverable policy known pending (s.disk.segment id)) :
    let result := child s id (nativeChildWorker dir policy reports) Decoded.cursor Decoded.batches
    let disk := (reached result).disk
    Child.Recoverable policy known pending (disk.segment id) ∧
    ∀ batches, returned result = some batches →
      WalRecoverySlice.Contract.Permitted known pending batches ∧
      Child.Installed policy (disk.segment id) (disk.cursor id) batches := by
  let run := nativeChildWorker dir policy reports
  have frame := child_reached named run Decoded.cursor Decoded.batches
  have observed := child_returned named run Decoded.cursor Decoded.batches
  have facts := prior.nativeOpen dir reports {image := s.disk.segment id} rfl
  dsimp only
  rw [frame, Disk.setSegment_here]
  have report : (run.run (s.disk.segment id)) =
      match SingleFile.openExistingModel dir policy reports {image := s.disk.segment id} with
      | .ok (.ok ready) after => .ok (.ok ready.recovered) after.image
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
    Decoded.cursor Decoded.batches

def HealthyChildren (reports : Nat → Nat → SingleFile.OpenReports) : Prop :=
  ∀ step id, reports step id = {}

theorem nativeOpenChild_effects (root : FilePath) (reports : Nat → Nat → SingleFile.OpenReports) :
    OpenChildEffects (nativeOpenChild root reports) (HealthyChildren reports) where
  frame _ _ _ named := child_frame named _ _ _
  settled {policy id s history} named entry bounded fits := by
    have frame := child_reached named
      (nativeChildWorker (Native.segmentPath root id) policy (reports s.step id))
      Decoded.cursor Decoded.batches
    have facts := nativeChild_recoverable (Native.segmentPath root id) (reports s.step id)
      named (entry.recoverable bounded fits)
    refine ⟨?_, fun batches observed => ?_⟩
    · change (reached (child s id _ Decoded.cursor Decoded.batches)).disk.segment id = _
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
    change returned (child s id (nativeChildWorker dir policy r) Decoded.cursor Decoded.batches) = _ at ack
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
      Decoded.cursor Decoded.batches) = _
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

/-- Reached Linux effects for the root operations. Child file unlinks are
projected out after retirement. Directory fsync and rmdir retain their
effects even when an error is reported. -/
structure RootReports where
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

/-- The unused write callbacks retain their model implementations. Reopen
uses only the filesystem schedules in these five fields. -/
def nativeReopenOps (root : FilePath) (r : RootReports)
    (childReports : Nat → Nat → SingleFile.OpenReports) : Ops M :=
  { ops healthy with
    readControl := fun s => read (r.controlRead s.step) (rootControl root s.disk) s
    syncRoot := rootSync root r
    listSegments := fun s => read (r.listFault s.step) (rootListing s.disk.liveNames) s
    removeSegment := rootRemove root r
    openSegment := nativeOpenChild root childReports }

/-- A fault-free root does not require an empty retired directory. The
checked listing may contain any number of members. -/
structure HealthyRoot (r : RootReports) : Prop where
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

theorem reopen_nativeRoot {known request} (root : FilePath) (r : RootReports)
    (reports : Nat → Nat → SingleFile.OpenReports) (s : State) (prior : Recoverable known request s.disk) :
    DiskPost (fun session after => Installed session after ∧ PermittedView known request session.view)
      (Recoverable known request) ((Segmented.reopen (nativeReopenOps root r reports)).run s) := by
  exact reopenWithEffects_refines (nativeRootEffects root r reports)
    (nativeOpenChild_effects root reports) s prior

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
    (nativeOpenChild_effects root reports) s prior rootOK childrenOK
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

/-- A child transferred by the active scope retains the exact writer and
marker authority produced by single-file open. -/
theorem nativeAppendAfterTransfer (dir : FilePath) (policy : Policy)
    (openReports : SingleFile.OpenReports) (start : SingleFile.OpenImage)
    (prior : Child.Recoverable policy known pending start.image) (free : start.held = false)
    (close : SingleFile.Opened SingleFile.OpenTarget (SingleFile.AppendFiles SingleFile.OpenTarget) →
      SingleFile.OpenM Unit)
    (transferred :
      (Native.withActiveChild (error := String)
        (ExceptT.mk (SingleFile.openExistingModel dir policy openReports)) close pure).run start =
          .ok (.ok ready) after)
    (reports : ∀ cursor, SingleFile.AppendReports policy cursor batch)
    (room : ready.recovered.batches.length < 255) (size : batch.length ≤ 32) :
    let old := ready.recovered.batches
    let result := SingleFile.appendModel reports ⟨after.image, SingleFile.storedPhase ready⟩
    Child.Recoverable policy old (some batch) (SingleFile.appendReached result).image ∧
    SingleFile.AppendGuarantee policy old batch result := by
  have scopeResult := Native.withActiveChild_reached (SingleFile.openExistingModel dir policy openReports)
    close (fun handle => (pure handle : SingleFile.OpenM _)) start
  rw [scopeResult] at transferred
  have opened : SingleFile.openExistingModel dir policy openReports start = .ok (.ok ready) after := by
    cases ran : SingleFile.openExistingModel dir policy openReports start with
    | error => rw [ran] at transferred; cases transferred
    | ok response _ =>
      rw [ran] at transferred
      cases response with
      | error => cases transferred
      | ok value => cases transferred; rfl
  exact ⟨(prior.nativeAppendAfterOpen dir openReports start free opened reports room size).1,
    (prior.nativeAppendAfterOpen dir openReports start free opened reports room size).2.1⟩

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
