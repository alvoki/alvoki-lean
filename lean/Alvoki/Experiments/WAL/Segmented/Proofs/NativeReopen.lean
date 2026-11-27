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

/-- Once the protected namespace is checked, the actual dispatch opens the
selected path and scans exactly the handle it stores under the selected ID. -/
theorem openChild_dispatch (root : FilePath) (p : Policy) (id : Nat) (returned : child)
    (scan : child → Except String (List Bytes)) :
    openChildWith (.ok ()) (fun path =>
      if path = segmentPath root id then .ok #["policy", "segment", "commit.0", "commit.1"]
      else .error "wrong child listing")
      (fun path => if path = (segmentPath root id) / "policy" then
        .ok (policyStamp p).utf8ByteSize else .error "wrong policy size path")
      (fun path => if path = (segmentPath root id) / "policy" then
        .ok (policyStamp p) else .error "wrong policy read path")
      (fun path => if path = segmentPath root id then .ok returned else .error "wrong child open")
      (fun index _ => if index = id then .ok () else .error "wrong child ID")
      scan root p id = scan returned := by
  have log : (Policy.logOnly == .boundary) = false := rfl
  have marked : (Policy.boundary == .boundary) = true := rfl
  cases p <;> simp [openChildWith, policyStamp, Bind.bind,
    Except.bind, Array.contains, log, marked] <;> rfl

end WalRecoverySlice.Segmented.Native

namespace WalRecoverySlice.Segmented.Model
open System
open Persistence

/-- The shared phase wrapper preserves the disk proof of the existing model
schedule and ties the public scan to the exact installed session. -/
theorem reopenPhase_refines (owned : store) (callbacks : Ops M) (s : State)
    (physical : DiskPost (fun session after => Installed session after ∧ PermittedView known request session.view)
      (Recoverable known request) ((Segmented.reopen callbacks).run s))
    :
    let result := (Native.reopenPhaseWith callbacks owned).run s
    match result with
    | .ok (.ok (.ready owner session)) after =>
      owner = owned ∧ Installed session after.disk ∧
      Contract.Step (.offline known request) (.opened session.view) (.online session.view) ∧
      Native.scanWith (m := Except String) (.ready owner session) = .ok session.view
    | .ok (.ok _) _ => False
    | .ok (.error _) after | .error _ after => Recoverable known request after.disk := by
  have phase :
      (Native.reopenPhaseWith callbacks owned).run s =
        match (Segmented.reopen callbacks).run s with
        | .ok (.ok session) after => .ok (.ok (.ready owned session)) after
        | .ok (.error err) after => .ok (.error err) after
        | .error token after => .error token after := by
    cases ran : (Segmented.reopen callbacks).run s with
    | error =>
      simp [Native.reopenPhaseWith, Bind.bind, ExceptT.run, ExceptT.bind,
        ExceptT.bindCont, ExceptT.mk, EStateM.bind] at ran ⊢
      rw [ran]
    | ok response _ =>
      cases response <;>
        simp [Native.reopenPhaseWith, Bind.bind, ExceptT.run, ExceptT.bind,
          ExceptT.bindCont, ExceptT.mk, EStateM.bind] at ran ⊢ <;> rw [ran] <;> rfl
  dsimp only
  rw [phase]
  cases issued : (Segmented.reopen callbacks).run s with
  | error => rw [issued] at physical; exact physical
  | ok response _ =>
    rw [issued] at physical
    cases response with
    | error => exact physical
    | ok session => exact ⟨rfl, physical.1, .opened physical.2, rfl⟩

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

theorem nativeOpenChild_effects (root : FilePath) (reports : Nat → Nat → SingleFile.OpenReports) :
    OpenChildEffects (nativeOpenChild root reports) False where
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
  healthy _ _ impossible := impossible.elim

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
        (fun path => observe (if path = dir then members else .error "wrong listing path"))
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
    (fun path t => read none (if path = dir then r.members s.step id else .error "wrong listing path") t)
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

theorem nativeRootEffects (root : FilePath) (r : RootReports) (reports : Nat → Nat → SingleFile.OpenReports) :
    OpenRootEffects (nativeReopenOps root r reports) False where
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
      · exact ⟨rfl, id⟩
    | some fault => cases fault <;> exact ⟨rfl, id⟩
  syncHealthy _ impossible := impossible.elim
  collectHealthy _ _ impossible := impossible.elim

theorem reopen_nativeRoot {known request} (root : FilePath) (r : RootReports)
    (reports : Nat → Nat → SingleFile.OpenReports) (s : State) (prior : Recoverable known request s.disk) :
    DiskPost (fun session after => Installed session after ∧ PermittedView known request session.view)
      (Recoverable known request) ((Segmented.reopen (nativeReopenOps root r reports)).run s) :=
  reopenWithEffects_refines (nativeRootEffects root r reports) (nativeOpenChild_effects root reports) s prior

theorem reopenPhase_nativeRoot (owned : store) (root : FilePath) (r : RootReports)
    (reports : Nat → Nat → SingleFile.OpenReports) (s : State)
    (prior : Recoverable known request s.disk) :
    let result := (Native.reopenPhaseWith (nativeReopenOps root r reports) owned).run s
    match result with
    | .ok (.ok (.ready owner session)) after =>
      owner = owned ∧ Installed session after.disk ∧
      Contract.Step (.offline known request) (.opened session.view) (.online session.view) ∧
      Native.scanWith (m := Except String) (.ready owner session) = .ok session.view
    | .ok (.ok _) _ => False
    | .ok (.error _) after | .error _ after => Recoverable known request after.disk :=
  reopenPhase_refines owned _ s (reopen_nativeRoot root r reports s prior)

/-- A fresh reference receives the exact phase. Reference and mutex creation
are BaseIO operations in the public adapter. This model erases their identities. -/
def nativeInstallModel (owned : store) (callbacks : Ops M) : M (Native.Phase store × Unit) :=
  Native.installPhaseWith (error := String) (Native.reopenPhaseWith callbacks owned)
    pure (pure ()) (pure ())

theorem nativeInstallModel_eq (owned : store) (callbacks : Ops M) (s : State) :
    (nativeInstallModel owned callbacks).run s =
      match (Native.reopenPhaseWith callbacks owned).run s with
      | .ok (.ok phase) after => .ok (.ok (phase, ())) after
      | .ok (.error err) after => .ok (.error err) after
      | .error token after => .error token after := by
  unfold nativeInstallModel
  simp only [Native.installPhaseWith, tryCatchThe, MonadExceptOf.tryCatch,
    ExceptT.tryCatch, ExceptT.run, ExceptT.mk, Bind.bind, EStateM.bind, ExceptT.bind]
  cases reopened : (Native.reopenPhaseWith callbacks owned).run s with
  | error =>
    simp only [ExceptT.run] at reopened
    rw [reopened]
  | ok value after =>
    simp only [ExceptT.run] at reopened
    rw [reopened]
    cases value <;> rfl

theorem nativeInstallModel_refines (owned : store) (root : FilePath) (r : RootReports)
    (reports : Nat → Nat → SingleFile.OpenReports) (s : State)
    (prior : Recoverable known request s.disk) :
    match (nativeInstallModel owned (nativeReopenOps root r reports)).run s with
    | .ok (.ok (.ready owner session, ())) after =>
      owner = owned ∧ Installed session after.disk ∧
      Contract.Step (.offline known request) (.opened session.view) (.online session.view) ∧
      Native.scanWith (m := Except String) (.ready owner session) = .ok session.view
    | .ok (.ok _) _ => False
    | .ok (.error _) after | .error _ after => Recoverable known request after.disk := by
  have opened := reopenPhase_nativeRoot owned root r reports s prior
  dsimp only at opened
  rw [nativeInstallModel_eq]
  cases ran : (Native.reopenPhaseWith (nativeReopenOps root r reports) owned).run s with
  | error => rw [ran] at opened; exact opened
  | ok value _ =>
    cases value with
    | error => rw [ran] at opened; exact opened
    | ok phase => rw [ran] at opened; cases phase <;> exact opened

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
