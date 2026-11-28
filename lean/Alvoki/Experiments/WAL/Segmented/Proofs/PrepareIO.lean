import Alvoki.Experiments.WAL.Segmented.Proofs.ControlIO

namespace WalRecoverySlice.Segmented.Native.PrepareIO
open System Model Alvoki.NativePost
open AppendIO (At)

def Returned (b : Model.M β) (s : State) (R : W → State → Prop) (y : β) (t : W) :=
  ∃ u, b.run s = .ok (.ok y) u ∧ R t u

def Stopped (b : Model.M β) (s : State) (R : W → State → Prop) (t : W) :=
  ∃ msg u, b.run s = .ok (.error msg) u ∧ R t u

private theorem ofReports {a : IO α} {b : Model.M β} {f : α → β}
    (receipt : IOReturns a w (fun x t => Returned b s R (f x) t) (Stopped b s R)) :
    At a b w s (fun x y t u => y = f x ∧ R t u) R := by
  unfold IOReturns At at *
  cases ran : a w with
  | error =>
    rw [ran] at receipt
    obtain ⟨_, _, eq, frame⟩ := receipt
    rw [eq]
    exact frame
  | ok =>
    rw [ran] at receipt
    obtain ⟨_, eq, frame⟩ := receipt
    rw [eq]
    exact ⟨rfl, frame⟩

/-- The concrete validation order follows the checked listing, even when
two different entries share a filename or one of the checks stops early. -/
inductive MemberAt (dir : FilePath) (items : Array IO.FS.DirEntry) (start : W) :
    List IO.FS.DirEntry → W → Prop where
  | first : MemberAt dir items start items.toList start
  | next : MemberAt dir items start (entry :: rest) w →
      childName entry.fileName = true →
      (dir / entry.fileName).symlinkMetadata w = .ok md t → ControlIO.Regular md →
      MemberAt dir items start rest t

private def checkedName (dir : FilePath) (x : IO.FS.DirEntry) (_ : PUnit) : IO (ForInStep PUnit) := do
  let path := dir / x.fileName
  unless childName x.fileName do throw (IO.userError s!"unexpected child {path}")
  regular path (← path.symlinkMetadata)
  return .yield ()

def Next (items : Array IO.FS.DirEntry) (b : Model.M (Array String)) (s : State) (R : W → State → Prop)
    (rest : List IO.FS.DirEntry) (w : W) : Prop :=
  match rest with
  | [] => Returned b s R (items.map (·.fileName)) w
  | x :: _ => childName x.fileName = false → Stopped b s R w

/-- Dir stat, checked readdir and the exact no-follow stat on each
listed member. A pure guard can reject the last primitive's result. -/
structure Inspect (dir : FilePath) (w : W) (s : State) (b : Model.M (Array String))
    (R : W → State → Prop) : Prop where
  stat : match dir.symlinkMetadata w with
    | .ok md t => (md.type == .dir) = false → Stopped b s R t
    | .error _ t => Stopped b s R t
  list : ∀ md t, dir.symlinkMetadata w = .ok md t → (md.type == .dir) = true →
    IOReturns (entries dir) t (fun items u => Next items b s R items.toList u) (Stopped b s R)
  member : ∀ md t, dir.symlinkMetadata w = .ok md t → (md.type == .dir) = true →
    ∀ items listed, entries dir t = .ok items listed →
    ∀ x rest u, MemberAt dir items listed (x :: rest) u → childName x.fileName = true →
    IOReturns (dir / x.fileName).symlinkMetadata u
      (fun child v => if ControlIO.Regular child then Next items b s R rest v else Stopped b s R v) (Stopped b s R)

private theorem memberLoop (p : Inspect dir w s b R)
    (mdStat : dir.symlinkMetadata w = .ok md t) (directory : (md.type == .dir) = true)
    (listed : entries dir t = .ok items start)
    (cursor : MemberAt dir items start rest u) (frame : Next items b s R rest u) :
    IOReturns (forIn rest () (checkedName dir)) u
      (fun _ v => Returned b s R (items.map (·.fileName)) v) (Stopped b s R) := by
  induction rest generalizing u with
  | nil => exact frame
  | cons x rest ih =>
    rw [List.forIn_cons]
    by_cases valid : childName x.fileName = true
    · have stat := p.member _ _ mdStat directory items start listed x rest u cursor valid
      unfold IOReturns at stat
      unfold checkedName
      simp only [valid, ite_true]
      unfold IOReturns
      cases run : (dir / x.fileName).symlinkMetadata u with
      | error e v =>
        rw [run] at stat
        simpa [Bind.bind, instMonadEIO._aux_13, EST.bind, run] using stat
      | ok child v =>
        rw [run] at stat
        dsimp only at stat
        by_cases file : ControlIO.Regular child
        · rw [ite_eq_left file] at stat
          have next := ih (.next cursor valid run file) stat
          unfold checkedName at next
          simpa [Bind.bind, instMonadEIO._aux_13, EST.bind, run, regular, file, Pure.pure,
            instMonadEIO._aux_5, EST.pure, IOReturns] using next
        · rw [ite_eq_right file] at stat
          simpa [Bind.bind, instMonadEIO._aux_13, EST.bind, run, regular, file, throw, throwThe,
            MonadExceptOf.throw, instMonadExceptOfEIO._aux_1, EST.throw, IOReturns] using stat
    · have invalid := Bool.eq_false_iff.mpr valid
      simpa [checkedName, invalid, Bind.bind, instMonadEIO._aux_13, EST.bind, throw, throwThe,
        MonadExceptOf.throw, instMonadExceptOfEIO._aux_1, EST.throw, IOReturns] using frame invalid

theorem Inspect.run (p : Inspect dir w s b R) :
    At (inspectChild dir) b w s (fun xs ys t u => ys = xs.map (·.fileName) ∧ R t u) R := by
  apply ofReports
  have stat := p.stat
  unfold inspectChild inspectChildWith
  apply IOReturns.bind (middle := fun md t => dir.symlinkMetadata w = .ok md t ∧
    ((md.type == .dir) = false → Stopped b s R t))
  · unfold IOReturns
    cases run : dir.symlinkMetadata w with
    | error => rw [run] at stat; exact stat
    | ok => rw [run] at stat; exact ⟨rfl, stat⟩
  rintro md t ⟨run, badType⟩
  split
  · rename_i good
    apply IOReturns.bind (middle := fun items u => entries dir t = .ok items u ∧ Next items b s R items.toList u)
    · have listing := p.list md t run good
      unfold IOReturns at *
      cases read : entries dir t with
      | error => rw [read] at listing; exact listing
      | ok => rw [read] at listing; exact ⟨rfl, listing⟩
    rintro xs start ⟨listed, entry⟩
    apply IOReturns.bind (middle := fun _ v => Returned b s R (xs.map (·.fileName)) v)
    · rw [← Array.forIn_toList]
      exact memberLoop p run good listed .first entry
    · exact fun _ _ receipt => receipt
  · exact badType (Bool.eq_false_iff.mpr (by assumption))

def present (r : RootReports) (initial : State) (id : Nat) : Model.M Bool := fun t =>
  read none (match r.presenceFault initial.step id with
    | some e => .error e
    | none => .ok (decide (id ∈ initial.disk.liveNames))) t

def listed (r : RootReports) (initial : State) (id : Nat) : Model.M (Array String) := fun t =>
  read none (r.members initial.step id) t

def unlink (r : RootReports) (initial : State) (path : FilePath) : Model.M Unit := fun t =>
  read (r.unlinkFault initial.step path) (.ok ()) t

def rmdir (r : RootReports) (initial : State) (id : Nat) : Model.M Unit := fun t =>
  namespaceChange (r.rmdir initial.step id) (fun d persist => d.remove id persist) t

def presenceIO (dir : FilePath) : IO Bool := do return (← metadata? dir).isSome

/-- The exact input of a member unlink, or of the final rmdir when
the remaining list is empty. Inspection itself modifies no root name. -/
inductive Deleting (dir : FilePath) (start : W) : List IO.FS.DirEntry → W → Prop where
  | listed : presenceIO dir start = .ok true t → inspectChild dir t = .ok xs u →
      Deleting dir start xs.toList u
  | unlinked : Deleting dir start (entry :: rest) t →
      IO.FS.removeFile (dir / entry.fileName) t = .ok () u → Deleting dir start rest u

structure Removal (root : FilePath) (id : Nat) (r : RootReports) (origin : W)
    (initial : State) (R : W → State → Prop) : Prop where
  stat : let dir := segmentPath root id
    match dir.symlinkMetadata origin with
    | .ok _ t => Returned (present r initial id) initial R true t
    | .error (.noFileOrDirectory ..) t => Returned (present r initial id) initial R false t
    | .error _ t => Stopped (present r initial id) initial R t
  inspect : ∀ t s, presenceIO (segmentPath root id) origin = .ok true t →
    (present r initial id).run initial = .ok (.ok true) s → R t s →
    Inspect (segmentPath root id) t s (listed r initial id) R
  unlinkFile : ∀ entry rest t s, Deleting (segmentPath root id) origin (entry :: rest) t → R t s →
    let path := segmentPath root id / entry.fileName
    At (IO.FS.removeFile path) (unlink r initial path) t s (fun _ _ v u => R v u) R
  removeDirectory : ∀ t s, Deleting (segmentPath root id) origin [] t → R t s →
    At (IO.FS.removeDir (segmentPath root id)) (rmdir r initial id) t s (fun _ _ v u => R v u) R

variable {id : Nat}

private theorem Removal.presence (receipt : Removal root id r origin s R) :
    At (presenceIO (segmentPath root id)) (present r s id) origin s
      (fun found model t u => found = model ∧ R t u ∧
        presenceIO (segmentPath root id) origin = .ok found t ∧ (present r s id).run s = .ok (.ok model) u) R := by
  have md := receipt.stat
  dsimp only at md
  unfold At
  cases stat : (segmentPath root id).symlinkMetadata origin with
  | ok data t =>
    rw [stat] at md
    obtain ⟨u, report, frame⟩ := md
    have ran : presenceIO (segmentPath root id) origin = .ok true t := by
      simp [presenceIO, metadata?, tryCatchThe, MonadExceptOf.tryCatch, instMonadExceptOfEIO._aux_3,
        EST.tryCatch, Bind.bind, instMonadEIO._aux_13, EST.bind, Functor.map, instMonadEIO._aux_1,
        Pure.pure, instMonadEIO._aux_5, EST.pure, stat]
    rw [ran, report]
    exact ⟨rfl, frame, rfl, rfl⟩
  | error e t =>
    rw [stat] at md
    cases e <;>
      simp only [presenceIO, metadata?, tryCatchThe, MonadExceptOf.tryCatch, instMonadExceptOfEIO._aux_3,
        EST.tryCatch, Bind.bind, instMonadEIO._aux_13, EST.bind, Functor.map, instMonadEIO._aux_1,
        Pure.pure, instMonadEIO._aux_5, EST.pure, throw, throwThe, MonadExceptOf.throw, instMonadExceptOfEIO._aux_1,
        EST.throw, stat]
    case noFileOrDirectory =>
      obtain ⟨u, report, frame⟩ := md
      rw [report]
      exact ⟨rfl, frame, rfl, rfl⟩
    all_goals obtain ⟨msg, u, report, frame⟩ := md; rw [report]; exact frame

private theorem Removal.members (io : Removal root id r origin initial R)
    (atMember : Deleting (segmentPath root id) origin rest w) (frame : R w s) :
    At (forM rest (fun entry => IO.FS.removeFile (segmentPath root id / entry.fileName)))
      (forM (rest.map (·.fileName)) (fun (name : String) => unlink r initial (segmentPath root id / name))) w s
      (fun _ _ t u => R t u ∧ Deleting (segmentPath root id) origin [] t) R := by
  induction rest generalizing w s with
  | nil => exact ⟨frame, atMember⟩
  | cons x rest ih =>
    simp only [List.map_cons, List.forM_cons]
    apply (ControlIO.trace (io.unlinkFile x rest w s atMember frame)).bind
    rintro _ _ t u ⟨kept, ran, _⟩
    exact ih (.unlinked atMember ran) kept

theorem Removal.run (io : Removal root id r origin initial R) :
    At (removeSegment root id) ((nativeReopenOps root r (fun _ _ => {})).removeSegment id) origin initial
      (fun _ _ t u => R t u) R := by
  unfold At
  rw [nativeRemove_schedule]
  change At (removeSegmentWith presenceIO inspectChild (·.fileName) IO.FS.removeFile IO.FS.removeDir root id)
    (removeSegmentWith (fun _ => present r initial id) (fun _ => listed r initial id) _root_.id
      (unlink r initial) (fun _ => rmdir r initial id) root id) origin initial _ _
  unfold removeSegmentWith
  apply io.presence.bind
  rintro found _ t s ⟨rfl, frame, ran, model⟩
  cases found with
  | false => exact frame
  | true =>
    apply (ControlIO.trace (io.inspect t s ran model frame).run).bind
    rintro xs _ u v ⟨⟨rfl, keep⟩, validated, _⟩
    apply At.bind (middle := fun _ _ x y => R x y ∧ Deleting (segmentPath root id) origin [] x)
    · cases xs with
      | mk names =>
        change At (forM names.toArray _) (forM ((names.toArray.map (·.fileName))) _) u v _ _
        rw [List.forM_toArray, List.map_toArray, List.forM_toArray]
        exact io.members (.listed ran validated) keep
    · rintro _ _ x y ⟨kept, cut⟩
      exact io.removeDirectory x y cut kept

end WalRecoverySlice.Segmented.Native.PrepareIO
