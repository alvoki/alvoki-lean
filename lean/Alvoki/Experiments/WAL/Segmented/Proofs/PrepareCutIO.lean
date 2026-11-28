import Alvoki.Experiments.WAL.Segmented.Proofs.ControlCutIO
import Alvoki.Experiments.WAL.Segmented.Proofs.SuccessorIO

namespace WalRecoverySlice.Segmented.Native.PrepareCutIO
open System Model Alvoki.NativePost

/-- Only the already selected files and names are protected. The prospective
successor can exist, be partly deleted, or contain partial create output. -/
structure Frame (c : Control) (before after : Disk) : Prop where
  live : after.liveControl = before.liveControl
  durable : after.durableControl = before.durableControl
  names : ∀ i, c.selects i →
    (i ∈ before.liveNames → i ∈ after.liveNames) ∧ (i ∈ before.durableNames → i ∈ after.durableNames)
  data : ∀ i, c.selects i → after.segment i = before.segment i
  cursor : after.cursor c.active = before.cursor c.active

theorem Frame.refl (c : Control) (d : Disk) : Frame c d d :=
  ⟨rfl, rfl, fun _ _ => ⟨id, id⟩, fun _ _ => rfl, rfl⟩

theorem Frame.trans (a : Frame c x y) (b : Frame c y z) : Frame c x z :=
  ⟨b.live.trans a.live, b.durable.trans a.durable,
   fun i sel => ⟨(b.names i sel).1 ∘ (a.names i sel).1, (b.names i sel).2 ∘ (a.names i sel).2⟩,
   fun i sel => (b.data i sel).trans (a.data i sel), b.cursor.trans a.cursor⟩

theorem Frame.survivor (f : Frame c before d) (ready : ReadyLayout c history before)
    (live : before.liveControl = some c) (durable : before.durableControl = some c) :
    d.liveControl = some c ∧ d.durableControl = some c ∧ Recoverable (historyView c history) none d ∧
      Recoverable (historyView c history) none d.powerLoss := by
  have layout := ready.frame (fun i h => ⟨(f.names i h).1 (ready.layout.names i h).1,
    (f.names i h).2 (ready.layout.names i h).2⟩) f.data f.cursor
  have choice := layout.choice (request := none) (.inl rfl)
  have l := f.live.trans live
  have r := f.durable.trans durable
  have recovery : Recoverable (historyView c history) none d := ⟨⟨_, l, choice⟩, ⟨_, r, choice⟩⟩
  exact ⟨l, r, recovery, recovery.powerLoss⟩

inductive Point
  | presence | dirStat | list
  | validate (all rest : List IO.FS.DirEntry)
  | erase (rest : List IO.FS.DirEntry)
  | mkdir | create

def successorDir (s : Store) (c : Control) := segmentPath s.root (c.active + 1)

inductive Issued (dir : FilePath) : Point → {α : Type} → IO α → Prop where
  | presence : Issued dir .presence dir.symlinkMetadata
  | dirStat : Issued dir .dirStat dir.symlinkMetadata
  | list : Issued dir .list (entries dir)
  | member : childName item.fileName = true →
      Issued dir (.validate all (item :: rest)) (dir / item.fileName).symlinkMetadata
  | erase : Issued dir (.erase (item :: rest)) (IO.FS.removeFile (dir / item.fileName))
  | rmdir : Issued dir (.erase []) (IO.FS.removeDir dir)
  | mkdir : Issued dir .mkdir (IO.FS.createDir dir)

inductive Step (dir : FilePath) : Point → W → Point → W → Prop where
  | present : dir.symlinkMetadata w = .ok md t → Step dir .presence w .dirStat t
  | absent : dir.symlinkMetadata w = .error (.noFileOrDirectory path code msg) t → Step dir .presence w .mkdir t
  | checkedDir : dir.symlinkMetadata w = .ok md t → (md.type == .dir) = true → Step dir .dirStat w .list t
  | listed : entries dir w = .ok xs t → Step dir .list w (.validate xs.toList xs.toList) t
  | checked : childName item.fileName = true → (dir / item.fileName).symlinkMetadata w = .ok md t →
      ControlIO.Regular md → Step dir (.validate all (item :: rest)) w (.validate all rest) t
  | validated : Step dir (.validate all []) w (.erase all) w
  | unlinked : IO.FS.removeFile (dir / item.fileName) w = .ok () t → Step dir (.erase (item :: rest)) w (.erase rest) t
  | removed : IO.FS.removeDir dir w = .ok () t → Step dir (.erase []) w .mkdir t
  | made : IO.FS.createDir dir w = .ok () t → Step dir .mkdir w .create t

inductive Prefix (dir : FilePath) (origin : W) : Point → W → Prop where
  | start : Prefix dir origin .presence origin
  | more : Prefix dir origin p w → Step dir p w q t → Prefix dir origin q t

private def member (dir : FilePath) (entry : IO.FS.DirEntry) (_ : PUnit) : IO (ForInStep PUnit) := do
  let path := dir / entry.fileName
  unless childName entry.fileName do throw (IO.userError s!"unexpected child {path}")
  regular path (← path.symlinkMetadata)
  return .yield ()

private def members (dir : FilePath) (rest : List IO.FS.DirEntry) := forIn rest () (member dir)
private def unlinkAll (dir : FilePath) (rest : List IO.FS.DirEntry) := forM rest (fun e => IO.FS.removeFile (dir / e.fileName))
private def eraseDir (dir : FilePath) (all : List IO.FS.DirEntry) := unlinkAll dir all >>= fun _ => IO.FS.removeDir dir

private def removeRest (dir : FilePath) : Point → IO Unit
  | .presence => do if ← PrepareIO.presenceIO dir then eraseDir dir (← inspectChild dir).toList
  | .dirStat => do eraseDir dir (← inspectChild dir).toList
  | .list => do
      let items ← entries dir
      let _ ← members dir items.toList
      eraseDir dir items.toList
  | .validate all rest => do
      let _ ← members dir rest
      eraseDir dir all
  | .erase rest => eraseDir dir rest
  | .mkdir | .create => pure ()

def remaining (s : Store) (c : Control) (p : Point) : IO SingleFile.Handle :=
  let dir := successorDir s c
  match p with
  | .create => SingleFile.create dir c.policy
  | _ => do
      removeRest dir p
      IO.FS.createDir dir
      SingleFile.create dir c.policy

private theorem concrete (s : Store) (c : Control) :
    s.prepareChild c.policy (c.active + 1) = remaining s c .presence := by
  change (removeSegment s.root (c.active + 1) >>= _) = _
  suffices eq : removeSegment s.root (c.active + 1) = removeRest (successorDir s c) .presence by
    rw [eq]
    rfl
  let dir := successorDir s c
  change (PrepareIO.presenceIO dir >>= fun present => if present then do
    let items ← inspectChild dir
    items.forM fun entry => IO.FS.removeFile (dir / entry.fileName)
    IO.FS.removeDir dir
    else pure ()) = _
  apply congrArg (fun k : Bool → IO Unit => PrepareIO.presenceIO dir >>= k)
  funext present
  cases present
  · rfl
  · apply congrArg (fun k : Array IO.FS.DirEntry → IO Unit => inspectChild dir >>= k)
    funext items
    cases items with
    | mk names =>
      change (forM names.toArray _ >>= _) = _
      rw [List.forM_toArray]
      rfl

private theorem Step.remove (edge : Step dir p w q t) (outside : p ≠ .mkdir) : removeRest dir p w = removeRest dir q t := by
  cases edge with
  | present observed =>
    simp [removeRest, PrepareIO.presenceIO, metadata?, tryCatchThe, MonadExceptOf.tryCatch, instMonadExceptOfEIO._aux_3,
      EST.tryCatch, Functor.map, instMonadEIO._aux_1, EST.bind, Bind.bind, instMonadEIO._aux_13,
      observed, Pure.pure, instMonadEIO._aux_5, EST.pure]
  | absent observed =>
    simp [removeRest, PrepareIO.presenceIO, metadata?, tryCatchThe, MonadExceptOf.tryCatch, instMonadExceptOfEIO._aux_3,
      EST.tryCatch, Functor.map, instMonadEIO._aux_1, EST.bind, Bind.bind, instMonadEIO._aux_13,
      observed, Pure.pure, instMonadEIO._aux_5, EST.pure]
  | checkedDir observed valid =>
    have checked (arr : Array IO.FS.DirEntry) : (forIn arr () (member dir)) = members dir arr.toList := by
      rw [← Array.forIn_toList]
      rfl
    have inspect : inspectChild dir w = (do
        let items ← entries dir
        let _ ← members dir items.toList
        pure items : IO _) t := by
      unfold inspectChild
      simp only [Bind.bind, instMonadEIO._aux_13, EST.bind, observed, valid, ↓reduceIte]
      cases listed : entries dir t <;> simp_all only
      rename_i items v
      change EST.bind (forIn items () (member dir) : IO PUnit) _ v = _
      rw [checked items]
      rfl
    simp only [removeRest, Bind.bind, instMonadEIO._aux_13, EST.bind, inspect,
      Pure.pure, instMonadEIO._aux_5, EST.pure]
    cases listed : entries dir t <;> simp_all only
    rename_i items v
    cases measured : members dir items.toList v <;> rfl
  | listed observed =>
    simp [removeRest, Bind.bind, instMonadEIO._aux_13, EST.bind, observed]
  | checked valid observed file =>
    simp [ControlIO.Regular] at file
    simp [removeRest, members, member, regular, List.forIn_cons, valid, observed, file.1, file.2,
      Bind.bind, instMonadEIO._aux_13, EST.bind, Pure.pure, instMonadEIO._aux_5, EST.pure]
  | validated => rfl
  | unlinked observed =>
    simp [removeRest, eraseDir, unlinkAll, List.forM_cons, Bind.bind, instMonadEIO._aux_13, EST.bind, observed]
  | removed observed =>
    exact observed
  | made => exact False.elim (outside rfl)

theorem Prefix.continuation (path : Prefix (successorDir s c) origin p w) :
    s.prepareChild c.policy (c.active + 1) origin = remaining s c p w := by
  induction path with
  | start => rw [concrete]
  | more prior edge ih =>
    rw [ih]
    rename_i p0 w0 q t
    by_cases made : p0 = .mkdir
    · subst p0
      cases edge with
      | made ok => simp [remaining, removeRest, Bind.bind, instMonadEIO._aux_13, EST.bind, Pure.pure, instMonadEIO._aux_5, EST.pure, ok]
    · have same := edge.remove made
      cases edge <;> dsimp only [remaining] <;> simp only [Bind.bind, instMonadEIO._aux_13, EST.bind, same] <;> contradiction

structure Primitives (s : Store) (c : Control) (origin : W) (disk : W → Disk) (stop : ControlCutIO.Stops) : Prop where
  returned : ∀ p w q t, Prefix (successorDir s c) origin p w → Step (successorDir s c) p w q t →
    Frame c (disk w) (disk t)
  stopped : ∀ p w, Prefix (successorDir s c) origin p w → ∀ {α} (a : IO α), Issued (successorDir s c) p a →
    ∀ d, stop a w d → Frame c (disk w) d

theorem Prefix.frame (prims : Primitives s c origin disk stop) (path : Prefix (successorDir s c) origin p w) :
    Frame c (disk origin) (disk w) := by
  induction path with
  | start => exact .refl ..
  | more prior step ih => exact ih.trans (prims.returned _ _ _ _ prior step)

theorem interrupted (prims : Primitives s c origin disk stop) (path : Prefix (successorDir s c) origin p w)
    (issued : Issued (successorDir s c) p a) (cut : stop a w d) : Frame c (disk origin) d :=
  (path.frame prims).trans (prims.stopped _ _ path _ issued _ cut)

/-- The pending child returned by prepare remains local until after payload
write. The next operation is the store directory fsync on that return world. -/
theorem beforePublish (stop : ControlCutIO.Stops) (disk : W → Disk) (s : Store) (c : Control)
    {child : SingleFile.Handle} (made : s.prepareChild c.policy (c.active + 1) origin = .ok child w)
    (before : Frame c (disk origin) (disk w)) (cut : stop (syncHandle s.directory) w d)
    (sync : ∀ h v, s.prepareChild c.policy (c.active + 1) origin = .ok h v →
      ∀ after, stop (syncHandle s.directory) v after → Frame c (disk v) after) :
    Frame c (disk origin) d := before.trans (sync _ _ made _ cut)

end WalRecoverySlice.Segmented.Native.PrepareCutIO
