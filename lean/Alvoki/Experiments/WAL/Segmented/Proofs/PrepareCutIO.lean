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
