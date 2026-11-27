import Alvoki.Experiments.WAL.CrashModel

namespace WalRecoverySlice.Persistence

/-- A comparison image for the bytes a surviving kernel exposes to a new process. -/
def FileImage.liveSnapshot (file : FileImage) : FileImage := ⟨file.live, file.live⟩

def Image.liveSnapshot (image : Image) : Image :=
  ⟨image.data.liveSnapshot, image.slot0.liveSnapshot, image.slot1.liveSnapshot⟩

private def Write.mirrorLive : Write → Write
  | .before abort => .before abort
  | .torn n _ abort => .torn n (.short n) abort
  | .full _ abort => .full .complete abort

def Effects.mirrorLive (e : Effects) : Effects :=
  { e with appendData := e.appendData.mirrorLive, writeMarker := e.writeMarker.mirrorLive }

def Result.liveSnapshot {α} : Result α → Result α
  | .ok a image => .ok a image.liveSnapshot
  | .error e image => .error e image.liveSnapshot

private def Mirrors {α} (a b : M α) := ∀ s, b.run s.liveSnapshot = Result.liveSnapshot (a.run s)

private theorem mirrors_bind {α β} {a b : M α} {f g : α → M β}
    (first : Mirrors a b) (rest : ∀ x, Mirrors (f x) (g x)) :
    Mirrors (a >>= f) (b >>= g) := by
  intro s
  have first := first s
  change b s.liveSnapshot = Result.liveSnapshot (a s) at first
  simp only [Bind.bind, ExceptT.bind, ExceptT.run, ExceptT.mk, EStateM.bind, first]
  cases h : a s with
  | error e t => rfl
  | ok x t => cases x with
    | error msg => rfl
    | ok x => exact rest x t

private theorem mirror_write (outcome : Write) (write : Bytes → Bytes → Bytes) (bytes : Bytes)
    (s : Image) (f : FileImage) (replace put : FileImage → Image)
    (law : ∀ file, put file.liveSnapshot = (replace file).liveSnapshot) :
    outcome.mirrorLive.result write bytes s.liveSnapshot f.liveSnapshot put =
      Result.liveSnapshot (outcome.result write bytes s f replace) := by
  cases outcome with
  | before a => cases a <;> rfl
  | torn n d a =>
    have eqn := law ⟨write f.live (bytes.take n), d.bytes write f.durable bytes⟩
    cases a <;> simp [Write.mirrorLive, Write.result, Abort.result, Result.liveSnapshot] <;> exact eqn
  | full d a =>
    have eqn := law ⟨write f.live bytes, d.bytes write f.durable bytes⟩
    cases a with
    | none => exact congrArg (EStateM.Result.ok (Except.ok ())) eqn
    | some a => cases a <;> first | exact congrArg (EStateM.Result.error ()) eqn
                                  | exact congrArg (EStateM.Result.ok (Except.error _)) eqn

private theorem mirror_sync (outcome : Primitive) (s : Image) (f : FileImage)
    (replace put : FileImage → Image)
    (law : ∀ file, put file.liveSnapshot = (replace file).liveSnapshot) :
    outcome.syncResult s.liveSnapshot f.liveSnapshot put =
      Result.liveSnapshot (outcome.syncResult s f replace) := by
  cases outcome with
  | before a => cases a <;> rfl
  | after a => cases a with
    | none => exact congrArg (EStateM.Result.ok (Except.ok ())) (law _)
    | some a => cases a <;> first | exact congrArg (EStateM.Result.error ()) (law _)
                                  | exact congrArg (EStateM.Result.ok (Except.error _)) (law _)

private theorem mirror_marker (s : Image) (slot : Nat) :
    s.liveSnapshot.marker slot = (s.marker slot).liveSnapshot := by
  by_cases h : slot = 0 <;> simp [Image.marker, Image.liveSnapshot, h]

private theorem mirror_put (s : Image) (slot : Nat) (f : FileImage) :
    s.liveSnapshot.withMarker slot f.liveSnapshot = (s.withMarker slot f).liveSnapshot := by
  by_cases h : slot = 0 <;> simp [Image.withMarker, Image.liveSnapshot, h]

/-- The same source append, run with visible effects mirrored into its comparison
image, gives the identical API response or interruption and exact live bytes. -/
theorem appendBatch_liveSnapshot (e : Effects) (p : Policy) (c : Cursor) (b : Bytes) (s : Image) :
    (appendBatch (ops e.mirrorLive) p c b).run s.liveSnapshot =
      Result.liveSnapshot ((appendBatch (ops e) p c b).run s) := by
  suffices h : Mirrors (appendBatch (ops e) p c b) (appendBatch (ops e.mirrorLive) p c b) from h s
  simp only [appendBatch]
  split <;> rename_i guard
  · intro t; rfl
  split
  · intro t; rfl
  apply mirrors_bind
  · intro t; exact mirror_write e.appendData List.append _ t t.data (fun f => {t with data := f}) (fun f => {t.liveSnapshot with data := f}) (fun _ => rfl)
  intro _
  apply mirrors_bind
  · intro t; exact mirror_sync e.dataSync t t.data (fun f => {t with data := f}) (fun f => {t.liveSnapshot with data := f}) (fun _ => rfl)
  intro _
  split
  · apply mirrors_bind
    · intro t
      change Write.result _ _ _ _ (t.liveSnapshot.marker _) _ = _
      rw [mirror_marker]
      exact mirror_write _ _ _ _ _ _ _ (mirror_put _ _)
    intro _
    apply mirrors_bind
    · intro t
      change Primitive.syncResult _ _ (t.liveSnapshot.marker _) _ = _
      rw [mirror_marker]
      exact mirror_sync _ _ _ _ _ (mirror_put _ _)
    intro _ t; rfl
  · intro t; rfl

end WalRecoverySlice.Persistence
