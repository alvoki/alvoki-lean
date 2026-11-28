import Alvoki.Experiments.DurableBlob.FileRead
import Alvoki.Experiments.WAL.Proofs.NativePost
import Alvoki.Experiments.WAL.Segmented.Proofs.NativeReopen

namespace WalRecoverySlice.Segmented.Native
open Alvoki.NativePost System
open Model (Disk)

-- The metadata read can itself fail, and either validation guard can reject it.
-- Only a returned byte read is interpreted against the protected CONTROL binding.
theorem Store.readControl_io (s : Store) {P : W → Prop}
    (md : IOReturns (s.root / "CONTROL").symlinkMetadata w (fun _ t => P t) P)
    (bytes : ∀ t, P t → IOReturns (IO.FS.readBinFile (s.root / "CONTROL")) t
      (fun raw u => P u ∧ raw = ControlCodec.encode c) P)
    (active : c.active ≤ ControlCodec.wordMax) (discarded : c.discarded ≤ ControlCodec.wordMax) :
    Returns s.callbacks.readControl w (fun result t => P t ∧ result = c) P := by
  change Returns (readControlWith controlMetadata (fun path => liftM (IO.FS.readBinFile path)) s.root) _ _ _
  unfold readControlWith controlMetadata
  apply Returns.bind (middle := fun _ t => P t)
  · apply Returns.bind (Returns.liftIO md)
    intro metadata t frame
    exact frame
  · intro metadata t frame
    obtain ⟨regular, size⟩ := metadata
    cases regular
    · exact frame
    · by_cases large : 80 < size
      · simp only [large, ite_true]; exact frame
      · simp only [large, ite_false]
        apply Returns.bind (Returns.liftIO (bytes t frame))
        intro raw u post
        obtain ⟨keep, rfl⟩ := post
        simp only [ControlCodec.decode_encode c active discarded]
        exact ⟨keep, rfl⟩

/-- Read CONTROL from its owned byte binding. Both the no-follow check and
the standard-library byte reader can fail before decoding. -/
theorem Store.readControl_fromFile (s : Store) {P : W → Prop} {state : W → σ}
    {contents : σ → ByteArray}
    (md : IOReturns (s.root / "CONTROL").symlinkMetadata w (fun _ t => P t) P)
    (file : FileRead.Primitives (s.root / "CONTROL") P state contents)
    (binding : ∀ t, P t → contents (state t) = ControlCodec.encode c)
    (active : c.active ≤ ControlCodec.wordMax) (discarded : c.discarded ≤ ControlCodec.wordMax) :
    Returns s.callbacks.readControl w (fun result t => P t ∧ result = c) P := by
  apply s.readControl_io md _ active discarded
  intro t held
  have read := FileRead.readBinFile file held
  unfold IOReturns FileRead.Effect at *
  cases run : IO.FS.readBinFile (s.root / "CONTROL") t with
  | error e u => rw [run] at read; exact read.1
  | ok raw u =>
    rw [run] at read
    exact ⟨read.1, read.2.2.trans (binding t held)⟩

/-- The joint root barrier targets the held directory description. A failed
barrier may already have made the live CONTROL and child names durable. -/
theorem Store.syncRoot_io (s : Store) {disk : W → Disk} {P : W → Prop}
    (sync : IOReturns (syncHandle s.directory) w
      (fun _ t => P t ∧ disk t = (disk w).syncRoot)
      (fun t => P t ∧ (disk t = disk w ∨ disk t = (disk w).syncRoot))) :
    Returns s.callbacks.syncRoot w
      (fun _ t => P t ∧ disk t = (disk w).syncRoot)
      (fun t => P t ∧ (disk t = disk w ∨ disk t = (disk w).syncRoot)) :=
  Returns.liftIO sync

def Keeps (P : W → Prop) (a : IO α) :=
  ∀ w, P w → IOReturns a w (fun _ t => P t) P

private theorem Keeps.forIn (xs : List α) (body : α → β → IO (ForInStep β))
    (frame : ∀ x ∈ xs, ∀ b, Keeps P (body x b)) (b : β) : Keeps P (forIn xs b body) := by
  induction xs generalizing b with
  | nil => exact fun _ h => h
  | cons x tail ih =>
    intro w h
    rw [List.forIn_cons]
    apply IOReturns.bind (frame x (by simp) b w h)
    intro step t kept
    cases step with
    | done => exact kept
    | yield b => exact ih (fun y member => frame y (by simp [member])) b t kept

private theorem Keeps.forM (xs : List α) (body : α → IO PUnit)
    (frame : ∀ x ∈ xs, Keeps P (body x)) : Keeps P (forM xs body) := by
  induction xs with
  | nil => exact fun _ h => h
  | cons x tail ih =>
    intro w h
    rw [List.forM_cons]
    apply IOReturns.bind (frame x (by simp) w h)
    intro _ t kept
    exact ih (fun y member => frame y (by simp [member])) t kept

/-- The checked directory listing supplies individual names directly inside
the listed directory, in any order. A cleanup frame need only protect files
and bindings still selected by CONTROL. An unlink in a retired directory can
leave that directory partially depleted on failure. -/
structure CollectionIO (root : FilePath) (first : Nat) (P : W → Prop) where
  stat : ∀ (path : FilePath), Keeps P path.symlinkMetadata
  list : ∀ dir w, P w → IOReturns (entries dir) w
    (fun items t => P t ∧ ∀ item ∈ items, (dir / item.fileName).parent = some dir) P
  unlink : ∀ id, id < first → ∀ (path : FilePath), path.parent = some (segmentPath root id) →
    Keeps P (IO.FS.removeFile path)
  rmdir : ∀ id, id < first → Keeps P (IO.FS.removeDir (segmentPath root id))

private theorem regular_frame (path : FilePath) (md : IO.FS.Metadata) : Keeps P (regular path md) := by
  unfold regular
  split <;> exact fun _ h => h

private theorem CollectionIO.inspect (io : CollectionIO root first P) (dir : FilePath)
    (hw : P w) : IOReturns (inspectChild dir) w
      (fun items t => P t ∧ ∀ item ∈ items, (dir / item.fileName).parent = some dir) P := by
  unfold inspectChild
  apply IOReturns.bind (io.stat dir w hw)
  intro md t held
  split
  · apply IOReturns.bind (io.list dir t held)
    intro xs u checked
    obtain ⟨valid, names⟩ := checked
    apply IOReturns.bind (middle := fun _ u => P u)
    · rw [← Array.forIn_toList]
      apply Keeps.forIn _ _ _ _ u valid
      intro x _ b state entry
      split
      · apply IOReturns.bind (io.stat _ state entry)
        intro data v hv
        apply IOReturns.bind (regular_frame _ data v hv)
        exact fun _ _ keep => keep
      · exact entry
    · exact fun _ _ keep => ⟨keep, names⟩
  · exact held

private theorem CollectionIO.present (io : CollectionIO root first P) (dir : FilePath) :
    Keeps P (metadata? dir) := by
  intro w owned
  have checked := io.stat dir w owned
  unfold metadata? IOReturns at *
  cases run : dir.symlinkMetadata w with
  | ok md t =>
    rw [run] at checked
    simpa [tryCatch, tryCatchThe, MonadExceptOf.tryCatch, instMonadExceptOfEIO._aux_3, Functor.map, instMonadEIO._aux_1, EST.tryCatch, throw, throwThe, MonadExceptOf.throw, instMonadExceptOfEIO._aux_1, EST.throw, Bind.bind,
      instMonadEIO._aux_13, EST.bind, run, Pure.pure, instMonadEIO._aux_5, EST.pure] using checked
  | error e t =>
    rw [run] at checked
    cases e <;> exact (by
      simpa [tryCatch, tryCatchThe, MonadExceptOf.tryCatch, instMonadExceptOfEIO._aux_3, Functor.map, instMonadEIO._aux_1, EST.tryCatch, throw, throwThe, MonadExceptOf.throw, instMonadExceptOfEIO._aux_1, EST.throw, Bind.bind,
        instMonadEIO._aux_13, EST.bind, run, Pure.pure, instMonadEIO._aux_5, EST.pure] using checked)

theorem CollectionIO.remove (io : CollectionIO root first P) {id : Nat} (retired : id < first) :
    Keeps P (removeSegment root id) := by
  intro w owned
  unfold removeSegment removeSegmentWith
  apply IOReturns.bind (middle := fun _ t => P t)
  · apply IOReturns.bind (io.present _ w owned)
    exact fun _ _ h => h
  intro found t valid
  cases found with
  | false => exact valid
  | true =>
    apply IOReturns.bind (io.inspect _ valid)
    intro items u checked
    apply IOReturns.bind (middle := fun _ v => P v)
    · obtain ⟨frame, names⟩ := checked
      cases items with
      | mk items =>
        change IOReturns (forM items.toArray _) u _ _
        rw [List.forM_toArray]
        apply Keeps.forM _ _ _ u frame
        intro item member
        exact io.unlink id retired _ (names _ (by simpa using member))
    · exact fun _ v frame => io.rmdir id retired v frame

theorem CollectionIO.collect (s : Store) (c : Control) (io : CollectionIO s.root c.firstNeeded P)
    (sync : Keeps P (syncHandle s.directory)) (start : P w) :
    Returns (Segmented.collect s.callbacks c) w (fun _ t => P t) P := by
  have remove (ids : List Nat) (t) (h : P t) :
      Returns (removeRetired s.callbacks c.firstNeeded ids) t (fun _ u => P u) P := by
    induction ids generalizing t with
    | nil => exact h
    | cons id rest ih =>
      unfold removeRetired
      split
      · rename_i retired
        apply Returns.bind (Returns.liftIO (io.remove retired t h))
        exact fun _ v held => ih v held
      · exact ih _ h
  unfold Segmented.collect
  apply Returns.bind (middle := fun _ t => P t)
  · change Returns s.listIds w _ _
    unfold Store.listIds
    apply Returns.bind (Returns.liftIO (io.list s.root w start))
    intro entries t got
    split <;> exact got.1
  intro ids t held
  apply Returns.bind (remove ids t held)
  exact fun _ v valid => Returns.liftIO (sync v valid)

end WalRecoverySlice.Segmented.Native
