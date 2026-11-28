import Alvoki.Experiments.L0.NativeWrite

namespace ExperimentalL0.NativeTableCreate

open System NativeScope
open NativeWrite (checked_bind checked_lift checked_pure checked_throw)

/-- The independently durable directory entries and file contents of the same inodes
whose live bindings the public SSTable reader uses. -/
structure Media (ns : TableNamespace W) where
  names : W → FilePath → Option ns.inode
  contents : W → ns.inode → Option ByteArray

def Media.stable (media : Media ns) : TableNamespace W :=
  ⟨ns.directory, ns.inode, media.names, media.contents⟩

def extend (old : Catalog) (id : UInt64) (rows : Rows) : Catalog :=
  fun key => if key = id then some rows else old key

theorem created {id : UInt64} (fresh : old id = none) : Catalog.Created old (extend old id rows) id rows := by
  refine ⟨fresh, by simp [extend], ?_⟩
  intro other value existing
  by_cases equal : other = id
  · subst other
    rw [fresh] at existing
    contradiction
  · simpa [extend, equal] using existing

abbrev occupied (dir : FilePath) (id : UInt64) : ExceptT String IO Bool :=
  liftM (Native.pathExists (tablePath dir id))

def allocate (dir : FilePath) (next : Nat) : IO UInt64 :=
  Native.checked (freeTableId (occupied dir) next)

theorem allocate_step (dir : FilePath) (next : Nat) :
    allocate dir next =
      if next ≥ UInt64.size then throw (IO.userError "table IDs exhausted")
      else (do
        if ← Native.pathExists (tablePath dir next.toUInt64) then allocate dir (next + 1)
        else return next.toUInt64 : IO UInt64) := by
  unfold allocate
  rw [freeTableId]
  split
  · simp_all only [checked_throw]
  · simp_all only [checked_bind, occupied, checked_lift]
    apply congrArg (Bind.bind _)
    funext b
    cases b <;> simp only [Bool.false_eq_true, ↓reduceIte, checked_pure]

theorem create_schedule (dir : FilePath) (rows : Rows) :
    Native.checked (Native.createTable dir rows) =
      (do
        let id ← allocate dir 0
        Native.buildSynced (tablePath dir id) id rows
        IO.FS.withFile dir .read Native.syncHandle
        return id : IO UInt64) := by
  unfold Native.createTable createTableUnder createTableAt
  rw [checked_bind]
  apply congrArg (Bind.bind _)
  funext id
  simp only [checked_bind, checked_lift, checked_pure]

/-- An occupied probe includes an unreachable orphan. Only a missing name
at the stat that just returned authorizes attempting exclusive creation. -/
structure Probe (ns : TableNamespace W) (P : W → Prop) : Prop where
  stat : ∀ id w, P w →
    match (tablePath ns.directory id).symlinkMetadata w with
    | .ok _ t => P t
    | .error (.noFileOrDirectory ..) t => P t ∧ ns.names t (tablePath ns.directory id) = none
    | .error _ t => P t

theorem Probe.checked (ops : Probe ns P) (id : UInt64) (pw : P w) :
    Post (Native.pathExists (tablePath ns.directory id)) w
      (fun b t => P t ∧ (b = false → ns.names t (tablePath ns.directory id) = none)) (fun _ => P) := by
  have stat := ops.stat id w pw
  unfold Native.pathExists Post
  simp only [MonadExceptOf.tryCatch, instMonadExceptOfEIO._aux_3, EST.tryCatch,
    Bind.bind, instMonadEIO._aux_13, EST.bind]
  cases ran : (tablePath ns.directory id).symlinkMetadata w with
  | ok md t => simp_all [Pure.pure, instMonadEIO._aux_5, EST.pure]
  | error e t =>
    rw [ran] at stat
    cases e <;> simp_all [Pure.pure, instMonadEIO._aux_5, EST.pure,
      throw, throwThe, MonadExceptOf.throw, instMonadExceptOfEIO._aux_1, EST.throw]

theorem allocate_fresh (ops : Probe ns P) (next : Nat) (pw : P w) :
    Post (allocate ns.directory next) w
      (fun id t => P t ∧ ns.names t (tablePath ns.directory id) = none) (fun _ => P) := by
  rw [allocate_step]
  split
  · exact pw
  · apply Post.bind
    apply (ops.checked next.toUInt64 pw).weaken
    · intro occupied t previous
      cases occupied with
      | false => exact ⟨previous.1, previous.2 rfl⟩
      | true => exact allocate_fresh ops (next + 1) previous.1
    · exact fun _ _ keep => keep
termination_by UInt64.size - next
decreasing_by omega

/-- A prefix consists exactly of earlier successful occupied probes. The
first exception, absent name, or exhausted counter terminates the search. -/
inductive Visited (dir : FilePath) (origin : W) : Nat → W → Prop where
  | start : Visited dir origin 0 origin
  | next : Visited dir origin n w → n < UInt64.size →
      Native.pathExists (tablePath dir n.toUInt64) w = .ok true t → Visited dir origin (n+1) t

theorem Visited.resume (path : Visited dir origin n w) : allocate dir 0 origin = allocate dir n w := by
  induction path with
  | start => rfl
  | next prior fits ran ih =>
    apply ih.trans
    rw [allocate_step]
    simp only [Nat.not_le_of_gt fits, ↓reduceIte, Bind.bind, instMonadEIO._aux_13, EST.bind, ran]

theorem Visited.frame (ops : Probe ns P) (path : Visited ns.directory origin n w) (start : P origin) : P w := by
  induction path with
  | start => exact start
  | next prior fits ran ih =>
    rename_i index front finish
    have reached := ops.checked index.toUInt64 ih
    rw [Post, ran] at reached
    exact reached.1

end ExperimentalL0.NativeTableCreate
