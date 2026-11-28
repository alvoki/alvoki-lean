import Alvoki.Experiments.L0.NativeRead

namespace ExperimentalL0.NativeRead
open ImmutableSSTable Unified

/-- Recovery checks and then discards the opened reader. This action does
not search a data block or evaluate a user-supplied continuation. -/
private theorem checkSource_frame {source : Source (EIO String)} {id : UInt64}
    (safe : ScopedRead P source bytes) :
    ReadPost P (fun _ => True) (withTableSource source id (fun _ => pure ())) := by
  intro w held
  have keep := checkedOpen_frame (crc := Alvoki.CRC32C.extend) (tableId := id) safe w held
  cases ran : openChecked source Alvoki.CRC32C.extend id w with
  | error e t =>
    rw [ran] at keep
    simpa [withTableSource, openTableChecked, Bind.bind, instMonadEIO._aux_13, EST.bind, ran] using keep
  | ok h t =>
    rw [ran] at keep
    simpa [withTableSource, openTableChecked, Bind.bind, instMonadEIO._aux_13, EST.bind, ran,
      Pure.pure, instMonadEIO._aux_5, EST.pure] using keep.1

private theorem checkSource_healthy {source : Source (EIO String)} {id : UInt64} {rows : Rows}
    (built : Image Alvoki.CRC32C.extend (tableLayout id)
      (rows.map (Entry.encode keyCodec mutationCodec)) bytes)
    (available : AvailableRead P source bytes) (w) (held : P w) :
    ∃ t, withTableSource source id (fun _ => pure ()) w = .ok () t ∧ P t := by
  obtain ⟨h, t, ran, frame⟩ := built.checkedOpen_healthy available w held
  change openChecked source Alvoki.CRC32C.extend id w = .ok h t at ran
  exact ⟨t, by simp [withTableSource, openTableChecked, Bind.bind, instMonadEIO._aux_13,
    EST.bind, ran, Pure.pure, instMonadEIO._aux_5, EST.pure], frame⟩

/-- A failed native table check stops recovery at that returned world. Each
successful check supplies the entry condition of the next check. -/
theorem checkTables_post (ops : Tables F) (ids : List UInt64)
    (check : ∀ id ∈ ids, FilePost P (fun _ => True) (ops.check id)) :
    FilePost P (fun _ => True) (checkTables ops ids) := by
  induction ids with
  | nil => exact fun _ held => ⟨held, trivial⟩
  | cons id ids ih =>
    intro w held
    have head := check id (by simp) w held
    simp only [checkTables, ExceptT.run_bind]
    cases ran : (ops.check id).run w with
    | error e t =>
      rw [ran] at head
      simpa [Bind.bind, instMonadEIO._aux_13, EST.bind, ran] using head
    | ok r t =>
      rw [ran] at head
      cases r with
      | error e => simpa [Bind.bind, instMonadEIO._aux_13, EST.bind, ran, Pure.pure, instMonadEIO._aux_5, EST.pure] using head
      | ok _ =>
        simpa [Bind.bind, instMonadEIO._aux_13, EST.bind, ran] using
          ih (fun id mem => check id (.tail _ mem)) t head.1

theorem checkTables_progress {P : W → Prop} (ops : Tables F) (ids : List UInt64)
    (check : ∀ id ∈ ids, ∀ w, P w → ∃ t, (ops.check id).run w = .ok (.ok ()) t ∧ P t)
    (w) (held : P w) :
    ∃ t, (checkTables ops ids).run w = .ok (.ok ()) t ∧ P t := by
  induction ids generalizing w with
  | nil => exact ⟨w, rfl, held⟩
  | cons id ids ih =>
    obtain ⟨t, head, frame⟩ := check id (by simp) w held
    obtain ⟨u, tail, frame⟩ := ih (fun id mem => check id (.tail _ mem)) t frame
    refine ⟨u, ?_, frame⟩
    simp only [checkTables, ExceptT.run_bind]
    simp [Bind.bind, instMonadEIO._aux_13, EST.bind, head, tail]

/-- The concrete check releases each successfully wrapped temporary handle
at the exit of this descriptor scope. -/
theorem checkAt {id : UInt64} (prim : Primitives ns life P)
    (bound : ∀ w, P w → ns.Bound w id rows) (w) (held : P w) :
    (Call.mk ns.directory id .check w).Balanced life ∧
    match (nativeTableAt ns.directory id (fun _ => pure ())).run w with
    | .ok (.ok x) t => P t ∧ (fun _ : Unit => True) x
    | .ok (.error _) t | .error _ t => P t := by
  have scopedCheck := tableAction prim .check (fun _ => True) bound
    (fun h inode bytes _ => checkSource_frame (prim.reads h inode bytes)) w held
  refine ⟨scopedCheck.1, ?_⟩
  have frame := scopedCheck.2
  cases ran : (nativeTableAt ns.directory id (fun _ => pure ())).run w with
  | error => simpa only [ran] using frame
  | ok r t => cases r <;> simpa only [ran] using frame

theorem checkTables_frame (prim : Primitives ns life P) (ops : Tables F)
    (checks : ops.check = fun id => nativeTableAt ns.directory id (fun _ => pure ()))
    (durable : Durable selected history) (catalog : ∀ w, P w → ns.Represents w selected.tables) :
    FilePost P (fun _ => True) (checkTables ops selected.version.tables) := by
  apply checkTables_post
  intro id member w held
  obtain ⟨rows, bound⟩ := durable.boundTable id member
  rw [checks]
  have frame := (checkAt prim (fun u hu => catalog u hu id rows bound) w held).2
  cases ran : (nativeTableAt ns.directory id (fun _ => pure ())).run w with
  | error => simpa only [ran] using frame
  | ok r t => cases r <;> simpa only [ran] using frame

/-- One reached check in the recursive native validation of a manifest.
Passing a head check is required to reach the tail. -/
inductive CheckReached (dir : System.FilePath) : List UInt64 → W → UInt64 → W → Prop where
  | here {id : UInt64} : CheckReached dir (id :: rest) w id w
  | next {id : UInt64} : (nativeTableAt dir id (fun _ => pure ())).run w = .ok (.ok ()) t →
      CheckReached dir rest t target u → CheckReached dir (id :: rest) w target u

theorem checkTables_balanced (prim : Primitives ns life P)
    (durable : Durable selected history) (catalog : ∀ w, P w → ns.Represents w selected.tables)
    (held : P start) (visit : CheckReached ns.directory selected.version.tables start target u) :
    (Call.mk ns.directory target .check u).Balanced life := by
  generalize listEq : selected.version.tables = ids at visit
  have included : ∀ id ∈ ids, id ∈ selected.version.tables := by simp [listEq]
  clear listEq
  induction visit with
  | here =>
    obtain ⟨rows, binding⟩ := durable.boundTable _ (included _ (.head _))
    exact (checkAt prim (fun t ht => catalog t ht _ rows binding) _ held).1
  | next step _ ih =>
    obtain ⟨rows, binding⟩ := durable.boundTable _ (included _ (.head _))
    have frame := (checkAt prim (fun t ht => catalog t ht _ rows binding) _ held).2
    rw [step] at frame
    exact ih frame.1 (fun id mem => included _ (.tail _ mem))

/-- Additional progress inputs are success of the regular-file stat, open,
fstat and bounded pread. Values, frames and inode selection come from the
safety primitives. Reads only need to succeed for the actual owned inode. -/
structure HealthyChecks {ns : TableNamespace W} {life : Lifetime} {P : W → Prop}
    (prim : Primitives ns life P) (ids : List UInt64) : Prop where
  stat : ∀ id ∈ ids, ∀ w, P w → ∃ md t,
    (nativeTableStat (tablePath ns.directory id)).run w = .ok (.ok md) t ∧ isTableFile md = true
  acquire : ∀ id ∈ ids, ∀ w, P w → ∃ h t, IO.FS.Handle.mk (tablePath ns.directory id) .read w = .ok h t
  size : ∀ h inode bytes w, P w → life.privateBorrow h w → prim.inodeOf h w = some inode →
    ns.contents w inode = some bytes → ∃ n t, nativeReadPrimitives.size h w = .ok n t
  pread : ∀ h inode bytes (offset : UInt64) (count : USize) w, P w → life.privateBorrow h w →
    prim.inodeOf h w = some inode → ns.contents w inode = some bytes →
    count.toNat ≤ maxRowSize → offset.toNat + count.toNat ≤ bytes.size →
    ∃ slice t, nativeReadPrimitives.pread h offset count w = .ok slice t

theorem HealthyChecks.available {ns : TableNamespace W} {life : Lifetime} {P : W → Prop}
    {prim : Primitives ns life P} {bytes : ByteArray} (ok : HealthyChecks prim ids)
    (extent : bytes.size ≤ maxFileSize) (h inode) :
    AvailableRead (fun w => P w ∧ life.privateBorrow h w ∧ prim.inodeOf h w = some inode ∧
      ns.contents w inode = some bytes) (handleSource h) bytes := by
  have safe := prim.reads h inode bytes
  constructor
  · intro w held
    obtain ⟨n, t, ran⟩ := ok.size h inode bytes w held.1 held.2.1 held.2.2.1 held.2.2.2
    have post := safe.size w held
    change (handleSource h).size w = .ok n t at ran
    rw [ran] at post
    exact ⟨t, post.2 ▸ ran, post.1⟩
  · intro offset count fits within w held
    have small : maxRowSize < USize.size := by
      rcases System.Platform.numBits_eq with bits | bits <;> simp [USize.size, bits, maxRowSize]
    have countCast := USize.toNat_ofNat_of_lt' (Nat.lt_of_le_of_lt fits small)
    have offsetCast := UInt64.toNat_ofNat_of_lt' (n := offset)
      (Nat.lt_of_le_of_lt (by omega : offset ≤ maxFileSize) (by decide))
    obtain ⟨slice, t, ran⟩ := ok.pread h inode bytes offset.toUInt64 count.toUSize w
      held.1 held.2.1 held.2.2.1 held.2.2.2 (countCast.symm ▸ fits) (by rwa [offsetCast, countCast])
    have step : (handleSource h).readAt offset count w = .ok slice t := by
      simpa only [handleSource, ReadPrimitives.source, Bool.or_eq_true, decide_eq_true_eq,
        Nat.not_lt_of_ge fits, Nat.not_lt_of_ge (Nat.le_trans within extent), or_self, ite_false] using ran
    have post := safe.read offset count w held
    rw [step] at post
    exact ⟨t, post.2 ▸ step, post.1⟩

theorem checkTables_healthy (prim : Primitives ns life P) (ops : Tables F)
    (checks : ops.check = fun id => nativeTableAt ns.directory id (fun _ => pure ()))
    (durable : Durable selected history) (catalog : ∀ w, P w → ns.Represents w selected.tables)
    (ok : HealthyChecks prim selected.version.tables) (w) (held : P w) :
    ∃ t, (checkTables ops selected.version.tables).run w = .ok (.ok ()) t ∧ P t := by
  apply checkTables_progress ops _ _ w held
  intro id member w held
  rw [checks]
  obtain ⟨rows, binding⟩ := durable.boundTable id member
  obtain ⟨md, t, stat, regular⟩ := ok.stat id member w held
  have afterStat := prim.stat (tablePath ns.directory id) w held
  rw [stat] at afterStat
  obtain ⟨inode, bytes, named, stored, built⟩ := catalog t afterStat.1 id rows binding
  obtain ⟨h, u, opened⟩ := ok.acquire id member t afterStat.1
  have borrowed := prim.openRead _ _ _ _ afterStat.1 named stored
  rw [opened] at borrowed
  obtain ⟨v, checked, frame⟩ :=
    checkSource_healthy built (ok.available built.extent h inode) u borrowed
  refine ⟨v, ?_, frame.1⟩
  rw [nativeTableAt_acquired stat regular opened]
  change (BaseIO.toEIO (withTableSource (handleSource h) id (fun _ => pure ())).toBaseIO) u = _
  simp [EIO.toBaseIO, BaseIO.toEIO, checked]

end ExperimentalL0.NativeRead
