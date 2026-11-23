import Alvoki.Storage.Table.PackedTable
import Alvoki.Storage.Disk.WriteAheadLog

namespace Alvoki.Storage
open Alvoki.WAL

/-- Compute the next state and its WAL event together. Publication may occur after the event is durable. -/
def prepareWrite (state : PackedTable) (key : UInt64) (value : Option UInt64) :
    Option (Write × PackedTable) :=
  (state.write key value).map fun result => (⟨result.committed, key, value⟩, result)

/-- Replay must use exactly the same sequence allocation as the write path. -/
def replayWrite (state : PackedTable) (event : Write) : Except String PackedTable :=
  match prepareWrite state event.key event.value with
  | none => .error "WAL sequence space exhausted"
  | some (expected, result) =>
    if expected.sequence = event.sequence then .ok result else .error "nonconsecutive WAL sequence"

def replay (state : PackedTable) (events : List Write) : Except String PackedTable :=
  events.foldlM replayWrite state

def recoverFrom (state : PackedTable) (bytes : ByteArray) : Except String PackedTable :=
  match WAL.decode bytes with
  | .error message => .error message
  | .ok events => replay state events

def recover (bytes : ByteArray) : Except String PackedTable := recoverFrom .empty bytes

theorem replay_prepared {state next : PackedTable} {key : UInt64} {value : Option UInt64}
    {event : Write} (prepared : prepareWrite state key value = some (event, next)) :
    replayWrite state event = .ok next := by
  unfold prepareWrite at prepared
  obtain ⟨result, success, same⟩ := Option.map_eq_some_iff.mp prepared
  cases same
  unfold replayWrite prepareWrite
  simp [success]

private theorem replayWrite_spec {state result : PackedTable} {event : Write}
    (applied : replayWrite state event = .ok result) :
    state.write event.key event.value = some result ∧ result.committed = event.sequence := by
  unfold replayWrite prepareWrite at applied
  cases written : state.write event.key event.value with
  | none => simp [written] at applied
  | some next =>
    simp only [written, Option.map_some] at applied
    split at applied
    · rename_i sequence
      cases applied
      exact ⟨rfl, sequence⟩
    · contradiction

private theorem replayWrite_advances {state result : PackedTable} {event : Write}
    (applied : replayWrite state event = .ok result) :
    result.committed.toNat = state.committed.toNat + 1 := by
  have written := (replayWrite_spec applied).1
  unfold PackedTable.write at written
  split at written
  · rename_i fits
    cases written
    exact UInt64.toNat_ofNat_of_lt' fits
  · contradiction

theorem replay_committed_count {state result : PackedTable} (events : List Write)
    (applied : replay state events = .ok result) :
    result.committed.toNat = state.committed.toNat + events.length := by
  induction events generalizing state with
  | nil =>
    change Except.ok state = Except.ok result at applied
    cases applied
    simp
  | cons event rest ih =>
    unfold replay at applied
    rw [List.foldlM_cons] at applied
    cases step : replayWrite state event with
    | error message =>
      rw [step] at applied
      change Except.error message = Except.ok result at applied
      contradiction
    | ok next =>
      rw [step] at applied
      change replay next rest = .ok result at applied
      simp only [ih applied, replayWrite_advances step, List.length_cons]
      omega

/-- Each correctly numbered event supplies a representable next sequence, so
replaying a contiguous suffix cannot hit the write path's exhaustion guard. -/
theorem replay_ordinals_complete (state : PackedTable) (events : List Write)
    (ordinals : WAL.OrdinalsFrom (state.committed.toNat + 1) events) :
    ∃ result, replay state events = .ok result ∧
      result.committed.toNat = state.committed.toNat + events.length := by
  have succeeds : ∃ result, replay state events = .ok result := by
    induction events generalizing state with
    | nil => exact ⟨state, rfl⟩
    | cons event rest ih =>
      obtain ⟨sequence, remaining⟩ := ordinals
      have fits : state.committed.toNat + 1 < UInt64.size :=
        sequence ▸ event.sequence.toNat_lt_size
      have sequenceMatches : UInt64.ofNat (state.committed.toNat + 1) = event.sequence :=
        UInt64.toNat_inj.mp ((UInt64.toNat_ofNat_of_lt' fits).trans sequence.symm)
      have canReplay : ∃ next, replayWrite state event = .ok next := by
        simp [replayWrite, prepareWrite, PackedTable.write, fits, sequenceMatches]
      obtain ⟨next, step⟩ := canReplay
      have numbered : WAL.OrdinalsFrom (next.committed.toNat + 1) rest := by
        rwa [replayWrite_advances step]
      obtain ⟨result, applied⟩ := ih next numbered
      refine ⟨result, ?_⟩
      unfold replay
      rw [List.foldlM_cons, step]
      exact applied
  obtain ⟨result, applied⟩ := succeeds
  exact ⟨result, applied, replay_committed_count events applied⟩

theorem replay_append {initial committed : PackedTable} {acknowledged : List Write}
    (safe : replay initial acknowledged = .ok committed) (extra : List Write) :
    replay initial (acknowledged ++ extra) = replay committed extra := by
  simp only [replay, List.foldlM_append]
  unfold replay at safe
  rw [safe]
  rfl

/-- The abstract table applies exactly the listed WAL writes in order. Each
step uses the recorded key and value and commits the recorded sequence. -/
inductive SnapshotWalReplay : Sequential.SnapshotTable UInt64 → List Write →
    Sequential.SnapshotTable UInt64 → Prop where
  | nil (state : Sequential.SnapshotTable UInt64) : SnapshotWalReplay state [] state
  | cons {before next after : Sequential.SnapshotTable UInt64} {event : Write} {rest : List Write}
      (written : before.write event.key event.value = some next)
      (sequence : next.committed = event.sequence) (suffix : SnapshotWalReplay next rest after) :
      SnapshotWalReplay before (event :: rest) after

theorem replay_refines {state result : PackedTable} {model : Sequential.SnapshotTable UInt64}
    {events : List Write} (same : state.Refines model) (applied : replay state events = .ok result) :
    ∃ after, SnapshotWalReplay model events after ∧ result.Refines after := by
  induction events generalizing state model with
  | nil =>
    change Except.ok state = Except.ok result at applied
    cases applied
    exact ⟨model, .nil model, same⟩
  | cons event rest ih =>
    unfold replay at applied
    rw [List.foldlM_cons] at applied
    cases step : replayWrite state event with
    | error message =>
      rw [step] at applied
      change Except.error message = Except.ok result at applied
      contradiction
    | ok next =>
      rw [step] at applied
      change replay next rest = .ok result at applied
      obtain ⟨written, sequence⟩ := replayWrite_spec step
      obtain ⟨nextModel, nextWrite, nextSame⟩ := PackedTable.write_refines same written
      obtain ⟨after, suffix, refined⟩ := ih nextSame applied
      exact ⟨after, .cons nextWrite (nextSame.committed.symm.trans sequence) suffix, refined⟩

theorem replay_sameData {left right result : PackedTable} (same : left.SameData right)
    (events : List Write) (applied : replay right events = .ok result) :
    ∃ reopened, replay left events = .ok reopened ∧ reopened.SameData result := by
  induction events generalizing left right with
  | nil =>
    change Except.ok right = Except.ok result at applied
    cases applied
    exact ⟨left, rfl, same⟩
  | cons event rest ih =>
    unfold replay at applied ⊢
    rw [List.foldlM_cons] at applied ⊢
    cases step : replayWrite right event with
    | error message =>
      rw [step] at applied
      change Except.error message = Except.ok result at applied
      contradiction
    | ok next =>
      rw [step] at applied
      change replay next rest = .ok result at applied
      obtain ⟨written, sequence⟩ := replayWrite_spec step
      obtain ⟨replayed, sameWrite, relation⟩ := same.write written
      have accepted : replayWrite left event = .ok replayed := by
        simp [replayWrite, prepareWrite, sameWrite, relation.committed, sequence]
      rw [accepted]
      change ∃ reopened, replay replayed rest = .ok reopened ∧ reopened.SameData result
      exact ih relation applied

/-- A torn tail has no effect on replay of the complete frames preceding it. -/
theorem recover_prefix (initial : PackedTable) (events : List Write) (tail : ByteArray)
    (incomplete : tail.size < frameSize) :
    recoverFrom initial (WAL.encode events ++ tail) = replay initial events := by
  rw [recoverFrom, decode_ignores_incomplete_tail _ _ incomplete]

/-- Given a durable acknowledged prefix, later complete events may also survive.
A final partial frame never applies a write. -/
theorem recover_acknowledged {initial committed : PackedTable} {acknowledged : List Write}
    (safe : replay initial acknowledged = .ok committed) (extra : List Write)
    (tail : ByteArray) (incomplete : tail.size < frameSize) :
    recoverFrom initial (WAL.encode (acknowledged ++ extra) ++ tail) = replay committed extra := by
  rw [recover_prefix _ _ _ incomplete, replay_append safe]

private def afterCheckpoint (checkpoint : UInt64) (events : List Write) : List Write :=
  events.filter (fun event => checkpoint < event.sequence)

def recoverCheckpoint (state : PackedTable) (bytes : ByteArray) : Except String PackedTable :=
  match WAL.decode bytes with
  | .error message => .error message
  | .ok events => replay state (afterCheckpoint state.committed events)

/-- The disk format keeps all selected frames, including those already stored
in the checkpoint. Each frame's position determines its expected sequence. -/
def recoverSelected (state : PackedTable) (bytes : ByteArray) : Except String PackedTable := do
  let events ← WAL.decodeOrdinals bytes
  let table ← replay state (events.drop state.committed.toNat)
  if table.committed.toNat == bytes.size / frameSize then .ok table
  else .error "selected WAL frame count disagrees with the recovered sequence"

theorem recoverCheckpoint_repair (state : PackedTable) (bytes : ByteArray) :
    recoverCheckpoint state ((WAL.repairPrefix bytes).getD bytes) = recoverCheckpoint state bytes := by
  simp only [recoverCheckpoint, WAL.decode_repairPrefix]

/-- Events covered by the installed run set are skipped. The contiguous suffix
passes through the ordinary sequence-checking replay worker. -/
theorem recoverCheckpoint_suffix (state : PackedTable) (installed later : List Write)
    (covered : ∀ e ∈ installed, e.sequence ≤ state.committed)
    (pending : ∀ e ∈ later, state.committed < e.sequence)
    (tail : ByteArray) (incomplete : tail.size < frameSize) :
    recoverCheckpoint state (WAL.encode (installed ++ later) ++ tail) = replay state later := by
  rw [recoverCheckpoint, decode_ignores_incomplete_tail _ _ incomplete]
  unfold afterCheckpoint
  simp only [List.filter_append]
  have old : installed.filter (fun event => decide (state.committed < event.sequence)) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro e mem h
    exact UInt64.not_lt.mpr (covered e mem) (of_decide_eq_true h)
  have new : later.filter (fun event => decide (state.committed < event.sequence)) = later :=
    List.filter_eq_self.mpr fun e mem => decide_eq_true (pending e mem)
  simp [old, new]

theorem recoverSelected_encoded (state : PackedTable) (covered pending : List Write)
    (ordinals : WAL.OrdinalsFrom 1 (covered ++ pending))
    (count : covered.length = state.committed.toNat) :
    recoverSelected state (WAL.encode (covered ++ pending)) = replay state pending := by
  rw [recoverSelected, WAL.decodeOrdinals_encode _ ordinals]
  change (do
    let table ← replay state ((covered ++ pending).drop state.committed.toNat)
    if table.committed.toNat == (WAL.encode (covered ++ pending)).size / frameSize then .ok table
    else .error "selected WAL frame count disagrees with the recovered sequence") = _
  rw [← count, List.drop_left]
  cases applied : replay state pending with
  | error => rfl
  | ok table =>
    have frames : (WAL.encode (covered ++ pending)).size / frameSize = covered.length + pending.length := by
      rw [WAL.encode_size, Nat.mul_div_cancel_left _ (by decide : 0 < frameSize), List.length_append]
    have guard : table.committed.toNat = (WAL.encode (covered ++ pending)).size / frameSize := by
      rw [replay_committed_count pending applied, ← count, frames]
    change (if table.committed.toNat == _ then Except.ok table else Except.error _) = _
    simp [guard]

private theorem ordinals_append_right (start : Nat) (covered pending : List Write)
    (ordinals : WAL.OrdinalsFrom start (covered ++ pending)) :
    WAL.OrdinalsFrom (start + covered.length) pending := by
  induction covered generalizing start with
  | nil => simpa using ordinals
  | cons event rest ih =>
    have next : start + (event :: rest).length = (start + 1) + rest.length := by
      simp only [List.length_cons]
      omega
    rw [next]
    exact ih (start + 1) ordinals.2

/-- The production selected-WAL loader succeeds if the checkpoint watermark
matches the covered length and the complete selected history is consecutive. -/
theorem recoverSelected_encoded_complete (state : PackedTable) (covered pending : List Write)
    (ordinals : WAL.OrdinalsFrom 1 (covered ++ pending))
    (count : covered.length = state.committed.toNat) :
    ∃ result, recoverSelected state (WAL.encode (covered ++ pending)) = .ok result ∧
      result.committed.toNat = covered.length + pending.length := by
  have numbered : WAL.OrdinalsFrom (state.committed.toNat + 1) pending := by
    simpa only [count, Nat.add_comm 1 state.committed.toNat] using
      ordinals_append_right 1 covered pending ordinals
  rw [recoverSelected_encoded state covered pending ordinals count, count]
  exact replay_ordinals_complete state pending numbered

/-- Reopening a flushed run set and replaying the durable suffix preserves
the committed data and floor, including when a final frame is incomplete. -/
theorem recoverPublished {checkpoint restored committed : PackedTable}
    (flushed : checkpoint.memory = Alvoki.Sequential.History.empty)
    (loaded : PackedTable.restore checkpoint.runs checkpoint.committed checkpoint.pins.floor = some restored)
    (installed later : List Write)
    (covered : ∀ e ∈ installed, e.sequence ≤ checkpoint.committed)
    (pending : ∀ e ∈ later, checkpoint.committed < e.sequence)
    (applied : replay checkpoint later = .ok committed) (tail : ByteArray)
    (incomplete : tail.size < frameSize) :
    ∃ reopened, recoverCheckpoint restored (WAL.encode (installed ++ later) ++ tail) = .ok reopened ∧
      reopened.SameData committed := by
  have same := PackedTable.restore_sameData flushed loaded
  rw [recoverCheckpoint_suffix restored installed later
    (by simpa only [same.committed] using covered)
    (by simpa only [same.committed] using pending) tail incomplete]
  exact replay_sameData same later applied

end Alvoki.Storage
