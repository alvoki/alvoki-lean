import PackedTable
import WriteAheadLog

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

private theorem replayWrite_advances {state result : PackedTable} {event : Write}
    (applied : replayWrite state event = .ok result) :
    result.committed.toNat = state.committed.toNat + 1 := by
  unfold replayWrite prepareWrite at applied
  cases written : state.write event.key event.value with
  | none => simp [written] at applied
  | some next =>
    simp only [written, Option.map_some] at applied
    split at applied
    · cases applied
      unfold PackedTable.write at written
      split at written
      · rename_i fits
        cases written
        exact UInt64.toNat_ofNat_of_lt' fits
      · contradiction
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

theorem replay_append {initial committed : PackedTable} {acknowledged : List Write}
    (safe : replay initial acknowledged = .ok committed) (extra : List Write) :
    replay initial (acknowledged ++ extra) = replay committed extra := by
  simp only [replay, List.foldlM_append]
  unfold replay at safe
  rw [safe]
  rfl

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
      unfold replayWrite prepareWrite at step
      cases written : right.write event.key event.value with
      | none => simp [written] at step
      | some after =>
        simp only [written, Option.map_some] at step
        split at step
        · rename_i sequence
          cases step
          obtain ⟨replayed, sameWrite, relation⟩ := same.write written
          have accepted : replayWrite left event = .ok replayed := by
            unfold replayWrite prepareWrite
            simp [sameWrite, relation.committed, sequence]
          rw [accepted]
          change ∃ reopened, replay replayed rest = .ok reopened ∧ reopened.SameData result
          exact ih relation applied
        · contradiction

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

/-- The current disk format keeps all selected frames, starting at sequence 1. -/
def recoverSelected (state : PackedTable) (bytes : ByteArray) : Except String PackedTable := do
  let table ← recoverCheckpoint state bytes
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
    (old : ∀ e ∈ covered, e.sequence ≤ state.committed)
    (new : ∀ e ∈ pending, state.committed < e.sequence)
    (count : covered.length = state.committed.toNat) :
    recoverSelected state (WAL.encode (covered ++ pending)) = replay state pending := by
  have decoded := recoverCheckpoint_suffix state covered pending old new ByteArray.empty (by decide)
  rw [ByteArray.append_empty] at decoded
  unfold recoverSelected
  rw [decoded]
  cases applied : replay state pending with
  | error => rfl
  | ok table =>
    have frames : (WAL.encode (covered ++ pending)).size / frameSize = covered.length + pending.length := by
      rw [WAL.encode_size, Nat.mul_div_cancel_left _ (by decide : 0 < frameSize), List.length_append]
    have guard : table.committed.toNat = (WAL.encode (covered ++ pending)).size / frameSize := by
      rw [replay_committed_count pending applied, ← count, frames]
    change (if table.committed.toNat == _ then Except.ok table else Except.error _) = _
    simp [guard]

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
