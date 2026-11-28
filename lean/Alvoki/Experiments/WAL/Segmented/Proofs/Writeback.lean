import Alvoki.Experiments.WAL.Segmented.Proofs.Invariant
import Alvoki.Experiments.WAL.Writeback

namespace WalRecoverySlice.Segmented

open Model (Disk)
open Persistence (WalFile)

/-- A selected sealed segment already has its durable image. Writeback can
therefore change a selected file only in the active segment, where the
single-segment recovery invariant admits that exact file's settlement. -/
theorem Readable.writeback {control history pending disk} (readable : Readable control history pending disk)
    (id : Nat) (file : WalFile) : Readable control history pending (disk.writeback id file) := by
  refine ⟨readable.layout.frame readable.layout.names ?_, readable.room, ?_⟩
  · intro i selected sealed
    by_cases hit : i = id
    · simpa [Disk.writeback, hit] using (readable.layout.sealed i selected sealed).writeback file
    · simp [Disk.writeback, hit]
  · by_cases hit : control.active = id
    · simpa [Disk.writeback, hit] using
        readable.active.settle file
    · simpa [Disk.writeback, hit] using readable.active

/-- Each authority keeps its own file-selection invariant across the same
physical writeback, including when the two controls select different active IDs. -/
theorem Recoverable.writeback {known request disk} (recoverable : Recoverable known request disk)
    (id : Nat) (file : WalFile) : Recoverable known request (disk.writeback id file) := by
  have preserve {c} (choice : RecoveryChoice known request c disk) :
      RecoveryChoice known request c (disk.writeback id file) := by
    obtain ⟨history, pending, readable, permitted⟩ := choice
    exact ⟨history, pending, readable.writeback id file, permitted⟩
  obtain ⟨c, live, chosen⟩ := recoverable.live
  obtain ⟨d, durable, other⟩ := recoverable.durable
  exact ⟨⟨c, live, preserve chosen⟩, ⟨d, durable, preserve other⟩⟩

inductive Writebacks (initial : Disk) :
    Disk → Prop where
  | nil : Writebacks initial initial
  | next : Writebacks initial middle → ∀ id file, Writebacks initial (middle.writeback id file)

theorem Writebacks.trans {finish : Disk} (a : Writebacks start middle) (b : Writebacks middle finish) :
    Writebacks start finish := by
  induction b with
  | nil => exact a
  | next _ id file ih => exact .next ih id file

/-- Selected files of an installed WAL child are clean after open. Whole-file
writeback on any other segment may change its durable bytes. -/
theorem Writebacks.installed (steps : Writebacks before after)
    (held : Installed child before) :
    Installed child after := by
  induction steps with
  | nil => exact held
  | @next middle _ id file ih =>
    obtain ⟨history, canonical, ready, live, durable⟩ := ih
    refine ⟨history, canonical, ready.frame ready.layout.names ?_ rfl, live, durable⟩
    intro i selects
    by_cases hit : i = id
    · have le := selects.2
      rcases Nat.eq_or_lt_of_le le with eq | lt
      · simp only [Disk.writeback, hit, ite_true]
        simpa only [← hit, eq] using ready.active.toSettled.writeback file
      · simpa [Disk.writeback, hit] using
          (ready.layout.sealed i selects lt).writeback file
    · simp [Disk.writeback, hit]

theorem Writebacks.live (steps : Writebacks before after) : after.liveControl = before.liveControl := by
  induction steps <;> first | rfl | assumption

theorem Writebacks.durable (steps : Writebacks before after) : after.durableControl = before.durableControl := by
  induction steps <;> first | rfl | assumption

theorem Writebacks.readable (steps : Writebacks before after) (entry : Readable c history pending before) :
    Readable c history pending after := by
  induction steps with
  | nil => exact entry
  | next _ id file ih => exact ih.writeback id file

theorem Writebacks.recoverable (steps : Writebacks before after) (entry : Recoverable known request before) :
    Recoverable known request after := by
  induction steps with
  | nil => exact entry
  | next _ id file ih => exact ih.writeback id file

theorem Writebacks.settled {id : Nat} (steps : Writebacks before after)
    (clean : Child.Settled p (before.segment id) bs) : after.segment id = before.segment id := by
  induction steps with
  | nil => rfl
  | next _ other file ih =>
    by_cases hit : id = other
    · subst other; simpa [Disk.writeback, ih] using clean.writeback file
    · simpa [Disk.writeback, hit] using ih

end WalRecoverySlice.Segmented
