import Alvoki.Experiments.SSTable.Proofs.UnifiedNativeEndToEnd

open ImmutableSSTable ImmutableSSTable.Unified

namespace SSTableProducerCheck

abbrev State := NativeWriteState Unit Nat
abbrev M := NativeWriteM Unit Nat
abbrev Result := EStateM.Result String State

def name : System.FilePath := "sstable"

def primitives : OutputOps M Unit where
  openFile path mode := fun s => match s.binding, mode with
    | none, .writeNew =>
      .ok () { s with
        binding := some (path, 17)
        description := some ((), 17)
        appended := .empty
        flushed := false
        durable := none }
    | _, _ => .error "create" s
  append _ bytes := fun s =>
    .ok () { s with appended := s.appended ++ bytes, flushed := false }
  flush _ := fun s => .ok () { s with flushed := true }
  sync _ := fun s => match s.description, s.flushed with
    | some (_, inode), true => .ok () { s with durable := some (inode, s.appended) }
    | _, _ => .error "sync" s
  remove _ := fun s => .ok () { s with binding := none }

def supplier : M (Option Entry) := fun s =>
  .ok s.rows.head? { s with rows := s.rows.tail }

theorem effects : NativeWriteEffects primitives name supplier := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro before after output run
    cases present : before.binding with
    | none =>
      have observed : (EStateM.Result.ok (ε := String) () { before with
        binding := some (name, 17)
        description := some ((), 17)
        appended := .empty
        flushed := false
        durable := none }) = .ok output after := by
        simpa [primitives, EStateM.run, present] using run
      cases observed
      exact ⟨rfl, 17, rfl⟩
    | some previous =>
      simp [primitives, EStateM.run, present] at run
  · intro output inode bytes before after same run
    cases run
    rfl
  · intro output inode before after same run
    cases run
    rfl
  · intro output inode before after same ready run
    have observed : EStateM.Result.ok (ε := String) () { before with durable := some (inode, before.appended) } =
        .ok () after := by
      simpa [primitives, EStateM.run, same.2, ready] using run
    cases observed
    rfl
  · intro output inode before after row same run
    cases run
    exact ⟨rfl, rfl⟩

def layout : Layout := ⟨some 0, some 0, 123⟩
def targets : BuildOptions := ⟨4, 44⟩
def input : State := { rows := [⟨.empty, .empty⟩] }
def crc : Checksum := fun _ _ => 0

set_option maxHeartbeats 1000000 in
theorem succeeds :
    ∃ after : State, (buildFileWith primitives crc name layout supplier id targets).run input =
      .ok 1 after ∧ after.BoundTo name () 17 := by
  exact ⟨_, rfl, rfl, rfl⟩

theorem produces :
    ∃ after : State, Image crc layout input.rows after.appended ∧
      after.BoundTo name () 17 ∧ after.durable = some (17, after.appended) := by
  obtain ⟨after, run, exactBinding⟩ := succeeds
  obtain ⟨_, _, image, output, inode, bound, _, durable, _⟩ := buildFileWith_refines effects run
  have same := congrArg (Option.map Prod.snd) (bound.1.symm.trans exactBinding.1)
  have inodeEq : inode = 17 := Option.some.inj same
  exact ⟨after, image, exactBinding, by simpa [inodeEq] using durable⟩

def failedSync : OutputOps M Unit :=
  { primitives with
    sync := fun _ s => .error "sync error after effect"
      { s with durable := some (17, s.appended) }
    remove := fun _ s => .error "cleanup error" s }

set_option maxHeartbeats 1000000 in
theorem uncertainResult :
    ∃ after : State, (buildFileWith failedSync crc name layout supplier id targets).run input =
      .error "sync error after effect" after ∧ after.durable = some (17, after.appended) := by
  exact ⟨_, rfl, rfl⟩

/-- A caller can open a separate description of the inode produced by the
actual build schedule and consume the result as a public table. -/
theorem checkedLookup :
    ∃ after : State, ∃ table : Table (EStateM String Unit),
      (buildFileWith primitives crc name layout supplier id targets).run input = .ok 1 after ∧
      openCheckedWith
        ((after.readSnapshot (fun (_ : Nat) => some (17 : Nat))).primitives
          (fun _ _ => (pure (42 : Nat) : EStateM String Unit Nat))) crc name layout.tableId () = .ok table () ∧
      table.lookup .empty = pure (some .empty) := by
  obtain ⟨after, run, binding⟩ := succeeds
  have selected : ∀ output identity, after.BoundTo name output identity →
      (some 17 : Option Nat) = some identity := by
    intro output identity same
    exact congrArg (Option.map Prod.snd) (binding.1.symm.trans same.1)
  obtain ⟨_, table, opened, represents⟩ := buildFileWith_open_represents
    (acquire := fun _ _ => pure (42 : Nat)) (start := ()) (acquired := ())
    (held := 42) (inodeAt := fun _ => some 17) effects run rfl selected
  exact ⟨after, table, run, opened, by simpa [input, Contents.lookup] using represents.lookup .empty⟩

end SSTableProducerCheck
