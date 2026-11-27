namespace Alvoki.Storage

/-- Preserve each selected name's binding, including absence, and the contents
of its bound inode. The observer determines whether contents are live bytes
or a set of permitted durable images. -/
def FileObservationFrame {state name payload : Type}
    (binding : state → name → Option Nat) (contents : state → Nat → payload)
    (selected : name → Prop) (before after : state) : Prop :=
  ∀ key, selected key → binding after key = binding before key ∧
    ∀ inode, binding before key = some inode → contents after inode = contents before inode

theorem FileObservationFrame.trans {binding : state → name → Option Nat} {contents : state → Nat → payload}
    {selected : name → Prop} {before middle after : state}
    (first : FileObservationFrame binding contents selected before middle)
    (last : FileObservationFrame binding contents selected middle after) :
    FileObservationFrame binding contents selected before after := by
  intro key needed
  obtain ⟨same, bytes⟩ := first key needed
  obtain ⟨reached, finalBytes⟩ := last key needed
  exact ⟨reached.trans same, fun inode bound => (finalBytes inode (same.trans bound)).trans (bytes inode bound)⟩

end Alvoki.Storage
