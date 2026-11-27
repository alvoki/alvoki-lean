import Alvoki.Experiments.SSTable.Proofs.NativeWrite
import Alvoki.Experiments.SSTable.Proofs.UnifiedNativeReader

namespace ImmutableSSTable.Unified

/-- Interpret the durable contents of the owned output inode. The acquisition
side supplies descriptor identity separately, so reopening by a published
name cannot silently select a different file. -/
def NativeWriteState.readSnapshot [DecidableEq inode] (state : NativeWriteState writer inode)
    (inodeAt : reader → Option inode) : ReadSnapshot reader inode where
  inodeAt
  contents identity := do
    let (recorded, bytes) ← state.durable
    if identity = recorded then some bytes else none

/-- Compose the shared native write and read schedules in their primitive
effect interpretations. The name selection belongs to the caller. The bytes
served by the selected inode come from the successful original-descriptor
sync, and the opened table exposes the actual indexed operations. -/
theorem buildFileWith_open_represents [DecidableEq inode]
    {outputOps : OutputOps (NativeWriteM writer inode) writer}
    {path readPath : System.FilePath}
    {nextRow : NativeWriteM writer inode (Option Entry)}
    {crc : Checksum} {layout : Layout} {options : BuildOptions}
    {before written : NativeWriteState writer inode} {count : Nat}
    {acquire : System.FilePath → IO.FS.Mode → EStateM String σ reader}
    {start acquired : σ} {held : reader} {inodeAt : reader → Option inode}
    (effects : NativeWriteEffects outputOps path nextRow)
    (built : (buildFileWith outputOps crc path layout nextRow id options).run before =
      .ok count written)
    (opened : acquire readPath .read start = .ok held acquired)
    (selected : ∀ output identity, written.BoundTo path output identity →
      inodeAt held = some identity) :
    count = before.rows.length ∧
    ∃ table,
      openCheckedWith ((written.readSnapshot inodeAt).primitives acquire)
        crc readPath layout.tableId start = .ok table acquired ∧
      table.Represents before.rows := by
  obtain ⟨_, countEq, image, output, identity, bound, _, durable, modeled⟩ :=
    buildFileWith_refines effects built
  have contents : (written.readSnapshot inodeAt).contents identity = some written.appended := by
    simp [NativeWriteState.readSnapshot, durable]
  have observed := (written.readSnapshot inodeAt).readsExactly acquire
    (selected output identity bound) contents image.extent
  obtain ⟨_, table, checked, represents⟩ := openCheckedWith_built_table_at modeled opened observed
  exact ⟨countEq, table, checked, represents⟩

end ImmutableSSTable.Unified
