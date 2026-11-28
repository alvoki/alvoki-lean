import Alvoki.Experiments.L0.NativeTableAllocation

namespace ExperimentalL0.NativeTableCreate

open System NativeScope ImmutableSSTable Unified

/-- The original writer's fsynced bytes are still named by the freshly
allocated path. Directory opening must preserve this inode and its bytes. -/
structure FileAt {ns : TableNamespace W} (media : Media ns) (id : UInt64)
    (inode : ns.inode) (bytes : ByteArray) (w : W) : Prop where
  named : ns.names w (tablePath ns.directory id) = some inode
  visible : ns.contents w inode = some bytes
  synced : media.contents w inode = some bytes

/-- The opened description is for the protected table directory. A
successful fsync of that description makes its current name durable. A
failed fsync may already have installed the unreferenced table name. -/
structure Directory {ns : TableNamespace W} (media : Media ns) (P : W → Prop) where
  bound : IO.FS.Handle → W → Prop
  opened : ∀ id ino bytes w, P w → FileAt media id ino bytes w →
    Post (IO.FS.Handle.mk ns.directory .read) w
      (fun fd t => P t ∧ bound fd t ∧ FileAt media id ino bytes t) (fun _ => P)
  sync : ∀ id ino bytes fd w, P w → bound fd w →
    (∃ before, IO.FS.Handle.mk ns.directory .read before = .ok fd w) →
    FileAt media id ino bytes w → Post (Native.syncHandle fd) w
      (fun _ t => P t ∧ FileAt media id ino bytes t ∧ media.names t (tablePath ns.directory id) = some ino)
      (fun _ => P)

def Persisted {ns : TableNamespace W} (media : Media ns) (id : UInt64) (rows : Rows) (w : W) : Prop :=
  ∃ ino bytes, FileAt media id ino bytes w ∧ media.names w (tablePath ns.directory id) = some ino ∧
    Image Alvoki.CRC32C.extend (tableLayout id) (rows.map (Entry.encode keyCodec mutationCodec)) bytes

structure Created {ns : TableNamespace W} (media : Media ns) (old : Catalog) (rows : Rows) (id : UInt64) (t : W) : Prop where
  fresh : Catalog.Created old (extend old id rows) id rows
  persisted : Persisted media id rows t
  live : ns.Represents t (extend old id rows)
  durable : media.stable.Represents t (extend old id rows)

theorem Persisted.created {ns : TableNamespace W} {media : Media ns} {id : UInt64} (saved : Persisted media id rows t)
    (fresh : old id = none) (live : ns.Represents t old) (durable : media.stable.Represents t old) :
    Created (ns := ns) media old rows id t := by
  obtain ⟨ino, bytes, file, name, image⟩ := saved
  refine ⟨NativeTableCreate.created fresh, ⟨ino, bytes, file, name, image⟩, ?_, ?_⟩
  · exact live.insert (fun _ _ _ _ _ n b => ⟨n,b⟩) ⟨ino,bytes,file.named,file.visible,image⟩
  · exact durable.insert (fun _ _ _ _ _ n b => ⟨n,b⟩) ⟨ino,bytes,name,file.synced,image⟩

/-- The file image proof is supplied by the streaming builder. Neither
directory syscall has a logical SSTable postcondition. -/
theorem Directory.install {ns : TableNamespace W} {media : Media ns} {inode : ns.inode} {id : UInt64} (io : Directory media P) (pw : P w)
    (file : FileAt media id inode bytes w)
    (image : Image Alvoki.CRC32C.extend (tableLayout id) (rows.map (Entry.encode keyCodec mutationCodec)) bytes) :
    Post (IO.FS.withFile ns.directory .read Native.syncHandle) w
      (fun _ t => P t ∧ Persisted (ns := ns) media id rows t) (fun _ => P) := by
  have opened := io.opened id inode bytes w pw file
  unfold IO.FS.withFile Post
  simp only [Bind.bind, instMonadEIO._aux_13, EST.bind]
  cases ran : IO.FS.Handle.mk ns.directory .read w with
  | error e t =>
    rw [Post, ran] at opened
    exact opened
  | ok fd t =>
    rw [Post, ran] at opened
    have settled := io.sync id inode bytes fd t opened.1 opened.2.1 ⟨w,ran⟩ opened.2.2
    exact settled.weaken (fun _ _ p => ⟨p.1,inode,bytes,p.2.1,p.2.2,image⟩) (fun _ _ keep => keep)

/-- The native result entails the exact returning allocation, streaming
file operation, directory open, and sync of that returned description. -/
theorem success_path {id : UInt64}
    (ran : Native.checked (Native.createTable dir rows) start = .ok id finish) :
    ∃ reserved built fd opened, allocate dir 0 start = .ok id reserved ∧
      Native.buildSynced (tablePath dir id) id rows reserved = .ok () built ∧
      IO.FS.Handle.mk dir .read built = .ok fd opened ∧ Native.syncHandle fd opened = .ok () finish := by
  rw [create_schedule] at ran
  unfold IO.FS.withFile at ran
  simp only [Bind.bind, instMonadEIO._aux_13, EST.bind] at ran
  cases alloc : allocate dir 0 start with
  | error e t => simp [alloc] at ran
  | ok number reserved =>
    simp only [alloc] at ran
    cases build : Native.buildSynced (tablePath dir number) number rows reserved with
    | error e t => simp [build] at ran
    | ok value built =>
      simp only [build] at ran
      cases acquire : IO.FS.Handle.mk dir .read built with
      | error e t => simp [acquire] at ran
      | ok fd entered =>
        simp only [acquire] at ran
        cases barrier : Native.syncHandle fd entered with
        | error e t => simp [barrier] at ran
        | ok value synced =>
          simp only [barrier, Pure.pure, instMonadEIO._aux_5, EST.pure, EST.Out.ok.injEq] at ran
          obtain ⟨rfl,rfl⟩ := ran
          exact ⟨reserved,built,fd,entered,rfl,build,acquire,barrier⟩

end ExperimentalL0.NativeTableCreate
