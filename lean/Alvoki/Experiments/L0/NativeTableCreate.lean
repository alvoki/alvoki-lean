import Alvoki.Experiments.L0.NativeTableDirectory
import Alvoki.Experiments.L0.NativeTableWriter

namespace ExperimentalL0.NativeTableCreate

open System NativeScope

/-- A primitive issued during table creation. A later stage requires the
actual preceding returns; the interrupted primitive needs no return value. -/
inductive Visits (dir : FilePath) (rows : Rows) (origin : W) : {α : Type} → IO α → W → Prop where
  | probe : Visited dir origin n w → n < UInt64.size →
      Visits dir rows origin (tablePath dir n.toUInt64).symlinkMetadata w
  | writer {id : UInt64} : allocate dir 0 origin = .ok id reserved →
      NativeTableWriter.Visits (tablePath dir id) id rows reserved leaf w →
      Visits dir rows origin leaf.action w
  | directory {id : UInt64} : allocate dir 0 origin = .ok id reserved →
      Native.buildSynced (tablePath dir id) id rows reserved = .ok () built →
      Visits dir rows origin (IO.FS.Handle.mk dir .read) built
  | sync {id : UInt64} : allocate dir 0 origin = .ok id reserved →
      Native.buildSynced (tablePath dir id) id rows reserved = .ok () built →
      IO.FS.Handle.mk dir .read built = .ok fd entered →
      Visits dir rows origin (Native.syncHandle fd) entered

/-- Failure and interruption leave the caller's old protected resources.
Only success exposes the newly durable catalog entry. Private names and
partial bytes outside that catalog are unrestricted. -/
structure Produced {ns : TableNamespace W} (media : Media ns) (old : Catalog) (P : W → Prop)
    (rows : Rows) (origin : W) : Prop where
  returned : Post (Native.checked (Native.createTable ns.directory rows)) origin
    (fun id t => P t ∧ Created media old rows id t) (fun _ => P)
  visited : ∀ {α : Type} {a : IO α} {last}, Visits ns.directory rows origin a last → P last

private theorem withReport {ok : α → W → Prop} (result : Post act w ok err) :
    Post act w (fun x t => act w = .ok x t ∧ ok x t) err := by
  unfold Post at *
  cases ran : act w with
  | ok x t => exact ⟨rfl,by simpa only [ran] using result⟩
  | error e t => simpa only [ran] using result

private theorem freshCatalog {ns : TableNamespace W} {old : Catalog} {id : UInt64} (live : ns.Represents w old)
    (missing : ns.names w (tablePath ns.directory id) = none) : old id = none := by
  cases bound : old id with
  | none => rfl
  | some value =>
    obtain ⟨ino, _, named, _⟩ := live id value bound
    rw [missing] at named
    contradiction

/-- The local syscall contracts for this allocation and this real writer
invocation. An occupied probe never acquires writer capabilities on that path. -/
structure Runtime {ns : TableNamespace W} (media : Media ns) (P : W → Prop) (rows : Rows) (origin : W) where
  probe : Probe ns P
  directory : Directory media P
  writer : ∀ id w, allocate ns.directory 0 origin = .ok id w →
    P w → ns.names w (tablePath ns.directory id) = none →
    NativeTableWriter.Primitives ns media.contents P id rows w

theorem create {ns : TableNamespace W} {media : Media ns}
    (io : Runtime media P rows origin) (start : P origin)
    (catalog : ∀ t, P t → ns.Represents t old ∧ media.stable.Represents t old) :
    Produced media old P rows origin := by
  have allocated := allocate_fresh io.probe 0 start
  have reached id w (selected : allocate ns.directory 0 origin = .ok id w) := by
    have atCall := allocated
    rw [Post, selected] at atCall
    exact NativeTableWriter.build (io.writer id w selected atCall.1 atCall.2) atCall.1
  constructor
  · rw [create_schedule]
    apply Post.bind
    apply (withReport allocated).weaken
    · rintro id w ⟨selected, pw, absent⟩
      have fresh := freshCatalog (catalog w pw).1 absent
      apply Post.bind
      apply (reached id w selected).1.weaken
      · rintro _ t ⟨kept, ino, bytes, named, content, synced, image⟩
        apply Post.bind
        apply (io.directory.install kept ⟨named,content,synced⟩ image).weaken
        · intro _ finish saved
          exact ⟨saved.1, saved.2.created fresh (catalog finish saved.1).1 (catalog finish saved.1).2⟩
        · exact fun _ _ h => h
      · exact fun _ _ h => h
    · exact fun _ _ h => h
  · intro α a last visit
    cases visit with
    | probe earlier _ => exact earlier.frame io.probe start
    | writer selected issued => exact (reached _ _ selected).2 _ _ issued
    | directory selected built =>
      have safe := (reached _ _ selected).1
      rw [Post,built] at safe
      exact safe.1
    | sync selected built opened =>
      have safe := (reached _ _ selected).1
      rw [Post,built] at safe
      obtain ⟨kept, ino, bytes, named, content, synced, _⟩ := safe
      have file : FileAt media _ ino bytes _ := ⟨named,content,synced⟩
      have d := io.directory.opened _ _ _ _ kept file
      rw [Post,opened] at d
      exact d.1

/-- Positive reports for the parent directory only after this invocation's
newly created SSTable has returned from its own flush and fsync. -/
structure HealthyDirectory (ns : TableNamespace W) (rows : Rows) {origin : W}
    (candidate : Candidate ns.directory origin) : Prop where
  openFile : ∀ built, Native.buildSynced (tablePath ns.directory candidate.number.toUInt64)
    candidate.number.toUInt64 rows candidate.reserved = .ok () built →
    ∃ fd entered, IO.FS.Handle.mk ns.directory .read built = .ok fd entered
  barrier : ∀ built fd entered, Native.buildSynced (tablePath ns.directory candidate.number.toUInt64)
    candidate.number.toUInt64 rows candidate.reserved = .ok () built →
    IO.FS.Handle.mk ns.directory .read built = .ok fd entered → ∃ finish, Native.syncHandle fd entered = .ok () finish

/-- Bounded rows and successful reports from the actual occupied-name probes,
exclusive stream, directory open and fsync force success of public creation. -/
theorem healthy {ns : TableNamespace W} {media : Media ns} (io : Runtime media P rows origin)
    (start : P origin) (catalog : ∀ t, P t → ns.Represents t old ∧ media.stable.Represents t old)
    (candidate : Candidate ns.directory origin)
    (valid : ImmutableSSTable.Unified.modelBuild Alvoki.CRC32C.extend (tableLayout candidate.number.toUInt64)
      (rows.map (ImmutableSSTable.Entry.encode keyCodec mutationCodec)) {} = .ok (count, bytes))
    (writer : NativeTableWriter.Healthy (tablePath ns.directory candidate.number.toUInt64)
      candidate.number.toUInt64 rows candidate.reserved)
    (dir : HealthyDirectory ns rows candidate) :
    ∃ finish, Native.checked (Native.createTable ns.directory rows) origin = .ok candidate.number.toUInt64 finish ∧
      P finish ∧ Created media old rows candidate.number.toUInt64 finish := by
  have absent := allocate_fresh io.probe 0 start
  rw [Post, candidate.allocate] at absent
  have leaves := io.writer _ _ candidate.allocate absent.1 absent.2
  obtain ⟨t, built, _⟩ := NativeTableWriter.healthy leaves absent.1 valid writer
  obtain ⟨fd, u, opened⟩ := dir.openFile t built
  obtain ⟨finish, synced⟩ := dir.barrier t fd u built opened
  have returned := success_of_reports candidate built opened synced
  have safe := (create io start catalog).returned
  rw [Post, returned] at safe
  exact ⟨finish, returned, safe⟩

end ExperimentalL0.NativeTableCreate
