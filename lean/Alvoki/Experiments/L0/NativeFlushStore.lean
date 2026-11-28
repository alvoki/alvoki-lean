import Alvoki.Experiments.L0.NativeFlushScope
import Alvoki.Experiments.L0.NativeFlushExit
import Alvoki.Experiments.L0.NativeTableCreate
import Alvoki.Experiments.L0.ManifestPublishSchedule

namespace ExperimentalL0.NativeFlushStore
open NativeScope (W Wal Ref Post)
open NativeRead (SessionAt Footprint RegisteredChild tableNamespace Owned)
open NativeFlushRestart (stored published proposal)
open NativeFlush (Selection Stored Uncertain)
open NativeTableCreate (Media Created)
open WalRecoverySlice.Segmented (Recoverable)
open WalRecoverySlice.Segmented.Native (returnedWorld)

structure Held (physical : W → Footprint inode) (root : System.FilePath) (lock : IO.FS.Handle)
    (ref : Ref) (wal : Wal) (image : Selected) (w : W) : Prop where
  owned : Owned (physical w) root lock ref
  phase : (physical w).phase = .updating wal
  child : RegisteredChild physical root image wal w

theorem Held.disk (h : Held physical root lock ref wal image w) :
    Recoverable image.view none (physical w).disk := by
  obtain ⟨_, _, _, installed, view⟩ := h.child
  exact installed.installed.offline (.inl view)

structure Pre (physical : W → Footprint inode) (root : System.FilePath) (lock : IO.FS.Handle)
    (ref : Ref) (wal : Wal) (image : Selected) (media : Media (tableNamespace physical root)) (w : W) : Prop
    extends Held physical root lock ref wal image w where
  manifest : (physical w).manifest.Stable (L0Manifest.encode image.version)
  live : (tableNamespace physical root).Represents w image.tables
  durable : media.stable.Represents w image.tables

structure Ready (physical : W → Footprint inode) (root : System.FilePath) (lock : IO.FS.Handle)
    (ref : Ref) (wal : Wal) (image : Selected) (s : Session) (id : UInt64)
    (media : Media (tableNamespace physical root)) (w : W) : Prop
    extends Held physical root lock ref wal image w where
  created : Created media image.tables s.mem.toList id w

/-- Read-only source fields protected from one issued table or manifest
primitive. A WAL background writeback may advance durability. Table frames
preserve the same name, inode and bytes independently in both namespaces. -/
structure FileFrame (physical : W → Footprint inode) (root : System.FilePath) (wal : Wal)
    (media : Media (tableNamespace physical root)) (tables : Catalog) (w t : W) : Prop where
  lock : (physical t).rootLock = (physical w).rootLock
  ref : (physical t).phaseRef = (physical w).phaseRef
  phase : (physical t).phase = (physical w).phase
  child : (physical t).readyWal wal = (physical w).readyWal wal
  operand : ∀ reg bs, (physical w).readyWal wal = some reg → (physical w).walChild reg bs → (physical t).walChild reg bs
  disk : WalRecoverySlice.Segmented.Writebacks (physical w).disk (physical t).disk
  live : (tableNamespace physical root).Keeps w t tables
  durable : media.stable.Keeps w t tables

theorem FileFrame.refl : FileFrame physical root wal media tables w w :=
  ⟨rfl,rfl,rfl,rfl,fun _ _ _ h => h,.nil,fun _ _ _ _ _ n b => ⟨n,b⟩,fun _ _ _ _ _ n b => ⟨n,b⟩⟩

theorem FileFrame.trans (a : FileFrame physical root wal media tables w t) (b : FileFrame physical root wal media tables t u) :
    FileFrame physical root wal media tables w u :=
  ⟨b.lock.trans a.lock,b.ref.trans a.ref,b.phase.trans a.phase,b.child.trans a.child,
    fun r xs slot held => b.operand r xs (a.child.trans slot) (a.operand r xs slot held),
    a.disk.trans b.disk,a.live.trans b.live,a.durable.trans b.durable⟩

private theorem Held.advance (h : Held physical root lock ref wal image w) (f : FileFrame physical root wal media tables w t) :
    Held physical root lock ref wal image t := by
  obtain ⟨reg,slot,origin,⟨history,shape,child,layout,lc,dc⟩,view⟩ := h.child
  exact ⟨⟨f.lock.trans h.owned.1,f.ref.trans h.owned.2⟩,f.phase.trans h.phase,
    reg,f.child.trans slot,origin,⟨history,shape,f.operand _ _ slot child,f.disk.readyLayout layout,
      f.disk.live.trans lc,f.disk.durable.trans dc⟩,view⟩

/-- Table preparation can create an unreferenced file. The prior manifest,
its possible survivors, and all previously selected table bindings stay held. -/
structure TableFrame (physical : W → Footprint inode) (root : System.FilePath) (wal : Wal)
    (media : Media (tableNamespace physical root)) (image : Selected) (manifest : NativeManifestPublish.Media inode) (w t : W) : Prop extends
    FileFrame physical root wal media image.tables w t where
  activeName : manifest.path (root / "manifest" / "BLOB") t = manifest.path (root / "manifest" / "BLOB") w
  stagingName : manifest.path (root / "manifest" / "BLOB.next") t = manifest.path (root / "manifest" / "BLOB.next") w
  active : (physical t).manifest.active = (physical w).manifest.active
  survivors : (physical t).manifest.survivors = (physical w).manifest.survivors

theorem TableFrame.refl : TableFrame physical root wal media image manifest w w := ⟨.refl,rfl,rfl,rfl,rfl⟩

theorem Pre.advance (pre : Pre physical root lock ref wal image media w) (f : TableFrame physical root wal media image namespaceMedia w t) :
    Pre physical root lock ref wal image media t :=
  ⟨pre.toHeld.advance f.toFileFrame,⟨f.active.trans pre.manifest.1,f.survivors.trans pre.manifest.2⟩,
    pre.live.frame f.live,pre.durable.frame f.durable⟩

abbrev PublishedFrame (physical : W → Footprint inode) (root : System.FilePath) (wal : Wal)
    (media : Media (tableNamespace physical root)) (image : Selected) (s : Session) (id : UInt64) :=
  FileFrame physical root wal media (NativeTableCreate.extend image.tables id s.mem.toList)

/-- Both the runtime name and the directory-fsynced name continue to select
the original inode. The two content observations refer to its original bytes. -/
theorem FileFrame.saved {id : UInt64} (f : PublishedFrame physical root wal media image s id w t)
    (source : NativeTableCreate.FileAt media id ident bytes w)
    (persisted : media.names w (tablePath (root / "tables") id) = some ident) :
    NativeTableCreate.FileAt media id ident bytes t ∧ media.names t (tablePath (root / "tables") id) = some ident := by
  have selected : NativeTableCreate.extend image.tables id s.mem.toList id = some s.mem.toList := by
    simp [NativeTableCreate.extend]
  obtain ⟨named,live⟩ := f.live id _ ident bytes selected source.named source.visible
  obtain ⟨durable,synced⟩ := f.durable id _ ident bytes selected persisted source.synced
  exact ⟨⟨named,live,synced⟩,durable⟩

theorem Ready.advance {id : UInt64} (r : Ready physical root lock ref wal image s id media w)
    (f : PublishedFrame physical root wal media image s id w t) : Ready physical root lock ref wal image s id media t := by
  obtain ⟨ident,bytes,file,named,exactBytes⟩ := r.created.persisted
  obtain ⟨held,name⟩ := f.saved file named
  exact ⟨r.toHeld.advance f,r.created.fresh,⟨ident,bytes,held,name,exactBytes⟩,
    r.created.live.frame f.live,r.created.durable.frame f.durable⟩

open NativeManifestPublish (Prefix Operand action Effect NextOperand)

/-- Only the manifest primitive named by this prefix and its attached
operand may act. Its frame is between the input and output of that syscall. -/
structure PublishIO (physical : W → Footprint inode) (root : System.FilePath) (lock : IO.FS.Handle)
    (ref : Ref) (wal : Wal) (image : Selected) (s : Session) (id : UInt64) (media : Media (tableNamespace physical root))
    (manifest : NativeManifestPublish.Media inode) (stop : NativeManifestPublish.Stop) (begin : W) : Prop where
  returned : ∀ p w, Prefix (root / "manifest") (L0Manifest.encode (proposal image s id)) begin p w →
    Owned (physical w) root lock ref → Operand manifest (root / "manifest") (L0Manifest.encode (proposal image s id)) w p →
    match action (root / "manifest") (L0Manifest.encode (proposal image s id)) p w with
    | .ok x t => PublishedFrame physical root wal media image s id w t ∧
      Effect manifest p true w (physical w).manifest (physical t).manifest ∧
      NextOperand manifest (root / "manifest") (L0Manifest.encode (proposal image s id)) p x t
    | .error _ t => PublishedFrame physical root wal media image s id w t ∧
      Effect manifest p false w (physical w).manifest (physical t).manifest
  interrupted : ∀ p w, Prefix (root / "manifest") (L0Manifest.encode (proposal image s id)) begin p w →
    Owned (physical w) root lock ref → Operand manifest (root / "manifest") (L0Manifest.encode (proposal image s id)) w p →
    ∀ t, stop (action (root / "manifest") (L0Manifest.encode (proposal image s id)) p) w t →
      PublishedFrame physical root wal media image s id w t ∧ Effect manifest p false w (physical w).manifest (physical t).manifest

private theorem PublishIO.frames {id : UInt64} (ops : PublishIO physical root lock ref wal image s id media manifest stop begin)
    (owned : ∀ w, P w → Owned (physical w) root lock ref)
    (keep : ∀ w t, P w → PublishedFrame physical root wal media image s id w t → P t) :
    NativeManifestPublish.Primitives (root / "manifest") (L0Manifest.encode (proposal image s id)) begin
      P (fun t => (physical t).manifest) stop manifest := by
  constructor
  · intro p w pc ready operand
    have step := ops.returned p w pc (owned w ready) operand
    cases ran : action _ _ p w <;> rw [ran] at step <;> exact ⟨keep w _ ready step.1,step.2⟩
  · intro p w pc ready operand t cut
    obtain ⟨edge,effects⟩ := ops.interrupted p w pc (owned w ready) operand t cut
    exact ⟨keep w _ ready edge,effects⟩

structure Runtime (physical : W → Footprint inode) (root : System.FilePath) (lock : IO.FS.Handle)
    (ref : Ref) (wal : Wal) (image : Selected) (s : Session) (media : Media (tableNamespace physical root))
    (manifest : NativeManifestPublish.Media inode) (stop : NativeManifestPublish.Stop) (origin : W) where
  table : NativeTableCreate.Runtime media (TableFrame physical root wal media image manifest origin) s.mem.toList origin
  initialNames : Owned (physical origin) root lock ref → manifest.Private (root / "manifest") origin
  publishIO : ∀ id w, NativeFlush.createTable root s.mem.toList origin = .ok id w →
    PublishIO physical root lock ref wal image s id media manifest stop w

theorem Runtime.publish (io : Runtime physical root lock ref wal image s media manifest stop origin)
    (id : UInt64) (w : W) (issued : NativeFlush.createTable root s.mem.toList origin = .ok id w) :
    NativeManifestPublish.Primitives (root / "manifest") (L0Manifest.encode (proposal image s id)) w
      (Ready physical root lock ref wal image s id media) (fun t => (physical t).manifest) stop manifest :=
  (io.publishIO id w issued).frames (fun _ ready => ready.owned) (fun _ _ ready edge => ready.advance edge)

private theorem Runtime.tableFrames (io : Runtime physical root lock ref wal image s media manifest stop origin)
    (start : Pre physical root lock ref wal image media origin) :
    NativeTableCreate.Produced media image.tables (TableFrame physical root wal media image manifest origin) s.mem.toList origin :=
  NativeTableCreate.create io.table TableFrame.refl (fun _ f => ⟨(start.advance f).live,(start.advance f).durable⟩)

theorem Runtime.tableProduced (io : Runtime physical root lock ref wal image s media manifest stop origin)
    (start : Pre physical root lock ref wal image media origin) :
    NativeTableCreate.Produced media image.tables (Pre physical root lock ref wal image media) s.mem.toList origin := by
  have result := io.tableFrames start
  exact ⟨result.returned.weaken (fun _ _ h => ⟨start.advance h.1,h.2⟩) (fun _ _ f => start.advance f),
    fun seen => start.advance (result.visited seen),fun seen => start.advance (result.afterVisit seen)⟩

theorem Runtime.reserved (io : Runtime physical root lock ref wal image s media manifest stop origin)
    (start : Pre physical root lock ref wal image media origin) (id : UInt64) (w : W)
    (issued : NativeFlush.createTable root s.mem.toList origin = .ok id w) : manifest.Private (root / "manifest") w := by
  have table := (io.tableFrames start).returned
  change Post (NativeFlush.createTable root s.mem.toList) origin _ _ at table
  rw [Post,issued] at table
  obtain ⟨ino,active,distinct⟩ := io.initialNames start.owned
  exact ⟨ino,table.1.activeName.trans active,table.1.stagingName ▸ distinct⟩

def Outcome (physical : W → Footprint inode) (root : System.FilePath) (lock : IO.FS.Handle)
    (ref : Ref) (wal : Wal) (s : Session) (image : Selected) (history : Rows)
    (media : Media (tableNamespace physical root)) (out : NativeFlushExit.Result) : Prop :=
  (match out with
   | .ok next t => Stored physical root lock ref wal s image history next t
   | .error _ t => Uncertain physical root lock ref wal s image t) ∧
  ∃ tables, NativeFlushExit.Media physical root image s (returnedWorld out) tables ∧
    media.stable.Represents (returnedWorld out) tables ∧ Recoverable image.view none (physical (returnedWorld out)).disk

private theorem failedManifest {id : UInt64}
    (ready : Ready physical root lock ref wal image s id media t) (fits : image.view.tail < UInt64.size)
    (allowed : (physical t).manifest.Admits (L0Manifest.encode image.version) (some (L0Manifest.encode (proposal image s id)))) :
    Uncertain physical root lock ref wal s image t := by
  have fresh := ready.created.fresh.1
  rcases allowed.1 with old | new
  · have catalog : (tableNamespace physical root).Represents t image.tables := by
      intro k rows found
      have ne : k ≠ id := by rintro rfl; simp [fresh] at found
      exact ready.created.live k rows (by simpa [NativeTableCreate.extend, ne] using found)
    exact ⟨_, _, .unchanged, ⟨ready.owned, ready.phase, catalog, old, ready.disk⟩, ready.child⟩
  · exact ⟨_, _, .newTable id fresh fits, ⟨ready.owned, ready.phase, ready.created.live,
      (Option.some.inj new).symm, ready.disk⟩, ready.child⟩

/-- Any table this invocation actually created retains its original bindings
in the world returned by manifest publication, including on reported errors. -/
def Anchored (physical : W → Footprint inode) (root : System.FilePath) (wal : Wal)
    (media : Media (tableNamespace physical root)) (image : Selected) (s : Session) (origin t : W) : Prop :=
  ∀ id w, NativeFlush.createTable root s.mem.toList origin = .ok id w →
    PublishedFrame physical root wal media image s id w t

theorem Runtime.pinned (io : Runtime physical root lock ref wal image s media manifest stop origin)
    (id : UInt64) (w : W) (issued : NativeFlush.createTable root s.mem.toList origin = .ok id w)
    (ready : Ready physical root lock ref wal image s id media w) :
    NativeManifestPublish.Primitives (root / "manifest") (L0Manifest.encode (proposal image s id)) w
      (PublishedFrame physical root wal media image s id w) (fun t => (physical t).manifest) stop manifest :=
  (io.publishIO id w issued).frames (fun _ f => (ready.advance f).owned) (fun _ _ prior edge => prior.trans edge)

set_option maxHeartbeats 900000 in
theorem producePinned (io : Runtime physical root lock ref wal image s media manifest stop origin)
    (start : Pre physical root lock ref wal image media origin)
    (valid : Installed s image history) (fits : image.view.tail < UInt64.size) :
    Outcome physical root lock ref wal s image history media (NativeFlush.store root image s origin) ∧
      Anchored physical root wal media image s origin (returnedWorld (NativeFlush.store root image s origin)) := by
  have table := (io.tableProduced start).returned
  change Post (NativeFlush.createTable root s.mem.toList) origin _ _ at table
  unfold NativeFlush.store flushTableWith
  cases allocated : NativeFlush.createTable root s.mem.toList origin with
  | error e t =>
    rw [Post, allocated] at table
    simp only [Bind.bind, instMonadEIO._aux_13, EST.bind, allocated, Outcome, returnedWorld]
    refine ⟨⟨⟨_,_,.unchanged, ⟨table.owned,table.phase,table.live,table.manifest.1,table.disk⟩,table.child⟩,
      _, .original table.live table.manifest, table.durable, table.disk⟩,?_⟩
    intro k v done
    rw [allocated] at done
    contradiction
  | ok id w =>
    rw [Post, allocated] at table
    obtain ⟨pre, created⟩ := table
    have ready : Ready physical root lock ref wal image s id media w := ⟨pre.toHeld, created⟩
    have installed := NativeFlushRestart.installedPublished valid created.fresh.1 fits
    obtain ⟨d, _⟩ := installed
    have anchor t (f : PublishedFrame physical root wal media image s id w t) : Anchored physical root wal media image s origin t := by
      intro k v done
      rw [allocated] at done
      cases done
      exact f
    have post := NativeManifestPublish.publish (io.pinned id w allocated ready) FileFrame.refl
      (io.reserved start id w allocated) pre.manifest d.unique
    let op := (NativeManifest.backend (root / "manifest")).publish (proposal image s id)
    change (match op.run w with
      | .ok (.ok ()) t => PublishedFrame physical root wal media image s id w t ∧ _
      | .ok (.error _) t | .error _ t => PublishedFrame physical root wal media image s id w t ∧ _) at post
    have fail e t (r : Ready physical root lock ref wal image s id media t)
        (a : (physical t).manifest.Admits (L0Manifest.encode image.version) (some (L0Manifest.encode (proposal image s id)))) :
        Outcome physical root lock ref wal s image history media (.error e t) :=
      ⟨failedManifest r fits a, (stored image s id).tables, .admitted id created.fresh.1 fits r.created.live a, r.created.durable, r.disk⟩
    simp only [Bind.bind, instMonadEIO._aux_13, EST.bind, allocated, show (⟨id :: s.version.tables, image.view.tail.toUInt64⟩ : L0Manifest.Version) = proposal image s id from rfl, NativeFlush.publish, Native.checked]
    generalize hop : ((NativeManifest.backend (root / "manifest")).publish (proposal image s id)).run w = returned
    change op.run w = returned at hop
    rw [hop] at post
    cases returned with
    | error e u =>
      exact ⟨fail e u (ready.advance post.1) post.2,anchor u post.1⟩
    | ok value u =>
      cases value with
      | error e => exact ⟨fail _ u (ready.advance post.1) post.2,anchor u post.1⟩
      | ok v =>
        obtain ⟨f, stable⟩ := post
        let r := ready.advance f
        exact ⟨⟨⟨_, .newTable id created.fresh.1 fits,
          ⟨r.owned,r.phase,r.child,stable,r.created.live,NativeFlushRestart.installedPublished valid created.fresh.1 fits⟩⟩,
          (stored image s id).tables, .published id created.fresh.1 fits r.created.live stable, r.created.durable, r.disk⟩,anchor u f⟩

/-- The directory-fsynced name and immutable payload in both worlds. The
existentials range over one identity and one byte string for the whole pair. -/
def SameFile {ns : TableNamespace W} (media : Media ns) (id : UInt64) (rows : Rows) (built returned : W) : Prop :=
  ∃ ident bytes, NativeTableCreate.FileAt media id ident bytes built ∧
    media.names built (tablePath ns.directory id) = some ident ∧
    ImmutableSSTable.Unified.Image Alvoki.CRC32C.extend (tableLayout id)
      (rows.map (ImmutableSSTable.Entry.encode keyCodec mutationCodec)) bytes ∧
    NativeTableCreate.FileAt media id ident bytes returned ∧ media.names returned (tablePath ns.directory id) = some ident

theorem FileFrame.sameFile {id : UInt64} (f : PublishedFrame physical root wal media image s id w t)
    (created : NativeTableCreate.Created media image.tables s.mem.toList id w) : SameFile media id s.mem.toList w t := by
  obtain ⟨ident,bytes,file,name,built⟩ := created.persisted
  exact ⟨ident,bytes,file,name,built,f.saved file name⟩

theorem anchoredFile (io : Runtime physical root lock ref wal image s media manifest stop origin)
    (start : Pre physical root lock ref wal image media origin) (valid : Installed s image history)
    (fits : image.view.tail < UInt64.size) (id : UInt64) (w : W)
    (made : NativeFlush.createTable root s.mem.toList origin = .ok id w) :
    SameFile media id s.mem.toList w (returnedWorld (NativeFlush.store root image s origin)) := by
  have created := (io.tableProduced start).returned
  change Post (NativeFlush.createTable root s.mem.toList) origin _ _ at created
  rw [Post,made] at created
  exact ((producePinned io start valid fits).2 id w made).sameFile created.2

/-- A reported directory-sync error after the manifest rename returns the
original error. The new live selector refers to the same previously fsynced
table inode; a power loss may still restore the prior selector. -/
theorem renamedError (io : Runtime physical root lock ref wal image s media manifest stop origin)
    (start : Pre physical root lock ref wal image media origin) (valid : Installed s image history)
    (fits : image.view.tail < UInt64.size) (id : UInt64) (w : W)
    (made : NativeFlush.createTable root s.mem.toList origin = .ok id w)
    (pc : Prefix (root / "manifest") (L0Manifest.encode (proposal image s id)) w (.rename writer) before)
    (renamed : IO.FS.rename (root / "manifest" / "BLOB.next") (root / "manifest" / "BLOB") before = .ok () moved)
    (opened : IO.FS.Handle.mk (root / "manifest") .read moved = .ok fd synced)
    (failed : DurableBlob.syncHandle fd synced = .error err t) :
    NativeFlush.store root image s origin = .error err t ∧
    (physical t).manifest.active = L0Manifest.encode (proposal image s id) ∧
    (physical t).manifest.Admits (L0Manifest.encode image.version) (some (L0Manifest.encode (proposal image s id))) ∧
    Ready physical root lock ref wal image s id media t ∧ SameFile media id s.mem.toList w t := by
  have table := (io.tableProduced start).returned
  change Post (NativeFlush.createTable root s.mem.toList) origin _ _ at table
  rw [Post,made] at table
  obtain ⟨pre,saved⟩ := table
  let r : Ready physical root lock ref wal image s id media w := ⟨pre.toHeld,saved⟩
  obtain ⟨d,_⟩ := NativeFlushRestart.installedPublished valid saved.fresh.1 fits
  obtain ⟨_,pub,frame,active,admitted⟩ := NativeManifestPublish.rename_then_barrier_error
    (io.pinned id w made r) FileFrame.refl (io.reserved start id w made) pre.manifest d.unique pc renamed opened failed
  have failedPublish : NativeFlush.publish root (proposal image s id) w = .error err t := pub
  refine ⟨?_,active,admitted,r.advance frame,frame.sameFile saved⟩
  simp only [NativeFlush.store,flushTableWith,Bind.bind,instMonadEIO._aux_13,EST.bind,made,
    show (⟨id :: s.version.tables,image.view.tail.toUInt64⟩ : L0Manifest.Version) = proposal image s id from rfl,failedPublish]

theorem produce (io : Runtime physical root lock ref wal image s media manifest stop origin)
    (start : Pre physical root lock ref wal image media origin)
    (valid : Installed s image history) (fits : image.view.tail < UInt64.size) :
    Outcome physical root lock ref wal s image history media (NativeFlush.store root image s origin) :=
  (producePinned io start valid fits).1

end ExperimentalL0.NativeFlushStore
