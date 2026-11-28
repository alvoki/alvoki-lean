import Alvoki.Experiments.L0.NativeFlushScope
import Alvoki.Experiments.L0.NativeFlushExit
import Alvoki.Experiments.L0.NativeTableCreate
import Alvoki.Experiments.L0.NativeManifestPublish

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

structure Runtime (physical : W → Footprint inode) (root : System.FilePath) (lock : IO.FS.Handle)
    (ref : Ref) (wal : Wal) (image : Selected) (s : Session) (media : Media (tableNamespace physical root))
    (manifest : NativeManifestPublish.Media inode) (stop : NativeManifestPublish.Stop) (origin : W) where
  table : NativeTableCreate.Runtime media (Pre physical root lock ref wal image media) s.mem.toList origin
  reserved : ∀ id w, NativeFlush.createTable root s.mem.toList origin = .ok id w →
    Ready physical root lock ref wal image s id media w → manifest.Private (root / "manifest") w
  publish : ∀ id w, NativeFlush.createTable root s.mem.toList origin = .ok id w →
    NativeManifestPublish.Primitives (root / "manifest") (L0Manifest.encode (proposal image s id)) w
      (Ready physical root lock ref wal image s id media) (fun t => (physical t).manifest) stop manifest

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

set_option maxHeartbeats 900000 in
theorem produce (io : Runtime physical root lock ref wal image s media manifest stop origin)
    (start : Pre physical root lock ref wal image media origin)
    (valid : Installed s image history) (fits : image.view.tail < UInt64.size) :
    Outcome physical root lock ref wal s image history media (NativeFlush.store root image s origin) := by
  have table := (NativeTableCreate.create io.table start fun _ p => ⟨p.live,p.durable⟩).returned
  change Post (NativeFlush.createTable root s.mem.toList) origin _ _ at table
  rw [NativeFlush.store_eq]
  cases allocated : NativeFlush.createTable root s.mem.toList origin with
  | error e t =>
    rw [Post, allocated] at table
    simp only [Bind.bind, instMonadEIO._aux_13, EST.bind, allocated, Outcome, returnedWorld]
    exact ⟨⟨_,_,.unchanged, ⟨table.owned,table.phase,table.live,table.manifest.1,table.disk⟩,table.child⟩,
      _, .original table.live table.manifest, table.durable, table.disk⟩
  | ok id w =>
    rw [Post, allocated] at table
    obtain ⟨pre, created⟩ := table
    have ready : Ready physical root lock ref wal image s id media w := ⟨pre.toHeld, created⟩
    have installed := NativeFlushRestart.installedPublished valid created.fresh.1 fits
    obtain ⟨d, _⟩ := installed
    have post := NativeManifestPublish.publish (io.publish id w allocated) ready
      (io.reserved id w allocated ready) pre.manifest d.unique
    let op := (NativeManifest.backend (root / "manifest")).publish (proposal image s id)
    change (match op.run w with
      | .ok (.ok ()) t => Ready _ _ _ _ _ _ _ _ _ t ∧ _
      | .ok (.error _) t | .error _ t => Ready _ _ _ _ _ _ _ _ _ t ∧ _) at post
    have fail e t (r : Ready physical root lock ref wal image s id media t)
        (a : (physical t).manifest.Admits (L0Manifest.encode image.version) (some (L0Manifest.encode (proposal image s id)))) :
        Outcome physical root lock ref wal s image history media (.error e t) :=
      ⟨failedManifest r fits a, (stored image s id).tables, .admitted id created.fresh.1 fits r.created.live a, r.created.durable, r.disk⟩
    simp only [Bind.bind, instMonadEIO._aux_13, EST.bind, allocated, NativeFlush.publish, Native.checked]
    generalize hop : ((NativeManifest.backend (root / "manifest")).publish (proposal image s id)).run w = returned
    change op.run w = returned at hop
    rw [hop] at post
    cases returned with
    | error e u =>
      exact fail e u post.1 post.2
    | ok value u =>
      cases value with
      | error e => exact fail _ u post.1 post.2
      | ok v =>
        obtain ⟨r, stable⟩ := post
        exact ⟨⟨_, .newTable id created.fresh.1 fits,
          ⟨r.owned,r.phase,r.child,stable,r.created.live,NativeFlushRestart.installedPublished valid created.fresh.1 fits⟩⟩,
          (stored image s id).tables, .published id created.fresh.1 fits r.created.live stable, r.created.durable, r.disk⟩

end ExperimentalL0.NativeFlushStore
