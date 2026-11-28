import Alvoki.Experiments.L0.NativeRecoverAt
import Alvoki.Experiments.L0.NativePublish
import Alvoki.Experiments.L0.NativeReadCallback

namespace ExperimentalL0.NativeReadScope
open System Lifecycle NativeScope NativeRead
open NativeRecoverAt (Opening Attached Failed)
abbrev W := NativeScope.W
abbrev Wal := NativeScope.Wal
abbrev Ref := NativeScope.Ref

/-- Persistent observations needed for another read-only open. The logical
history may have multiple equivalent witnesses for the same selected image. -/
structure Files (physical : W → Footprint inode) (root : FilePath) (image : Selected) (w : W) : Prop where
  catalog : (tableNamespace physical root).Represents w image.tables
  manifest : (physical w).manifest.active = L0Manifest.encode image.version
  disk : WalRecoverySlice.Segmented.Recoverable image.view none (physical w).disk

theorem filesOfChild (child : NativeRecoverAt.Child physical image wal w)
    (catalog : (tableNamespace physical root).Represents w image.tables)
    (manifest : (physical w).manifest.active = L0Manifest.encode image.version) :
    Files physical root image w := by
  obtain ⟨c, _, installed, view⟩ := child
  exact ⟨catalog, manifest, installed.offline (.inl view)⟩

theorem filesOfFailed (failed : Failed physical root lock ref image w) : Files physical root image w := by
  rcases failed with ⟨opening, manifest⟩ | ⟨wal, attached⟩
  · exact ⟨opening.catalog, manifest, opening.disk⟩
  · exact filesOfChild attached.2 attached.1.catalog attached.1.manifest.1

theorem filesOfOnline (online : Online physical root lock ref wal session image history w) :
    Files physical root image w := filesOfChild online.child online.catalog online.manifest.1

/-- The caller owns an initialized directory binding. Acquiring the root
lock adds the exact descriptor; allocation installs an opening phase on the
fresh reference while preserving the represented storage. -/
structure Entry (physical : W → Footprint inode) (path root : FilePath) (image : Selected) where
  bound : IO.FS.Handle → W → Prop
  resolve : ∀ w, Files physical root image w → Post (IO.FS.realPath path) w
    (fun canonical t => canonical = root ∧ Files physical root image t) (fun _ t => Files physical root image t)
  stat : ∀ (p : FilePath) w, Files physical root image w → Post p.symlinkMetadata w
    (fun _ t => Files physical root image t) (fun _ t => Files physical root image t)
  openFile : ∀ w, Files physical root image w → Post (IO.FS.Handle.mk (root / "l0.lock") .append) w
    (fun lock t => bound lock t ∧ Files physical root image t) (fun _ t => Files physical root image t)
  lock : ∀ h w, bound h w → Files physical root image w → Post (h.tryLock true) w
    (fun yes t => Files physical root image t ∧ (yes = true → (physical t).rootLock = some (root, h)))
    (fun _ t => Files physical root image t)
  fresh : ∀ h w, (physical w).rootLock = some (root, h) → Files physical root image w →
    let f := IO.mkRef (.opening : Phase Wal) w
    Owned (physical f.state) root h f.val ∧ (physical f.state).phase = .opening ∧ Files physical root image f.state

/-- Root validation, reported failure to obtain the lock, and construction
of the phase cell come from the concrete public scope. -/
theorem Entry.withOpen (entry : Entry physical path root image) (initial : Files physical root image start)
    (use : Native.Handle → IO α)
    (reject : ∀ e t, Files physical root image t → err e t)
    (recover : ∀ lock ref w, Opening physical root lock ref image w →
      (physical w).manifest.active = L0Manifest.encode image.version →
      ∀ handle, handle.AtRoot root ref →
      Post (Native.recoverAt root ref) w
        (fun session t => Publish ref lock (use handle) session t ok err)
        (fun e t => Release ref lock t (err e) (fun _ u => err e u))) :
    Post (Native.withOpen path use) start ok err := by
  let held := fun canonical h w => canonical = root ∧
    Files physical root image w ∧ (physical w).rootLock = some (root, h)
  apply withOpen_rule path use held
  · have resolved := validatedRoot_rule path (entry.resolve start initial)
      (fun r w hr p => (entry.stat p w hr.2).weaken
        (fun _ _ f => ⟨hr.1, f⟩) (fun _ _ f => ⟨hr.1, f⟩))
      (fun _ _ hr _ => hr.2)
    apply resolved.weaken
    · rintro _ t ⟨rfl, files⟩
      apply (entry.openFile t files).weaken
      · rintro h u ⟨bound, files⟩
        apply (entry.lock h u bound files).weaken
        · intro yes v succeeded
          cases yes with
          | true => exact ⟨rfl, succeeded.1, succeeded.2 rfl⟩
          | false => exact reject _ _ succeeded.1
        · exact reject
      · exact reject
    · exact reject
  · rintro _ lock v ⟨rfl, files, owns⟩ fresh handle binding
    obtain ⟨owned, phase, ready⟩ := entry.fresh lock v owns files
    exact recover lock _ _ ⟨owned, phase, ready.catalog, ready.disk⟩ ready.manifest handle binding

end ExperimentalL0.NativeReadScope
