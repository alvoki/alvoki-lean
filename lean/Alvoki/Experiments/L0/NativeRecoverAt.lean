import Alvoki.Experiments.L0.NativeRecoverSelected

namespace ExperimentalL0.NativeRecoverAt

open System Lifecycle Alvoki.NativePost
open NativeRead (Footprint tableNamespace)

variable {inode : Type} {physical : W → Footprint inode} {root : FilePath}
  {lock : IO.FS.Handle} {ref : Ref} {image : Selected} {history : Rows}

/-- A native recovery started on the selected files produces the replayed
session and the still-attached physical child that the outer phase publish
uses. The WAL producer supplies its actual CONTROL read, root barrier,
child access and retired-file collection under the acquired store. -/
theorem recoverAt_checks (d : Durable image history)
    (opening : Opening physical root lock ref image start)
    (bytes : (physical start).manifest.active = L0Manifest.encode image.version)
    (manifestPrim : NativeManifest.Primitives (root / "manifest")
      (ManifestFrame physical root image.tables start) (fun w => (physical w).manifest))
    (heap : WalRecoverySlice.Segmented.Native.PhaseMemory) (cache : Cached heap physical root lock ref)
    (walIO : WalRecoverySlice.Segmented.Native.OpenIO heap (root / "wal") (fun w => (physical w).disk)
      image.view (Held physical root lock ref image .opening))
    (childCache : ChildCache physical root lock ref walIO)
    (phase : PhasePrimitives physical root lock ref image)
    (scanPrim : ∀ wal w, Attached physical root lock ref image wal w →
      ScanPrimitives physical root wal image.tables w)
    (tablePrim : ∀ wal w, Attached physical root lock ref image wal w →
      NativeRead.Primitives (tableNamespace physical root) life (NativeRead.Frame physical root wal image.tables w)) :
    NativeScope.Post (Native.recoverAt root ref) start
      (fun session t => (Installed session image history ∧ ∃ wal, Attached physical root lock ref image wal t) ∧
        CheckReceipt root ref image life start t true)
      (fun _ t => Failed physical root lock ref image t ∧
        (NoChecks root ref image start ∨ CheckReceipt root ref image life start t false)) :=
by
  have same v (p : WalRecoverySlice.Segmented.PermittedView image.view none v) : v = image.view := by
    simpa [WalRecoverySlice.Segmented.PermittedView] using p
  apply (recoverAt_selected_checks (hist := fun _ => history) (req := none)
    (fun v p => same v p ▸ d) opening bytes manifestPrim heap cache walIO childCache phase
    (fun v wal t p => by cases same v p; exact scanPrim wal t)
    (fun v wal t p => by cases same v p; exact tablePrim wal t)).weaken
  · rintro session u ⟨v, p, installed, attached, receipt⟩
    cases same v p
    exact ⟨⟨installed, attached⟩, receipt⟩
  · rintro _ t (⟨early, noneReached⟩ | ⟨v, p, attached, receipt⟩)
    · exact ⟨.inl early, .inl (noneReached _)⟩
    · cases same v p
      exact ⟨.inr attached, .inr receipt⟩

theorem recoverAt (d : Durable image history)
    (opening : Opening physical root lock ref image start)
    (bytes : (physical start).manifest.active = L0Manifest.encode image.version)
    (manifestPrim : NativeManifest.Primitives (root / "manifest")
      (ManifestFrame physical root image.tables start) (fun w => (physical w).manifest))
    (heap : WalRecoverySlice.Segmented.Native.PhaseMemory) (cache : Cached heap physical root lock ref)
    (walIO : WalRecoverySlice.Segmented.Native.OpenIO heap (root / "wal") (fun w => (physical w).disk)
      image.view (Held physical root lock ref image .opening))
    (childCache : ChildCache physical root lock ref walIO)
    (phase : PhasePrimitives physical root lock ref image)
    (scanPrim : ∀ wal w, Attached physical root lock ref image wal w →
      ScanPrimitives physical root wal image.tables w)
    (tablePrim : ∀ wal w, Attached physical root lock ref image wal w →
      NativeRead.Primitives (tableNamespace physical root) life (NativeRead.Frame physical root wal image.tables w)) :
    NativeScope.Post (Native.recoverAt root ref) start
      (fun session t => Installed session image history ∧ ∃ wal, Attached physical root lock ref image wal t)
      (fun _ t => Failed physical root lock ref image t) :=
  (recoverAt_checks d opening bytes manifestPrim heap cache walIO childCache phase scanPrim tablePrim).weaken
    (fun _ _ h => h.1) (fun _ _ h => h.1)

/-- The first failed manifest stat is propagated with its exact error and
world. Neither WAL acquisition nor any table check runs on this branch. -/
theorem recoverAt_manifestStatError (root : FilePath) (ref : Ref)
    (failed : (root / "manifest" / "BLOB").metadata w = .error e t) :
    Native.recoverAt root ref w = .error e t := by
  have file : IO.FS.readBinFile (root / "manifest" / "BLOB") w = .error e t := by
    simp only [IO.FS.readBinFile, Bind.bind, instMonadEIO._aux_13, EST.bind, failed]
  have blob : (DurableBlob.native (root / "manifest")).reopen w = .error e t := by
    rw [DurableBlob.native_reopen_schedule]
    simp only [Bind.bind, instMonadEIO._aux_13, EST.bind, file]
  have manifest : (Native.callbackComponents root ref).manifest.reopen.run w = .error e t := by
    change (NativeManifest.backend _).reopen.run w = _
    rw [NativeManifest.decodeReached, blob]
  unfold Native.recoverAt Native.checked ExperimentalL0.recover
  rw [ExceptT.run_bind]
  simp only [Bind.bind, instMonadEIO._aux_13, EST.bind, manifest]

/-- A manifest error after the concrete root lock was granted skips the
callback. The owned fresh reference contains no child and cleanup unlocks
the root; the manifest exception stays primary even if unlock reports one. -/
theorem withOpen_manifestStatError (path root : FilePath) (use : Native.Handle → IO α)
    (resolved : Native.validatedRoot path start = .ok root t)
    (opened : IO.FS.Handle.mk (root / "l0.lock") .append t = .ok lock u)
    (held : lock.tryLock true u = .ok true v)
    (failed : (root / "manifest" / "BLOB").metadata
      (IO.mkRef (.opening : Phase Wal) v).state = .error e reached)
    (old : let ref := (IO.mkRef (.opening : Phase Wal) v).val
      ((ref.swap .offline : BaseIO (Phase Wal)) reached).val = .opening) :
    let ref := (IO.mkRef (.opening : Phase Wal) v).val
    let after := ((ref.swap .offline : BaseIO (Phase Wal)) reached).state
    Native.withOpen path use start = .error e (lock.unlock.toBaseIO after).state := by
  have result := NativeScope.withOpen_recoveryError path root use resolved opened held
    (recoverAt_manifestStatError root _ failed)
  dsimp only at old result ⊢
  rw [old] at result
  exact result

end ExperimentalL0.NativeRecoverAt
