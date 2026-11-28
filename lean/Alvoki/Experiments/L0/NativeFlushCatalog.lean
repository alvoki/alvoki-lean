import Alvoki.Experiments.L0.NativeFlush
import Alvoki.Experiments.L0.NativeTableAllocation
import Alvoki.Experiments.L0.WithOpenReads

namespace ExperimentalL0.NativeFlushCatalog
open System NativeScope
open NativeRead (Footprint tableNamespace SessionAt Online)
open NativeTableCreate (Media)
open WalRecoverySlice.Segmented.Native (PhaseMemory)

/-- Keep an observation only when both the live and durable filesystem
expose the same value. This is a proof projection on owned entries. -/
private noncomputable def agree (live durable : Option α) : Option α := by
  classical
  exact if live = durable then live else none

private theorem agree_some {live durable : Option α} :
    agree live durable = some x ↔ live = some x ∧ durable = some x := by
  classical
  by_cases eq : live = durable <;> simp_all [agree]
  exact fun l r => eq (l.trans r.symm)

/-- Recovery and phase operations run unchanged. A catalog proof on the
joint projection pins both the directory entry and the bytes of the same
inode. Physical allocation still uses the full live namespace. -/
noncomputable def joint (physical : W → Footprint inode) (root : FilePath)
    (media : Media (tableNamespace physical root)) (w : W) : Footprint inode :=
  {physical w with
    names := fun path => agree ((physical w).names path) (media.names w path)
    contents := fun i => agree ((physical w).contents i) (media.contents w i)}

variable {physical : W → Footprint inode} {root : FilePath} {media : Media (tableNamespace physical root)}

/-- One materialized native inode, including its checked immutable
encoding, under its live and durable directory entry. -/
theorem jointBound {id : UInt64} :
    (tableNamespace (joint physical root media) root).Bound w id rows ↔
      ∃ i bytes, (physical w).names (tablePath (root / "tables") id) = some i ∧
        media.names w (tablePath (root / "tables") id) = some i ∧
        (physical w).contents i = some bytes ∧ media.contents w i = some bytes ∧
        ImmutableSSTable.Unified.Image Alvoki.CRC32C.extend (tableLayout id)
          (rows.map (ImmutableSSTable.Entry.encode keyCodec mutationCodec)) bytes := by
  constructor
  · rintro ⟨i, bytes, name, content, format⟩
    obtain ⟨live, saved⟩ := agree_some.mp name
    obtain ⟨visible, stable⟩ := agree_some.mp content
    exact ⟨i, bytes, live, saved, visible, stable, format⟩
  · rintro ⟨i, bytes, live, saved, visible, stable, format⟩
    exact ⟨i, bytes, agree_some.mpr ⟨live,saved⟩, agree_some.mpr ⟨visible,stable⟩, format⟩

theorem splitCatalog (selected : (tableNamespace (joint physical root media) root).Represents w tables) :
    (tableNamespace physical root).Represents w tables ∧ media.stable.Represents w tables := by
  have bind (id rows) (found : tables id = some rows) := jointBound.mp (selected id rows found)
  constructor
  · intro id rows found
    obtain ⟨i, bytes, live, _, visible, _, format⟩ := bind id rows found
    exact ⟨i, bytes, live, visible, format⟩
  · intro id rows found
    obtain ⟨i, bytes, _, saved, _, stable, format⟩ := bind id rows found
    exact ⟨i, bytes, saved, stable, format⟩

/-- At the initial root only the currently represented catalog entries
need to have survived. No equality is required for unrelated orphan names. -/
def Saved (physical : W → Footprint inode) (root : FilePath) (media : Media (tableNamespace physical root))
    (tables : Catalog) (w : W) : Prop :=
  ∀ id rows i bytes, tables id = some rows →
    (physical w).names (tablePath (root / "tables") id) = some i →
    (physical w).contents i = some bytes →
    media.names w (tablePath (root / "tables") id) = some i ∧ media.contents w i = some bytes

theorem initialized (files : NativeReadScope.RestartFiles pending physical root image w)
    (saved : Saved physical root media image.tables w) :
    NativeReadScope.RestartFiles pending (joint physical root media) root image w := by
  refine ⟨?_, files.manifest, files.disk⟩
  intro id rows present
  obtain ⟨i, bytes, name, content, format⟩ := files.catalog id rows present
  obtain ⟨sn, sc⟩ := saved id rows i bytes present name content
  exact jointBound.mpr ⟨i,bytes,name,sn,content,sc,format⟩

theorem savedEmpty (empty : tables = fun _ => none) : Saved physical root media tables w := by
  intro id rows i bytes found
  rw [empty] at found
  contradiction

/-- At an actual boot the live namespace is instantiated from the chosen
durable names and bytes. This suffices even for a nonempty manifest. -/
theorem savedAtBoot (names : (physical w).names = media.names w)
    (contents : (physical w).contents = media.contents w) : Saved physical root media tables w := by
  intro id rows i bytes found name data
  exact ⟨names ▸ name, contents ▸ data⟩

theorem liveFiles (files : NativeReadScope.RestartFiles pending (joint physical root media) root image w) :
    NativeReadScope.RestartFiles pending physical root image w :=
  ⟨(splitCatalog files.catalog).1, files.manifest, files.disk⟩

theorem liveClosed (closed : NativeReadRelease.Closed (joint physical root media) root lock ref image w pending) :
    NativeReadRelease.Closed physical root lock ref image w pending := by
  obtain ⟨offline, grant, u, custody, report⟩ := closed
  exact ⟨⟨liveFiles offline.files, offline.phaseRef, offline.offline⟩, grant, u,
    ⟨⟨liveFiles custody.files, custody.phaseRef, custody.offline⟩, custody.owner⟩, report⟩

theorem catalogs (entry : SessionAt (joint physical root media) root lock ref wal s image history w stage) :
    SessionAt physical root lock ref wal s image history w stage ∧ media.stable.Represents w image.tables := by
  obtain ⟨visible, stable⟩ := splitCatalog entry.catalog
  exact ⟨⟨entry.owned, entry.phase, entry.child, entry.manifest, visible, entry.installed⟩, stable⟩

/-- Two local primitive frames on the actual selected inodes produce the
single frame used by the existing recovery and phase proofs. -/
theorem keeps (live : (tableNamespace physical root).Keeps a b tables)
    (durable : media.stable.Keeps a b tables) : (tableNamespace (joint physical root media) root).Keeps a b tables := by
  intro id rows i bytes found name content
  obtain ⟨liveName, durableName⟩ := agree_some.mp name
  obtain ⟨liveData, durableData⟩ := agree_some.mp content
  obtain ⟨ln, lc⟩ := live id rows i bytes found liveName liveData
  obtain ⟨dn, dc⟩ := durable id rows i bytes found durableName durableData
  exact ⟨agree_some.mpr ⟨ln,dn⟩, agree_some.mpr ⟨lc,dc⟩⟩

theorem dispatch (online : Online (joint physical root media) root lock ref wal s image history start)
    (binding : Native.Handle.AtRoot handle root ref)
    (heap : PhaseMemory) (cached : NativeRecoverAt.Cached heap (joint physical root media) root lock ref)
    (phase : NativeRecoverAt.PhasePrimitives (joint physical root media) root lock ref image)
    (scan : ∀ w, SessionAt (joint physical root media) root lock ref wal s image history w (.updating wal) →
      NativeRecoverAt.ScanPrimitives (joint physical root media) root wal image.tables w) :
    ∃ t, SessionAt physical root lock ref wal s image history t (.updating wal) ∧ media.stable.Represents t image.tables ∧
      Native.flush handle start = NativeWrite.afterWrite ref
        (if s.mem.isEmpty then .ok s t else if image.view.tail < UInt64.size then NativeFlush.store root image s t
         else .error (IO.userError "absolute WAL position exhausted") t) := by
  obtain ⟨t, produced, ran⟩ := NativeFlush.dispatch online binding heap cached phase scan
  obtain ⟨raw, stable⟩ := catalogs produced
  exact ⟨t,raw,stable,ran⟩

/-- Start at the initialized public root, recover, publish the online
phase, reserve it for flush and scan the actual WAL. The continuation
receives both catalog observations in the world that issues table creation. -/
theorem withOpen {ok : Unit → W → Prop} {err : IO.Error → W → Prop}
    (entry : NativeReadScope.Entry (joint physical root media) path root image)
    (files : NativeReadScope.Files physical root image start) (saved : Saved physical root media image.tables start)
    (heap : PhaseMemory) (runtime : ∀ lock ref, WithOpenReads.Runtime (joint physical root media) root lock ref image life heap)
    (prior : Execution.Run before none image)
    (scans : ∀ lock ref wal s history u, SessionAt (joint physical root media) root lock ref wal s image history u (.updating wal) →
      NativeRecoverAt.ScanPrimitives (joint physical root media) root wal image.tables u)
    (rejected : ∀ e t, NativeReadScope.Files physical root image t →
      Execution.Run (before ++ [.openFailed]) none image → err e t)
    (body : ∀ lock ref wal s history handle entered t, NativeReadScope.Grant root lock ref →
      Native.Handle.AtRoot handle root ref → Execution.Run (before ++ [.reopened]) (some s) image →
      SessionAt physical root lock ref wal s image history t (.updating wal) → media.stable.Represents t image.tables →
      Native.flush handle entered = NativeWrite.afterWrite ref
        (if s.mem.isEmpty then .ok s t else if image.view.tail < UInt64.size then NativeFlush.store root image s t
         else .error (IO.userError "absolute WAL position exhausted") t) →
      Callback ref lock (Native.flush handle) entered ok err) :
    Post (Native.withOpen path Native.flush) start ok err := by
  apply WithOpenReads.withRecovered entry (initialized files saved) heap runtime prior
  · exact fun e t retained trace => rejected e t (liveFiles retained) trace
  · exact fun _ _ _ _ e t closed _ _ trace => rejected e t (liveFiles closed.files) trace
  intro lock ref wal s history handle opening recovered grant _ _ binding installed attached trace
  let ops := runtime lock ref
  apply NativeRead.publishOnline (attached.sessionAt installed) (ops.phase.refRead wal) (ops.phase.refSwap wal)
  intro entered online
  obtain ⟨t, raw, stable, equality⟩ := dispatch online binding heap ops.cleanup.cached ops.phase (scans _ _ _ _ _)
  exact body lock ref wal s history handle entered t grant binding trace raw stable equality

end ExperimentalL0.NativeFlushCatalog
