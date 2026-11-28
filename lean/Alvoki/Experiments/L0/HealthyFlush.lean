import Alvoki.Experiments.L0.NativeFlushPublic
import Alvoki.Experiments.L0.HealthyFlushStore
import Alvoki.Experiments.L0.HealthyMutation

namespace ExperimentalL0.NativeFlush
open NativeRead (Footprint SessionAt tableNamespace)
open NativeScope (W Post)
open NativeFlushRestart (stored published proposal)
open NativeFlushCatalog (joint)
open NativeTableCreate (Candidate HealthyDirectory)
open WalRecoverySlice.Segmented.Native (PhaseMemory)

/-- A nonempty recovered memtable goes all the way through the real public
flush. All positive IO reports are on reached primitive operands. A final
unlock error preserves the same manifest, read input and lost-reply trace. -/
theorem healthy {physical : W → Footprint inode}
    {media : NativeTableCreate.Media (tableNamespace physical root)}
    (p : InterruptedMutation.Prefix path root start)
    (entry : NativeReadScope.Entry (joint physical root media) path root image)
    (files : NativeReadScope.Files physical root image start) (saved : NativeFlushCatalog.Saved physical root media image.tables start)
    (heap : PhaseMemory) (ops : WithOpenReads.Runtime (joint physical root media) root p.lock p.ref image life heap)
    (prior : Execution.Run before none image)
    (scan : ∀ history w, SessionAt (joint physical root media) root p.lock p.ref p.wal p.session image history w (.updating p.wal) →
      NativeRecoverAt.ScanPrimitives (joint physical root media) root p.wal image.tables w)
    (nonempty : p.session.mem.isEmpty = false) (fits : image.view.tail < UInt64.size)
    (storage : NativeFlushStore.Runtime physical root p.lock p.ref p.wal image p.session media manifest stop
      (origin p.ref p.wal p.session p.callback))
    (candidate : Candidate (root / "tables") (origin p.ref p.wal p.session p.callback))
    (rows : ImmutableSSTable.Unified.modelBuild Alvoki.CRC32C.extend (tableLayout candidate.number.toUInt64)
      (p.session.mem.toList.map (ImmutableSSTable.Entry.encode keyCodec mutationCodec)) {} = .ok (count, bytes))
    (writer : NativeTableWriter.Healthy (tablePath (root / "tables") candidate.number.toUInt64)
      candidate.number.toUInt64 p.session.mem.toList candidate.reserved)
    (dir : HealthyDirectory (tableNamespace physical root) p.session.mem.toList candidate)
    (reports : ∀ w, createTable root p.session.mem.toList (origin p.ref p.wal p.session p.callback) = .ok candidate.number.toUInt64 w →
      NativeManifestPublish.Healthy (root / "manifest") (L0Manifest.encode (proposal image p.session candidate.number.toUInt64)) w
        (NativeFlushStore.Ready physical root p.lock p.ref p.wal image p.session candidate.number.toUInt64 media) manifest)
    (phase : NativeRecoverAt.PhasePrimitives physical root p.lock p.ref (published image p.session candidate.number.toUInt64))
    (laws : NativeReadRelease.Laws heap physical root p.lock p.ref (published image p.session candidate.number.toUInt64))
    (cleanup : HealthyMutation.Cleanup physical heap root p.lock p.ref (published image p.session candidate.number.toUInt64) report)
    (reader : ReadRuntime physical path root life heap) (keys : List UInt64) (rootLife : NativeReadRelease.RootLifetime) :
    let img := published image p.session candidate.number.toUInt64
    let events := before ++ [.reopened]
    ∃ w, Native.withOpen path Native.flush start = (match report with | none => .ok () w | some e => .error e w) ∧
      (∃ made t, createTable root p.session.mem.toList (origin p.ref p.wal p.session p.callback) =
        .ok candidate.number.toUInt64 made ∧
        store root image p.session (origin p.ref p.wal p.session p.callback) = .ok ⟨img.version, ∅⟩ t ∧
        NativeFlushStore.SameFile media candidate.number.toUInt64 p.session.mem.toList made t) ∧
      NativeReadRelease.Closed physical root p.lock p.ref img w ∧
      (report = none → ReadAt physical path root life rootLife keys ((events ++ [.flushed]) ++ [.stop]) img w) ∧
      ReadAt physical path root life rootLife keys ((events ++ [.flushUncertain]) ++ [.stop]) img w := by
  intro img events
  obtain ⟨trace,history,online⟩ := p.online entry (NativeFlushCatalog.initialized files saved) heap ops prior
  obtain ⟨h,binding,scope⟩ := p.withOpen Native.flush
  obtain ⟨_,jointEntry,called⟩ := dispatchAt online binding heap ops.cleanup.cached ops.phase (scan history)
  obtain ⟨raw, durable⟩ := NativeFlushCatalog.catalogs jointEntry
  obtain ⟨t,storedAt,ready,stable,made,allocated,sameFile⟩ := NativeFlushStore.healthyPinned storage
    ⟨⟨raw.owned,raw.phase,raw.child⟩,raw.manifest,raw.catalog,durable⟩ raw.installed fits candidate rows writer dir reports
  simp only [nonempty, Bool.false_eq_true, ↓reduceIte, fits, storedAt] at called
  let next : Session := ⟨proposal image p.session candidate.number.toUInt64, ∅⟩
  have updated : SessionAt physical root p.lock p.ref p.wal next img history t (.updating p.wal) :=
    ⟨ready.owned,ready.phase,ready.child,stable,ready.created.live,
      NativeFlushRestart.installedPublished raw.installed ready.created.fresh.1 fits⟩
  obtain ⟨_,v,_,_,read,swap,_,publishRet⟩ := NativeWrite.afterWrite_publish
    ⟨updated.owned,updated.phase,updated.catalog,updated.manifest⟩ phase next
  have done := called.trans publishRet
  have accepted := (updated.advance read).advance swap
  have grant : NativeReadScope.Grant root p.lock p.ref := ⟨_,_,_,p.openFile,p.exclusive,rfl⟩
  have closed := NativeScope.release (NativeReadRelease.online laws grant accepted)
  obtain ⟨reg,slot,org,child,view⟩ := accepted.child
  have held : NativeWriteRelease.Held none physical root p.lock p.ref img (.online p.wal next) v :=
    ⟨accepted.owned,accepted.phase,accepted.catalog,accepted.manifest.1,child.installed.offline (.inl view)⟩
  obtain ⟨det,endWal,took,registered,wclosed,normal⟩ := HealthyMutation.release phase laws.cached held
    ((laws.cached _ held.owned p.wal reg).mp slot) (cleanup.child _ _ _ _ · held)
  have unlocked := cleanup.rootUnlock _ _ _ _ _ _ held took registered wclosed
  rw [Post, normal] at closed
  unfold Post at unlocked
  have returned := scope.trans (Lifecycle.finish_io ..)
  simp only [EIO.toBaseIO, done, normal] at returned
  have readOut w (c : NativeReadRelease.Closed physical root p.lock p.ref img w) :
      ReadAt physical path root life rootLife keys ((events ++ [.flushed]) ++ [.stop]) img w ∧
      ReadAt physical path root life rootLife keys ((events ++ [.flushUncertain]) ++ [.stop]) img w := by
    have ack := NativeFlushRestart.publishedStop trace ready.created.fresh.1 fits
    have sel : Selection image p.session next img := .newTable candidate.number.toUInt64 ready.created.fresh.1 fits
    have tr := (trace.flushUncertain fun _ i => sel.durable i).stop
    constructor
    · exact ⟨ack,ack.refines,WithOpenReads.withOpen (reader.entry _) c.files heap (reader.runtime _) ack keys rootLife⟩
    · exact ⟨tr,tr.refines,WithOpenReads.withOpen (reader.entry _) c.files heap (reader.runtime _) tr keys rootLife⟩
  cases ret : p.lock.unlock endWal with
  | ok _ w | error e w =>
    rw [ret] at unlocked closed returned
    exact ⟨w,by simpa only [unlocked] using returned,⟨made,t,allocated,storedAt,sameFile⟩,closed,(fun _ => (readOut _ closed).1),(readOut _ closed).2⟩

end ExperimentalL0.NativeFlush
