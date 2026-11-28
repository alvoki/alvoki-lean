import Alvoki.Experiments.L0.HealthyPublishedOpen
import Alvoki.Experiments.L0.HealthyFlush
import Alvoki.Experiments.L0.NativeFlushPinned

namespace ExperimentalL0.NativeFlush
open NativeRead (Footprint SessionAt tableNamespace)
open NativeScope (W Post)
open NativeFlushRestart (stored published proposal)
open NativeFlushCatalog (joint)
open NativeTableCreate (Candidate HealthyDirectory)
open WalRecoverySlice.Segmented.Native (PhaseMemory)

open HealthyPublishedRecovery (pinned ReadProgress ReadResult)
open WalRecoverySlice.Segmented.Native (returnedWorld)
open NativeFlushInterrupted (result storeWorld)

theorem healthyRead {physical : W → Footprint inode}
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
    (reader : ReadRuntime physical path root life heap) (rootLife : NativeReadRelease.RootLifetime)
    (key : UInt64) (value : Mutation) (hit : lookupRows p.session.mem.toList key = some value)
    (frames : MutationExitCut.Frames (NativeFlushExit.Edge physical root media (stored image p.session candidate.number.toUInt64).tables)
      cutStop (MutationExitCut.afterStore p.ref p.lock p.session (result p image)) (returnedWorld (result p image)))
    (next : ∀ w, Native.withOpen path Native.flush start =
        (match report with | none => .ok () w | some e => .error e w) → HealthyReads.Entry path root w)
    (progress : ∀ w ret (ident : inode) bytes,
      (physical w).names (tablePath (root / "tables") candidate.number.toUInt64) = some ident →
      (physical w).contents ident = some bytes →
      ReadProgress (pinned physical root candidate.number.toUInt64 ident bytes) life heap (next w ret)
        (published image p.session candidate.number.toUInt64)) :
    ∃ w, ∃ ret : Native.withOpen path Native.flush start = (match report with | none => .ok () w | some e => .error e w),
      ∃ made ident b, createTable root p.session.mem.toList (storeWorld p) = .ok candidate.number.toUInt64 made ∧
        NativeTableCreate.FileAt media candidate.number.toUInt64 ident b made ∧
        ∃ (named : (physical w).names (tablePath (root / "tables") candidate.number.toUInt64) = some ident)
          (content : (physical w).contents ident = some b),
          ReadResult physical path root key value candidate.number.toUInt64 ident b life w heap (next w ret)
            (published image p.session candidate.number.toUInt64) (progress w ret ident b named content) := by
  obtain ⟨w,ret,⟨made,t,allocated,storedAt,file⟩,closed,_,after⟩ :=
    healthy p entry files saved heap ops prior scan nonempty fits storage candidate rows writer dir reports phase laws
      cleanup reader [key] rootLife
  have entered := NativeFlushInterrupted.ingress p entry files saved heap ops prior scan
  have storeEnd : returnedWorld (store root image p.session (storeWorld p)) = t := by rw [storedAt]; rfl
  have carried := entered.pinAtReturn nonempty fits (storeEnd.symm ▸ file) frames
  have ended : returnedWorld (Native.withOpen path Native.flush start) = w := by rw [ret]; cases report <;> rfl
  rw [ended] at carried
  obtain ⟨i,b,built,_,_,live,_⟩ := carried
  exact ⟨w,ret,made,i,b,allocated,built,live.named,live.visible,
    HealthyPublishedRecovery.withOpen (next w ret) image p.session key value fits hit closed.files after.1
      i b live.named live.visible heap (progress w ret i b live.named live.visible)⟩

end ExperimentalL0.NativeFlush
