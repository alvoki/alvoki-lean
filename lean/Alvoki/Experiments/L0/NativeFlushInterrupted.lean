import Alvoki.Experiments.L0.ReserveScanCut
import Alvoki.Experiments.L0.NativeFlushStore
import Alvoki.Experiments.L0.NativeFlushCatalog

namespace ExperimentalL0.NativeFlushInterrupted
open System Lifecycle
open NativeRead (Footprint tableNamespace SessionAt Online)
open NativeScope (W Ref Wal Post)
open NativeReadScope (Files)
open NativeFlushExit (resultAt Media Edge)
open NativeFlushRestart (Boot Survivor)
open MutationExitCut (Tail Cut Frames afterStore)
open InterruptedMutation (Prefix)
open WalRecoverySlice.Segmented.Native (returnedWorld)

abbrev storeWorld (p : Prefix path root start) := NativeFlush.origin p.ref p.wal p.session p.callback

abbrev result (p : Prefix path root start) (image : Selected) :=
  resultAt root image p.session (storeWorld p)

/-- This physical callback and its ready reference belong to the actual root open.
The public scope fixes the reference, lock, WAL, memtable and both sides of the
store invocation before a cut position is considered. -/
structure Ingress (p : Prefix path root start) (physical : W → Footprint inode)
    (media : NativeTableCreate.Media (tableNamespace physical root)) (image : Selected)
    (events : List Event) : Prop where
  opened : Execution.Run (events ++ [.reopened]) (some p.session) image
  online : ∃ history, Online physical root p.lock p.ref p.wal p.session image history p.callback ∧
    media.stable.Represents p.callback image.tables
  source : ∃ history, SessionAt physical root p.lock p.ref p.wal p.session image history (storeWorld p) (.updating p.wal) ∧
    media.stable.Represents (storeWorld p) image.tables
  issued : NativeFlush.Issued root p.ref p.wal p.session image p.callback
  dispatch : ∃ h, Native.Handle.AtRoot h root p.ref ∧
    Native.withOpen path Native.flush start = finish (ε := IO.Error) (Native.flush h)
      (finish (ε := IO.Error) ((Native.phaseCell p.ref).close WalRecoverySlice.Segmented.Native.close)
        p.lock.unlock) p.callback ∧ Native.flush h p.callback = NativeWrite.afterWrite p.ref (result p image)

theorem ingress {physical : W → Footprint inode} {media : NativeTableCreate.Media (tableNamespace physical root)}
    (p : Prefix path root start)
    (entry : NativeReadScope.Entry (NativeFlushCatalog.joint physical root media) path root image)
    (files : Files physical root image start) (saved : NativeFlushCatalog.Saved physical root media image.tables start)
    (heap : WithOpenReads.Heap)
    (ops : WithOpenReads.Runtime (NativeFlushCatalog.joint physical root media) root p.lock p.ref image life heap)
    (run : Execution.Run events none image)
    (scan : ∀ h w, SessionAt (NativeFlushCatalog.joint physical root media) root p.lock p.ref p.wal p.session image h w (.updating p.wal) →
      NativeRecoverAt.ScanPrimitives (NativeFlushCatalog.joint physical root media) root p.wal image.tables w) :
    Ingress p physical media image events := by
  obtain ⟨opened, history, online⟩ := p.online entry (NativeFlushCatalog.initialized files saved) heap ops run
  obtain ⟨h, binding, scope⟩ := p.withOpen Native.flush
  obtain ⟨issued, updating, invoked⟩ := NativeFlush.dispatchAt online binding heap ops.cleanup.cached ops.phase (scan history)
  exact ⟨opened, ⟨history, NativeFlushCatalog.catalogs online⟩,
    ⟨history, NativeFlushCatalog.catalogs updating⟩, issued, h, binding, scope, invoked⟩

theorem Ingress.exitState {p : Prefix path root start} (inScope : Ingress p physical media image events) :
    ((afterStore p.ref p.lock p.session (result p image)).run (returnedWorld (result p image))).state =
      returnedWorld (Native.withOpen path Native.flush start) := by
  obtain ⟨_, _, invoked, ran⟩ := inScope.dispatch
  rw [invoked]
  exact MutationExitCut.afterWrite_state _ ran p.lock p.session

noncomputable abbrev prelude (ref : Ref) := ReserveScanCut.reserveScan ref fun s => !s.mem.isEmpty

theorem prelude_state (issued : NativeFlush.Issued root ref wal s image start) :
    ((prelude ref).run start).state = NativeFlush.origin ref wal s start := by
  have path := ReserveScanCut.state (fun session => !session.mem.isEmpty) issued.read
    (fun wanted => (issued.scan (by simpa using wanted)).1)
  cases empty : s.mem.isEmpty <;> simpa [prelude, NativeFlush.origin, empty] using path

abbrev observed (events : List Event) := (((events ++ [.reopened]) ++ [.flushUncertain]) ++ [.stop])

/-- The reopened reader consumes exactly these files in the selected post-reboot
world. Its own typed postconditions retain all reported open/read/cleanup errors. -/
structure Recovered (physical : W → Footprint inode) (path root : FilePath) (s : Session) (image : Selected)
    (events : List Event) (after : W) : Prop where
  outcome : ∃ img, Survivor physical root image s after img ∧ Files physical root img after ∧
    Execution.Run (observed events) none img ∧
    ∀ (_entry : NativeReadScope.Entry physical path root img) (heap : WithOpenReads.Heap) (life : NativeRead.Lifetime)
      (_ : ∀ lock ref, WithOpenReads.Runtime physical root lock ref img life heap) (keys : List UInt64)
      (rootLife : NativeReadRelease.RootLifetime),
      let c : NativeReadRelease.RootCall := ⟨path, keys, after⟩
      Post c.run after (WithOpenReads.Finished physical root img life (observed events) c rootLife)
        (WithOpenReads.Failure physical root img life (observed events) c rootLife)

theorem recovered (run : Execution.Run (events ++ [.reopened]) (some s) image)
    (survivor : Survivor physical root image s after img) (files : Files physical root img after) :
    Recovered physical path root s image events after :=
  ⟨img, survivor, files, (survivor.uncertain run).stop, fun entry heap _ runtime keys rootLife =>
    NativeFlushRestart.uncertainReopen survivor files run entry heap runtime keys rootLife⟩

/-- Every intermediate boundary or interrupted primitive before store issue
keeps the old selection, including while waiting on the WAL mutex. -/
theorem beforeStore {p : Prefix path root start} (inScope : Ingress p physical media image events)
    (position : Cut stop (prelude p.ref) p.callback cut)
    (frames : Frames (Edge physical root media image.tables) stop (prelude p.ref) p.callback)
    (boot : Boot physical root media image.tables cut mode after) :
    ((prelude p.ref).run p.callback).state = storeWorld p ∧
      Files physical root image after ∧ Recovered physical path root p.session image events after := by
  obtain ⟨_, online, saved⟩ := inScope.online
  have keep := position.accumulate frames (fun _ => Edge.same ..) Edge.trans
  have files : Files physical root image after := ⟨boot.catalog (online.catalog.frame keep.catalog) (saved.frame keep.stable),
    boot.active ⟨keep.manifest.trans online.manifest.1, keep.survivors.trans online.manifest.2⟩,
    boot.wal.recoverable (keep.disk.recoverable (NativeReadScope.filesOfOnline online).disk)⟩
  exact ⟨prelude_state inScope.issued, files, recovered inScope.opened (.old files.manifest) files⟩

theorem Ingress.produced {p : Prefix path root start} (inScope : Ingress p physical media image events)
    (storage : p.session.mem.isEmpty ≠ true → image.view.tail < UInt64.size →
      NativeFlushStore.Runtime physical root p.lock p.ref p.wal image p.session media manifest stop (storeWorld p)) :
    ∃ tables, Media physical root image p.session (returnedWorld (result p image)) tables ∧
      media.stable.Represents (returnedWorld (result p image)) tables ∧
      WalRecoverySlice.Segmented.Recoverable image.view none (physical (returnedWorld (result p image))).disk := by
  obtain ⟨history, reached, stable⟩ := inScope.source
  have start : NativeFlushStore.Pre physical root p.lock p.ref p.wal image media (storeWorld p) :=
    ⟨⟨reached.owned, reached.phase, reached.child⟩, reached.manifest, reached.catalog, stable⟩
  by_cases empty : p.session.mem.isEmpty = true
  · simpa only [result, resultAt, empty, ↓reduceIte, returnedWorld] using
      (show ∃ tables, Media physical root image p.session (storeWorld p) tables ∧ media.stable.Represents _ tables ∧ _ from
        ⟨_, .original reached.catalog reached.manifest, stable, start.disk⟩)
  by_cases fits : image.view.tail < UInt64.size
  · simpa only [result, resultAt, empty, Bool.false_eq_true, fits, ↓reduceIte] using
      (NativeFlushStore.produce (storage empty fits) start reached.installed fits).2
  · simpa only [result, resultAt, empty, Bool.false_eq_true, fits, ↓reduceIte, returnedWorld] using
      (show ∃ tables, Media physical root image p.session (storeWorld p) tables ∧ media.stable.Represents _ tables ∧ _ from
        ⟨_, .original reached.catalog reached.manifest, stable, start.disk⟩)

/-- The actual store return determines the cleanup suffix and the media to frame.
A caller supplies raw effects only for that suffix, its cut and its retained files. -/
theorem afterStoreCut {p : Prefix path root start} (inScope : Ingress p physical media image events)
    (storage : p.session.mem.isEmpty ≠ true → image.view.tail < UInt64.size →
      NativeFlushStore.Runtime physical root p.lock p.ref p.wal image p.session media manifest manifestStop (storeWorld p))
    (cutAt : Cut stop (afterStore p.ref p.lock p.session (result p image)) (returnedWorld (result p image)) cut)
    (frames : ∀ tables, Media physical root image p.session (returnedWorld (result p image)) tables →
      Frames (Edge physical root media tables) stop (afterStore p.ref p.lock p.session (result p image)) (returnedWorld (result p image)))
    (boot : ∀ tables, Media physical root image p.session (returnedWorld (result p image)) tables →
      Boot physical root media tables cut mode after) :
    ((afterStore p.ref p.lock p.session (result p image)).run (returnedWorld (result p image))).state =
      returnedWorld (Native.withOpen path Native.flush start) ∧ Recovered physical path root p.session image events after := by
  obtain ⟨tables, source, stable, wal⟩ := inScope.produced storage
  have edge := cutAt.accumulate (frames tables source) (fun _ => Edge.same ..) Edge.trans
  obtain ⟨img, sel, files⟩ := (source.advance edge.toFrame).reboot (stable.frame edge.stable)
    (edge.disk.recoverable wal) (boot tables source)
  exact ⟨inScope.exitState, recovered inScope.opened sel files⟩

end ExperimentalL0.NativeFlushInterrupted
