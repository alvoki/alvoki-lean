import Alvoki.Experiments.L0.NativeFlushBodyRestart

namespace ExperimentalL0.NativeFlushObserver
open System Lifecycle
open NativeScope (W Ref)
open NativeRead (Footprint tableNamespace)
open InterruptedMutation (Prefix)
open NativeFlushInterrupted (Ingress Position result storeWorld Recovered)
open ReserveScanCut (Destination View)
open MutationExitCut (LeafStop afterStore)
open NativeManifestPublish (Stop)
open WalRecoverySlice.Segmented.Native (returnedWorld)

private def restore (report : Except IO.Error α) (w : W) : EST.Out IO.Error IO.RealWorld α :=
  match report with
  | .ok x => .ok x w
  | .error e => .error e w

private def outer (ref : Ref) (lock : IO.FS.Handle) : IO Unit :=
  finish (ε := IO.Error) ((Native.phaseCell ref).close WalRecoverySlice.Segmented.Native.close) lock.unlock

/-- Observe the shared publication and complete inner/outer cleanup tree. The ordinary
value preserves primary errors and uses the actual state reached by root unlock. -/
private noncomputable def returned (stop : LeafStop) (ref : Ref) (lock : IO.FS.Handle) (s : Session)
    (report : Except IO.Error Session) : ObservedIO Unit :=
  ⟨finish (ε := IO.Error) (fun w => NativeWrite.afterWrite ref (restore report w)) (outer ref lock),
    fun w t => MutationExitCut.Cut stop (afterStore ref lock s (restore report w)) w t⟩

private def storage (stop : Stop) (root : FilePath) (s : Session) (view : View) : ObservedIO Session :=
  if view.tail < UInt64.size then
    flushTableWith (NativeFlushStoreCut.tableOp stop root) (NativeFlushStoreCut.manifestOp stop root) s view.tail
  else
    ⟨throw (IO.userError "absolute WAL position exhausted"), fun w t => t = w⟩

/-- The continuation is selected by the actual reference and scan results. A
nonempty successful scan runs the checked table/publication bind. On a reported
store error the same result handler still observes both finalizers. -/
private noncomputable def terminal (stop : Stop) (volatile : LeafStop) (root : FilePath) (ref : Ref)
    (lock : IO.FS.Handle) : Destination → ObservedIO Unit
  | .invalid =>
    ⟨finish (ε := IO.Error) (throw (IO.userError "L0 requires reopen")) (outer ref lock),
      fun w t => MutationExitCut.Cut volatile (MutationExitCut.close ref (.call lock.unlock.toBaseIO (fun _ => .done))) w t⟩
  | .skipped s => returned volatile ref lock s (.ok s)
  | .scanned s (.error e) => returned volatile ref lock s (.error e)
  | .scanned s (.ok view) => (storage stop root s view).thenResult (returned volatile ref lock s)

/-- The single observer for the recovered flush callback and its outer finalizers.
The recovery prefix supplies only the actual callback entry, reference and lock. -/
noncomputable def raw (p : Prefix path root start) (stop : Stop) (volatile : LeafStop) : ObservedIO Unit :=
  (ReserveScanCut.program p.ref fun s => !s.mem.isEmpty).observe volatile (terminal stop volatile root p.ref p.lock)

private theorem reached {p : Prefix path root start} (scope : Ingress p physical media image events) :
    (ReserveScanCut.program p.ref fun s => !s.mem.isEmpty).eval p.callback =
      ⟨if p.session.mem.isEmpty then .skipped p.session else .scanned p.session (.ok image.view), storeWorld p⟩ := by
  have scanEq : Native.checked (Native.callbackComponents root p.ref).scan =
      NativeWrite.borrow p.ref WalRecoverySlice.Segmented.Native.scan := by
    unfold Native.callbackComponents Cell.components Native.storageCallbacks
    apply NativeWrite.checked_borrow
  have d := ReserveScanCut.destination (fun s => !s.mem.isEmpty) scope.issued.read
    (fun h => (scope.issued.scan (by simpa using h)).1)
    (fun h => scanEq ▸ (scope.issued.scan (by simpa using h)).2)
  cases empty : p.session.mem.isEmpty <;> simpa [storeWorld, NativeFlush.origin, empty] using d

private theorem finishAt {body other : IO α} (equal : body w = other u) (cleanup : IO Unit) :
    finish (ε := IO.Error) body cleanup w = finish (ε := IO.Error) other cleanup u := by
  rw [finish_io body, finish_io other]
  simp only [EIO.toBaseIO, equal]

private theorem store_return (a : IO Session) (w : W) :
    restore (a.toBaseIO w).val (a.toBaseIO w).state = a w := by
  cases ran : a w <;> simp only [EIO.toBaseIO, ran, restore]

/-- The observer returns exactly the public scope's result and world, including
skipped flush, guard error, failed storage, and cleanup failure. -/
theorem erase {p : Prefix path root start} (scope : Ingress p physical media image events)
    (stop : Stop) (volatile : LeafStop) :
    (raw p stop volatile).run p.callback = Native.withOpen path Native.flush start := by
  obtain ⟨h, _, invoked, issued⟩ := scope.dispatch
  rw [invoked]
  unfold raw
  rw [ReserveScanCut.Program.observe_run, ReserveScanCut.Program.resume_eval, reached scope]
  cases empty : p.session.mem.isEmpty with
  | true =>
    simp only [empty, ↓reduceIte, NativeFlushInterrupted.result, NativeFlushExit.resultAt] at issued ⊢
    exact finishAt issued.symm _
  | false =>
    simp only [empty, Bool.false_eq_true, ↓reduceIte, NativeFlushInterrupted.result, NativeFlushExit.resultAt] at issued ⊢
    by_cases fits : image.view.tail < UInt64.size
    · simp only [fits, ↓reduceIte] at issued
      change (returned volatile p.ref p.lock p.session
        (((storage stop root p.session image.view).run).toBaseIO (storeWorld p)).val).run
          (((storage stop root p.session image.view).run).toBaseIO (storeWorld p)).state = _
      have same : (storage stop root p.session image.view).run = NativeFlush.store root image p.session := by
        simp only [storage, fits, ↓reduceIte]; rfl
      rw [same]
      apply finishAt _ _
      exact (congrArg (NativeWrite.afterWrite p.ref) (store_return _ _)).trans issued.symm
    · simp only [fits, ↓reduceIte] at issued
      change (returned volatile p.ref p.lock p.session
        (((storage stop root p.session image.view).run).toBaseIO (storeWorld p)).val).run
          (((storage stop root p.session image.view).run).toBaseIO (storeWorld p)).state = _
      simp only [storage, fits, ↓reduceIte]
      exact finishAt issued.symm _

/-- Reverse completeness starts with one cut of the composed source. Recursing
through its binds supplies the side of the store, its actual terminal world and,
where applicable, the reported error that selects cleanup. -/
theorem classify {p : Prefix path root start} (scope : Ingress p physical media image events)
    (rawCut : (raw p stop volatile).cut p.callback cut) :
    Position p image stop volatile cut := by
  rcases ReserveScanCut.Program.classify _ volatile _ rawCut with during | later
  · exact .reserve during
  rw [reached scope] at later
  cases empty : p.session.mem.isEmpty with
  | true =>
    simp only [empty, ↓reduceIte] at later
    apply Position.exit
    simpa only [result, NativeFlushExit.resultAt, empty, ↓reduceIte, returnedWorld, terminal, returned, restore] using later
  | false =>
    simp only [empty, Bool.false_eq_true, ↓reduceIte] at later
    change (storage stop root p.session image.view).cut (storeWorld p) cut ∨ _ at later
    by_cases fits : image.view.tail < UInt64.size
    · rcases later with body | exit
      · apply Position.store (by simp [empty]) fits
        simpa only [NativeFlushStoreCut.Cut, NativeFlushStoreCut.schedule, storage, fits, ↓reduceIte] using body
      · apply Position.exit
        have eq : (storage stop root p.session image.view).run = NativeFlush.store root image p.session := by
          simp only [storage, fits, ↓reduceIte]; rfl
        change MutationExitCut.Cut volatile (afterStore p.ref p.lock p.session (restore _ _)) _ cut at exit
        rw [eq, store_return] at exit
        cases r : NativeFlush.store root image p.session (storeWorld p) with
        | ok _ _ | error _ _ =>
          simpa only [result, NativeFlushExit.resultAt, empty, Bool.false_eq_true, fits, ↓reduceIte,
            EIO.toBaseIO, r, returnedWorld] using exit
    · apply Position.exit
      simp only [result, NativeFlushExit.resultAt, empty, Bool.false_eq_true, fits, ↓reduceIte, returnedWorld]
      rcases later with rejected | exit
      · have eq : cut = storeWorld p := by simpa only [storage, fits, ↓reduceIte] using rejected
        exact eq ▸ .boundary .here
      · change MutationExitCut.Cut volatile (afterStore p.ref p.lock p.session (restore _ _)) _ cut at exit
        simpa only [storage, fits, ↓reduceIte, EIO.toBaseIO, throw, throwThe, MonadExceptOf.throw, instMonadExceptOfEIO._aux_1, EST.throw, restore] using exit

/-- A caller supplies a cut of the single executable observer, including cuts
with no return from the last syscall. Public recovery constructs the flush
session and the reached storage selects the next public read's image. -/
theorem interrupted {physical : W → Footprint inode}
    {media : NativeTableCreate.Media (tableNamespace physical root)} (p : Prefix path root start)
    (entry : NativeReadScope.Entry (NativeFlushCatalog.joint physical root media) path root image)
    (files : NativeReadScope.Files physical root image start) (saved : NativeFlushCatalog.Saved physical root media image.tables start)
    (heap : WithOpenReads.Heap)
    (ops : WithOpenReads.Runtime (NativeFlushCatalog.joint physical root media) root p.lock p.ref image life heap)
    (run : Execution.Run events none image)
    (scan : ∀ history w, NativeRead.SessionAt (NativeFlushCatalog.joint physical root media) root p.lock p.ref p.wal
      p.session image history w (.updating p.wal) → NativeRecoverAt.ScanPrimitives
        (NativeFlushCatalog.joint physical root media) root p.wal image.tables w)
    (rawCut : (raw p stop volatile).cut p.callback cut)
    (reserve : MutationExitCut.Cut volatile (NativeFlushInterrupted.prelude p.ref) p.callback cut →
      MutationExitCut.Frames (NativeFlushExit.Edge physical root media image.tables) volatile
        (NativeFlushInterrupted.prelude p.ref) p.callback)
    (storage : p.session.mem.isEmpty ≠ true → image.view.tail < UInt64.size →
      NativeFlushStore.Runtime physical root p.lock p.ref p.wal image p.session media manifest stop (storeWorld p))
    (during : NativeFlushStoreCut.Cut stop root image p.session (storeWorld p) cut →
      NativeFlushStoreCut.TableStops stop physical root media image p.session (storeWorld p))
    (exitFrames : ∀ tables, let w := returnedWorld (result p image)
      NativeFlushExit.Media physical root image p.session w tables → media.stable.Represents w tables →
      MutationExitCut.Frames (NativeFlushExit.Edge physical root media tables) volatile
        (afterStore p.ref p.lock p.session (result p image)) w)
    (boot : ∀ tables, NativeFlushExit.Media physical root image p.session cut tables → media.stable.Represents cut tables →
      NativeFlushRestart.Boot physical root media tables cut mode after) :
    (raw p stop volatile).run p.callback = Native.withOpen path Native.flush start ∧
      Recovered physical path root p.session image events after := by
  have scope := NativeFlushInterrupted.ingress p entry files saved heap ops run scan
  exact ⟨erase scope stop volatile, NativeFlushInterrupted.anyCut scope (classify scope rawCut) reserve storage during exitFrames boot⟩

end ExperimentalL0.NativeFlushObserver
