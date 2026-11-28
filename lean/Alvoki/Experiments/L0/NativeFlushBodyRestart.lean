import Alvoki.Experiments.L0.NativeFlushInterrupted
import Alvoki.Experiments.L0.NativeFlushStoreCut

namespace ExperimentalL0.NativeFlushInterrupted
open NativeRead (Footprint tableNamespace)
open NativeScope (W)
open NativeFlushRestart (Boot)
open NativeFlushExit (Media)
open InterruptedMutation (Prefix)

/-- The issued scan and reservation fix the sole origin of a nonempty, in-range
flush. The actual interrupted table or manifest instruction supplies both live
and durable file observations needed to reboot and read this selection. -/
theorem duringStore {p : Prefix path root start} (inScope : Ingress p physical media image events)
    (nonempty : p.session.mem.isEmpty ≠ true) (fits : image.view.tail < UInt64.size)
    (cutAt : NativeFlushStoreCut.Cut stop root image p.session (storeWorld p) cut)
    (storage : NativeFlushStore.Runtime physical root p.lock p.ref p.wal image p.session media manifest stop (storeWorld p))
    (localStops : NativeFlushStoreCut.TableStops stop physical root media image p.session (storeWorld p))
    (boot : ∀ tables, Media physical root image p.session cut tables → media.stable.Represents cut tables →
      Boot physical root media tables cut mode after) :
    (∃ h, Native.Handle.AtRoot h root p.ref ∧
      Native.flush h p.callback = NativeWrite.afterWrite p.ref (NativeFlush.store root image p.session (storeWorld p))) ∧
      Recovered physical path root p.session image events after := by
  obtain ⟨h, binding, _, ran⟩ := inScope.dispatch
  refine ⟨⟨h, binding, by simpa only [result, NativeFlushExit.resultAt, nonempty, Bool.false_eq_true, fits, ↓reduceIte] using ran⟩, ?_⟩
  obtain ⟨history, reached, saved⟩ := inScope.source
  have pre : NativeFlushStore.Pre physical root p.lock p.ref p.wal image media (storeWorld p) :=
    ⟨⟨reached.owned, reached.phase, reached.child⟩, reached.manifest, reached.catalog, saved⟩
  obtain ⟨tables, observed, stable, disk⟩ :=
    NativeFlushStoreCut.mediaResult cutAt storage pre localStops reached.installed fits
  obtain ⟨img, selected, files⟩ := observed.reboot stable disk (boot tables observed stable)
  exact recovered inScope.opened selected files

/-- The actual outer scope and the raw tree use the very same update/close/finally
recipe. On either return of the issued operation the continuation is precisely
the publication/error suffix used by the exit-cut case. -/
theorem Ingress.exitSource {p : Prefix path root start} (inScope : Ingress p physical media image events) :
    Native.withOpen path Native.flush start =
      (MutationExitCut.Instructions.ordinary.updating p.ref p.lock
        (fun s => Native.checked (flush (Native.callbackComponents root p.ref) s))) p.callback ∧
    ∀ (op : Session → MutationExitCut.PathM Session),
      MutationExitCut.updateTree p.ref p.lock op = .call p.ref.get fun old =>
        match old.beginUpdate with
        | none => MutationExitCut.close p.ref (.call p.lock.unlock.toBaseIO (fun _ => .done))
        | some (phase,s) => .call (p.ref.swap phase) fun _ =>
          op s (fun next => MutationExitCut.suffix p.ref p.lock next true)
            (fun _ => MutationExitCut.suffix p.ref p.lock s false) := by
  obtain ⟨_, bound, scope, _⟩ := inScope.dispatch
  exact ⟨by rw [scope, MutationExitCut.Instructions.updating_ordinary, Native.flush_atRoot bound],
    MutationExitCut.updateTree_eq p.ref p.lock⟩

/-- A cut in the updating callback or its finalizers. The middle interval exists
only when the real memtable and the observed WAL watermark enter the store. Both
ends use the prefix relation of the actual primitive tree. -/
inductive Position (p : Prefix path root start) (image : Selected) (stop : NativeManifestPublish.Stop)
    (volatile : MutationExitCut.LeafStop) (cut : W) : Prop where
  | reserve : MutationExitCut.Cut volatile (prelude p.ref) p.callback cut → Position p image stop volatile cut
  | store : p.session.mem.isEmpty ≠ true → image.view.tail < UInt64.size →
      NativeFlushStoreCut.Cut stop root image p.session (storeWorld p) cut → Position p image stop volatile cut
  | exit : MutationExitCut.Cut volatile (MutationExitCut.afterStore p.ref p.lock p.session (result p image))
      (WalRecoverySlice.Segmented.Native.returnedWorld (result p image)) cut → Position p image stop volatile cut

/-- One public recovery/read conclusion at any of the three consecutive intervals.
The raw restoration contract is required only for catalogs actually represented
in *both* namespaces at the cut. -/
theorem anyCut {p : Prefix path root start} (inScope : Ingress p physical media image events)
    (position : Position p image stop volatile cut)
    (reserve : MutationExitCut.Cut volatile (prelude p.ref) p.callback cut →
      MutationExitCut.Frames (NativeFlushExit.Edge physical root media image.tables) volatile (prelude p.ref) p.callback)
    (storage : p.session.mem.isEmpty ≠ true → image.view.tail < UInt64.size →
      NativeFlushStore.Runtime physical root p.lock p.ref p.wal image p.session media manifest stop (storeWorld p))
    (during : NativeFlushStoreCut.Cut stop root image p.session (storeWorld p) cut →
      NativeFlushStoreCut.TableStops stop physical root media image p.session (storeWorld p))
    (exitFrames : ∀ tables, let w := WalRecoverySlice.Segmented.Native.returnedWorld (result p image)
      Media physical root image p.session w tables → media.stable.Represents w tables →
      MutationExitCut.Frames (NativeFlushExit.Edge physical root media tables) volatile
        (MutationExitCut.afterStore p.ref p.lock p.session (result p image)) w)
    (boot : ∀ tables, Media physical root image p.session cut tables → media.stable.Represents cut tables →
      Boot physical root media tables cut mode after) :
    Recovered physical path root p.session image events after := by
  cases position with
  | reserve atCut =>
    obtain ⟨_, online, saved⟩ := inScope.online
    have frames := reserve atCut
    have edge := atCut.accumulate frames (fun _ => NativeFlushExit.Edge.same ..) NativeFlushExit.Edge.trans
    have pre : Media physical root image p.session p.callback image.tables := .original online.catalog online.manifest
    exact (beforeStore inScope atCut frames (boot _ (pre.advance edge.toFrame) (saved.frame edge.stable))).2.2
  | store nonempty fits atCut =>
    exact (duringStore inScope nonempty fits atCut (storage nonempty fits) (during atCut) boot).2
  | exit atCut => exact (afterStoreCut inScope storage atCut exitFrames boot).2

end ExperimentalL0.NativeFlushInterrupted
