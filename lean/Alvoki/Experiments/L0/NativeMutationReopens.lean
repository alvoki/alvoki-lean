import Alvoki.Experiments.L0.NativeMutationScope

namespace ExperimentalL0.NativeMutationScope
open System NativeScope NativeReadRelease
open NativeRead (Footprint Lifetime)
open WalRecoverySlice.Segmented.Native (PhaseMemory)

abbrev deliveredEvents (before : List Event) (change : Change) :=
  ((before ++ [.reopened]) ++ [.written change]) ++ [.stop]

/-- Each failed public mutation determines both the request and the image
on which the first reopen starts. The two calls also retain their own
validation, read, release and cleanup outcomes. -/
inductive FailedReopens (physical : W → Footprint inode) (heap : PhaseMemory)
    (path root : FilePath) (before : List Event) (image : Selected) (change : Change)
    (life : Lifetime) (a b : List UInt64) (rootLife : RootLifetime) (err : IO.Error) (w : W) : Prop where
  | unopened : Retry physical root (before ++ [.openFailed]) image none w →
      PendingReadScope.TwoReads none physical path root image life (before ++ [.openFailed]) w a b rootLife →
      FailedReopens physical heap path root before image change life a b rootLife err w
  | rejected : ¬ image.view.tail + 1 < UInt64.size →
      Closed physical root lock ref image w →
      PendingReadScope.TwoReads none physical path root image life (uncertainEvents before change) w a b rootLife →
      FailedReopens physical heap path root before image change life a b rootLife err w
  | reported : WalRecoverySlice.Segmented.Native.append wal (encode change) issued = .error err appended →
      Closed physical root lock ref image w (some (.append (encode change))) →
      PendingReadScope.TwoReads (some (.append (encode change))) physical path root image life
        (uncertainEvents before change) w a b rootLife →
      FailedReopens physical heap path root before image change life a b rootLife err w
  | cleanup : Written physical heap root (before ++ [.reopened]) image change w →
      PendingReadScope.TwoReads none physical path root (image.append (encode change)) life
        (uncertainEvents before change) w a b rootLife →
      FailedReopens physical heap path root before image change life a b rootLife err w

structure MutationReopens (physical : W → Footprint inode) (heap : PhaseMemory)
    (path root : FilePath) (before : List Event) (image : Selected) (change : Change)
    (start : W) (life : Lifetime) (a b : List UInt64) (rootLife : RootLifetime) : Prop where
  released : (mutationCall path change start).Released rootLife
  returned : Post (Native.withOpen path (fun h => Native.mutation h change)) start
    (fun _ w => Written physical heap root (before ++ [.reopened]) image change w ∧
      PendingReadScope.TwoReads none physical path root (image.append (encode change)) life
        (deliveredEvents before change) w a b rootLife ∧
      PendingReadScope.TwoReads none physical path root (image.append (encode change)) life
        (uncertainEvents before change) w a b rootLife)
    (fun err w => Failure physical heap root before image change err w ∧
      FailedReopens physical heap path root before image change life a b rootLife err w)

/-- Feed the concrete mutation's reached world to both public reopens. A
success and its lost acknowledgement share the settled extended WAL; a
reported append failure carries precisely the issued encoded mutation. -/
theorem withOpen_twice
    (produced : Post (Native.withOpen path (fun h => Native.mutation h change)) start
      (fun _ => Written physical heap root (before ++ [.reopened]) image change)
      (Failure physical heap root before image change))
    (original : Reopens physical heap path root image life none)
    (uncertain : Reopens physical heap path root image life (some (.append (encode change))))
    (extended : Reopens physical heap path root (image.append (encode change)) life none)
    (a b : List UInt64) (rootLife : RootLifetime) :
    MutationReopens physical heap path root before image change start life a b rootLife := by
  refine ⟨mutation_released path change start rootLife, produced.weaken ?_ ?_⟩
  · intro _ w written
    exact ⟨written, written.delivered.readTwice extended a b rootLife, written.lost.readTwice extended a b rootLife⟩
  · intro e w failed
    refine ⟨failed, ?_⟩
    cases failed with
    | unopened retry => exact .unopened retry (retry.readTwice original a b rootLife)
    | rejected guard closed retry => exact .rejected guard closed (retry.readTwice original a b rootLife)
    | reported issued closed retry => exact .reported issued closed (retry.readTwice uncertain a b rootLife)
    | cleanup written => exact .cleanup written (written.lost.readTwice extended a b rootLife)

end ExperimentalL0.NativeMutationScope
