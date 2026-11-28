import Alvoki.Experiments.SSTable.UnifiedNative

import Alvoki.Experiments.SSTable.Proofs.BuilderRelation

namespace SortedRun

open ImmutableSSTable ImmutableSSTable.Unified

abbrev World := Void IO.RealWorld

/-- Observe an IO action at its actual world. Keep both the original error
and reached world. This is used in proofs only. -/
def effect (action : EIO ε α) : EStateM ε World α := fun world =>
  match action world with
  | .ok value reached => .ok value reached
  | .error error reached => .error error reached

@[simp] theorem effect_pure (value : α) :
    effect (pure value : EIO ε α) = pure value := rfl

@[simp] theorem effect_throw (error : ε) :
    effect (throw error : EIO ε α) = throw error := rfl

@[simp] theorem effect_throwThe (error : ε) :
    effect (throwThe ε error : EIO ε α) = throwThe ε error := rfl

@[simp] theorem effect_bind (action : EIO ε α) (rest : α → EIO ε β) :
    effect (action >>= rest) = effect action >>= fun value => effect (rest value) := by
  funext world
  cases ran : action world <;>
    simp [effect, Bind.bind, instMonadEIO._aux_13, EST.bind, EStateM.bind, ran]

@[simp] theorem effect_map (f : α → β) (action : EIO ε α) :
    effect (f <$> action) = f <$> effect action := by
  funext world
  cases ran : action world <;>
    simp [effect, Functor.map, EStateM.map, ran, instMonadEIO._aux_1, EST.bind, EST.pure]

@[simp] theorem effect_catch (action : EIO ε α) (handler : ε → EIO ε α) :
    effect (tryCatchThe ε action handler) =
      tryCatchThe ε (effect action) (fun error => effect (handler error)) := by
  funext world
  cases ran : action world <;>
    simp [effect, tryCatchThe, MonadExceptOf.tryCatch, EStateM.tryCatch, instMonadExceptOfEIO._aux_3, EST.tryCatch,
      EStateM.Backtrackable.restore, EStateM.dummyRestore, ran]

@[simp] theorem effect_ite (p : Prop) [Decidable p] (yes no : EIO ε α) :
    effect (if p then yes else no) = if p then effect yes else effect no := by
  by_cases h : p <;> simp [h]

def effectOutput (ops : OutputOps (EIO ε) handle) : OutputOps (EStateM ε World) handle :=
  ⟨fun path mode => effect (ops.openFile path mode), fun held bytes => effect (ops.append held bytes),
    fun held => effect (ops.flush held), fun held => effect (ops.sync held),
    fun path => effect (ops.remove path)⟩

private def effectSink (sink : Sink (EIO ε)) : Sink (EStateM ε World) :=
  ⟨fun bytes => effect (sink.write bytes), effect sink.flush⟩

private def transport (invalid : String → ε) :
    BuilderRelation.Rules (EIO ε) (EStateM ε World) invalid invalid where
  rel _ _ a b := effect a = b
  ret _ := rfl
  seq first next := by
    simp only [effect_bind, first]
    exact congrArg _ (funext next)
  raise _ := rfl
  abort _ _ _ := rfl

private theorem effect_stream (crc : Checksum) (layout : Layout)
    (sink : Sink (EIO ε)) (supply : EIO ε (Option Entry))
    (invalid : String → ε) (options : BuildOptions) :
    effect (buildStream crc layout sink supply invalid options) =
      buildStream crc layout (effectSink sink) (effect supply) invalid options := by
  exact BuilderRelation.stream crc layout options (law := transport invalid)
    (left := sink) (right := effectSink sink) ⟨fun _ => rfl, rfl⟩ supply (effect supply) rfl

theorem effect_buildFileWith (ops : OutputOps (EIO ε) handle)
    (crc : Checksum) (path : System.FilePath) (layout : Layout)
    (supply : EIO ε (Option Entry)) (invalid : String → ε) (options : BuildOptions) :
    effect (buildFileWith ops crc path layout supply invalid options) =
      buildFileWith (effectOutput ops) crc path layout (effect supply) invalid options := by
  simp [buildFileWith, withFreshOutputWith, effect_stream, effectOutput, effectSink, OutputOps.sink]

end SortedRun
