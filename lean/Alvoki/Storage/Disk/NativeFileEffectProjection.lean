import Init.Data.List.Monadic
import Init.System.IO

namespace Alvoki.Storage.DiskSession

variable {heap : Type}

namespace NativeFileEffectProjection

def result {error files α : Type} (project : heap → files) :
    EStateM.Result error heap α → EStateM.Result error files α
  | .ok value reached => .ok value (project reached)
  | .error cause reached => .error cause (project reached)

def reached {error α : Type} : EStateM.Result error heap α → heap
  | .ok _ reached | .error _ reached => reached

end NativeFileEffectProjection

/-- Each local callback fixes its projected response and file effects
and preserves the specified frame on the reached raw state. -/
def NativeFileEffectProjection {files frame α : Type} (project : heap → files) (retain : heap → frame)
    (raw : EStateM IO.Error heap α) (modeled : EStateM IO.Error files α) : Prop :=
  ∀ before, NativeFileEffectProjection.result project (raw before) = modeled (project before) ∧
    retain (NativeFileEffectProjection.reached (raw before)) = retain before

namespace NativeFileEffectProjection

theorem bind {files frame α β : Type} {project : heap → files} {retain : heap → frame}
    {raw : EStateM IO.Error heap α} {modeled : EStateM IO.Error files α}
    (step : NativeFileEffectProjection project retain raw modeled)
    {rawNext : α → EStateM IO.Error heap β} {modeledNext : α → EStateM IO.Error files β}
    (next : ∀ value, NativeFileEffectProjection project retain (rawNext value) (modeledNext value)) :
    NativeFileEffectProjection project retain (raw >>= rawNext) (modeled >>= modeledNext) := by
  intro before
  obtain ⟨observed, framed⟩ := step before
  cases result : raw before with
  | error cause reached =>
    rw [result] at observed framed
    exact ⟨by simp only [Bind.bind, EStateM.bind, result, ← observed, NativeFileEffectProjection.result],
      by simpa only [Bind.bind, EStateM.bind, result, NativeFileEffectProjection.reached] using framed⟩
  | ok value reached =>
    rw [result] at observed framed
    obtain ⟨after, retained⟩ := next value reached
    exact ⟨by simpa only [Bind.bind, EStateM.bind, result, ← observed, NativeFileEffectProjection.result] using after,
      by simpa only [Bind.bind, EStateM.bind, result] using retained.trans framed⟩

theorem pure {files frame α : Type} (project : heap → files) (retain : heap → frame) (value : α) :
    NativeFileEffectProjection project retain (pure value) (pure value) := fun _ => ⟨rfl, rfl⟩

theorem failure {files frame α : Type} (project : heap → files) (retain : heap → frame) (cause : IO.Error) :
    NativeFileEffectProjection (α := α) project retain (throw cause) (throw cause) := fun _ => ⟨rfl, rfl⟩

theorem forM {files frame α : Type} {project : heap → files} {retain : heap → frame}
    (items : List α) {raw : α → EStateM IO.Error heap Unit}
    {modeled : α → EStateM IO.Error files Unit}
    (observes : ∀ item ∈ items, NativeFileEffectProjection project retain (raw item) (modeled item)) :
    NativeFileEffectProjection project retain (items.forM raw) (items.forM modeled) := by
  induction items with
  | nil => exact NativeFileEffectProjection.pure _ _ ()
  | cons item remaining ih =>
    simp only [List.forM_eq_forM, List.forM_cons]
    exact (observes item List.mem_cons_self).bind fun _ =>
      ih fun other member => observes other (List.mem_cons_of_mem _ member)

theorem returnsOk {files frame α : Type} {project : heap → files} {retain : heap → frame}
    {raw : EStateM IO.Error heap α} {modeled : EStateM IO.Error files α}
    (observed : NativeFileEffectProjection project retain raw modeled) (before : heap) {value : α} {after : files}
    (returned : modeled (project before) = .ok value after) :
    ∃ reached, raw before = .ok value reached ∧ project reached = after ∧ retain reached = retain before := by
  obtain ⟨effect, kept⟩ := observed before
  rw [returned] at effect
  cases rawResult : raw before with
  | error cause reached =>
    simp [rawResult, result] at effect
  | ok actual reached =>
    simp only [rawResult, result, EStateM.Result.ok.injEq] at effect
    exact ⟨reached, congrArg (fun x => EStateM.Result.ok x reached) effect.1, effect.2,
      by simpa only [rawResult, NativeFileEffectProjection.reached] using kept⟩

theorem filterMapM {files frame α β : Type} {project : heap → files} {retain : heap → frame}
    (items : List α) {raw : α → EStateM IO.Error heap (Option β)}
    {modeled : α → EStateM IO.Error files (Option β)}
    (observes : ∀ item ∈ items, NativeFileEffectProjection project retain (raw item) (modeled item)) :
    NativeFileEffectProjection project retain (items.filterMapM raw) (items.filterMapM modeled) := by
  induction items with
  | nil => exact NativeFileEffectProjection.pure _ _ []
  | cons item remaining ih =>
    rw [List.filterMapM_cons, List.filterMapM_cons]
    apply (observes item List.mem_cons_self).bind
    intro first
    have tail := ih fun value member => observes value (List.mem_cons_of_mem _ member)
    cases first
    · exact tail
    · exact tail.bind fun _ => NativeFileEffectProjection.pure _ _ _

end NativeFileEffectProjection

end Alvoki.Storage.DiskSession
