import Alvoki.Experiments.DurableBlob.Proofs
import Alvoki.Experiments.Manifest.Proofs

namespace L0Manifest.RefinementExperiment
open DurableBlob

private def directory : System.FilePath := "manifest"
private def healthy : LinuxEffects.Reports :=
  ⟨true, true, .ok, true, true, true, .ok, .ok⟩
private def proposed : Version := ⟨[7], 1⟩
private def oldBytes : ByteArray := encode Version.empty
private def newBytes : ByteArray := encode proposed
private def uncertainImage : Image := ⟨newBytes, [newBytes, oldBytes], none, none⟩

private def lostRename : Backend (EStateM Unit Image) ByteArray :=
  LinuxEffects.backend directory { healthy with rename := .afterEffect }
private def lateBarrier : Backend (EStateM Unit Image) ByteArray :=
  LinuxEffects.backend directory { healthy with syncDirectory := .afterEffect }
private def healthyBlob := LinuxEffects.backend directory healthy

private theorem renameCut :
    lostRename.publish newBytes (.settled oldBytes) = .error () uncertainImage := by
  simp [lostRename, LinuxEffects.backend, Primitives.backend, Primitives.files, Files.backend,
    LinuxEffects.primitives, healthy, Bind.bind, EStateM.bind] <;> rfl

private theorem barrierCut :
    lateBarrier.reopen uncertainImage = .error () (.settled newBytes) := by
  simp [lateBarrier, LinuxEffects.backend, Primitives.backend, Primitives.files, Files.backend,
    LinuxEffects.primitives, healthy, Bind.bind, EStateM.bind] <;> rfl

private theorem healthyRetry :
    healthyBlob.reopen (.settled newBytes) = .ok newBytes (.settled newBytes) := by
  simp [healthyBlob, LinuxEffects.backend, Primitives.backend, Primitives.files, Files.backend,
    LinuxEffects.primitives, healthy, Bind.bind, EStateM.bind] <;> rfl

/-- The actual typed consumer observes the same version after failed recovery
and after power loss. The failure itself follows the effected directory sync. -/
theorem typedRetry :
    Run oldBytes [.opened oldBytes, .uncertain newBytes, .openFailed, .opened newBytes]
      true (.settled newBytes) ∧
    (L0Manifest.backend (fun _ => ()) healthyBlob).reopen (.settled newBytes) =
      .ok proposed (.settled newBytes) := by
  have firstOpen : Run oldBytes [.opened oldBytes] true (.settled oldBytes) :=
    (Run.initial (initial := oldBytes)).healthy_open
  have submitted := LinuxEffects.publishUncertain directory
    { healthy with rename := .afterEffect } newBytes firstOpen
  change Run oldBytes _ false
    (match lostRename.publish newBytes (.settled oldBytes) with
     | .ok _ after | .error _ after => after) at submitted
  rw [renameCut] at submitted
  have attempted := LinuxEffects.reopen directory { healthy with syncDirectory := .afterEffect } submitted
  change (match lateBarrier.reopen uncertainImage with
    | .ok bytes after => Run oldBytes (_ ++ [.opened bytes]) true after
    | .error _ after => Run oldBytes (_ ++ [.openFailed]) false after) at attempted
  rw [barrierCut] at attempted
  have retry := LinuxEffects.reopen directory healthy attempted
  change (match healthyBlob.reopen (.settled newBytes) with
    | .ok bytes after => Run oldBytes (_ ++ [.opened bytes]) true after
    | .error _ after => Run oldBytes (_ ++ [.openFailed]) false after) at retry
  rw [healthyRetry] at retry
  refine ⟨retry, ?_⟩
  simp only [L0Manifest.backend, Bind.bind, EStateM.bind, healthyRetry]
  rw [show decode newBytes = some proposed from decode_encode (by decide)]
  rfl

theorem typedRetry_same :
    let start := Image.settled oldBytes
    let first := uncertainImage
    let pinned := Image.settled newBytes
    lostRename.publish newBytes start = .error () first ∧
      lateBarrier.reopen first = .error () pinned ∧
      healthyBlob.reopen pinned = .ok newBytes pinned ∧
      pinned.Stable newBytes := by
  dsimp only
  have pending := (LinuxEffects.publishUncertainAdmits directory
    { healthy with rename := .afterEffect } (before := Image.settled oldBytes)
    (old := oldBytes) ⟨rfl, rfl⟩ newBytes).2
  change (match lostRename.publish newBytes (.settled oldBytes) with
    | .ok _ after | .error _ after => after).Admits oldBytes (some newBytes) at pending
  rw [renameCut] at pending
  have afterFailure := (LinuxEffects.reopenFailedAdmits directory
    { healthy with syncDirectory := .afterEffect } pending
    (after := Image.settled newBytes) (err := ()) barrierCut).2
  have settled := LinuxEffects.reopenAgain directory healthy healthy afterFailure
    (bytes := newBytes) (again := newBytes) (settled := Image.settled newBytes)
    (rebooted := Image.settled newBytes) (after := Image.settled newBytes)
    healthyRetry (.inr ⟨newBytes, by simp [Image.settled], rfl⟩) healthyRetry
  exact ⟨renameCut, barrierCut, healthyRetry, settled.2⟩

/-- Lose a successful publication reply, then use the existing healthy
open theorem on the exact reached image. -/
theorem lostSuccess :
    Run oldBytes [.opened oldBytes, .uncertain newBytes, .opened newBytes]
      true (.settled newBytes) := by
  have firstOpen : Run oldBytes [.opened oldBytes] true (.settled oldBytes) :=
    (Run.initial (initial := oldBytes)).healthy_open
  have reached := LinuxEffects.publishUncertain directory healthy newBytes firstOpen
  have ack : healthyBlob.publish newBytes (.settled oldBytes) = .ok () (.settled newBytes) := by
    simp [healthyBlob, LinuxEffects.backend, Primitives.backend, Primitives.files, Files.backend,
      LinuxEffects.primitives, healthy, Bind.bind, EStateM.bind] <;> rfl
  change Run oldBytes _ false
    (match healthyBlob.publish newBytes (.settled oldBytes) with
     | .ok _ after | .error _ after => after) at reached
  rw [ack] at reached
  exact reached.healthy_open

end L0Manifest.RefinementExperiment
