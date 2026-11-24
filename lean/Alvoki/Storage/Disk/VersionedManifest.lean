import Alvoki.Storage.Disk.LegacyManifest
import Alvoki.Storage.Disk.ManifestIntegrity

namespace Alvoki.Manifest
open Alvoki.ByteWords

/-! Both formats are interpreted here for verification of publication and recovery. -/

/-- The version tag distinguishes an original manifest from one with a
run integrity table. -/
inductive VersionedCheckpoint where
  | legacy (header : Checkpoint)
  | integrity (manifest : IntegrityCheckpoint)
  deriving Repr, DecidableEq

def VersionedCheckpoint.header : VersionedCheckpoint → Checkpoint
  | .legacy header => header
  | .integrity manifest => manifest.header

def VersionedCheckpoint.encode : VersionedCheckpoint → ByteArray
  | .legacy header => Manifest.encode header
  | .integrity manifest => manifest.encode

def VersionedCheckpoint.decode (bytes : ByteArray) : Except String VersionedCheckpoint :=
  if bytes.size < 8 then .error "invalid manifest length"
  else if word bytes 0 = integrityMagic then .integrity <$> IntegrityCheckpoint.decode bytes
  else .legacy <$> Manifest.decode bytes

private theorem legacyTag (header : Checkpoint) : word (Manifest.encode header) 0 = 0x31464e4d4f564c41 := by
  change word (encodeWords ([0x31464e4d4f564c41, header.generation, header.committed,
    header.floor, header.runCount] ++ [_])) (8 * 0) = _
  rw [word_encodeWords]
  · rfl
  · simp

theorem VersionedCheckpoint.decode_legacy {bytes : ByteArray} {header : Checkpoint}
    (accepted : Manifest.decode bytes = .ok header) :
    VersionedCheckpoint.decode bytes = .ok (.legacy header) := by
  have tag : word bytes 0 ≠ integrityMagic := by
    rw [← Manifest.decode_reencode accepted, legacyTag]
    decide
  have enough : ¬ bytes.size < 8 := by rw [← Manifest.decode_reencode accepted, Manifest.encode_size]; decide
  simp [VersionedCheckpoint.decode, enough, tag, accepted, Functor.map, Except.map]

theorem VersionedCheckpoint.decode_integrity {bytes : ByteArray} {manifest : IntegrityCheckpoint}
    (accepted : IntegrityCheckpoint.decode bytes = .ok manifest) :
    VersionedCheckpoint.decode bytes = .ok (.integrity manifest) := by
  have tag : word bytes 0 = integrityMagic := by
    rw [← (IntegrityCheckpoint.decode_spec accepted).1, IntegrityCheckpoint.encodedTag]
  have enough : ¬ bytes.size < 8 := by rw [← (IntegrityCheckpoint.decode_spec accepted).1, manifest.encode_size]; omega
  simp [VersionedCheckpoint.decode, enough, tag, accepted, Functor.map, Except.map]

theorem VersionedCheckpoint.decode_reencode {bytes : ByteArray} {manifest : VersionedCheckpoint}
    (accepted : VersionedCheckpoint.decode bytes = .ok manifest) : manifest.encode = bytes := by
  unfold VersionedCheckpoint.decode at accepted
  split at accepted
  · contradiction
  split at accepted
  · cases decoded : IntegrityCheckpoint.decode bytes with
    | error message => simp [decoded, Functor.map, Except.map] at accepted
    | ok parsed =>
      simp [decoded, Functor.map, Except.map] at accepted
      subst manifest
      exact (IntegrityCheckpoint.decode_spec decoded).1
  · cases decoded : Manifest.decode bytes with
    | error message => simp [decoded, Functor.map, Except.map] at accepted
    | ok parsed =>
      simp [decoded, Functor.map, Except.map] at accepted
      subst manifest
      exact Manifest.decode_reencode decoded

theorem IntegrityCheckpoint.legacy_reader_rejects (manifest : IntegrityCheckpoint) (header : Checkpoint) :
    Manifest.decode manifest.encode ≠ .ok header := by
  intro accepted
  have tag := congrArg (fun bytes => word bytes 0) (Manifest.decode_reencode accepted)
  rw [legacyTag, IntegrityCheckpoint.encodedTag] at tag
  exact (by decide : (0x31464e4d4f564c41 : UInt64) ≠ integrityMagic) tag

/-- The v2-only decoder rejects every checkpoint emitted by the old writer. -/
theorem IntegrityCheckpoint.rejectsLegacy (header : Checkpoint) :
    ∃ cause, IntegrityCheckpoint.decode (Manifest.encode header) = .error cause := by
  cases decoded : IntegrityCheckpoint.decode (Manifest.encode header) with
  | error cause => exact ⟨cause, rfl⟩
  | ok manifest =>
    have tag := congrArg (fun bytes => word bytes 0) (IntegrityCheckpoint.decode_spec decoded).1
    rw [IntegrityCheckpoint.encodedTag, legacyTag] at tag
    exact False.elim ((by decide : integrityMagic ≠ (0x31464e4d4f564c41 : UInt64)) tag)

end Alvoki.Manifest
