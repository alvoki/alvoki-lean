import Alvoki.Storage.Disk.ManifestIntegrity
import CompactionCodec

open Alvoki.Manifest
open Alvoki.Compaction

private def oneRow (key sequence value : UInt64) : ByteArray :=
  appendV3Row (encodeV3Header 1) ⟨key, sequence, (0, value)⟩

def main : IO Unit := do
  unless checksumRun "hello".toUTF8 == 0xa430d84680aabd0b do
    throw (IO.userError "unexpected FNV-1a test vector")

  let header : Checkpoint := ⟨7, 2, 1, 2⟩
  let first := oneRow 3 1 40
  let second := oneRow 4 2 80
  let substituted := oneRow 3 1 41
  unless (parse first).isOk && (parse second).isOk && (parse substituted).isOk do
    throw (IO.userError "integrity fixtures require structurally valid v3 runs")
  let files := [first, second]
  let manifest := IntegrityCheckpoint.fromRuns header files
  let encoded := manifest.encode
  let .ok (.integrity decoded) := VersionedCheckpoint.decode encoded |
    throw (IO.userError "could not reopen integrity manifest")
  unless decoded == manifest && encoded.size == 80 && decoded.validateRuns files do
    throw (IO.userError "integrity manifest did not round trip with its runs")

  unless first.size == substituted.size && !decoded.validateRuns [substituted, second] do
    throw (IO.userError "same-length valid run substituted at one index was accepted")
  for invalid in [[second, first], [first], [first, second, first], [first.push 0, second]] do
    if decoded.validateRuns invalid then
      throw (IO.userError "reordered, missing, extra, or long run was accepted")
  for invalid in [ByteArray.empty, encoded.extract 0 7, encoded.extract 0 (encoded.size - 1),
      encoded.set! 48 (encoded[48]! ^^^ 1), encoded.push 0,
      ({ manifest with header := { header with runCount := UInt64.ofNat (UInt64.size - 1) } }).encode,
      ({ manifest with header := { header with floor := 3 } }).encode] do
    if (VersionedCheckpoint.decode invalid).isOk then
      throw (IO.userError "corrupt, wrong-size, or invalid-floor manifest was accepted")

  let .ok (.legacy legacy) := VersionedCheckpoint.decode (Alvoki.Manifest.encode header) |
    throw (IO.userError "could not reopen v1 manifest with the versioned reader")
  unless legacy == header do throw (IO.userError "v1 header changed")
  let empty := IntegrityCheckpoint.fromRuns ⟨8, 0, 0, 0⟩ []
  let .ok (.integrity decodedEmpty) := VersionedCheckpoint.decode empty.encode |
    throw (IO.userError "48-byte v2 manifest for zero runs was classified as v1")
  unless decodedEmpty == empty && decodedEmpty.validateRuns [] &&
      !(Alvoki.Manifest.decode empty.encode).isOk do
    throw (IO.userError "zero-run v2 handling changed")
  IO.println "Manifest v1 and v2, exact run bindings, and corruption checks passed."
