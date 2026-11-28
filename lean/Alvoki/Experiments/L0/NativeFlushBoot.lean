import Alvoki.Experiments.WAL.Segmented.Proofs.AppendCut
import Alvoki.Experiments.L0.NativeFlushRestart
import Alvoki.Experiments.L0.NativeTableAllocation

namespace ExperimentalL0.NativeFlushRestart
open NativeRead (Footprint tableNamespace)
open NativeScope (W)
open System
open WalRecoverySlice.Segmented (Restart)

/-- Read the booted entry and inode from the live filesystem on process exit or
the durable filesystem on power loss. The protected catalog scopes these raw
file observations; unrelated orphan names and incomplete files are unrestricted. -/
structure Boot (physical : W → Footprint inode) (root : FilePath)
    (media : NativeTableCreate.Media (tableNamespace physical root)) (tables : Catalog)
    (cut : W) (mode : Restart) (after : W) : Prop where
  wal : WalRecoverySlice.Segmented.Native.AppendCut.Survivor (physical cut).disk mode (physical after).disk
  manifest : match mode with
    | .processExit => (physical after).manifest.active = (physical cut).manifest.active
    | .powerLoss => (physical after).manifest.active ∈ (physical cut).manifest.survivors
  table : match mode with
    | .processExit => ∀ id rows i bytes, tables id = some rows →
        (physical cut).names (tablePath (root / "tables") id) = some i →
        (physical cut).contents i = some bytes →
        (physical after).names (tablePath (root / "tables") id) = some i ∧ (physical after).contents i = some bytes
    | .powerLoss => ∀ id rows i bytes, tables id = some rows →
        media.names cut (tablePath (root / "tables") id) = some i →
        media.contents cut i = some bytes →
        (physical after).names (tablePath (root / "tables") id) = some i ∧ (physical after).contents i = some bytes

theorem Boot.catalog (boot : Boot physical root media tables cut mode after)
    (live : (tableNamespace physical root).Represents cut tables)
    (saved : media.stable.Represents cut tables) :
    (tableNamespace physical root).Represents after tables := by
  intro id rows found
  cases mode with
  | processExit =>
    obtain ⟨i, bytes, name, content, image⟩ := live id rows found
    obtain ⟨n, c⟩ := boot.table id rows i bytes found name content
    exact ⟨i, bytes, n, c, image⟩
  | powerLoss =>
    obtain ⟨i, bytes, name, content, image⟩ := saved id rows found
    obtain ⟨n, c⟩ := boot.table id rows i bytes found name content
    exact ⟨i, bytes, n, c, image⟩

theorem Boot.active (boot : Boot physical root media tables cut mode after)
    (stable : (physical cut).manifest.Stable bytes) : (physical after).manifest.active = bytes := by
  cases mode with
  | processExit => exact boot.manifest.trans stable.1
  | powerLoss => simpa only [stable.2, List.mem_singleton] using boot.manifest

theorem Boot.selected {proposal : ByteArray} (boot : Boot physical root media tables cut mode after)
    (allowed : (physical cut).manifest.Admits old (some proposal)) :
    (physical after).manifest.active = old ∨ (physical after).manifest.active = proposal := by
  have allowedAfter : DurableBlob.Permitted old (some proposal) (physical after).manifest.active := by
    cases mode with
    | processExit => rw [boot.manifest]; exact allowed.1
    | powerLoss => exact allowed.2 _ boot.manifest
  exact allowedAfter.imp_right fun h => (Option.some.inj h).symm

end ExperimentalL0.NativeFlushRestart
