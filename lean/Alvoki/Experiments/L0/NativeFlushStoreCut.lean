import Alvoki.Experiments.L0.NativeFlushStore
import Alvoki.Experiments.L0.ManifestPublishSchedule
import Alvoki.Experiments.L0.TableCreateSchedule

namespace ExperimentalL0.NativeFlushStoreCut
open System
open NativeScope (W Ref Wal)
open NativeRead (Footprint tableNamespace)
open NativeManifestPublish (Stop)
open NativeFlushStore (Pre Ready Runtime)
open NativeFlushRestart (proposal stored Boot Survivor)
open NativeReadScope (Files)
open WalRecoverySlice.Segmented (Recoverable)
open NativeTableCreate (Media)

abbrev tablePrefix := NativeTableCreate.Schedule.Prefix

inductive TableCut (stop : Stop) (dir : FilePath) (rows : Rows) (origin : W) : W → Prop where
  | start : TableCut stop dir rows origin origin
  | boundary : NativeTableCreate.Schedule.Boundary dir rows origin w → TableCut stop dir rows origin w
  | during : tablePrefix dir rows origin leaf w → stop leaf.action w t → TableCut stop dir rows origin t

private theorem TableCut.eliminate {Q : W → Prop} (cut : TableCut stop dir rows origin t) (start : Q origin)
    (boundary : ∀ w, NativeTableCreate.Schedule.Boundary dir rows origin w → Q w)
    (inside : ∀ leaf w u, tablePrefix dir rows origin leaf w → stop leaf.action w u → Q u) : Q t := by
  cases cut with
  | start => exact start
  | boundary b => exact boundary _ b
  | during h fault => exact inside _ _ _ h fault

/-- Each continuation starts at the actual preceding success. A cut in the table stage
can precede a failed allocation or a failed writer without any returned table id. -/
structure Observed (α : Type) where
  run : IO α
  cut : W → W → Prop

instance : Monad Observed where
  pure x := ⟨pure x,fun w t => t = w⟩
  bind a f := ⟨a.run >>= fun x => (f x).run, fun w t =>
    a.cut w t ∨ ∃ x u, a.run w = .ok x u ∧ (f x).cut u t⟩

def tableOp (stop : Stop) (root : FilePath) (rows : Rows) : Observed UInt64 :=
  ⟨NativeFlush.createTable root rows,
    TableCut stop (root / "tables") rows⟩

def manifestOp (stop : Stop) (root : FilePath) (version : L0Manifest.Version) : Observed Unit :=
  ⟨NativeFlush.publish root version,fun w t => t = w ∨
    version.Valid ∧ NativeManifestPublish.Cut stop (root / "manifest") (L0Manifest.encode version) w t⟩

def schedule (stop : Stop) (root : FilePath) (image : Selected) (s : Session) : Observed Session :=
  flushTableWith (tableOp stop root) (manifestOp stop root) s image.view.tail

abbrev Cut (stop : Stop) (root : FilePath) (image : Selected) (s : Session) := (schedule stop root image s).cut

theorem table_erase : Native.checked (NativeTableCreate.Schedule.project
    (NativeTableCreate.Schedule.trace (root / "tables") rows)) = (tableOp stop root rows).run := by
  rw [NativeTableCreate.Schedule.erase]
  rfl

theorem manifest_erase (h : version.Valid) : (manifestOp stop root version).run =
    (NativeManifestPublish.schedule (root / "manifest") (L0Manifest.encode version)).run := by
  rw [NativeManifestPublish.schedule_erase]
  simp only [manifestOp, NativeFlush.publish, NativeManifest.backend, L0Manifest.backend, h, ↓reduceIte,
    NativeWrite.checked_lift]

theorem erase : (schedule stop root image s).run = NativeFlush.store root image s := rfl

variable {physical : W → Footprint inode} {root : FilePath} {media : Media (tableNamespace physical root)}

/-- A table syscall may alter an unreferenced candidate. Only names and bytes of the
old catalog, the manifest selector and the independently writing WAL are protected. -/
def TableStops (stop : Stop) (physical : W → Footprint inode) (root : FilePath)
    (media : Media (tableNamespace physical root)) (image : Selected) (s : Session) (origin : W) :=
  ∀ (leaf : NativeTableCreate.Schedule.Leaf) w t, tablePrefix (root / "tables") s.mem.toList origin leaf w →
    stop leaf.action w t → MutationExitCut.Frame physical root image.tables w t ∧ media.stable.Keeps w t image.tables

def Result (physical : W → Footprint inode) (root : FilePath) (media : Media (tableNamespace physical root))
    (image : Selected) (s : Session) (cut : W) :=
  ∃ tables, NativeFlushExit.Media physical root image s cut tables ∧ media.stable.Represents cut tables ∧
    Recoverable image.view none (physical cut).disk

private theorem old (p : Pre physical root lock ref wal image media t) :
    Result physical root media image s t :=
  ⟨_,.original p.live p.manifest,p.durable,p.disk⟩

private theorem boundaryResult
    (table : NativeTableCreate.Produced media image.tables (Pre physical root lock ref wal image media) s.mem.toList origin)
    (b : NativeTableCreate.Schedule.Boundary (root / "tables") s.mem.toList origin t) :
    Result physical root media image s t :=
  old (NativeTableCreate.Schedule.Boundary.frame table b)

private theorem before {leaf : NativeTableCreate.Schedule.Leaf} {dir : FilePath} {rows : Rows}
    (hit : tablePrefix dir rows origin leaf w) : NativeTableCreate.Schedule.Boundary dir rows origin w :=
  @NativeTableCreate.Schedule.Boundary.before dir rows origin leaf w hit

private theorem duringResult (p : Pre physical root lock ref wal image media w)
    (edge : MutationExitCut.Frame physical root image.tables w t) (stable : media.stable.Keeps w t image.tables) :
    Result physical root media image s t :=
  ⟨_, (NativeFlushExit.Media.original (s := s) p.live p.manifest).advance edge,
    p.durable.frame stable, edge.disk.recoverable p.disk⟩

private theorem tableResult (cut : TableCut stop (root / "tables") s.mem.toList origin t)
    (table : NativeTableCreate.Produced media image.tables (Pre physical root lock ref wal image media)
      s.mem.toList origin)
    (start : Pre physical root lock ref wal image media origin)
    (tableStops : TableStops stop physical root media image s origin) :
    Result physical root media image s t := by
  apply cut.eliminate (old start)
  · exact fun _ site => boundaryResult table site
  · intro leaf w t hit fault
    obtain ⟨edge,stable⟩ := tableStops _ _ _ hit fault
    have site := before (dir := root / "tables") (rows := s.mem.toList) (leaf := leaf) (origin := origin) (w := w) hit
    exact duringResult (NativeTableCreate.Schedule.Boundary.frame table site) edge stable

theorem mediaResult (cut : Cut stop root image s origin t)
    (io : Runtime physical root lock ref wal image s media manifest stop origin)
    (start : Pre physical root lock ref wal image media origin)
    (tableStops : TableStops stop physical root media image s origin)
    (valid : Installed s image history) (fits : image.view.tail < UInt64.size) :
    Result physical root media image s t := by
  have table := io.tableProduced start
  have returned := table.returned
  change NativeScope.Post (NativeFlush.createTable root s.mem.toList) origin _ _ at returned
  rcases cut with early | ⟨id,w,allocated,later⟩
  · exact tableResult early table start tableStops
  · change NativeFlush.createTable root s.mem.toList origin = .ok id w at allocated
    rw [NativeScope.Post,allocated] at returned
    obtain ⟨pre,created⟩ := returned
    have ready : Ready physical root lock ref wal image s id media w := ⟨pre.toHeld,created⟩
    rcases later with (rfl | ⟨_,fault⟩) | ⟨_,z,ran,rfl⟩
    · exact old pre
    · obtain ⟨frame,allowed⟩ := fault.state (io.pinned id w allocated ready) NativeFlushStore.FileFrame.refl (io.reserved start id w allocated) pre.manifest
      let r := ready.advance frame
      exact ⟨_,.admitted id created.fresh.1 fits r.created.live allowed,r.created.durable,r.disk⟩
    · have prod := NativeFlushStore.produce io start valid fits
      rw [NativeFlush.store_eq] at prod
      change NativeFlush.publish root (proposal image s id) w = .ok () t at ran
      simp only [Bind.bind,instMonadEIO._aux_13,EST.bind,allocated,ran] at prod
      exact prod.2

theorem restart (cut : Cut stop root image s origin t)
    (io : Runtime physical root lock ref wal image s media manifest stop origin)
    (start : Pre physical root lock ref wal image media origin)
    (tableStops : TableStops stop physical root media image s origin)
    (valid : Installed s image history) (fits : image.view.tail < UInt64.size)
    (boot : ∀ tables, Boot physical root media tables t mode after) :
    ∃ selected, Survivor physical root image s after selected ∧ Files physical root selected after := by
  obtain ⟨tables,source,saved,wal⟩ := mediaResult cut io start tableStops valid fits
  exact source.reboot saved wal (boot tables)

end ExperimentalL0.NativeFlushStoreCut
