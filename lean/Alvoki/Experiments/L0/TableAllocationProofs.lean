import Alvoki.Experiments.L0.TableAllocation
import Alvoki.Experiments.L0.ComponentContract
import Alvoki.Experiments.L0.TableRowProofs
import Alvoki.Experiments.SSTable.Proofs.UnifiedNativeEndToEnd

namespace ExperimentalL0

/-- The syscall reports presence at the reached name and leaves the
namespace unchanged. Recursion adds only successive probes. -/
theorem freeTableId_spec (occupied : UInt64 → StorageM σ Bool) (image : σ → α)
    (present : α → UInt64 → Bool)
    (probe : ∀ s id, match occupied id s with
      | .ok result after => result = present (image s) id ∧ image after = image s
      | .error _ after => image after = image s)
    (next : Nat) (s : σ) :
    match freeTableId occupied next s with
    | .ok id after => present (image s) id = false ∧ image after = image s
    | .error _ after => image after = image s := by
  rw [freeTableId]
  by_cases full : next ≥ UInt64.size
  · simp [full]
    rfl
  · have report := probe s next.toUInt64
    cases issue : occupied next.toUInt64 s with
    | error error after =>
      rw [issue] at report
      simpa [full, Bind.bind, EStateM.bind, issue] using report
    | ok result after =>
      rw [issue] at report
      cases result
      · simp [full, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure, issue]
        exact ⟨report.1.symm, report.2⟩
      · have tail := freeTableId_spec occupied image present probe (next + 1) after
        simp [full, Bind.bind, EStateM.bind, issue]
        cases recurse : freeTableId occupied (next + 1) after <;>
          simp_all
termination_by UInt64.size - next
decreasing_by omega

/-- Every successful result passed the original rows to the builder under the
returned ID, and reached a successful directory barrier afterward. -/
theorem createTableAt_success {id : UInt64}
    {occupied : UInt64 → StorageM σ Bool} {build : UInt64 → Rows → StorageM σ Unit}
    {syncDirectory : StorageM σ Unit}
    (ran : createTableAt occupied build syncDirectory rows s = .ok id after) :
    ∃ reserved built, freeTableId occupied 0 s = .ok id reserved ∧
      build id rows reserved = .ok () built ∧ syncDirectory built = .ok () after := by
  unfold createTableAt at ran
  cases probe : freeTableId occupied 0 s with
  | error error reached => simp [Bind.bind, EStateM.bind, probe] at ran
  | ok name reserved =>
    cases built : build name rows reserved with
    | error error reached => simp [Bind.bind, EStateM.bind, probe, built] at ran
    | ok value reached =>
      cases sync : syncDirectory reached with
      | error error reached => simp [Bind.bind, EStateM.bind, probe, built, sync] at ran
      | ok value synced =>
        simp [Bind.bind, EStateM.bind, Pure.pure, EStateM.pure, probe, built, sync] at ran
        obtain ⟨rfl, rfl⟩ := ran
        exact ⟨reserved, reached, rfl, built, sync⟩

def Selected.TableFrame (before after : Selected) : Prop :=
  after.view = before.view ∧ after.version = before.version ∧ before.tables.Preserves after.tables

private theorem Selected.TableFrame.trans {before middle after : Selected} (first : before.TableFrame middle)
    (second : middle.TableFrame after) : before.TableFrame after :=
  ⟨second.1.trans first.1, second.2.1.trans first.2.1,
    fun id rows bound => second.2.2 id rows (first.2.2 id rows bound)⟩

/-- A probe has no effects. A file build may leave an orphan on either
outcome but keeps other bindings. A successful directory barrier installs
a file that the builder left prepared. Derive the L0 creation law from
these separate effects of the actual creation schedule. -/
theorem createTableAt_bindings
    (selected : σ → Selected) (names : σ → UInt64 → Bool)
    (prepared : σ → UInt64 → Rows → Prop)
    (occupied : UInt64 → StorageM σ Bool) (build : UInt64 → Rows → StorageM σ Unit)
    (syncDirectory : StorageM σ Unit)
    (absent : ∀ s id, names s id = false → (selected s).tables id = none)
    (probe : ∀ s id, match occupied id s with
      | .ok result after => result = names s id ∧ (names after, selected after) = (names s, selected s)
      | .error _ after => (names after, selected after) = (names s, selected s))
    (buildEffect : ∀ s id rows, match build id rows s with
      | .ok _ after => (selected s).TableFrame (selected after) ∧ prepared after id rows
      | .error _ after => (selected s).TableFrame (selected after))
    (syncEffect : ∀ s, match syncDirectory s with
      | .ok _ after => (selected s).TableFrame (selected after) ∧
          ∀ id rows, prepared s id rows → (selected after).tables id = some rows
      | .error _ after => (selected s).TableFrame (selected after))
    (rows : Rows) (s : σ) :
    match createTableAt occupied build syncDirectory rows s with
    | .ok id after => (selected after).view = (selected s).view ∧
        (selected after).version = (selected s).version ∧
        (selected s).tables.Created (selected after).tables id rows
    | .error _ after => (selected s).TableFrame (selected after) := by
  have free := freeTableId_spec occupied (fun state => (names state, selected state)) (·.1)
    probe 0 s
  unfold createTableAt
  cases allocated : freeTableId occupied 0 s with
  | error error after =>
    rw [allocated] at free
    have frame : selected after = selected s := congrArg Prod.snd free
    simp [Bind.bind, EStateM.bind, allocated, frame, Selected.TableFrame, Catalog.Preserves]
  | ok id reserved =>
    rw [allocated] at free
    have frame : selected reserved = selected s := congrArg Prod.snd free.2
    have built := buildEffect reserved id rows
    cases done : build id rows reserved with
    | error error after =>
      rw [done] at built
      simpa [Bind.bind, EStateM.bind, allocated, done, frame] using built
    | ok value written =>
      rw [done] at built
      have synced := syncEffect written
      cases barrier : syncDirectory written with
      | error error after =>
        rw [barrier] at synced
        have kept := built.1.trans synced
        simpa [Bind.bind, EStateM.bind, allocated, done, barrier, frame] using kept
      | ok value after =>
        rw [barrier] at synced
        have kept := built.1.trans synced.1
        rw [frame] at kept
        simp [Bind.bind, EStateM.bind, Pure.pure, EStateM.pure, allocated, done, barrier]
        exact ⟨kept.1, kept.2.1, absent s id free.1, synced.2 id rows built.2, kept.2.2⟩

open ImmutableSSTable Unified

/-- The successful writer and parent barrier publish the same inode at
the allocated name. The contents and format come from the writer theorem. -/
theorem createTableUnder_image {id : UInt64}
    {dir : System.FilePath} {occupied : System.FilePath → StorageM σ Bool}
    {build : System.FilePath → UInt64 → Rows → StorageM σ Unit}
    {syncDirectory : System.FilePath → StorageM σ Unit}
    {inode writer : Type}
    (names durableNames : σ → System.FilePath → Option inode)
    (contents : σ → inode → Option ByteArray)
    (outputOps : OutputOps (NativeWriteM writer inode) writer)
    (nextRow : NativeWriteM writer inode (Option Entry))
    (effects : ∀ path, NativeWriteEffects outputOps path nextRow)
    (buildCall : ∀ path allocated input before after, build path allocated input before = .ok () after →
      ∃ initial written count,
        initial.rows = (readSupplied input.length |>.run input).1 ∧
        (buildFileWith outputOps Alvoki.CRC32C.extend path (tableLayout allocated) nextRow (fun message => message)).run initial =
          .ok count written ∧
        ∀ output identity bytes, written.BoundTo path output identity →
          written.durable = some (identity, bytes) →
          names after path = some identity ∧ contents after identity = some bytes)
    (directoryEffect : ∀ before after, syncDirectory dir before = .ok () after →
      ∀ id identity bytes, names before (tablePath dir id) = some identity →
        contents before identity = some bytes →
        durableNames after (tablePath dir id) = some identity ∧ contents after identity = some bytes)
    (created : createTableUnder dir occupied build syncDirectory rows s = .ok id after) :
    ∃ identity bytes, durableNames after (tablePath dir id) = some identity ∧ contents after identity = some bytes ∧
      Image Alvoki.CRC32C.extend (tableLayout id)
        (rows.map (Entry.encode keyCodec mutationCodec)) bytes := by
  obtain ⟨_, written, _, built, barrier⟩ := createTableAt_success created
  obtain ⟨initial, reached, _, input, run, installed⟩ := buildCall _ _ _ _ _ built
  obtain ⟨_, _, image, output, identity, bound, _, durable, _⟩ :=
    buildFileWith_refines (effects (tablePath dir id)) run
  obtain ⟨name, content⟩ := installed output identity reached.appended bound durable
  obtain ⟨published, persisted⟩ := directoryEffect written after barrier id identity reached.appended name content
  have exactInput : (readSupplied rows.length |>.run rows).1 =
      rows.map (Entry.encode keyCodec mutationCodec) := (supplied_builder_input rows).2
  rw [input, exactInput] at image
  exact ⟨identity, reached.appended, published, persisted, image⟩

end ExperimentalL0
