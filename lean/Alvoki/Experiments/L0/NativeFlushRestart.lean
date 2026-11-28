import Alvoki.Experiments.L0.WithOpenReads

namespace ExperimentalL0.NativeFlushRestart
open System NativeRead NativeReadScope
open WalRecoverySlice.Segmented

/-- The exact catalog entry created from the live session before manifest publication. -/
def stored (before : Selected) (session : Session) (id : UInt64) : Selected :=
  { before with tables := fun k => if k = id then some session.mem.toList else before.tables k }

def proposal (before : Selected) (session : Session) (id : UInt64) : L0Manifest.Version :=
  ⟨id :: session.version.tables, before.view.tail.toUInt64⟩

def published (before : Selected) (session : Session) (id : UInt64) : Selected :=
  (stored before session id).publish (proposal before session id)

/-- This proof uses the actual memtable rows, so it works for every history admitted
by the incoming trace, including overwrites and tombstones. -/
theorem installedPublished {id : UInt64} (installed : Installed session before history)
    (fresh : before.tables id = none) (fits : before.view.tail < UInt64.size) :
    Installed ⟨proposal before session id, ∅⟩ (published before session id) history := by
  obtain ⟨d, version, mem⟩ := installed
  have created : before.tables.Created (stored before session id).tables id session.mem.toList := by
    refine ⟨fresh, by simp [stored], ?_⟩
    intro k rows bound
    have ne : k ≠ id := by rintro rfl; simp [fresh] at bound
    simpa [stored, ne] using bound
  have contents (key : UInt64) : lookupRows session.mem.toList key = latest d.pending key := by
    simp [rows_lookup, mem, replay_lookup]
  let choices := flushPublicationChoices d (stored := stored before session id) rfl rfl created
    contents (rows_ordered session.mem) fits
  have sel : proposal before session id =
      ⟨id :: before.version.tables, before.view.tail.toUInt64⟩ := by simp [proposal, version]
  change Installed ⟨proposal before session id, ∅⟩ ((stored before session id).publish _) history
  rw [sel]
  exact ⟨choices.2, rfl, rfl⟩

/-- At an old-manifest survivor, even a complete unreferenced table under the candidate
name is unnecessary for restart. At a published survivor its actual binding is required. -/
inductive Survivor (physical : NativeScope.W → Footprint inode) (root : FilePath)
    (before : Selected) (session : Session) (w : NativeScope.W) : Selected → Prop where
  | old (active : (physical w).manifest.active = L0Manifest.encode before.version) :
      Survivor physical root before session w before
  | newTable (id : UInt64) (fresh : before.tables id = none) (fits : before.view.tail < UInt64.size)
      (bound : (tableNamespace physical root).Bound w id session.mem.toList)
      (active : (physical w).manifest.active = L0Manifest.encode (proposal before session id)) :
      Survivor physical root before session w (published before session id)

theorem Survivor.files (s : Survivor physical root before session w image)
    (oldTables : (tableNamespace physical root).Represents w before.tables)
    (wal : Recoverable before.view none (physical w).disk) : Files physical root image w := by
  cases s with
  | old active => exact ⟨oldTables, active, wal⟩
  | newTable id fresh fits bound active =>
    exact ⟨oldTables.insert (fun _ _ _ _ _ name content => ⟨name, content⟩) bound, active, wal⟩

theorem Survivor.uncertain (s : Survivor physical root before session w image)
    (prior : Execution.Run events (some session) before) :
    Execution.Run (events ++ [.flushUncertain]) none image := by
  apply prior.flushUncertain
  intro history installed
  cases s with
  | old _ => obtain ⟨d, _⟩ := installed; exact ⟨d⟩
  | newTable id fresh fits _ _ =>
    obtain ⟨d, _⟩ := installedPublished installed fresh fits
    exact ⟨d⟩

/-- The success path first acknowledges the flush, then loses the live session on
close or process exit. Both empty and published flushes preserve the client history. -/
theorem publishedStop {id : UInt64} (prior : Execution.Run events (some session) before)
    (fresh : before.tables id = none) (fits : before.view.tail < UInt64.size) :
    Execution.Run ((events ++ [.flushed]) ++ [.stop]) none (published before session id) :=
  (prior.flushed fun _ installed => installedPublished installed fresh fits).stop

theorem unchangedStop (prior : Execution.Run events (some session) before) :
    Execution.Run ((events ++ [.flushed]) ++ [.stop]) none before :=
  (prior.flushed fun _ installed => installed).stop

/-- Reuse the reached storage world as the starting world of the next public call.
Recovery can fail before invoking the callback. Successful recovery performs the
requested reads, including caught errors, and then closes the actual owned session. -/
theorem withOpen (survivor : Survivor physical root before session w image)
    (catalog : (tableNamespace physical root).Represents w before.tables)
    (wal : Recoverable before.view none (physical w).disk)
    (prior : Execution.Run events none image) (entry : Entry physical path root image)
    (heap : WithOpenReads.Heap) (runtime : ∀ lock ref, WithOpenReads.Runtime physical root lock ref image life heap)
    (keys : List UInt64) (rootLife : NativeReadRelease.RootLifetime) :
    NativeScope.Post (Native.withOpen path (fun h => (readMany h keys : IO (List Reply)))) w
      (WithOpenReads.Finished physical root image life events ⟨path, keys, w⟩ rootLife)
      (WithOpenReads.Failure physical root image life events ⟨path, keys, w⟩ rootLife) :=
  WithOpenReads.withOpen entry (survivor.files catalog wal) heap runtime prior keys rootLife

/-- A lost reply can leave either manifest selected. The subsequent process stop is
recorded distinctly from the uncertain flush and from the later public open. -/
theorem uncertainReopen (survivor : Survivor physical root before session w image)
    (files : Files physical root image w) (prior : Execution.Run events (some session) before)
    (entry : Entry physical path root image) (heap : WithOpenReads.Heap)
    (runtime : ∀ lock ref, WithOpenReads.Runtime physical root lock ref image life heap)
    (keys : List UInt64) (rootLife : NativeReadRelease.RootLifetime) :
    let stopped := (events ++ [.flushUncertain]) ++ [.stop]
    NativeScope.Post (Native.withOpen path (fun h => (readMany h keys : IO (List Reply)))) w
      (WithOpenReads.Finished physical root image life stopped ⟨path, keys, w⟩ rootLife)
      (WithOpenReads.Failure physical root image life stopped ⟨path, keys, w⟩ rootLife) :=
  WithOpenReads.withOpen entry files heap runtime (survivor.uncertain prior).stop keys rootLife

/-- On the published branch replay starts at the exact WAL tail. Every recovered
lookup reaches the newly installed table first, including lookups for absent keys. -/
theorem publishedLookup {id : UInt64}
    (installed : Installed recovered (published before session id) history)
    (fits : before.view.tail < UInt64.size)
    (phase : (ref.get : IO (Lifecycle.Phase NativeRead.Wal)) start = .ok (.online wal recovered) w) (key : UInt64) :
    Call.mk dir id (.lookup key) w ∈ publicCalls ref dir key start := by
  obtain ⟨d, version, mem⟩ := installed
  have replayed := d.replay_pending
  change (before.view.batches.drop
    (before.view.tail.toUInt64.toNat - before.view.base)).mapM decode = some d.pending at replayed
  rw [UInt64.toNat_ofNat_of_lt' fits] at replayed
  simp [Contract.View.tail] at replayed
  apply callsFirst phase
  · rw [mem, replayed]
    rfl
  · rw [version]
    rfl

/-- Under the old manifest the orphan cannot appear anywhere in the reached
lookup trace, even when every older table is visited. -/
theorem orphanIgnored {id : UInt64} (fresh : before.tables id = none)
    (installed : Installed recovered before history)
    (phase : (ref.get : IO (Lifecycle.Phase NativeRead.Wal)) start = .ok (.online wal recovered) w)
    (member : c ∈ publicCalls ref dir key start) : c.id ≠ id := by
  obtain ⟨durable, version, _⟩ := installed
  have listed := callsInManifest phase member
  rw [version] at listed
  intro eq
  obtain ⟨rows, bound⟩ := durable.boundTable c.id listed
  simp [eq, fresh] at bound

/-- The first recovered public get in a completed scope really did visit the table
created by the flush. Its actual reply satisfies the recovered history and its
descriptor has left the private scope, including when the first read reported an error. -/
theorem finishedPublishedLookup {id : UInt64}
    (finished : WithOpenReads.Finished physical root (published before session id) life events
      ⟨path, key :: keys, start⟩ rootLife replies after)
    (fits : before.view.tail < UInt64.size) (heap : WithOpenReads.Heap)
    (runtime : ∀ lock ref, WithOpenReads.Runtime physical root lock ref (published before session id) life heap) :
    ∃ lock ref wal recovered history handle opening recoveredAt entered w,
      Native.recoverAt root ref opening = .ok recovered recoveredAt ∧
      Online physical root lock ref wal recovered (published before session id) history entered ∧
      NativeReadRelease.Closed physical root lock ref (published before session id) after ∧
      (readMany handle (key :: keys) entered).val = replies ∧
      Observes history key ((Native.get handle key).toBaseIO entered).val ∧
      Call.mk (root / "tables") id (.lookup key) w ∈ publicCalls ref (root / "tables") key entered ∧
      (Call.mk (root / "tables") id (.lookup key) w).Balanced life := by
  obtain ⟨lock, ref, closed, wal, recovered, history, handle, entered, opening, recoveredAt, recoveredRun, _, binding,
    online, equal, _, _, _⟩ := finished.callback
  let ops := runtime lock ref
  have read := ops.phase.refRead wal
  obtain ⟨w, phase, _⟩ := read entered online.owned (by rw [online.phase]; rfl)
  rw [online.phase] at phase
  have visited := publishedLookup (dir := root / "tables") online.installed fits phase key
  have checked := onlineGet online binding read (ops.tables wal entered online.owned) .refl key
  refine ⟨lock, ref, wal, recovered, history, handle, opening, recoveredAt, entered, w,
    recoveredRun, online, closed, equal, ?_, visited, checked.1 _ visited⟩
  have post := checked.2
  cases ran : Native.get handle key entered with
  | ok _ t => simpa only [EIO.toBaseIO, ran] using (show _ from (ran ▸ post).1)
  | error _ t => simp [EIO.toBaseIO, ran, Observes]

end ExperimentalL0.NativeFlushRestart
