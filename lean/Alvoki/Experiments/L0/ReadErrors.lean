import Alvoki.Experiments.L0.ComponentContract

namespace ExperimentalL0
open WalRecoverySlice.Segmented
variable {ops : Components (StorageM σ)}

/-- A needed probe fails either immediately or after a sequence of misses. -/
inductive RequiredReadError (tables : Tables (StorageM σ)) (key : UInt64) :
    List UInt64 → σ → String → σ → Prop where
  | here {id : UInt64} : tables.lookup id key s = .error error after →
      RequiredReadError tables key (id :: ids) s error after
  | later {id : UInt64} : tables.lookup id key s = .ok none middle →
      RequiredReadError tables key ids middle error after →
      RequiredReadError tables key (id :: ids) s error after

theorem RequiredReadError.propagates (needed : RequiredReadError tables key ids s error after) :
    lookupTables tables key ids s = .error error after := by
  induction needed with
  | here failed => simp [lookupTables, Bind.bind, EStateM.bind, failed]
  | later miss _ ih => simp [lookupTables, Bind.bind, EStateM.bind, miss, ih]

theorem get_required_error (miss : session.mem[key]? = none)
    (needed : RequiredReadError ops.tables key session.version.tables s error after) :
    get ops session key s = .error error after := by
  simp [get, miss, Bind.bind, EStateM.bind, needed.propagates]

/-- Only earlier successful table opens can make a later one necessary. -/
inductive RequiredOpenError (tables : Tables (StorageM σ)) :
    List UInt64 → σ → String → σ → Prop where
  | here {id : UInt64} : tables.check id s = .error error after →
      RequiredOpenError tables (id :: ids) s error after
  | later {id : UInt64} : tables.check id s = .ok () middle →
      RequiredOpenError tables ids middle error after →
      RequiredOpenError tables (id :: ids) s error after

theorem RequiredOpenError.propagates (needed : RequiredOpenError tables ids s error after) :
    checkTables tables ids s = .error error after := by
  induction needed with
  | here failed => simp [checkTables, Bind.bind, EStateM.bind, failed]
  | later opened _ ih => simp [checkTables, Bind.bind, EStateM.bind, opened, ih]

theorem recover_required_table_error {version : L0Manifest.Version} {view : Contract.View}
    (manifest : ops.manifest.reopen s = .ok version middle)
    (wal : ops.reopenWal middle = .ok view checked)
    (bounds : view.base ≤ version.flushedThrough.toNat ∧ version.flushedThrough.toNat ≤ view.tail)
    (decoded : (view.batches.drop (version.flushedThrough.toNat - view.base)).mapM decode = some changes)
    (needed : RequiredOpenError ops.tables version.tables checked error after) :
    recover ops s = .error error after := by
  simp [recover, Bind.bind, EStateM.bind, manifest, wal, bounds, decoded, needed.propagates]

end ExperimentalL0
