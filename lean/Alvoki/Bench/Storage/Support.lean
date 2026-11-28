namespace StorageBench

@[extern "alvoki_bench_cpu_ns"] private opaque cpuNanos : IO UInt64
@[extern "alvoki_bench_peak_rss"] private opaque peakRss : IO UInt64
@[extern "alvoki_bench_resident_rss"] private opaque residentRss : IO UInt64

@[extern "alvoki_bench_begin_sync_timing"] private opaque beginSyncTiming : IO Unit
@[extern "alvoki_bench_end_sync_timing"] private opaque endSyncTiming : IO Unit

def check (ok : Bool) (message : String) : IO Unit :=
  unless ok do throw (IO.userError message)

def checked (action : EIO String α) : IO α :=
  do
  match ← action.toBaseIO with
  | .ok result => return result
  | .error message => throw (IO.userError message)

def number (text : String) : IO Nat :=
  match text.toNat? with
  | some n => pure n
  | none => throw (IO.userError s!"expected a natural number: {text}")

structure Measurement where
  elapsed : Nat
  cpu : UInt64
  allocations : Nat
  rss : UInt64
  resident : UInt64

def measure (action : IO α) : IO (α × Measurement) := do
  let trace := (← IO.getEnv "ALVOKI_BENCH_TRACE") == some "1"
  let syncTiming := (← IO.getEnv "ALVOKI_BENCH_SYNC_FILE").isSome
  if trace then IO.eprintln "STORAGE_BENCH_BEGIN"
  if syncTiming then beginSyncTiming
  let cpu ← cpuNanos
  let allocated ← IO.getNumHeartbeats
  let start ← IO.monoNanosNow
  let result ← action
  let elapsed := (← IO.monoNanosNow) - start
  let allocations := (← IO.getNumHeartbeats) - allocated
  let cpu := (← cpuNanos) - cpu
  if syncTiming then endSyncTiming
  if trace then IO.eprintln "STORAGE_BENCH_END"
  return (result, ⟨elapsed, cpu, allocations, ← peakRss, ← residentRss⟩)

def Measurement.report (m : Measurement) (operation : String) (items : Nat) : IO Unit :=
  IO.println s!"batch,{operation},{items},{m.elapsed},{m.cpu},{m.allocations},{m.rss},{m.resident}"

structure Sample where
  operation : String
  elapsed : Nat

-- Per-call clocks and sample storage are used only in the latency pass.
@[inline] def observe (enabled : Bool) (samples : Array Sample) (operation : String)
    (action : IO α) : IO (α × Array Sample) := do
  if !enabled then return (← action, samples)
  let start ← IO.monoNanosNow
  let result ← action
  let elapsed := (← IO.monoNanosNow) - start
  return (result, samples.push ⟨operation, elapsed⟩)

def reportSamples (samples : Array Sample) : IO Unit := do
  for sample in samples do
    IO.println s!"call,{sample.operation},1,{sample.elapsed},,,,"

end StorageBench
