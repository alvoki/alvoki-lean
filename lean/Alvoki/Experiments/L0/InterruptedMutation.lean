import Alvoki.Experiments.L0.NativeAppendCut

namespace ExperimentalL0.InterruptedMutation

open System Lifecycle NativeScope
open NativeRead (Footprint SessionAt Online)
open NativeMutationScope (Retry Reopens)
open WalRecoverySlice.Segmented.Native (PhaseMemory)

/-- Returning instructions before the cut. The WAL invocation, the public
mutation and the scope itself need not return in an interrupted execution. -/
structure Prefix (path root : FilePath) (start : W) where
  checked : W
  opened : W
  granted : W
  recovered : W
  lock : IO.FS.Handle
  wal : Wal
  session : Session
  resolved : Native.validatedRoot path start = .ok root checked
  openFile : IO.FS.Handle.mk (root / "l0.lock") .append checked = .ok lock opened
  exclusive : lock.tryLock true opened = .ok true granted
  recovery : let fresh := IO.mkRef (.opening : Phase Wal) granted
    Native.recoverAt root fresh.val fresh.state = .ok session recovered
  phaseRead : let ref := (IO.mkRef (.opening : Phase Wal) granted).val
    ((ref.get : BaseIO _) recovered).val = .recovering wal

abbrev Prefix.ref (p : Prefix path root start) := (IO.mkRef (.opening : Phase Wal) p.granted).val

def Prefix.callback (p : Prefix path root start) : W :=
  ((p.ref.swap (.online p.wal p.session) : BaseIO _)
    ((p.ref.get : BaseIO _) p.recovered).state).state

def Prefix.issue (p : Prefix path root start) : W := NativeWrite.issueWorld p.ref p.wal p.callback

private theorem finish_at {body other : IO α} (equal : body w = other u) (close : IO Unit) :
    finish (ε := IO.Error) body close w = finish (ε := IO.Error) other close u := by
  rw [finish_io body, finish_io other]
  simp only [EIO.toBaseIO, equal]

/-- Publication invokes the callback at the successor of the same recovery read and swap. -/
theorem Prefix.withOpen (p : Prefix path root start) (use : Native.Handle → IO α) :
    ∃ h, h.AtRoot root p.ref ∧ Native.withOpen path use start =
      finish (ε := IO.Error) (use h)
        (finish (ε := IO.Error) ((Native.phaseCell p.ref).close WalRecoverySlice.Segmented.Native.close)
          p.lock.unlock) p.callback := by
  have expanded := Native.withOpen_reached path use start
  simp only [p.resolved, p.openFile, p.exclusive] at expanded
  obtain ⟨h, binding, scope⟩ := expanded
  refine ⟨h, binding, scope.trans ?_⟩
  have published : (Native.phaseCell p.ref).publish (IO.userError "L0 cannot publish a session")
      p.session p.recovered = .ok () p.callback := by
    simp [Cell.publish, Native.phaseCell, Bind.bind, instMonadEIO._aux_13, EST.bind,
      read_io, p.phaseRead, Phase.publish, swap_io, Prefix.callback]
    rfl
  unfold Cell.withSession
  apply finish_at
  have recover : Native.recoverAt root p.ref (IO.mkRef (.opening : Phase Wal) p.granted).state =
      .ok p.session p.recovered := p.recovery
  dsimp only [Prefix.ref] at recover published
  simp only [Bind.bind, instMonadEIO._aux_13, EST.bind, recover, published]

theorem Prefix.issued (p : Prefix path root start)
    (entry : NativeReadScope.Entry physical path root image)
    (files : NativeReadScope.Files physical root image start)
    (heap : PhaseMemory) (ops : WithOpenReads.Runtime physical root p.lock p.ref image life heap)
    (prior : Execution.Run before none image) (change : Change)
    (scans : ∀ history w, SessionAt physical root p.lock p.ref p.wal p.session image history w (.updating p.wal) →
      NativeRecoverAt.ScanPrimitives physical root p.wal image.tables w)
    (fits : image.view.tail + 1 < UInt64.size) :
    Execution.Run (before ++ [.reopened]) (some p.session) image ∧
      ∃ history, SessionAt physical root p.lock p.ref p.wal p.session image history p.issue (.updating p.wal) ∧
        ∃ handle, handle.AtRoot root p.ref ∧
          Native.withOpen path (fun h => Native.mutation h change) start =
            finish (ε := IO.Error) (Native.mutation handle change)
              (finish (ε := IO.Error) ((Native.phaseCell p.ref).close WalRecoverySlice.Segmented.Native.close)
                p.lock.unlock) p.callback ∧
          Native.mutation handle change p.callback = NativeWrite.afterWrite p.ref
            (match WalRecoverySlice.Segmented.Native.append p.wal (encode change) p.issue with
             | .ok _ t => .ok {p.session with mem := insert p.session.mem change} t
             | .error e t => .error e t) := by
  have validated := validatedRoot_rule path (entry.resolve start files)
    (fun r w hr file => (entry.stat file w hr.2).weaken
      (fun _ _ f => ⟨hr.1, f⟩) (fun _ _ f => ⟨hr.1, f⟩))
    (fun _ _ hr _ => hr.2)
  rw [Post, p.resolved] at validated
  have opened := entry.openFile p.checked validated.2
  rw [Post, p.openFile] at opened
  have held := entry.lock p.lock p.opened ⟨_, p.openFile⟩ opened.1 opened.2
  rw [Post, p.exclusive] at held
  obtain ⟨owned, stage, fresh⟩ := entry.fresh p.lock p.granted
    ⟨_, ⟨_, p.openFile⟩, p.exclusive⟩ (held.2 rfl) held.1
  have opening : NativeRecoverAt.Opening physical root p.lock p.ref image
      (IO.mkRef (.opening : Phase Wal) p.granted).state := ⟨owned, stage, fresh.catalog, fresh.disk⟩
  have safe history (d : Durable image history) := by
    have r := NativeRecoverAt.recoverAt_checks d opening fresh.manifest (ops.manifest _ opening)
      heap ops.cleanup.cached ops.wal.toOpenIO ops.childCache ops.phase ops.scan
      (fun wal w a => ops.tables wal w a.1.owned)
    rw [Post, p.recovery] at r
    exact r.1
  have reopened := prior.reopened (fun h d => (safe h d).1)
  obtain ⟨state, _, represented⟩ := prior.refines
  obtain ⟨history, durable⟩ : ∃ h, Nonempty (Durable image h) := by
    cases state with
    | ready db => obtain ⟨_, _, impossible, _⟩ := represented; cases impossible
    | offline known pending => obtain ⟨_, h, _, d⟩ := represented; exact ⟨_, d⟩
  obtain ⟨d⟩ := durable
  obtain ⟨valid, wal, attached⟩ := safe history d
  have beforePublish := attached.sessionAt valid
  obtain ⟨t, read, frame⟩ := ops.phase.refRead wal _ beforePublish.owned (by rw [beforePublish.phase]; rfl)
  rw [read_io] at read
  obtain ⟨value, rfl⟩ := EST.Out.ok.inj read
  have same : Phase.recovering p.wal = .recovering wal :=
    p.phaseRead.symm.trans (value.trans beforePublish.phase)
  obtain rfl := Phase.recovering.inj same
  have mid := beforePublish.advance frame
  have online : Online physical root p.lock p.ref p.wal p.session image history p.callback :=
    mid.advance (ops.phase.refSwap p.wal _ mid.owned (.online p.wal p.session)).2
  obtain ⟨handle, binding, invoked⟩ := p.withOpen (fun h => Native.mutation h change)
  have atIssue := NativeWrite.dispatchAt online binding heap ops.cleanup.cached ops.phase (scans history) change
  simp only [fits, ↓reduceIte] at atIssue
  exact ⟨reopened, history, atIssue.1, handle, binding, invoked, atIssue.2⟩

end ExperimentalL0.InterruptedMutation
