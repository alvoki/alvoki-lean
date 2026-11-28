import Alvoki.Experiments.L0.NativeRead
import Alvoki.Experiments.L0.Trace

namespace ExperimentalL0.NativeRead
open Lifecycle

abbrev Reply := Except IO.Error (Option UInt64)

/-- Caught read errors do not append a client event. -/
def readEvent (key : UInt64) : Reply → List Event
  | .ok value => [.got key value]
  | .error _ => []

private theorem advance (run : Execution.Run events (some session) image)
    (valid : ∀ history, Installed session image history → Observes history key reply) :
    Execution.Run (events ++ readEvent key reply) (some session) image := by
  cases reply with
  | ok value => exact run.got valid
  | error => simpa [readEvent] using run

private theorem Online.forHistory (ready : Online physical root lock ref wal session image history w)
    (installed : Installed session image actual) : Online physical root lock ref wal session image actual w :=
  ⟨ready.owned, ready.phase, ready.child, ready.manifest, ready.catalog, installed⟩

/-- The client theorem consumes the two actual replies in order. Execution.Run
needs each success to denote every compatible installed history. -/
theorem readTwice_run (ready : Online physical root lock ref wal session image history start)
    (binding : Native.Handle.AtRoot handle root ref)
    (read : RefRead physical root lock ref wal image.tables)
    (prim : Primitives (tableNamespace physical root) life (Frame physical root wal image.tables start))
    (prior : Execution.Run events (some session) image) (first second : UInt64) :
    let r := readTwice handle first second start
    let observed := (events ++ readEvent first r.val.1) ++ readEvent second r.val.2
    Execution.Run observed (some session) image ∧
      (∃ state, Client.Allows observed state ∧ Execution.Represents (some session) image state) ∧
      Released life ref (root / "tables") first start ∧
      Released life ref (root / "tables") second ((Native.get handle first).toBaseIO start).state ∧
      Online physical root lock ref wal session image history r.state := by
  intro r observed
  have valid actual (installed : Installed session image actual) :=
    onlineGetTwice (ready.forHistory installed) binding read prim first second
  have r1 := advance prior (fun _ installed => (valid _ installed).1)
  have r2 := advance r1 (fun _ installed => (valid _ installed).2.1)
  obtain ⟨_, _, release1, release2, _, final⟩ := valid history ready.installed
  exact ⟨r2, r2.refines, release1, release2, final⟩

/-- Execute the public operation for each key, catching errors in the client
so that the next read consumes the actual world left by the previous one. -/
def readMany (handle : Native.Handle) : List UInt64 → BaseIO (List Reply)
  | [] => pure []
  | k :: keys => do
    let r ← (Native.get handle k).toBaseIO
    return r :: (← readMany handle keys)

def readEvents : List UInt64 → List Reply → List Event
  | k :: ks, r :: rs => readEvent k r ++ readEvents ks rs
  | _, _ => []

/-- The concrete reply sequence has exactly one entry for every requested key.
The client projection agrees with the finite-read guarantee of the model. -/
theorem readMany_length (handle : Native.Handle) (keys : List UInt64) (w : W) :
    ((readMany handle keys) w).val.length = keys.length := by
  induction keys generalizing w with
  | nil => rfl
  | cons k ks ih =>
    change ((_ :: (readMany handle ks ((Native.get handle k).toBaseIO w).state).val).length = _)
    simp [ih]

theorem readEvents_eq_zip (keys : List UInt64) (replies : List Reply) :
    readEvents keys replies = (keys.zip replies).filterMap (fun (key, reply) =>
      match reply with | .ok v => some (.got key v) | .error _ => none) := by
  induction keys generalizing replies with
  | nil => simp [readEvents]
  | cons key ks ih =>
    cases replies with
    | nil => simp [readEvents]
    | cons r rs => cases r <;> simp [readEvents, readEvent, ih]

def allReleased (life : Lifetime) (ref : IO.Ref (Phase Wal)) (dir : System.FilePath)
    (handle : Native.Handle) : List UInt64 → W → Prop
  | [], _ => True
  | key :: keys, w => Released life ref dir key w ∧
      allReleased life ref dir handle keys ((Native.get handle key).toBaseIO w).state

/-- The concrete replacement for the interpreted finite-read consumer.
The state used for every observed scope is the one actually reached. -/
theorem readMany_run (ready : Online physical root lock ref wal session image history epoch)
    (binding : Native.Handle.AtRoot handle root ref)
    (read : RefRead physical root lock ref wal image.tables)
    (prim : Primitives (tableNamespace physical root) life (Frame physical root wal image.tables epoch))
    (frame : Frame physical root wal image.tables epoch start)
    (prior : Execution.Run events (some session) image) (keys : List UInt64) :
    let r := readMany handle keys start
    Execution.Run (events ++ readEvents keys r.val) (some session) image ∧
      Frame physical root wal image.tables epoch r.state ∧
      Online physical root lock ref wal session image history r.state ∧
      allReleased life ref (root / "tables") handle keys start := by
  induction keys generalizing events start with
  | nil => exact ⟨by simpa [readEvents] using prior, frame, ready.frame frame, trivial⟩
  | cons k keys ih =>
    let reached := (Native.get handle k).toBaseIO start
    have post (actual) (installed : Installed session image actual) :
        Observes actual k reached.val ∧
          Released life ref (root / "tables") k start ∧
          Frame physical root wal image.tables epoch reached.state := by
      obtain ⟨released, result⟩ := onlineGet (ready.forHistory installed) binding read prim frame k
      cases ran : Native.get handle k start with
      | error e t =>
        rw [ran] at result
        simpa only [reached, EIO.toBaseIO, ran] using
          (show Observes actual k (.error e) ∧ _ from ⟨trivial, released, result.1⟩)
      | ok x t =>
        rw [ran] at result
        simpa only [reached, EIO.toBaseIO, ran] using
          (show Observes actual k (.ok x) ∧ _ from ⟨result.1, released, result.2.1⟩)
    have step := advance prior (fun _ installed => (post _ installed).1)
    obtain ⟨_, released, next⟩ := post history ready.installed
    obtain ⟨run, final, online, rest⟩ := ih next step
    let tail := readMany handle keys reached.state
    change Execution.Run (events ++ (readEvent k reached.val ++ readEvents keys tail.val)) _ _ ∧ _
    exact ⟨by simpa only [List.append_assoc] using run, final, online, released, rest⟩

/-- The first call fails at size on its actually acquired descriptor. The
caller catches that error, and the second public get hits the memtable in
the online session on the reached world. Its value is the only new event. -/
theorem caughtSizeError_thenHit {id : UInt64}
    (ready : Online physical root lock ref wal session image history start)
    (binding : Native.Handle.AtRoot handle root ref)
    (read : RefRead physical root lock ref wal image.tables)
    (prim : Primitives (tableNamespace physical root) life (Frame physical root wal image.tables start))
    (prior : Execution.Run events (some session) image)
    (phase : (ref.get : IO (Phase Wal)) start = .ok (.online wal session) w)
    (miss : session.mem[first]? = none) (head : session.version.tables = id :: older)
    (stat : (nativeTableStat (tablePath (root / "tables") id)).run w = .ok (.ok md) checked)
    (regular : isTableFile md = true)
    (opened : IO.FS.Handle.mk (tablePath (root / "tables") id) .read checked = .ok h entered)
    (failed : (ImmutableSSTable.handleSource h).size entered = .error e after)
    (hit : session.mem[second]? = some mutation) :
    let c := Call.mk (root / "tables") id (.lookup first) w
    ∃ final, readTwice handle first second start =
        ⟨(.error (IO.userError e), .ok mutation.value), final⟩ ∧
      ¬ life.liveAtReturn (c.exitOfAcquire stat regular opened) h ∧
      Online physical root lock ref wal session image history final ∧
      Execution.Run (events ++ [.got second mutation.value]) (some session) image ∧
      ∃ state, Client.Allows (events ++ [.got second mutation.value]) state ∧
        Execution.Represents (some session) image state := by
  intro c
  obtain ⟨firstReply, firstCalls⟩ := firstSizeError root ref binding phase miss head stat regular opened failed
  obtain ⟨all, post⟩ := onlineGet ready binding read prim .refl first
  rw [firstReply] at post
  have one : c.Balanced life := all c (by simp [firstCalls, c])
  have actualRelease := one.released stat regular opened
  obtain ⟨final, phaseRead, keeps⟩ := read after post.2.owned (by rw [post.2.phase]; rfl)
  have secondReply := memHit ref binding (post.2.phase ▸ phaseRead) hit
  have ran : readTwice handle first second start =
      ⟨(.error (IO.userError e), .ok mutation.value), final⟩ := by
    simp [readTwice, EIO.toBaseIO, Bind.bind, instMonadBaseIO._aux_13, ST.bind, firstReply, secondReply]
    rfl
  have trace := readTwice_run ready binding read prim prior first second
  rw [ran] at trace
  exact ⟨final, ran, actualRelease, trace.2.2.2.2, by simpa [readEvent] using trace.1,
    by simpa [readEvent] using trace.2.1⟩

end ExperimentalL0.NativeRead
