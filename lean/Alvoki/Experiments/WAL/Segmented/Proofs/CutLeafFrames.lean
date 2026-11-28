import Alvoki.Experiments.WAL.Segmented.Proofs.CreateCutIO
import Alvoki.Experiments.WAL.Proofs.ConcreteAppendCut

namespace WalRecoverySlice.Segmented.Native.CutLeafFrames
open Alvoki.NativePost (W)
open System
open SingleFile (AppendFiles)
open SingleFile.ConcreteRecovery (Program Op)
open SingleFile.ConcreteAppend (nativeOps)
open SingleFile.ConcreteAppendCut (Issued Site Terminal)

/-- The external frame on a primitive that has actually returned. Both
success and error can be followed by another primitive. -/
def Returned (P : W → Prop) (action : IO α) (w : W) : Prop :=
  P w → P (action.toBaseIO w).state

def Prepare (P : W → Prop) (dir : FilePath) (origin : W) : Prop :=
  ∀ point w, PrepareCutIO.Prefix dir origin point w → ∀ {α} (action : IO α),
    PrepareCutIO.Issued dir point action → Returned P action w

def Create (P : W → Prop) (dir : FilePath) (policy : Policy) (origin : W) : Prop :=
  ∀ leaf w, (CreateCutIO.program dir policy).visits origin leaf w → Returned P leaf.action w

def Control (P : W → Prop) (s : Store) (c : Segmented.Control) (origin : W) : Prop :=
  ∀ point w, ControlCutIO.Prefix s c origin point w → ∀ {α} (action : IO α) k,
    ControlCutIO.Issued s c point action k → Returned P action w

private theorem Returned.ok (held : Returned P action w) (ran : action w = .ok x t) : P w → P t := by
  simpa only [Returned,EIO.toBaseIO,ran] using held

private theorem Returned.error (held : Returned P action w) (ran : action w = .error e t) : P w → P t := by
  simpa only [Returned,EIO.toBaseIO,ran] using held

theorem prepare (frames : Prepare P dir origin) (path : PrepareCutIO.Prefix dir origin p w) : P origin → P w := by
  induction path with
  | start => exact id
  | more prior edge ih =>
    intro start
    have before := ih start
    cases edge with
    | present ran => exact (frames _ _ prior _ .presence).ok ran before
    | absent ran => exact (frames _ _ prior _ .presence).error ran before
    | checkedDir ran _ => exact (frames _ _ prior _ .dirStat).ok ran before
    | listed ran => exact (frames _ _ prior _ .list).ok ran before
    | checked name ran _ => exact (frames _ _ prior _ (.member name)).ok ran before
    | validated => exact before
    | unlinked ran => exact (frames _ _ prior _ .erase).ok ran before
    | removed ran => exact (frames _ _ prior _ .rmdir).ok ran before
    | made ran => exact (frames _ _ prior _ .mkdir).ok ran before

theorem create (frames : Create P dir policy origin) (visit : (CreateCutIO.program dir policy).visits origin leaf t) :
    P origin → P t := by
  intro start
  apply ((CreateCutIO.program dir policy).fold P origin start ?_).2 _ _ visit
  intro op w used before
  have kept := frames op w used before
  cases ran : op.action w <;> simpa only [EIO.toBaseIO,CreateCutIO.world,ran] using kept

theorem control (frames : Control P s c origin) (path : ControlCutIO.Prefix s c origin p w) : P origin → P w := by
  induction path with
  | start => exact id
  | more prior edge ih =>
    intro start
    have before := ih start
    cases edge with
    | regular ran _ => exact (frames _ _ prior _ _ .stat).ok ran before
    | missing ran => exact (frames _ _ prior _ _ .stat).error ran before
    | cleared ran => exact (frames _ _ prior _ _ .unlink).ok ran before
    | opened ran => exact (frames _ _ prior _ _ .openWriter).ok ran before
    | unbuffered ran => exact (frames _ _ prior _ _ (.unbuffer _)).ok ran before
    | written ran => exact (frames _ _ prior _ _ (.write _)).ok ran before
    | flushed ran => exact (frames _ _ prior _ _ (.flush _)).ok ran before
    | synced ran => exact (frames _ _ prior _ _ (.syncWriter _)).ok ran before
    | renamed ran => exact (frames _ _ prior _ _ .rename).ok ran before
    | settled ran => exact (frames _ _ prior _ _ .directory).ok ran before

/-- The child descriptor must be named by this issued instruction of this
specific worker. Each frame starts at the syscall's own world, also when
the syscall follows a completed rewind or write. -/
def ProgramFrame (P : W → Prop) (files : AppendFiles IO.FS.Handle) (source : Program α) (origin : W) : Prop :=
  ∀ op k w, Issued (nativeOps files) source origin (.call op k) w →
    ∀ action t, Site files op w action t → Returned P action t

private abbrev Leaves (P : W → Prop) (files : AppendFiles IO.FS.Handle) (op : Op) (w : W) :=
  ∀ action t, Site files op w action t → Returned P action t

private theorem toSite (leaves : Leaves P files op w) (used : Site files op w action t) : P w → P t := by
  intro before
  cases used with
  | marker chosen eq rewound => exact (leaves _ _ (.rewind chosen eq)).ok rewound before
  | markerFlush chosen eq rewound wrote =>
    exact (leaves _ _ (.marker chosen eq rewound)).ok wrote ((leaves _ _ (.rewind chosen eq)).ok rewound before)
  | dataFlush wrote => exact (leaves _ _ .data).ok wrote before
  | data | dataSync | rewind | markerSync => exact before

private theorem bindFrame {a : IO α} {k : α → IO β} (first : Returned P a w)
    (later : ∀ x t, a w = .ok x t → Returned P (k x) t) : Returned P (a >>= k) w := by
  intro before
  cases ran : a w with
  | ok x t =>
    simpa only [Bind.bind,instMonadEIO._aux_13,EST.bind,EIO.toBaseIO,ran] using later x t ran (first.ok ran before)
  | error e t =>
    simpa only [Bind.bind,instMonadEIO._aux_13,EST.bind,EIO.toBaseIO,ran] using first.error ran before

private theorem returnedOp (files : AppendFiles IO.FS.Handle) (op : Op) (w : W) (leaves : Leaves P files op w) :
    Returned P (op.eval (nativeOps files)).run w := by
  cases op with
  | readData | readMarker | truncate => exact id
  | syncData =>
    change Returned P (do let v ← SingleFile.Internal.syncHandle files.writer; return (.ok v : Except String Unit)) w
    exact bindFrame (leaves _ _ .dataSync) (fun _ _ _ => id)
  | append bytes =>
    rw [show (Op.eval (nativeOps files) (.append bytes)).run = _ from SingleFile.Internal.append_data_run ..]
    apply bindFrame (leaves _ _ .data)
    intro _ _ written
    exact bindFrame (leaves _ _ (.dataFlush written)) (fun _ _ _ => id)
  | syncMarker slot =>
    cases chosen : files.markers with
    | none =>
      obtain ⟨writer,markers⟩ := files
      cases chosen
      exact id
    | some pair =>
      obtain ⟨a,b⟩ := pair
      rw [show (Op.eval (nativeOps files) (.syncMarker slot)).run = _ from SingleFile.Internal.append_sync_marker_run files chosen slot]
      exact bindFrame (leaves _ _ (.markerSync chosen rfl)) (fun _ _ _ => id)
  | writeMarker slot bytes =>
    cases chosen : files.markers with
    | none =>
      obtain ⟨writer,markers⟩ := files
      cases chosen
      exact id
    | some pair =>
      obtain ⟨a,b⟩ := pair
      rw [show (Op.eval (nativeOps files) (.writeMarker slot bytes)).run = _ from SingleFile.Internal.append_marker_run files chosen slot bytes]
      apply bindFrame (leaves _ _ (.rewind chosen rfl))
      intro _ _ rewound
      apply bindFrame (leaves _ _ (.marker chosen rfl rewound))
      intro _ _ written
      exact bindFrame (leaves _ _ (.markerFlush chosen rfl rewound written)) (fun _ _ _ => id)

theorem program (frames : ProgramFrame P files source origin) (path : Issued (nativeOps files) source origin rest w) :
    P origin → P w := by
  induction path with
  | start => exact id
  | next prior ran ih =>
    exact fun h => (returnedOp _ _ _ (frames _ _ _ prior)).ok ran (ih h)

theorem atSite (frames : ProgramFrame P files source origin)
    (path : Issued (nativeOps files) source origin (.call op k) w)
    (site : Site files op w action t) : P origin → P t :=
  fun start => toSite (frames _ _ _ path) site (program frames path start)

theorem terminal (frames : ProgramFrame P files source origin)
    (path : Issued (nativeOps files) source origin rest w) (end_ : Terminal (nativeOps files) rest w result t) :
    P origin → P t := by
  intro start
  have before := program frames path start
  cases end_ with
  | ok | rejected => exact before
  | error ran => exact (returnedOp _ _ _ (frames _ _ _ path)).error ran before
  | fault ran => exact (returnedOp _ _ _ (frames _ _ _ path)).ok ran before

end WalRecoverySlice.Segmented.Native.CutLeafFrames
