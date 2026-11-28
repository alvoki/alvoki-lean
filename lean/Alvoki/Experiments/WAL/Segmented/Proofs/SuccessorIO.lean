import Alvoki.Experiments.WAL.Segmented.Proofs.PrepareIO
import Alvoki.Experiments.WAL.Proofs.ConcreteCreate

namespace WalRecoverySlice.Segmented.Native.PrepareIO
open Model System Alvoki.NativePost
open AppendIO (At)

def mkdir (reports : Effects) (id : Nat) : Model.M Unit := fun s =>
  namespaceChange (reports.prepare s.step id) (fun disk persist => disk.prepare id persist) s

def createdDisk (s : State) (id : Nat) (child : SingleFile.OpenImage) : State :=
  {s with disk := s.disk.setSegment id child.image {}}

def make (root : FilePath) (id : Nat) (p : Policy) (r : SingleFile.CreateReports) :
    Model.M SingleFile.AppendPhase := fun s =>
  match SingleFile.createModel (segmentPath root id) p r with
  | .ok (.ok ready) child => .ok (.ok (SingleFile.storedPhase ready)) (createdDisk s id child)
  | .ok (.error msg) child => .ok (.error msg) (createdDisk s id child)
  | .error token child => .error token (createdDisk s id child)

variable {id : Nat}

/-- The newly created successor is live and cursor-bound before its parent
directory entry is made durable by the following root fsync. -/
structure PreparedFile (disk : W → Disk) (id : Nat) (w : W) : Prop where
  named : id ∈ (disk w).liveNames
  image : (disk w).segment id = Persistence.freshImage
  cursor : (disk w).cursor id = {}

/-- The installed child owns actual private bytes after the child-directory
barrier. Earlier states admit partial initialization, including failed writes. -/
def Material (disk : W → Disk) (id : Nat) (w : W) (child : SingleFile.OpenImage) : Prop :=
  child.namesDurable = true → id ∈ (disk w).liveNames ∧
    (disk w).segment id = child.image ∧ (disk w).cursor id = {}

/-- Creation is interpreted on the successor which was just given a
directory. The outer state may abstract its private contents on failure.
The success projection receives the actual newly allocated cell and mutex. -/
structure Creation (s : Store) (id : Nat) (p : Policy) (r : SingleFile.CreateReports)
    (w : W) (before : State) (R : W → State → Prop)
    (owns : SingleFile.Handle → SingleFile.AppendPhase → W → Prop) (disk : W → Disk) where
  role : IO.FS.Handle → SingleFile.OpenTarget → Prop
  building : W → SingleFile.OpenImage → Prop
  steps : SingleFile.ConcreteCreate.Steps
    (fun t child => R t (createdDisk before id child) ∧ Material disk id t child ∧ building t child) role
    (segmentPath s.root id) p r w
  owned : ∀ h ready t, SingleFile.create (segmentPath s.root id) p w = .ok h t →
    SingleFile.ConcreteRecovery.Owns steps.runtime role p (segmentPath s.root id) w t h ready →
    owns h (SingleFile.storedPhase ready) t

private theorem Creation.run (creation : Creation s id p r w before R owns disk)
    (linux : System.Platform.isWindows = false) :
    At (SingleFile.create (segmentPath s.root id) p) (make s.root id p r) w before
      (fun h phase t u => owns h phase t ∧ R t u ∧ PreparedFile disk id t) R := by
  have run := SingleFile.ConcreteCreate.create creation.steps
  unfold At make
  dsimp only [ExceptT.run]
  cases actual : SingleFile.create (segmentPath s.root id) p w <;>
    cases model : SingleFile.createModel (segmentPath s.root id) p r <;> rw [actual, model] at run
  case ok.ok h t result u =>
    cases result with
    | error => contradiction
    | ok ready =>
      have guarantee := (SingleFile.createModel_opened _ _ _ linux model).1
      have names := guarantee.2.2.2.2.2.2.2.2.2.1
      have data := (nativeCreatedChild _ _ _ linux model).1
      obtain ⟨name, image, cursor⟩ := run.1.2.1 names
      exact ⟨creation.owned h ready t actual run.2, run.1.1, name, image.trans data, cursor⟩
  case error.ok e t result u =>
    cases result <;> first | contradiction | exact run.1
  all_goals contradiction

/-- The create primitive is available only after the actual checked
successor cleanup and mkdir both returned on this invocation. -/
structure Successor (s : Store) (p : Policy) (id : Nat) (removal : RootReports)
    (reports : Effects) (create : SingleFile.CreateReports) (origin : W) (initial : State)
    (R : W → State → Prop) (owns : SingleFile.Handle → SingleFile.AppendPhase → W → Prop) (disk : W → Disk) where
  remove : Removal s.root id removal origin initial R
  createDirectory : ∀ t u, removeSegment s.root id origin = .ok () t →
    ((nativeReopenOps s.root removal (fun _ _ => {})).removeSegment id).run initial = .ok (.ok ()) u → R t u →
    At (IO.FS.createDir (segmentPath s.root id)) (mkdir reports id) t u (fun _ _ v n => R v n) R
  child : ∀ t u v n, removeSegment s.root id origin = .ok () t →
    ((nativeReopenOps s.root removal (fun _ _ => {})).removeSegment id).run initial = .ok (.ok ()) u →
    IO.FS.createDir (segmentPath s.root id) t = .ok () v →
    (mkdir reports id).run u = .ok (.ok ()) n → R v n → Creation s id p create v n R owns disk

variable {create : SingleFile.CreateReports}

theorem Successor.prepare (steps : Successor s p id removal reports create w initial R owns disk)
    (linux : System.Platform.isWindows = false) :
    At (s.prepareChild p id) (prepareNativeChild s.root removal (fun step => reports.prepare step id) create p id)
      w initial (fun h phase t u => owns h phase t ∧ R t u ∧ PreparedFile disk id t) R := by
  unfold Store.prepareChild prepareNativeChild prepareChildWith
  apply (ControlIO.trace steps.remove.run).bind
  rintro _ _ t u ⟨frame, removed, result⟩
  simp only [BEq.rfl, ite_true]
  apply (ControlIO.trace (steps.createDirectory t u removed result frame)).bind
  rintro _ _ v n ⟨kept, made, next⟩
  have output := (steps.child t u v n removed result made next kept).run linux
  unfold At make at output
  unfold At
  dsimp only [ExceptT.run] at output ⊢
  cases actual : SingleFile.createModel (segmentPath s.root id) p create <;> rw [actual] at output
  case ok response child => cases response <;> exact output
  case error => exact output

theorem Successor.acquire (steps : Successor s p id removal reports create w initial R owns disk)
    (phase : SingleFile.AppendPhase) (linux : System.Platform.isWindows = false) :
    At (s.prepareChild p id) (acquireSuccessor s.root removal reports create p id) w (initial, phase)
      (fun h tag t u => tag = .acquired id ∧ owns h u.2 t ∧ R t u.1 ∧ PreparedFile disk id t) (fun t u => u.2 = phase ∧ R t u.1) := by
  have run := steps.prepare linux
  unfold At acquireSuccessor at *
  dsimp only [ExceptT.run, Prod.fst, Prod.snd] at *
  cases actual : s.prepareChild p id w <;>
    cases model : (prepareNativeChild s.root removal (fun k => reports.prepare k id) create p id).run initial <;>
    simp only [ExceptT.run] at model
  all_goals rw [actual, model] at run
  all_goals rw [model]
  case ok.ok h t result u =>
    cases result <;> first | contradiction | exact ⟨rfl, run⟩
  case error.ok e t result u =>
    cases result <;> first | contradiction | exact ⟨rfl, run⟩
  all_goals contradiction

end WalRecoverySlice.Segmented.Native.PrepareIO
