import Alvoki.Experiments.L0.DurableCatalog
import Alvoki.Experiments.L0.NativeScope
import Alvoki.Experiments.SSTable.Proofs.BuilderRelation

namespace ExperimentalL0.NativeTableWriter
open System ImmutableSSTable Unified
open NativeScope (W)

/-- The exclusively written inode has both current and fsynced bytes.
The parent directory barrier establishes durability of its name. -/
def Prepared (ns : TableNamespace W) (durable : W → ns.inode → Option ByteArray)
    (id : UInt64) (rows : Rows) (w : W) : Prop :=
  ∃ identity bytes, ns.names w (tablePath ns.directory id) = some identity ∧
    ns.contents w identity = some bytes ∧ durable w identity = some bytes ∧
    Image Alvoki.CRC32C.extend (tableLayout id) (rows.map (Entry.encode keyCodec mutationCodec)) bytes

/-- Operands of individual primitive operations in the native table writer. -/
inductive Leaf where
  | allocate (rows : Rows)
  | readRows (ref : IO.Ref Rows)
  | advance (ref : IO.Ref Rows) (tail : Rows)
  | openFile (path : FilePath) (mode : IO.FS.Mode)
  | write (fd : IO.FS.Handle) (bytes : ByteArray)
  | flush (fd : IO.FS.Handle)
  | sync (fd : IO.FS.Handle)
  | remove (path : FilePath)

def Leaf.Result : Leaf → Type
  | .allocate _ => IO.Ref Rows
  | .readRows _ => Rows
  | .openFile .. => IO.FS.Handle
  | _ => Unit

def Leaf.action : (leaf : Leaf) → IO leaf.Result
  | .allocate rows => IO.mkRef rows
  | .readRows ref => ref.get
  | .advance ref tail => ref.set tail
  | .openFile path mode => IO.FS.Handle.mk path mode
  | .write fd bytes => fd.write bytes
  | .flush fd => fd.flush
  | .sync fd => syncFileHandle fd
  | .remove path => IO.FS.removeFile path

/-- IO instrumented with the site and world of each issued primitive. -/
structure ObservedAt (site α : Type) where
  run : IO α
  visits : W → site → W → Prop

instance : Monad (ObservedAt site) where
  pure x := ⟨pure x,fun _ _ _ => False⟩
  bind a f := ⟨a.run >>= fun x => (f x).run,fun w leaf t =>
    a.visits w leaf t ∨ ∃ x u, a.run w = .ok x u ∧ (f x).visits u leaf t⟩

instance : MonadExceptOf IO.Error (ObservedAt site) where
  throw e := ⟨throw e,fun _ _ _ => False⟩
  tryCatch a f := ⟨tryCatchThe IO.Error a.run (fun e => (f e).run),fun w leaf t =>
    a.visits w leaf t ∨ ∃ e u, a.run w = .error e u ∧ (f e).visits u leaf t⟩

abbrev Observed := ObservedAt Leaf

def issue (leaf : Leaf) : Observed leaf.Result :=
  ⟨leaf.action,fun w l t => l = leaf ∧ t = w⟩

def ops : OutputOps Observed IO.FS.Handle :=
  ⟨fun p m => issue (.openFile p m),fun h b => issue (.write h b),fun h => issue (.flush h),
    fun h => issue (.sync h),fun p => issue (.remove p)⟩

def supply (ref : IO.Ref Rows) :=
  nextTableRow (issue (.readRows ref)) (fun xs => issue (.advance ref xs))

def schedule (path : FilePath) (id : UInt64) (rows : Rows) : Observed Unit := do
  let ref ← issue (.allocate rows)
  let _ ← buildFileWith ops Alvoki.CRC32C.extend path (tableLayout id) (supply ref) IO.userError

abbrev Visits (path : FilePath) (id : UInt64) (rows : Rows) := (schedule path id rows).visits

private theorem runSupply (ref : IO.Ref Rows) :
    (supply ref).run = nextTableRow (ref.get : IO Rows) ref.set := by
  unfold supply nextTableRow
  apply congrArg (Bind.bind (ref.get : IO Rows))
  funext xs
  cases xs <;> rfl

private theorem runStream (ref : IO.Ref Rows) (fd : IO.FS.Handle) (id : UInt64) :
    (buildStream Alvoki.CRC32C.extend (tableLayout id) (ops.sink fd) (supply ref) IO.userError {}).run =
      buildStream Alvoki.CRC32C.extend (tableLayout id) ((nativeOutputOps syncFileHandle).sink fd)
        (nextTableRow (ref.get : IO Rows) ref.set) IO.userError {} := by
  let rel : BuilderRelation.Rules Observed IO IO.userError IO.userError := {
    rel := fun _ _ a b => a.run = b
    ret := fun _ => rfl
    seq := fun h k => by simp only [Bind.bind] at *; rw [h]; exact congrArg _ (funext k)
    raise := fun _ => rfl
    abort := fun _ _ _ => rfl }
  exact BuilderRelation.stream _ _ _ (law := rel) ⟨fun _ => rfl,rfl⟩ _ _ (runSupply ref)

/-- The marked program erases to the actual native writer, including its
primary-error cleanup on the exclusively created path. -/
theorem erase (path : FilePath) (id : UInt64) (rows : Rows) : (schedule path id rows).run = Native.buildSynced path id rows := by
  unfold schedule Native.buildSynced
  apply congrArg (Bind.bind (IO.mkRef rows : IO (IO.Ref Rows)))
  funext ref
  apply congrArg (fun action : IO Nat => action >>= fun _ => pure ())
  unfold buildFileSynced buildFileWithSync buildFileWith withFreshOutputWith
  apply congrArg (Bind.bind (IO.FS.Handle.mk path .writeNew))
  funext fd
  have same := runStream ref fd id
  change (tryCatchThe IO.Error (_ >>= _) _) = tryCatchThe IO.Error (_ >>= _) _
  rw [same]
  rfl

end ExperimentalL0.NativeTableWriter
