import Init.System.IO

namespace Alvoki.Storage.RunCollection

inductive Step (address : Type) where
  | unlink (name : address)
  | syncDirectory

def steps (names : List address) : List (Step address) := names.map Step.unlink ++ [.syncDirectory]

/-- Complete the approved unlinks in order, then sync the owning directory.
The barrier remains necessary when resuming with an empty list. -/
def run [Monad m] (names : List address) (perform : Step address → m Unit) : m Unit :=
  (steps names).forM perform

/-- In the owned stable parent directory, Linux ENOENT at an approved unlink
identifies an already absent name. Keep every other error. -/
def ownedUnlinkResult (result : Except IO.Error Unit) : Except IO.Error Unit :=
  match result with
  | .error (.noFileOrDirectory _ code _) => if code = 2 then .ok () else result
  | _ => result

theorem ownedUnlinkResult_ok_iff {result : Except IO.Error Unit} :
    ownedUnlinkResult result = .ok () ↔ result = .ok () ∨
      ∃ path message, result = .error (.noFileOrDirectory path 2 message) := by
  cases result with
  | ok value => cases value; simp [ownedUnlinkResult]
  | error error => cases error <;> simp [ownedUnlinkResult]

/-- Dispatch only addresses already approved by the inventory. The caller
keeps the locked parent, regular-file choice and holds stable through this
sequence. The unlink callback exposes its raw result for ENOENT handling. -/
def performPaths [Monad m] {address path : Type}
    (removeFile : path → m (Except IO.Error Unit)) (syncDirectory : path → m Unit)
    (raise : IO.Error → m Unit) (file : address → path) (directory : path) : Step address → m Unit
  | .unlink name => do
    match ownedUnlinkResult (← removeFile (file name)) with
    | .ok () => pure ()
    | .error error => raise error
  | .syncDirectory => syncDirectory directory

theorem run_performPaths [Monad m] [LawfulMonad m] {address path : Type} (names : List address)
    (removeFile : path → m (Except IO.Error Unit)) (syncDirectory : path → m Unit)
    (raise : IO.Error → m Unit) (file : address → path) (directory : path) :
    run names (performPaths removeFile syncDirectory raise file directory) = (do
      names.forM fun name => do
        match ownedUnlinkResult (← removeFile (file name)) with
        | .ok () => pure ()
        | .error error => raise error
      syncDirectory directory) := by
  simp [run, steps, performPaths]

end Alvoki.Storage.RunCollection
