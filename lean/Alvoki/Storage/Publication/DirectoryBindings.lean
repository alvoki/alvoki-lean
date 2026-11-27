namespace Alvoki.Storage.DirectoryPublication

inductive Entry where
  | manifest
  | walBoundary
  deriving DecidableEq

/-- The checkpoint and WAL marker read from one directory image. -/
structure Bindings where
  manifest : Option ByteArray
  walBoundary : Option ByteArray

def Bindings.get (bindings : Bindings) : Entry → Option ByteArray
  | .manifest => bindings.manifest
  | .walBoundary => bindings.walBoundary

def Bindings.replace (bindings : Bindings) : Entry → ByteArray → Bindings
  | .manifest, bytes => { bindings with manifest := some bytes }
  | .walBoundary, bytes => { bindings with walBoundary := some bytes }

end Alvoki.Storage.DirectoryPublication
