import Alvoki.Experiments.DurableBlob.Contract
import Alvoki.Codec.Block

namespace L0Manifest

/-- IDs are interpreted only by the LSM. List order is newest first. -/
structure Version where
  tables : List UInt64
  /-- Absolute inclusive WAL batch position. Zero is the initial boundary. -/
  flushedThrough : UInt64
  deriving DecidableEq, Repr

def Version.Valid (v : Version) : Prop := v.tables.Nodup
instance (v : Version) : Decidable v.Valid := inferInstanceAs (Decidable v.tables.Nodup)

def Version.empty : Version := ⟨[], 0⟩

def magic : UInt64 := 0x3130464e4d564c41 -- ALVMNF01

def encode (v : Version) : ByteArray :=
  (magic :: v.flushedThrough :: v.tables).foldl Alvoki.pushWordFast ByteArray.empty

def decode (bytes : ByteArray) : Option Version := do
  if bytes.size < 16 || bytes.size % 8 != 0 || Alvoki.word bytes 0 != magic then none
  else
    let v : Version :=
      ⟨(List.range (bytes.size / 8 - 2)).map (fun i => Alvoki.word bytes (8 * (i + 2))),
        Alvoki.word bytes 8⟩
    if v.Valid then some v else none

/-- Invalid proposals are rejected before invoking the byte backend. -/
def backend [Monad m] [MonadExceptOf error m] (makeError : String → error) (blob : DurableBlob.Backend m ByteArray) :
    DurableBlob.Backend m Version where
  publish v := if v.Valid then blob.publish (encode v) else throw (makeError "duplicate manifest table ID")
  reopen := do
    let bytes ← blob.reopen
    match decode bytes with
    | some v => pure v
    | none => throw (makeError "invalid L0 manifest")

end L0Manifest
