import Alvoki.Experiments.SSTable.UnifiedNative
import Alvoki.Experiments.SSTable.Recursive.Native

namespace ImmutableSSTable.SSTableWorkload

private def benchKey (n : Nat) : ByteArray :=
  ⟨#[(n >>> 56).toUInt8, (n >>> 48).toUInt8, (n >>> 40).toUInt8, (n >>> 32).toUInt8,
    (n >>> 24).toUInt8, (n >>> 16).toUInt8, (n >>> 8).toUInt8, n.toUInt8]⟩

def benchKeyFor (layout : Unified.Layout) (index : Nat) : ByteArray :=
  let bytes := benchKey index
  if layout.keyWidth.isSome then bytes
  else bytes ++ ByteArray.mk (Array.replicate ((index / 2) % 8) 0x42)

private def benchRows (layout : Unified.Layout) (rows : Nat) : IO (IO (Option Entry)) := do
  let next ← IO.mkRef 0
  return do
    let index ← next.get
    if index == rows then return none
    next.set (index + 1)
    let value := encodeOffset (index + 1)
    let value := if layout.valueWidth.isSome then value
      else value ++ ByteArray.mk (Array.replicate (index % 16) 0x56)
    return some ⟨benchKeyFor layout (2 * index), value⟩

def benchmarkBuild (path : System.FilePath) (layout : Unified.Layout)
    (rows dataTarget indexTarget : Nat) (recursive : Bool) : IO Nat := do
  let provider ← benchRows layout rows
  if recursive then
    Recursive.buildFileWith (nativeOutputOps (fun _ => pure ())) Alvoki.CRC32C.extend
      path layout provider IO.userError ⟨dataTarget, indexTarget⟩
  else Unified.buildFile path layout provider ⟨dataTarget, indexTarget⟩

end ImmutableSSTable.SSTableWorkload
