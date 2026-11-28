import Alvoki.Experiments.SSTable.UnifiedFormat
import Alvoki.Experiments.SSTable.UnifiedIntegrity

namespace ImmutableSSTable.Recursive

open Unified

def maxHeight : Nat := 63

/-- The soft index target is at most one native read. Two individually valid
fences may together require a second read. -/
def maxIndexSize : Nat := 2 * maxRowSize

def dataKind : UInt64 := 0x600
def indexKind (height : Nat) : UInt64 := 0x600 + height.toUInt64
def footerKind : UInt64 := 0x640

def magic : ByteArray := "ALVSST06".toUTF8
def footerBodySize : Nat := Unified.footerBodySize + 8
def footerPacketSize : Nat := footerBodySize + checksumSize

structure Footer where
  base : Unified.Footer
  height : Nat
  deriving DecidableEq, Repr

def Footer.rootRef (footer : Footer) : Ref :=
  ⟨ByteArray.empty, footer.base.rootOffset, footer.base.rootSize, 0, footer.base.count⟩

def encodeFooter (footer : Footer) : ByteArray :=
  let body := encodeFooterBody footer.base
  Alvoki.pushWordFast (magic ++ body.extract 8 Unified.footerBodySize) footer.height.toUInt64

def decodeFooter (bytes : ByteArray) : Except String Footer := do
  unless bytes.size = footerBodySize && bytes.extract 0 8 == magic do
    throw "invalid ALVSST06 footer"
  let base ← decodeFooterBody (Unified.magic ++ bytes.extract 8 Unified.footerBodySize)
  let height := (Alvoki.word bytes Unified.footerBodySize).toNat
  unless height ≤ maxHeight ∧ (height = 0 ↔ base.count = 0) do
    throw "invalid SSTable index height"
  return ⟨base, height⟩

def decodePage (bytes : ByteArray) : Except String (Array Ref) := do
  unless refPrefixSize ≤ bytes.size ∧ bytes.size + checksumSize ≤ maxIndexSize do
    throw "invalid SSTable index size"
  let refs ← decodeRefs bytes 0 #[] (bytes.size / refPrefixSize)
  -- Large logical packets are only needed for a pair of individually valid fences.
  unless bytes.size + checksumSize ≤ maxRowSize || refs.size == 2 do
    throw "invalid oversized SSTable index"
  unless refs.all (fun ref => indexEntrySize ref.lastKey + checksumSize ≤ maxRowSize) do
    throw "invalid SSTable index key size"
  return refs

/-- A child can be read only when its positive extent ends before or at
the start of its parent. Offset arithmetic stays in Nat. -/
def checkedChild (child : Ref) (parentOffset limit : Nat) : Except String Unit :=
  if checksumSize ≤ child.size ∧ child.size ≤ limit ∧
      child.offset + child.size ≤ parentOffset then .ok ()
  else .error "invalid SSTable child packet extent"

end ImmutableSSTable.Recursive
