import Alvoki.Experiments.SSTable.Recursive.FilteredReader
import Alvoki.Checks.Benchmarks.BloomWord
import Alvoki.Codec.ByteWords

namespace ImmutableSSTable.Recursive.CoarseFilter

open Unified (Layout Ref)

def partitionRows : Nat := 16 * 1024

def regionWords (first count : Nat) (lower : Option ByteArray) : List UInt64 :=
  [first.toUInt64, count.toUInt64, lower.elim 0 (fun lower => (lower.size + 1).toUInt64)]

def encodeRegion (first count : Nat) (lower : Option ByteArray) (mask : ByteArray) : ByteArray :=
  Alvoki.ByteWords.encodeWords (regionWords first count lower) ++ lower.getD .empty ++ mask

def onlyKey (entry : Entry) : Entry := ⟨entry.key, .empty⟩

/-- A source of coarse masks retains only the current partition's keys and the preceding fence. -/
def supply (next : IO (Option Entry)) (target : Nat := partitionRows) :
    IO (IO (Option Entry)) := do
  unless 0 < target && target ≤ partitionRows do throw (IO.userError "invalid filter partition size")
  let cursor ← IO.mkRef (0, (none : Option ByteArray))
  let ended ← IO.mkRef false
  return do
    if ← ended.get then return none
    let (first, lower) ← cursor.get
    let mut rows : Array Entry := #[]
    for _ in [:target] do
      match ← next with
      | none =>
        ended.set true
        break
      | some entry => rows := rows.push (onlyKey entry)
    let some last := rows.back? | return none
    let mask := BloomPlacement.packedWordBuild rows
    cursor.set (first + rows.size, some last.key)
    return some ⟨last.key, encodeRegion first rows.size lower mask⟩

def layout (tableId : UInt64) : Layout := ⟨none, none, tableId⟩

inductive Representation where
  | packed
  | decoded
  deriving BEq

inductive MaskView where
  | packed (bytes : ByteArray) (start : Nat)
  | decoded (mask : ByteArray)

def MaskView.bytes : MaskView → Nat
  | .packed bytes _ | .decoded bytes => bytes.size

def MaskView.logical : MaskView → ByteArray
  | .packed bytes start => bytes.extract start bytes.size
  | .decoded mask => mask

def MaskView.maybe (view : MaskView) (key : ByteArray) : Bool :=
  match view with
  | .decoded mask => Bloom.mayContain mask key
  | .packed bytes start =>
    (Bloom.positions (bytes.size - start) key).all fun p =>
      bytes[start + p / 8]!.toNat.testBit (p % 8)

structure CheckedMask where private mk ::
  ref : Ref
  first : Nat
  count : Nat
  lower : Option ByteArray
  upper : ByteArray
  view : MaskView

def CheckedMask.covers (mask : CheckedMask) (key : ByteArray) : Bool :=
  mask.lower.all (· < key) && decide (key ≤ mask.upper)

def CheckedMask.bytes (mask : CheckedMask) : Nat :=
  mask.view.bytes + mask.upper.size + (mask.lower.map ByteArray.size).getD 0

/-- Decode once after the recursive reader has verified the containing packet.
The packed representation retains the payload and its mask offset. -/
def decodeRegion (representation : Representation) (rowCount : Nat) (ref : Ref) (entry : Entry) :
    Except String CheckedMask := do
  let payload := entry.value
  unless 24 ≤ payload.size do throw "short coarse filter header"
  let first := (Alvoki.word payload 0).toNat
  let count := (Alvoki.word payload 8).toNat
  let lowerLength := (Alvoki.word payload 16).toNat
  let start := 24 + (lowerLength - 1)
  unless 0 < count ∧ count ≤ partitionRows ∧ first + count ≤ rowCount ∧
      start + Bloom.bytesFor count = payload.size do
    throw "invalid coarse filter extent"
  unless (lowerLength = 0 ↔ first = 0) do throw "invalid coarse filter interval start"
  let lower := if lowerLength = 0 then none else some (payload.extract 24 start)
  unless lower.all (· < entry.key) do throw "invalid coarse filter fence order"
  let view := match representation with
    | .packed => .packed payload start
    | .decoded => .decoded (payload.extract start payload.size)
  return ⟨ref, first, count, lower, entry.key, view⟩

def load [Monad m] [MonadExceptOf String m] (filters : Handle m)
    (representation : Representation) (rowCount : Nat) (key : ByteArray) :
    m (Option CheckedMask) := do
  let some (ref, data, index) ← filters.locate key | return none
  let entry ← liftDecode (data.readRow index)
  let mask ← liftDecode (decodeRegion representation rowCount ref entry)
  unless mask.covers key do throw "key routed outside its coarse filter interval"
  return some mask

inductive Policy where
  | latest (budget : Nat)
  | eager (budget : Nat)
  deriving Repr

def Policy.budget : Policy → Nat
  | .latest budget | .eager budget => budget

structure Resident where private mk ::
  masks : Array CheckedMask := #[]
  bytes : Nat := 0

private def Resident.retain (resident : Resident) (limit : Nat) (mask : CheckedMask) :
    Except String Resident :=
  if resident.bytes + mask.bytes ≤ limit then
    .ok ⟨resident.masks.push mask, resident.bytes + mask.bytes⟩
  else .error "coarse filter eager cache exceeds its budget"

def Resident.latest (resident : Resident) (limit : Nat) (mask : CheckedMask) : Resident :=
  if mask.bytes ≤ limit then ⟨#[mask], mask.bytes⟩ else resident

private def scan [Monad m] [MonadExceptOf String m] (filters : Handle m)
    (representation : Representation) (rowCount limit : Nat)
    (ref : Ref) (parent : Nat) (resident : Resident) : Nat → m Resident
  | 0 => do
    let data ← filters.readData ref parent
    let mut cache := resident
    for i in [:ref.count] do
      let entry ← liftDecode (data.readRow i)
      let mask ← liftDecode (decodeRegion representation rowCount ref entry)
      cache ← liftDecode (cache.retain limit mask)
    return cache
  | height + 1 => do
    let raw ← readIndexPacket filters.source filters.crc filters.layout.tableId (height + 1) ref parent
    let children ← liftDecode (pageChildren raw ref true)
    let mut cache := resident
    for child in children do
      cache ← scan filters representation rowCount limit child ref.offset cache height
    return cache

structure Session (m : Type → Type) where private mk ::
  base : Handle m
  filters : Handle m
  representation : Representation
  policy : Policy
  resident : Resident

/-- For the benchmark's paired files. The ID check detects an ID mismatch.
The paired-image proof must supply common origin at the two exact descriptors. -/
def openSession [Monad m] [MonadExceptOf String m] (base filters : Handle m)
    (representation : Representation) (policy : Policy) : m (Session m) := do
  unless filters.layout = layout base.layout.tableId do throw "coarse filter table identity mismatch"
  let mut resident : Resident := {}
  if let .eager limit := policy then
    for ref in filters.root do
      resident ← scan filters representation base.rowCount limit ref filters.rootOffset
        resident (filters.height - 1)
  return ⟨base, filters, representation, policy, resident⟩

structure Probe where
  value : Option ByteArray
  cacheHit : Bool
  filterTest : Option Bool

def Session.probe [Monad m] [MonadExceptOf String m] (session : Session m) (key : ByteArray) :
    m (Probe × Session m) := do
  let cached := session.resident.masks.find? (·.covers key)
  let selected ← match cached with
    | some mask => pure (some mask)
    | none => load session.filters session.representation session.base.rowCount key
  let some mask := selected | return (⟨← session.base.lookup key, false, none⟩, session)
  let result := mask.view.maybe key
  let value ← if result then session.base.lookup key else pure none
  let resident := if cached.isNone then
      match session.policy with
      | .latest limit => session.resident.latest limit mask
      | .eager _ => session.resident
    else session.resident
  return (⟨value, cached.isSome, some result⟩, { session with resident })

end ImmutableSSTable.Recursive.CoarseFilter
