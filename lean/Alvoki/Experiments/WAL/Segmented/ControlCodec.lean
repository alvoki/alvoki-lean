import Alvoki.Experiments.WAL.Segmented.Protocol

namespace WalRecoverySlice.Segmented.ControlCodec

def wordMax : Nat := 18446744073709551615

def digit (n : Nat) : UInt8 := (48 + n % 10).toUInt8

/-- The decimal fields use ASCII with no leading zeroes. -/
def decimal (n : Nat) : Bytes :=
  if n < 10 then [digit n] else decimal (n / 10) ++ [digit n]
termination_by n
decreasing_by omega

def version : Bytes := "swal1".toList.map (fun ch => ch.toNat.toUInt8)

def modeBytes : Policy → Bytes
  | .logOnly => "log".toList.map (fun ch => ch.toNat.toUInt8)
  | .boundary => "boundary".toList.map (fun ch => ch.toNat.toUInt8)

def fields (c : Control) : List Bytes :=
  [version, modeBytes c.policy,
   decimal c.capacity, decimal c.active, decimal c.discarded]

def encode (c : Control) : ByteArray :=
  let body := [32].intercalate (fields c)
  ⟨(body ++ checksumBytes body).toArray⟩

def readDecimal (xs : Bytes) : Nat :=
  xs.foldl (fun n b => 10 * n + (b.toNat - 48)) 0

/-- Canonical re-encoding validates the digits, policy, version and checksum. -/
def decode (bytes : ByteArray) : Option Control := do
  let raw := bytes.data.toList
  let [_, mode, cap, last, base] := (raw.take (raw.length - 8)).splitOn 32 | none
  let c : Control := ⟨if mode == modeBytes .logOnly then .logOnly else .boundary,
    readDecimal cap, readDecimal last, readDecimal base⟩
  if c.active ≤ wordMax && c.discarded ≤ wordMax && bytes == encode c then some c else none

end WalRecoverySlice.Segmented.ControlCodec
