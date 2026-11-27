import Alvoki.Experiments.L0.Basic
import Alvoki.Experiments.SSTable.Contract

namespace ExperimentalL0
open ImmutableSSTable

/-- Fixed-width base-256 digits, most significant first. -/
def keyDigits : Nat → Nat → List UInt8
  | 0, _ => []
  | n + 1, key =>
    let place := 256 ^ n
    UInt8.ofNat (key / place) :: keyDigits n (key % place)

def readDigits : List UInt8 → Nat
  | [] => 0
  | digit :: rest => digit.toNat * 256 ^ rest.length + readDigits rest

def keyCodec : Codec UInt64 where
  encode key := ⟨(keyDigits 8 key.toNat).toArray⟩
  decode bytes :=
    if bytes.size = 8 then .ok (readDigits bytes.data.toList).toUInt64
    else .error "invalid L0 table key width"

/-- The tombstone tag never overlaps a put, even for the zero value. -/
def mutationCodec : Codec Mutation where
  encode
    | .delete => ⟨#[0]⟩
    | .put value => Alvoki.pushWordFast ⟨#[1]⟩ value
  decode bytes :=
    if bytes.size = 1 && bytes[0]! == 0 then .ok .delete
    else if bytes.size = 9 && bytes[0]! == 1 then .ok (.put (Alvoki.word bytes 1))
    else .error "invalid L0 table mutation"

end ExperimentalL0
