import Alvoki.Codec.CRC32C

open Alvoki.CRC32C

private def inputs (size : Nat) : Array ByteArray := Id.run do
  let mut state : UInt64 := 42
  let mut buffers := #[]
  for _ in [:8] do
    let mut bytes := ByteArray.emptyWithCapacity size
    for _ in [:size] do
      state := state * 6364136223846793005 + 1
      bytes := bytes.push (state >>> 56).toUInt8
    buffers := buffers.push bytes
  return buffers

private def checkCRC : IO Unit := do
  let bytes := "123456789".toUTF8
  let first := bytes.extract 0 4
  let suffix := bytes.extract 4 bytes.size
  let expected : UInt32 := 0xe3069283
  unless extend 0 bytes == expected && extend (extend 0 first) suffix == expected &&
      extend expected ByteArray.empty == expected do
    throw (IO.userError "checksum test vector failed")

@[noinline] private def run (buffers : Array ByteArray) (iterations : Nat) : IO UInt64 := do
  let mut sum : UInt64 := 0
  for i in [:iterations] do
    sum := sum + (extend 0 buffers[i % 8]!).toUInt64
  return sum

private def timeTrial (buffers : Array ByteArray) (size trial : Nat) : IO Unit := do
  let iterations := (64 * 1024 * 1024) / size
  discard <| run buffers 1000
  let start ← IO.monoNanosNow
  let sum ← run buffers iterations
  let elapsed := (← IO.monoNanosNow) - start
  IO.println s!"{size},google-crc32c,{trial},{iterations},{elapsed},{sum}"

def main : IO Unit := do
  checkCRC
  IO.println "bytes,implementation,trial,iterations,total_ns,sum"
  for size in #[32, 256, 1024, 4096, 16384] do
    let buffers := inputs size
    for bytes in buffers do
      for previous in #[0, 0xfedcba98] do
        unless extend previous bytes == crc32c previous bytes do
          throw (IO.userError "native and portable CRC32C differ")
    for trial in [:7] do
      timeTrial buffers size trial
