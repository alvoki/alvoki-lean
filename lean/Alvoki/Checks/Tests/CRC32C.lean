import Alvoki.Codec.CRC32C

open Alvoki.CRC32C

private def check (condition : Bool) (label : String) : IO Unit :=
  unless condition do throw (IO.userError label)

def main : IO Unit := do
  let vector := "123456789".toUTF8
  check (crc32c 0 vector == 0xe3069283) "portable CRC32C standard vector"
  check (extend 0 vector == 0xe3069283) "CRC32C standard vector"
  for size in [0, 1, 7, 8, 9, 63, 64, 255, 256, 1024, 4096, 16384] do
    let bytes : ByteArray := ⟨(Array.range size).map fun i => (i * 37 + i / 256).toUInt8⟩
    for seed in [0, 1, 0x89abcdef, 0xffffffff] do
      let reference := crc32c seed bytes
      check (extend seed bytes == reference) s!"CRC32C mismatch at size {size}, seed {seed}"
      for split in [0, size / 2, size] do
        let firstChunk := bytes.extract 0 split
        let suffix := bytes.extract split size
        check (extend (extend seed firstChunk) suffix == reference)
          s!"Incremental CRC32C mismatch at size {size}, split {split}, seed {seed}"
  IO.println "CRC32C native consumer checks passed"
