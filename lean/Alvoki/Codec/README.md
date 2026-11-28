# Shared byte codecs

[`Block`](Block.lean) provides little-endian word access and lower-bound search, [`WordChecksum`](WordChecksum.lean) and [`ByteWords`](ByteWords.lean) provide word encoding and checksums used by manifest and SSTable components. These shared modules remain separate from the component implementations.

Their kernel and axiom checks run through [`scripts/reproduce.sh`](../../../scripts/reproduce.sh).

## CRC32C

`Alvoki.Codec.CRC32C` defines incremental Castagnoli CRC32C over a byte
array. Start with seed zero and pass the returned checksum as the seed
for the next chunk. `Alvoki.CRC32C.extend` uses the Lean definition in
proofs and the native backend in compiled code. Their agreement is a
runtime assumption checked by known-answer and differential tests.
The logical laws `extend_empty` and `extend_append` show that an empty
chunk preserves the seed and that extending twice equals extending over
the concatenated chunks.

A normal Lake executable can import the module and call `extend`. The
`CRC32C` library target supplies the native archive transitively. Run
`lake exe crc32cCheck` from the Lean package to build and exercise that
link path. The first native build requires Linux x86-64, Git, GCC and G++.
The build fetches [Google CRC32C 1.1.2](https://github.com/google/crc32c/tree/02e65f4fd3065d27b2e29324800ca6d04df16126)
at a pinned commit under its [BSD 3-Clause license](https://github.com/google/crc32c/blob/02e65f4fd3065d27b2e29324800ca6d04df16126/LICENSE).
Upstream CPU dispatch selects SSE4.2 when available and uses the portable
implementation otherwise.
