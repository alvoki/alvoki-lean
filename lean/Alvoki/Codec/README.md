# Shared byte codecs

[`Block`](Block.lean) defines block layout and byte access, [`WordChecksum`](WordChecksum.lean) and [`ByteWords`](ByteWords.lean) provide word encoding and checksums used by manifest and SSTable components. These shared modules remain separate from the component implementations.

Their kernel and axiom checks run through [`scripts/reproduce.sh`](../../../scripts/reproduce.sh).
