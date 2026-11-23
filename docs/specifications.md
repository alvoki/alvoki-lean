# Immutable sorted block, version 1

Every field is an unsigned 64-bit little-endian integer. The format has no padding and imposes no address alignment requirement.

| Byte offset | Field |
|---:|---|
| 0 | Record count `n` |
| 8 | Format version, exactly 1 |
| `16 + 16*i` | Key of record `i` |
| `24 + 16*i` | Value of record `i` |

The byte length must be exactly `16 + 16*n`. Keys are strictly increasing in unsigned order. Empty blocks and the full `u64` domain are valid. The parser rejects short headers, unknown versions, truncated or trailing records, count mismatches, duplicate keys and out-of-order keys. It derives the maximum record count from the actual payload before comparing the header count. There is no checksum.

The encoder expects strictly ordered input. Parsing performs the order check. Lower bound returns the first index with a key greater than or equal to the target, or `n`. Point lookup returns the associated value if the lower-bound key is equal to the target. A scan over `[start, end)` walks from the lower bound of `start` to the lower bound of `end` in record order. Equal or reversed endpoints yield no records. An exclusive upper endpoint of `u64::MAX` excludes that key. The benchmark chooses `end` by saturating addition from each query's key and declared width.

## Experimental version 2

The optimization suite also reads a columnar block. It uses the same 16-byte header, with version set to 2 and the same total byte length. Keys occupy one contiguous region at offsets `16 + 8*i`. Values start at `16 + 8*n` and occupy offsets `16 + 8*n + 8*i`. Key and value at the same index form a record. Validation, lookup, and range semantics are the same as in version 1.

Version 2 is exercised through the separate optimization binaries. The experimental encoders produce version 1.
