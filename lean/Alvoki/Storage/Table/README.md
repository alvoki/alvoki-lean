# Follow a snapshot read

Start at `PackedTable.lookup`. The table resolves the snapshot handle to a pin and reads at that pin's sequence. An unknown handle returns outer `none`. For a known handle the result is `some value`, where the inner option records whether a value was visible. [Packed table](PackedTable.lean)

| To follow | Open |
|---|---|
| How one run supplies a candidate | `CheckedRun.lookupEntry` searches a checked v3 run for the newest eligible version of the key. It preserves tombstones so that a newer deletion can override an older value. [Run reader](CompactionRead.lean) |
| How the table chooses a value | `PackedTable.lookupAt` combines candidates from the memtable and immutable runs, then projects the winning payload. [Table implementation](PackedTable.lean) |
| Why the read agrees with history | `CheckedRun.lookupEntry_eq` relates the run search to the model's winning entry. `PackedTable.lookupAt_eq` lifts it to the table and `PackedTable.lookup_refines` handles the snapshot lookup. [Run proof](../Proofs/Table/CheckedRunLookup.lean) · [Table proof](../Proofs/Table/PackedTableLookup.lean) |

## Which evidence belongs with the code?

The private constructor of `CheckedRun` requires evidence that parsing its bytes succeeds. `openBytes` obtains that evidence from the parser call. Similarly, `rangeHistory` returns a `Sequential.History`, whose constructor requires ordered rows. The runtime imports `OptProofs` for the ordering evidence used by range history construction. Filtering the checked history to the half-open interval preserves that ordering. These contracts explain why the next operation can use the result. [Checked run](CompactionRead.lean) · [History contract](CompactionReadContract.lean)

For compaction and retention, import the run or table refinement when you need its guarantees. Code calling the operations can import the corresponding table implementation. [Run compaction proof](../Proofs/Table/CheckedRunCompaction.lean) · [Table compaction proof](../Proofs/Table/PackedTableCompaction.lean)

Run `bash scripts/check-sequential.sh` from the repository root for the table fixtures, kernel checks and axiom audit. The fixtures compare reads from both memtable backends against the snapshot model, including overwritten and deleted keys. [Executable fixtures](../../Checks/Tests/PackedTableChecks.lean)
