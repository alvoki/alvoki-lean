namespace Alvoki.Manifest

/-- A generation names an ordered set of run files by consecutive index.
The WAL covers all writes beyond the installed watermark. -/
structure Checkpoint where
  generation : UInt64
  committed : UInt64
  floor : UInt64
  runCount : UInt64
  deriving Repr, DecidableEq

end Alvoki.Manifest
