# Experimental L0 model

The [shared schedule](Basic.lean) implements serialized put, delete, get, flush
and reopen. The [component interpreter](Model.lean) starts with an empty logical
store and retains the WAL prefix. Its [component proofs](ComponentProofs.lean)
establish the [callback laws](ComponentContract.lean) consumed by the
[operation proofs](Refinement.lean).

The [client contract](Client.lean) observes a key-value map.
`Model.Run.refines` in [Execution](Execution.lean) proves that the modeled
execution preserves acknowledged mutations, that recovery permits at most the
one uncertain mutation, and that a flush preserves the map even when publication
is uncertain. `Model.Run.healthy_open` supplies a fault-free reopen from each
reachable offline model state. [Recovery choices](RecoveryChoices.lean) proves
that retries narrow the admissible component choices.
[Read error proofs](ReadErrors.lean) show that a required table error propagates
with the reached state.

The modeled fault reports exercise before-effect and after-effect outcomes.
The scope of this milestone is the shared schedule and its model interpreter.
Native adapter refinement, including concrete interruption prefixes and
filesystem recovery, is separate work.

Run `bash scripts/check-experimental-l0.sh` for kernel replay, axiom checks and
the [modeled scenarios](Tests.lean). The same runner is part of
`bash scripts/reproduce.sh`.
