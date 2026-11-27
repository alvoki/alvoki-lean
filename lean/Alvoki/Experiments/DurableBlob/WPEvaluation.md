# DurableBlob weakest-precondition evaluation

Baseline `f759217c577adcd13fd55b8614e382d4c342170f`. Proof candidate
`bc343a9c1e6ffd6f14e306a9116f3b4bd00bc539`. Both use Lean 4.36.0.
The evaluation uses the existing [file schedule](Protocol.lean) and
[Linux adapter](Native.lean).

## Proof boundary

`FileEffects` specifies the reached projected result of each of five
callbacks. A successful stage returns the designated writer and the exact
staged bytes. The sync contract applies to that same returned writer.
Rename uses the staged binding under the existing stable namespace and
ownership premises. Each reported error allows the projected state before
or after its effect. Arbitrary private scratch effects still rely on the
existing projection. Linux reports establish these local facts under the
same [primitive correspondence](README.md#primitive-correspondence).

`vcgen` composes the contracts along `Files.backend`. Publication produces
the exact settled proposal or one of the reached cuts. Reopen produces the
selected binding and its settlement, or an unchanged or settled image on
error. The model and Linux-report adapters instantiate the same proof in
`EStateM Unit Image`. This experiment generalizes the interpretation within
that monad. The code does not prove the runtime semantics of arbitrary IO.

The original Run indices, public event guarantees and retry theorems are
retained. The experimental Run constructors take a local effect witness and
an equation for the actual result. Direct constructor calls or inductions
over Run may need adaptation. Safety continues through the same trace
induction. Process stops, crash survivors and lost replies remain explicit
Run steps. `Run.healthy_open` still gives a constructive healthy execution
using successful model reports. The [typed manifest fixture](../Manifest/RefinementExperiment.lean)
checks the Linux report interpretation, including lost success separately
from returned failure.

## Matched changes

Line counts below exclude blank lines. The algorithmic column counts changes
to the common schedule or correspondence proofs. For the new adapter, the
producer total includes its definitions, the two theorem entry points and
two exact-result fixtures. The adapter has the same behavior and initial
conditions in both copies.

| Case | Executable change, both copies | Algorithmic proof | Primitive or interpreter producer | Lifecycle | General infrastructure |
| --- | --- | --- | --- | --- | --- |
| Repeat the publish directory barrier | One extra call in the shared schedule | Baseline unchanged. WP adds idempotence and passes it to `grind` (+2/-1). | None | None | None |
| Choose a directory report from the reached survivor set | None in production. Both add the same experimental report adapter. | Existing schedule proofs unchanged. | Baseline adds two whole-result equalities, both `rfl`, and their uses. WP adds one local effect witness and two instantiations. Total +35 baseline and +28 WP nonblank lines. | None | None |
| Refine a staged write failure to also report a full write effect | Production unchanged. Both add a modeled report flag and branch (+3/-1). | Unchanged | Baseline updates report projection and staged correspondence (+3/-2). WP updates only the local stage proof (+2/-1). | None | None |
| Failed recovery barrier after effect, then retry | None. Same consumer fixture compiled in both copies. | Unchanged | Reuse the existing report and retry theorems in both copies. | Same fixture reuses the reached image, the public Run and retry theorems. | None |
| Remove the publish directory barrier | Delete one call | Both reject the mutation in the publication proof. | None | None | None |

The duplicate barrier experiment is favorable to the baseline. It reuses the
same report for both calls, a second call is only reached after the first
succeeds, and the existing case proof simplifies the two barriers into one.
The WP proof needs the explicit idempotence fact. The adaptive interpreter
favors the WP boundary a little. The baseline predicts which image reaches
the barrier. Its whole-result equations are definitionally true for this
transparent adapter, so the saving is small. The adaptive publication example
always loses the barrier reply from a settled input. The fixture independently
checks that healthy recovery from the settled result succeeds.

Removing the final barrier can acknowledge after rename with old and new
survivors. The baseline rejects that in `publish_outcome`. The WP candidate
rejects it in `publish_spec`, where the rename postcondition cannot establish
the required settled state. The typed failure fixture separately checks that
a rename error can leave the proposal visible, the failed recovery barrier
can pin it, and the same bytes reach typed recovery and a subsequent restart.

## Automation and proof reuse

- `vcgen` composes four primitive calls for publication and two for reopen,
  using Lean's bind and pure rules. No manual bind-result cases remain in
  those two proofs. The proofs still unfold the structure projection once,
  provide the local specs and give the solver the cut invariant. The writer
  equality must be in the sync precondition, since the call uses a bound
  variable. Scheduling and effect facts are ordinary theorem statements.
- The [comparison module](WPComparison.lean) compiles both `mvcgen` and
  `vcgen` on a barrier that changes state and then throws. The existing
  `ExceptT` and `EStateM` WP instances also support separate error postconditions
  for `.ok (.error …)` and `.error …` in a nested stack. The module proves the
  case split from its triple to the actual reached result without a custom
  instance. Nested *execution* remains a separate probe. DurableBlob itself
  represents interruptions at the public trace boundary. The component
  schedule has no traversal to measure.
- The [relational variant](../../../../scripts/experiments/durableblob-perturb.py)
  replaces only the reopen WP proof with an explicit reached-result proof.
  It uses a case split on read and another on sync. Both prove the same
  triple via the existing result adequacy lemma. This is a readable option
  for a short schedule with few continuations. A shared `bindPost` rule
  of the kind already used by segmented WAL can remove these cases when
  many schedules consume the same result representation.
- **Composition reuse and fact reuse pay for different work.** The
  EStateM triple-to-result rule is reusable for the interpreter. Independently,
  `publish_stable` supplies the settled image or cut for the Run and live
  binding proofs. `reopen_binding` supplies the selected value and settled
  state once. `reopen_outcome` and the L0-facing `reopenBinding` consume
  that fact. No downstream proof needs to run the schedule again to derive
  it. WP postconditions express these facts naturally, but the producer
  still has to name the witness and the consumer has to select it. This is
  the same reason to pass SSTable's proved Image directly to the reader.
  Keep such evidence in the proof interface, outside the runtime path.

This comparison favors keeping the existing architecture for today's short
DurableBlob while making local contracts and established facts easier to
reuse. The candidate `Proofs.lean` is approximately 120 lines larger than
main, including three observations subsequently needed by the pinned L0
consumer. No observed change demonstrates a broad maintenance win sufficient
to require `vcgen` for new components. Use it selectively when a second
interpreter can reuse a substantial schedule theorem. Extract a small
composition or adequacy rule only when another concrete consumer will replace
existing proof work with it. Postpone a common effect framework.

## Reproduction

Run the [focused manifest suite](../../../../scripts/check-experimental-manifest.sh)
and the repository [reproduction suite](../../../../scripts/reproduce.sh) at
the candidate. The focused suite kernel-checks and audits the WP probes,
DurableBlob Run/retry theorems and typed consumer, and runs the Linux Manifest
fixture. The native L0 runner also compiled and passed in a scratch copy of
PR #5 head `859f68d0ba1cf6aece0064b896a7d051f1281d18`, substituting the
candidate DurableBlob proof module.

Run the comparison on disposable checkouts. The python driver edits the copy
passed to it. Set `ALVOKI_TOOLCHAINS` to the bootstrap directory before running
the checks.

```bash
reference=f759217c577adcd13fd55b8614e382d4c342170f
candidate=bc343a9c1e6ffd6f14e306a9116f3b4bd00bc539
driver="$PWD/scripts/experiments/durableblob-perturb.py"
# Set one of schedule, adapter, local, remove-barrier or relational.
scenario=schedule
scratch=$(mktemp -d)
for flavor in base wp; do
  revision="$reference"
  if [[ $flavor == wp ]]; then revision="$candidate"; fi
  if [[ $scenario == relational && $flavor == base ]]; then continue; fi
  mkdir -p "$scratch/$flavor"
  git archive "$revision" | tar -x -C "$scratch/$flavor"
  python3 "$driver" "$scratch/$flavor" "$scenario" "$flavor" --repair
  (cd "$scratch/$flavor" && bash scripts/check-experimental-manifest.sh)
done
```

Expected exit status is zero except for `remove-barrier`. Omit `--repair`
to see the initial WP failure on the duplicate barrier. For the identical
consumer comparison, copy `RefinementExperiment.lean` into the baseline
scratch tree and compile it after Manifest proofs.

Lean-generated `Protocol.c` and `Native.c`, and their objects built with
`cc -O2 -fPIC`, matched byte for byte across the baseline and candidate.
`Protocol.c` SHA-256 is
`a5c88b8660a0a3633123de88b8d7b58357470861e67ab4d66e0f84ca3726d6ee`.
`Native.c` SHA-256 is
`e78920be8249c627b04dfcb428f0a251b80f051cadd2042cdf97e808861cc219`.
The proof-only imports are outside the executable import path. No throughput
measurement was performed.
