# Durable blob replacement

The owner starts offline with one initialized durable byte string. First call
`reopen`. A successful `publish bytes` makes the supplied bytes durable. If
publication fails or its reply is lost, stop using the session and reopen.
The first successful reopen returns the previous value or the complete
proposal, according to the surviving state. With no intervening publication,
another successful reopen returns that same value, even after power loss.
A failed reopen returns no value and may be retried. The caller serializes
operations and observes this session discipline. [Client contract](Contract.lean)

[Protocol](Protocol.lean) writes the private staging file, syncs
its bytes through the same write handle, renames it over the active name,
and syncs the parent directory. Reopen reads the active file and syncs
the directory before returning. A process exit after rename can leave the
new file visible before the name is durable. Returning the read alone would
allow a second crash to reverse a successful reopen.

The [Linux adapter](Native.lean) reserves `BLOB` and `BLOB.next` in a
durably named, stable directory. The caller supplies exclusive ownership
and an initialized active file. Both names, whenever present, refer to
distinct regular files without aliases to other files. Missing active data
or a read error propagates as an error. The staging file can be left behind
and overwritten by the next publication.

The native backend and the proof interpreter instantiate the same
`Primitives.backend`. This fixes the paths, modes, descriptor passed to
each write, flush and fsync, and the order and error handling of the calls.
The interpreter in [Proofs](Proofs.lean) takes outcomes of those individual
primitives. `LinuxEffects.reopen` and `LinuxEffects.publish` extend the
existing `Run` with the exact returned or submitted bytes.
`Run.refines` yields the public `Allows` trace, while
`LinuxEffects.reopenSettles` gives the public open step and the settled
image directly. `Run.healthy_open` shows that a reachable offline image
can reopen when the read and barrier succeed.

## Primitive correspondence

For a reached call, the Linux IO result and its physical effect must match
the following interpretation. Success/failure flags come from that call.
For rename and fsync, an observed error allows either effect. Reports for
unreached operations are immaterial.

| Linux primitive at the reached argument | Correspondence to `LinuxEffects.primitives` |
| --- | --- |
| `readBinFile BLOB` | Success returns the exact bytes of the visible binding, `Image.active`. A failure returns an error. Neither changes the binding or its crash choices. |
| Open the directory for read | Success holds the managed directory and yields `.directory`. Failure skips fsync. Opening leaves the blob image unchanged. |
| Open `BLOB.next` for write, then write and flush | Successful open holds the private, truncated or newly created inode and yields `.writer`. The write records the supplied bytes for staging. Successful flush makes those full bytes visible on that inode. Open, write or flush failure can leave arbitrary scratch contents, including effects of a late close. Scratch effects preserve the active binding and every active crash choice. |
| File fsync through `.writer` | The effect persists the flushed bytes on that inode, recorded in `Image.synced`. A pre-effect error preserves the prior projected image. Closing after successful flush and sync preserves the synced bytes. |
| Rename `BLOB.next` over `BLOB` | The effect switches the visible binding atomically to the synced inode. Until a barrier, the model covers both intact crash choices. Physical writeback may narrow that set. |
| Directory fsync through `.directory` | The effect settles the visible binding and narrows the modeled survivors to that binding. A pre-effect error leaves the previous choices. |

The shared schedule fixes which paths and modes are used and passes the
actual handle returned by each open to the relevant primitives. The runtime
must keep that handle tied to its open file description, including through
the native fsync wrapper. The owner's exclusive stable namespace ties the
directory handle to the parent of both names and keeps the staging name
bound to the writer's inode until rename. Non-aliasing also keeps scratch
effects private. These facts make the two abstract identities sufficient
within each call. Each successful open resolves its own descriptor again,
so neither tag asserts descriptor equality across calls or restarts.
Compiler and runtime fidelity, the primitive effects above, and the device's
preservation of synced data remain external. [Filesystem premises](../../../../docs/proofs/filesystem.md)

A process stop retains the reached visible binding. A power loss selects a
surviving binding. An interruption uses the effect at the cut, or the
completed effect if the final reply was lost. `LinuxEffects.publishUncertain`
and `LinuxEffects.reopenInterrupted` retain that image without issuing an
acknowledgement or ready session. `LinuxEffects.reopenAgain` checks that a
second successful open after stop or power loss returns the first reply.
The focused manifest check exercises rename and barrier errors in the
interpreter and uses the native adapter for its Linux fixture.

## L0 producer check

The PR #5 consumer requires an open receipt and a publication run. Start at
`Run.initial` for the owner's initialized empty manifest. The primitive
interpreter and producer theorems construct both runs below. L0 supplies
codec validity and the selected-manifest projection. A returned reopen
error records `.openFailed`. An interrupted reopen, including a lost
reply, records `.stop`. A publication error or lost reply records
`.uncertain`. If a later L0 action fails after the blob has opened
successfully, L0 records that open followed by stop. [PR #5 consumer](https://github.com/alvoki/alvoki-lean/blob/56a422f6/lean/Alvoki/Experiments/L0/NativeFacts.lean)

```lean
import Alvoki.Experiments.L0.NativeFacts

open DurableBlob L0Manifest ExperimentalL0.NativeBridge

example (dir : System.FilePath) (proposal : Version) (valid : proposal.Valid) :
    ManifestOpenReceipt .empty .empty ∧
    decode (Image.settled (encode proposal)).active = some proposal := by
  let reports : LinuxEffects.Reports := {
    readActive := true
    openDirectory := true
    syncDirectory := .ok
    openWriter := true
    write := true
    flush := true
    syncWriter := .ok
    rename := .ok
  }
  let initial := encode Version.empty
  have opened : Run initial [.opened initial] true (.settled initial) := by
    have run := LinuxEffects.reopen dir reports (Run.initial (initial := initial))
    have returned : (LinuxEffects.backend dir reports).reopen (.settled initial) =
        .ok initial (.settled initial) := by
      simp [LinuxEffects.backend, Primitives.backend, Primitives.files, Files.backend,
        LinuxEffects.primitives, reports, Bind.bind, EStateM.bind] <;> rfl
    rw [returned] at run
    exact run
  have published : Run initial ([.opened initial] ++ [.published (encode proposal)])
      true (.settled (encode proposal)) := by
    have run := LinuxEffects.publish dir reports (encode proposal) opened
    have returned : (LinuxEffects.backend dir reports).publish (encode proposal)
        (.settled initial) = .ok () (.settled (encode proposal)) := by
      simp [LinuxEffects.backend, Primitives.backend, Primitives.files, Files.backend,
        LinuxEffects.primitives, reports, Bind.bind, EStateM.bind] <;> rfl
    rw [returned] at run
    exact run
  have decoded : decode initial = some Version.empty :=
    decode_encode (by simp [Version.Valid, Version.empty])
  refine ⟨.issued (events := []) opened ?_ decoded decoded,
    manifest_publish published ?_ valid⟩
  · simp [Event.Submitted]
  · simp [Event.Submitted]
    exact ⟨proposal, valid, rfl⟩
```

The same boundary supports recovery for arbitrary valid manifest versions
and primitive reports. The equations below select branches of the pure
interpreter. The first open settles its choice, so a later L0 error and
stop leave that choice pinned for a retry.

```lean
import Alvoki.Experiments.L0.RecoveryChoices
import Alvoki.Experiments.DurableBlob.Proofs
import Alvoki.Experiments.Manifest.Proofs

open DurableBlob L0Manifest ExperimentalL0.RecoveryChoices
open WalRecoverySlice.Segmented

example (dir : System.FilePath) (publish failed opened : LinuxEffects.Reports)
    (view : Contract.View) (old proposal : Version)
    (oldValid : old.Valid) (proposalValid : proposal.Valid)
    (before afterFailure settled : Image) (bytes : ByteArray)
    (stable : before.Stable (encode old))
    (failure :
      let afterPublish := match (LinuxEffects.backend dir publish).publish (encode proposal) before with
        | .ok _ image | .error _ image => image
      (LinuxEffects.backend dir failed).reopen afterPublish = .error () afterFailure)
    (success : (LinuxEffects.backend dir opened).reopen afterFailure = .ok bytes settled) :
    ∃ version, decode bytes = some version ∧ settled.Stable (encode version) ∧
      (version = old ∨ version = proposal) ∧
      Retry (.online view) (.offline old (some proposal))
        (.online view) (.offline version none) := by
  have pending := (LinuxEffects.publishUncertainAdmits dir publish stable (encode proposal)).2
  have admissible := (LinuxEffects.reopenFailedAdmits dir failed pending failure).2
  obtain ⟨openedStep, pinned⟩ := LinuxEffects.reopenSettles dir opened admissible success
  have permitted : Permitted (encode old) (some (encode proposal)) bytes := by
    cases openedStep with
    | opened allowed => exact allowed
  have chosen : ∃ version, version.Valid ∧ bytes = encode version ∧ Permitted old (some proposal) version := by
    rcases permitted with same | next
    · exact ⟨old, oldValid, same, Or.inl rfl⟩
    · exact ⟨proposal, proposalValid, (Option.some.inj next).symm, Or.inr rfl⟩
  obtain ⟨version, valid, rfl, allowed⟩ := chosen
  have retry : Retry (.online view) (.offline old (some proposal))
      (.online view) (.ready version) :=
    .manifest (.manifest .initial .openFailed trivial) (.opened allowed) trivial
  exact ⟨version, decode_encode valid, pinned, retry.afterPublish.2,
    .manifest retry .stop trivial⟩
```

The focused manifest script checks the producer modules and audits their
axiom dependencies, and runs the Linux fixture. Compile these examples with
the PR #5 consumer to check the premise handoff. The kernel and axiom
checks establish the derivation and its logical dependencies. The table
above records the external IO premises, and the fixture samples their
native behavior. When PR #5 is integrated, move these checked examples into
the permanent L0 composition proofs or integration checks. The L0 agent
owns that integration and the native L0 lifecycle proof.

## Follow-up for WAL and SSTable

PR #5 already retains the original `CONTROL` writer for WAL sync. Try
sharing the staged writer and directory barrier with that path once its
producer establishes durability of newly referenced segments and settles
the control binding before collection. WAL owns its codec and segment
lifetime. For SSTable, try sharing held-file identity, exact positional
reads and file sync with its checked open or builder. SSTable owns content
immutability, range checks, codec validity and publication by the caller.
Extract a primitive only after the second consumer shows what proof or
executable code it can reuse.
