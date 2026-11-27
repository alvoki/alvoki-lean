from pathlib import Path
import argparse

p = argparse.ArgumentParser()
p.add_argument('root', type=Path)
p.add_argument('case', choices=['schedule', 'remove-barrier', 'local', 'adapter', 'relational'])
p.add_argument('architecture', choices=['base', 'wp'])
p.add_argument('--repair', action='store_true', help='apply the WP repair for a second barrier')
args = p.parse_args()
blob = args.root / 'lean/Alvoki/Experiments/DurableBlob'
proof = blob / 'Proofs.lean'
text = proof.read_text()

if args.case in ('schedule', 'remove-barrier'):
    protocol = blob / 'Protocol.lean'
    source = protocol.read_text()
    needle = '    files.renameStaged\n    files.syncDirectory\n'
    sync = '    files.syncDirectory\n' * (2 if args.case == 'schedule' else 0)
    assert source.count(needle) == 1
    protocol.write_text(source.replace(needle, '    files.renameStaged\n' + sync))
    if args.repair and args.case == 'schedule' and args.architecture == 'wp':
        text = text.replace('private theorem publish_spec',
            'private theorem barrier_twice (s : Image) : s.barrier.barrier = s.barrier := rfl\n\n'
            'private theorem publish_spec', 1)
        text = text.replace('grind [PublishCut]', 'grind [PublishCut, barrier_twice]', 1)
        proof.write_text(text)


if args.case == 'local':
    # Distinguish a reported staged write error after a full write effect.
    # Existing constructors keep their meaning through the default.
    text = text.replace('  rename : Report\n', '  rename : Report\n  writeErrorAfterEffect : Bool := false\n', 1)
    text = text.replace('perform (if reports.write then .ok else .beforeEffect)',
        'perform (if reports.write then .ok else\n        if reports.writeErrorAfterEffect then .afterEffect else .beforeEffect)', 1)
    if args.architecture == 'base':
        text = text.replace('    else .beforeEffect\n  | .syncStaged', '    else if reports.openWriter && reports.writeErrorAfterEffect then .afterEffect else .beforeEffect\n  | .syncStaged', 1)
        text = text.replace('cases o : reports.openWriter <;> cases w : reports.write <;> cases f : reports.flush <;>', 'cases o : reports.openWriter <;> cases w : reports.write <;> cases f : reports.flush <;>\n    cases late : reports.writeErrorAfterEffect <;>', 1)
        text = text.replace('checked, Reports.publication, perform,\n      Bind', 'checked, Reports.publication, perform, late,\n      Bind', 1)
    else:
        text = text.replace('cases o : reports.openWriter <;> cases w : reports.write <;> cases f : reports.flush <;>', 'cases o : reports.openWriter <;> cases w : reports.write <;> cases f : reports.flush <;>\n      cases late : reports.writeErrorAfterEffect <;>', 1)
        text = text.replace('checked, perform, Effect, o, w, f,','checked, perform, Effect, o, w, f, late,',1)
    # Update positional struct fixture for either interpretation.
    consumer = args.root / 'lean/Alvoki/Experiments/Manifest/RefinementExperiment.lean'
    if consumer.exists():
        consumer.write_text(consumer.read_text().replace('.ok, .ok⟩', '.ok, .ok, false⟩'))
    proof.write_text(text)

if args.case == 'adapter':
    shared = """
namespace AdaptiveBarrierExperiment

-- Choose the report at the reached directory state. A pending alternative
-- triggers a lost barrier reply, even though the barrier takes effect.
private def choose (s : Image) : Report :=
  if s.survivors.length > 1 then .afterEffect else .ok

private def files : Files (EStateM Unit Image) Unit :=
  { model (fun _ => .ok) true with
    syncDirectory := fun s => perform (choose s) Image.barrier s }

"""
    commonPub = """theorem publish (before : Image) (stable : before.Stable old) (bytes : ByteArray) :
    match files.backend.publish bytes before with
    | .ok _ after => after.Stable bytes
    | .error _ after => after.Admits old (some bytes) := """
    commonOpen = """theorem reopen (before : Image) (admitted : before.Admits old pending) :
    match files.backend.reopen before with
    | .ok value after => Permitted old pending value ∧ after.Stable value
    | .error _ after => after.Admits old pending := """
    if args.architecture == 'base':
        extra = """private theorem publish_eq (before : Image) (bytes : ByteArray) :
    files.backend.publish bytes before =
      (model (fun op => match op with
        | .syncDirectory => choose (before.recordWrite bytes).syncWriter.replace
        | _ => .ok) true).backend.publish bytes before := by
  rfl

private theorem reopen_eq (before : Image) :
    files.backend.reopen before =
      (model (fun _ => choose before) true).backend.reopen before := by
  rfl

"""
        cert = (commonPub + """by
  rw [publish_eq]
  exact publish_outcome _ before stable bytes

""" + commonOpen + """by
  rw [reopen_eq]
  exact reopen_outcome _ true before admitted

""")
    else:
        extra = """private theorem effects : FileEffects files () :=
  { modelEffects (fun _ => .ok) true with
    barrier := fun s => perform_effect (choose s) Image.barrier s }

"""
        cert = (commonPub + """by
  cases ran : files.backend.publish bytes before <;>
    simpa only [ran, Post] using publish_outcome effects before stable bytes

""" + commonOpen + """by
  cases ran : files.backend.reopen before <;>
    simpa only [ran, Post] using reopen_outcome effects before admitted

""")
    checks = """
example (old bytes : ByteArray) :
    files.backend.publish bytes (.settled old) = .error () (.settled bytes) := rfl

example (bytes : ByteArray) :
    files.backend.reopen (.settled bytes) = .ok bytes (.settled bytes) := rfl

end AdaptiveBarrierExperiment

"""
    text = text.removesuffix('end DurableBlob\n') + shared + extra + cert + checks + 'end DurableBlob\n'
    proof.write_text(text)

if args.case == 'relational':
    assert args.architecture == 'wp'
    start = text.index('  have read {s : Image} :=', text.index('private theorem reopen_spec'))
    end = text.index('\ntheorem publish_stable', start)
    proof.write_text(text[:start] + '''  rw [triple_iff]
  intro s same
  subst s
  have read := effects.read before
  simp only [Files.backend, Bind.bind, EStateM.bind]
  cases r : files.readActive before with
  | error _ reached =>
    exact Or.inl (by simpa only [r, Effect, or_self] using read)
  | ok value reached =>
    have entered : value = before.active ∧ reached = before := by
      simpa only [r, Effect] using read
    obtain ⟨sameValue, sameState⟩ := entered
    subst reached
    subst value
    have barrier := effects.barrier before
    cases cut : files.syncDirectory before with
    | error _ reached => simpa [Post, cut, Effect] using barrier
    | ok _ reached =>
      have settled : reached = before.barrier := by
        simpa only [cut, Effect, and_true, eq_self, true_and] using barrier
      simpa [Post, cut, Pure.pure, EStateM.pure] using settled

''' + text[end:])
