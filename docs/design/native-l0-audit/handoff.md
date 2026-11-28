# Handoff voor Astra en de writer-integrator

De twee branchkoppen zijn het geteste experiment. Review of integreer hun wijzigingen in een eigen worktree. De latere geïntegreerde stand van PR #5 die hieronder als doel dient is 13a655eadd4967b08da6acc54ae9bf8f2a393ce4.

## Astra · runtimecorrectness van WAL-read

**Urgentie:** een positief korte fread met ferror kan de boundary-WAL tijdens dezelfde falende leespoging tot tail-repair laten overgaan. De bestaande regressiesuite op de auditpin was groen. De bevestigde batch [7] bleef in deze minimale reproductie behouden. Het waarneembare probleem is de succesmelding én de gewijzigde segmentbytes. Dit kan afzonderlijk van de migratie naar compact WAL of de PhaseMemory-reparatie worden verholpen.

- Bronbranch `audit/wal-read-boundary`, pin [c3080f1b](https://github.com/alvoki/alvoki-lean/commit/c3080f1bcd789f32ab3dd5e77390ab78cf7819b7), basis `335bbff0`. De [eerste commit](https://github.com/alvoki/alvoki-lean/commit/41e0f13813d46c0e7208def09dfef0f98e564432) bevat de drie productie-/proofbestanden en de foutfixture. De volgende commit bewaart de rookmeting en postconditieproef. De C-leaf stamt uit PR #34; voorkom een dubbele extern bij die latere integratie.
- Neem de checked chunk in lean/native/fsync.c, de binding plus aanroep in WAL/SingleFile.lean en de twee koppelingen in Segmented/Proofs/CreateCutIO.lean samen over. Inspecteer ferror ook bij positief resultaat, laat kort succes uitsluitend bij EOF toe en behoud de errno-diagnose op de betreffende FILE-pointer. Laat de 1.024-byte-lus en de afzonderlijke latere operands zichtbaar. De concrete loop bedient ook het lezen van de policy. Het wijzigen van uitsluitend de runtimeleaf deed ChunkPrefix.remaining daadwerkelijk falen.
- Bijdrage aan acceptatie: een fout vóór truncation, ongewijzigde bytes op die terugkeer, daarop twee gezonde opens op dezelfde geschiedenis en de bijpassende prefix-/cut-stellingen. Bewaar bij de integratie de foutfixture als doorlopende regressie. De oorspronkelijke suite riep deze nieuwe experimentele fixture nog niet aan.
- De drie betrokken bestanden waren tussen auditpin en `13a655ea` identiek. Op een afzonderlijke worktree van de laatste is de gezamenlijke baseline/leaf-proef hieronder uitgevoerd. Baseline retourneerde succes en repareerde vroegtijdig; met de drie wijzigingen retourneerde reopen hardware fault 5, de bytevergelijking en beide retries slaagden. De volledige native-L0-suite draaide eerder op de gepinde experimentele variant. Dit blijft een fysieke runtimefix ook terwijl de heap-afhankelijke end-to-end-acceptatie openstaat.

Uitvoerbaar recept op een reviewworktree, vanaf de repositoryroot met Lean 4.36.0 en Lake op PATH:

```bash
git fetch origin audit/wal-read-boundary audit/streaming-writer-transport
git worktree add --detach ../review-wal-read 13a655eadd4967b08da6acc54ae9bf8f2a393ce4
cd ../review-wal-read
git restore --source=c3080f1b -- tests/audit
bash tests/audit/check-short-read.sh baseline
git restore --source=41e0f138 -- lean/native/fsync.c \
  lean/Alvoki/Experiments/WAL/SingleFile.lean \
  lean/Alvoki/Experiments/WAL/Segmented/Proofs/CreateCutIO.lean
bash tests/audit/check-short-read.sh leaf
bash scripts/check-native-l0.sh
```

De modus baseline verwacht juist het verkeerde gedrag. Gebruik leaf als acceptatiecheck. Bij een latere doelrevisie eerst de drie bestanden vergelijken en de kleine diff toepassen; een hele nieuwere implementatie overschrijven zou werk kunnen verliezen.

## BuilderRelation · integratie op de gezamenlijke basis

Bronbranch `audit/streaming-writer-transport`, pin [a4e8f5fd](https://github.com/alvoki/alvoki-lean/commit/a4e8f5fdca1f999832d4763a5fe4ee93c350634d), basis `275e348b` op main. De experimentcommit brengt de 160 regels van BuilderRelation onveranderd mee van PR #5 omdat main die inductie miste. Op `13a655ea` staat die exacte inductie al in de tree. Daar is alleen het proofbestand SortedRun/IOEffects.lean nodig. Die gerichte overname en de volledige sorted-run-suite zijn op die integratiestand opnieuw getest.

De gedeelde inductie volgt de uitvoerbare writer vanaf buildStream via de row-loop en packet-/leaf-/dataflush tot de finale flush. Het supply-contract geeft de gerelateerde volgende rij, SinkAgreement levert de append- en flushwetten, de algemene Rules verzorgen pure, seq, raise en abort. De L0-interpreter kan de fase vóór/na eindflush gebruiken. De merge-instantie kiest voor beide actie-uitdrukkingen exacte gelijkheid na effectobservatie en negeert de fase-index. Dezelfde inductie geldt voor beide. De outer schedule met exclusive create, cleanup, flush en sync blijft expliciet.

Het publieke contract blijft voor alle oorspronkelijke ops, crc, path, layout, supply, invalid en options:

```lean
effect (buildFileWith ops crc path layout supply invalid options) =
  buildFileWith (effectOutput ops) crc path layout (effect supply) invalid options
```

Dat is gelijkheid van berekening inclusief exacte fout en laatste wereld, zonder nieuwe succes- of heap-premisse. De downstream-stellingen voor gesyncte output en inputerror blijven dezelfde. Een gemaskeerde sink-flush wordt door het nieuwe lokale bewijs geweigerd. Op de oorspronkelijke experimentele basis waren de native binaries identiek.

```bash
git worktree add --detach ../review-writer 13a655eadd4967b08da6acc54ae9bf8f2a393ce4
cd ../review-writer
git diff --exit-code a4e8f5fd HEAD -- lean/Alvoki/Experiments/SSTable/Proofs/BuilderRelation.lean
git restore --source=a4e8f5fd -- lean/Alvoki/Experiments/SortedRun/IOEffects.lean
bash scripts/check-sorted-run.sh
```

## Verificatiearchief

| Materiaal | Betekenis |
|---|---|
| [reproduce.log](evidence/reproduce.log) | Originele volledige suite op 335bbff0, exit 0. Kernel- en axiomaresultaten voor conditionele stellingen bewijzen de premissen niet. |
| [public-check.log](evidence/public-check.log), [leaf-before.log](evidence/leaf-before.log), [leaf-after.log](evidence/leaf-after.log), [leaf-l0.log](evidence/leaf-l0.log) | Positief kort lezen op de variant, verwachte proofbreuk vóór aanpassing, herstelde modulebuild en geslaagde native-L0-suite. Een initiële gezamenlijke losse leanchecker-invocatie eindigde met status 139; afzonderlijke kernelchecks van CreateCutIO en PublicAppendCut en de check_axioms-proef slaagden daarna. |
| [merge-check.log](evidence/merge-check.log), [binarydigests](evidence/writer-sha256.txt), [negatieve baseline](evidence/mutation-baseline.log), [negatieve variant](evidence/mutation.log) | Geslaagde sorted-run-suite, gelijke executable en de twee verwachte Lean-afwijzingen. |
| [Geïntegreerde WAL-baseline](evidence/integrated-wal-baseline.log), [WAL-fix](evidence/integrated-wal-fix.log), [writer](evidence/integrated-writer.log) | Nieuwe gerichte integratiechecks op disposable kopieën van 13a655ea. Alle drie exit 0; de baselinefixture slaagt door het defect waar te nemen. |
| [Oorspronkelijke hulpbronnen](../../../tests/architecture-audit/original) en [experimentele WAL-fixtures](https://github.com/alvoki/alvoki-lean/tree/c3080f1b/tests/audit) | Cookie-FFI-bron en Lean-probe, beide gemuteerde writerproeven, oorspronkelijke timingdriver en alle 14 ruwe samples. De csv is byte-identiek aan de geteste WAL-branch. De cookie- en timinghulpbronnen bewaren het oorspronkelijke scratchpad en binaire namen. Het portable WAL-regressierecept staat hierboven. |
| [PhaseMemory-proef](../../../tests/architecture-audit/PhaseMemory.lean) | Nieuwe zelfstandige contradictie, kernel en repository-axiomabeleid op de auditpin. Zie het [reproductierecept](phase-memory.md). |
