# Verificatie van de oorspronkelijke kandidaat

De suite draaide met Lean 4.36.0 (compilercommit `611c117bfaf7b7ae1cfcf246ce6fba31e8f509e9`) en Lake 5.0.0-src+611c117 op een detached worktree van commit `335bbff012b09d70847b9caef3dbf7be13a53296` met tree `867325cb266c85371af7b5b21463f3a974d85ca3`, op Linux x86-64. [Toolchainlog](toolchain.log)

## Stockverificatie

Voer dit op Linux uit vanuit een checkout waarin de kandidaatcommit beschikbaar is. De tijdelijke worktree en de toolchain komen in dezelfde nieuw aangemaakte map. Bewaar de shellvariabelen voor de controles hieronder. [Toolchainuitvoer](toolchain.log)

```bash
set -euo pipefail
repo=$(git rev-parse --show-toplevel)
commit=335bbff012b09d70847b9caef3dbf7be13a53296
tree=867325cb266c85371af7b5b21463f3a974d85ca3
review_tmp=$(mktemp -d)
candidate="$review_tmp/candidate"
git -C "$repo" worktree add --detach "$candidate" "$commit"
test "$(git -C "$candidate" rev-parse HEAD)" = "$commit"
test "$(git -C "$candidate" rev-parse 'HEAD^{tree}')" = "$tree"
export ALVOKI_TOOLCHAINS="$review_tmp/toolchains"
(cd "$candidate" && bash scripts/bootstrap.sh "$ALVOKI_TOOLCHAINS")
export ELAN_HOME="$ALVOKI_TOOLCHAINS/elan"
export PATH="$ELAN_HOME/bin:$PATH"
(cd "$candidate" && LEAN_NUM_THREADS=4 bash scripts/reproduce.sh)
```

De kandidaat voltooide `scripts/reproduce.sh` met exitcode 0, inclusief de Linux-fixtures, de door de scripts uitgevoerde kernel- en axiomacontroles en de controle van 30 Markdownbestanden. De native-L0-fixture geeft bij succes geen eigen samenvattingsregel. Het fragment bevat gemeten regels uit de volledige run. [Uitvoer van de stockverificatie](reproduce-excerpt.log)

## Manifestdescriptor

De bestaande `manifestNativeCheck` publiceert via `DurableBlob.native`. Deze fixture is ook afzonderlijk op de kandidaat uitgevoerd onder `strace`. Het aaneengesloten fragment toont de laatste `fsync` en `close` van de stagingdescriptor, vervolgens de geslaagde `rename` en het hergebruik van descriptornummer 9 voor de directory. Het tijdelijke pad, PID en descriptornummer kunnen per uitvoering verschillen. [Syscalltrace](manifest-fd.trace)

```bash
(
  cd "$candidate/lean"
  lake build manifestNativeCheck
  strace -f -yy -e trace=openat,fsync,close,rename,renameat,renameat2 \
    -o "$review_tmp/manifest-fd.trace" .lake/build/bin/manifestNativeCheck
)
grep -m 1 -A 6 'BLOB.next.*O_TRUNC' "$review_tmp/manifest-fd.trace"
```

## Negatieve test van de staging-fsync

De mutatie vervangt uitsluitend de file-fsync in de productionbinding van de publisher door `pure ()`. De directorybarrière blijft bereikbaar via de originele code. Met de originele binding compileert `NativeManifestPublish.concrete`. De gemuteerde binding wordt op regel 60 afgewezen wanneer de proof de definitie van de uitvoerbare publisher ontvouwt. Na het terugdraaien compileert dezelfde consumer weer. [Patch](staging-sync-negative.patch) · [Lean-diagnose](staging-sync-negative.log)

Voer vanuit de reviewcheckout, met de hierboven geïnstalleerde Lean op `PATH`, het volgende commando uit.

```bash
python3 "$repo/docs/reviews/native-l0-335bbff0/evidence/check-staging-sync.py"
```

Het script maakt een eigen tijdelijke detached worktree op de kandidaat. Voor elk van de drie fasen bouwt het alle lokale imports van de proof opnieuw op in een lege, afzonderlijke `LEAN_PATH`, inclusief `DurableBlob.Native`. Het controleert de verwachte foutmelding, draait de patch terug, controleert de Git-status, herbouwt de herstelde consumer en ruimt zijn eigen worktree op. De SHA-256 van de patch is `0dbf70f05e6ce8d2737ccf2761eb309e1caae0076397cad38c2b38edb5bc0e45`. [Reproductiescript](check-staging-sync.py)

## Aanvullende controles

De reviewrunner herbouwde de dependencies en controleerde beide losse Lean-modules ook met `leanchecker`. [Meetuitvoer](lean-controls.log)

De axiomauitvoer van het tegenvoorbeeld noemt alleen `Classical.choice`. Het native probelog bevat de resultaten van de grotere WAL-histories voor beide policies, de exitcodes bij onderbreking tijdens recovery en de twee heropeningen na tail repair. [Axiomauitvoer](phase-memory.log) · [Native probelog](native-probes.log)

Na de controles kan de tijdelijke kandidaatworktree worden verwijderd. De toolchain en nieuwe logbestanden staan dan nog onder `$review_tmp`.

```bash
git -C "$repo" worktree remove "$candidate"
```
