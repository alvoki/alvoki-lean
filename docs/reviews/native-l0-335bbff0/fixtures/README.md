# Reproductie van de aanvullende Linux-proeven

Draai vanuit deze directory op Linux x86-64 met Bash, Git, een C- en C++-compiler,
GNU binutils, Python 3 en `strace`. De gepinde Lean 4.36.0 moet op het pad staan
of via de bestaande bootstrap van de repository beschikbaar zijn. Voor de bouw
van de CRC32C-bibliotheek is toegang tot de gepinde upstream Git-revisie nodig.

```bash
./run.sh /pad/naar/alvoki-lean
```

Met een toolchain uit `scripts/bootstrap.sh` kan dit ook als volgt.

```bash
ALVOKI_TOOLCHAINS=/pad/naar/toolchains ./run.sh /pad/naar/alvoki-lean
```

De repository moet het object `335bbff012b09d70847b9caef3dbf7be13a53296`
bevatten. De runner controleert de tree
`867325cb266c85371af7b5b21463f3a974d85ca3` en bouwt vanuit een
tijdelijke export van de Lean-bronnen op die commit. De twee auditdrivers
worden naast de geëxporteerde bronnen gecompileerd. Bij succes of een
fout verwijdert de runner de tijdelijke bouwbestanden en de testdatabases.

- **Grotere WAL-geschiedenis.** `HistoryProbe.lean` vergelijkt alle 31
  sleutels met een onafhankelijke array na twee tussentijdse flushes, aan
  het eind van 205 puts/deletes, tijdens twee heropeningen en na een laatste
  flush en heropening. De segmentcapaciteit is 72. De proef vereist het
  bestaan van segment 2 en loopt voor `logOnly` en `boundary`.
- **Onderbroken recovery.** `RecoveryProbe.lean` maakt voor elk beleid een
  database met vijf acknowledged mutaties en segmentcapaciteit 3. De runner
  voegt één byte `ff` toe aan het actieve segment. De eerste heropening
  stopt direct na de eerste geslaagde `ftruncate` met exitcode 75. Op
  dezelfde database stopt de tweede heropening na de eerste geslaagde
  `fsync` van een bestand met naam `segment` met exitcode 73. Die tweede
  injectie gebruikt de bestaande interposer van de kandidaat. De runner
  controleert de oorspronkelijke lengte en laat twee nieuwe processen
  de tombstone, de waarde uit het afgesloten segment en de waarde uit het
  actieve segment lezen. De kernel en de bestandssysteemcache blijven
  voor alle vier heropeningen actief.
- **Levensduur van de manifestwriter.** De runner voert het originele
  `manifestNativeCheck` van de kandidaat onder `strace -f -yy` uit.
  `check-trace.py` zoekt binnen één thread de eerste volledige geslaagde
  reeks met open en fsync van `BLOB.next`, close van die writer, rename
  naar `BLOB`, open van de parent en fsync van de teruggegeven
  directorydescriptor. Het script toont de zes syscallregels en eindigt
  met een fout als het die volgorde niet vindt.

Een exitcode 0 bevestigt deze concrete waarnemingen. De Linux-proeven voor
onderbroken recovery bestrijken de twee beschreven processtops. Power loss,
andere cutposities en de formele kwantificatie over histories vereisen
afzonderlijk bewijs.
