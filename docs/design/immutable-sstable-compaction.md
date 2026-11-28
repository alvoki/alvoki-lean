# Immutable SSTable-compaction voor L0

Onderzoeksbasis is `main` op `a375c871879e51558be60661d86f73b9cbaa904c`.
De productie-implementatie begint na acceptatie van de geïntegreerde native
L0-baseline. Dit ontwerp gebruikt de L0-semantiek en componentcontracten
op `main`. De proof-of-concept staat buiten de productie-imports.
[Lean-experiment](../../tests/compaction/CompactionProof.lean)

## Publieke garantie

Compaction van een ready database is een logische identiteitstransitie.
Elke succesvolle `get k` na compaction geeft dezelfde waarde als ervoor,
tot de volgende mutatie. Bij een fout of verloren antwoord blijft diezelfde
database herstelbaar. Ook een reeds bevestigde maar nog niet geflushte
mutatie blijft behouden. Compaction introduceert geen onzekere mutatie.
Een gezonde reopen moet slagen vanaf iedere toegelaten fysieke uitkomst.
Bestaande leesfouten blijven fouten, bijvoorbeeld wanneer een vereiste
SSTable-probe of typed decode faalt.

De nuttige interne gelijkheid is sterker dan gelijkheid van `Database`.
De table overlay levert voor elke sleutel `none`, `some (.put v)` of
`some .delete`. Nieuwste treffer wint en `some .delete` stopt de zoeklus.
Pas de publieke lookup projecteert een tombstone op afwezigheid. Een
merge die `delete(k)` laat vallen kan een put uit een ongemoeid gelaten
oudere tabel zichtbaar maken. Een verkeerde plaatsing kan een nieuwere
put overschrijven. Beide gevallen staan als uitvoerbare Lean-voorbeelden
in de proef.
[L0-operaties](../../lean/Alvoki/Experiments/L0/Basic.lean) ·
[Clientcontract](../../lean/Alvoki/Experiments/L0/Client.lean) ·
[Lean-experiment](../../tests/compaction/CompactionProof.lean)

## Eerste beleid en alternatieven

Voer compaction expliciet en geserialiseerd uit onder de bestaande
engine-eigenaarschapgrens. Selecteer bij minstens twee tabellen de twee
nieuwste aangrenzende L0-tabellen uit de geïnstalleerde manifestversie.
Voor `[newer, older] ++ suffix` wordt het voorstel `[out] ++ suffix`,
met exact dezelfde `flushedThrough`. Prioriteit volgt de lijstpositie.
Een vers ID is een identiteit en draagt geen recency-informatie. Houd alle
winnende mutaties, inclusief tombstones. Laat memtable en WAL ongemoeid
tijdens de operatie. Bij nul of één tabel is de operatie een no-op.

| Mogelijkheid | Producent- en bewijscomplexiteit | Operationele afweging |
| --- | --- | --- |
| Twee nieuwste, materialiseren via de bestaande replay en TreeMap | Kleinste referentie. Hergebruikt bewezen sortering en lookup. Tijd circa O(N log U), geheugen O(U) voor U unieke sleutels. | Bruikbaar als testorakel. Grote invoer verhoogt geheugengebruik. |
| Twee nieuwste, streaming naar één output | Twee cursors en één prioriteitsregel. O(N) mergebeslissingen en constante merge-frontier. Readerprobes en writerbuffers komen erbij. | Aanbevolen eerste productiepad. Een herhaald gekozen paar kan grote outputs opnieuw schrijven. |
| Alle L0-tabellen naar één output | Eén manifestsplice, maar k cursors, rang bij gelijke sleutels en een lineaire selectie of heap. Grotere fout- en resourceoppervlakte. | Meer fan-in en vaak meer tijdelijk schijfgebruik. Eén output kan een formatlimiet bereiken. |
| Aangrenzend paar op willekeurige positie | Dezelfde merge. Plan moet de exacte prefix, het paar en de suffix vastleggen en de splice op zijn oorspronkelijke positie bewaren. | Later bruikbaar voor groottebeleid of de oudste twee. |
| Niet-aangrenzende overlapselectie of plaatsing in een volgend level | Heeft een bewijs nodig dat de gekozen runverplaatsing en range-overlap de prioriteit tegenover alle ongemoeid gelaten runs behouden. | Laat beleidskeuze, levelmetadata en meerdere outputs wachten op een stabiele compositie. |

`N` is het totale aantal inputrijen. De bestaande geïndexeerde `next` kan per
rij opnieuw leaf- en datapakketten lezen. O(N) mergebeslissingen is daarom
geen claim over I/O-volume. Hergebruik `next` eerst en meet een cache voor
een gevalideerd blok later. ALVSST05 begrenst ieder pakket, ook de root, op
16 MiB en begrenst de bestandsgrootte. Ondersteun een afgebroken build zonder
publicatie wanneer de output te groot blijkt. De eerste versie geeft
geen garantie dat een overgroot paar kan worden gecompacteerd. Dat is een
expliciete beperking van één output. Plan voor grootschalig gebruik een
gedocumenteerde selectiegrens of outputsplitsing. Vrije ruimte en een
geldige nieuwe ID blijven eveneens voorwaarden voor voltooiing.
[SSTable-capaciteit en reader](../../lean/Alvoki/Experiments/SSTable/README.md)

## Streamingproducent

Open de twee geselecteerde bestanden met hun onafhankelijke verwachte ID.
De descriptor blijft aan de immutable inode gebonden. Begin beide cursors
op nul. Houd per invoer één huidige rij of het bewezen einde bij. Vergelijk
de sleutels in dezelfde orde als de schrijver. Bij een kleinere kop emitteert
de producer die rij en verbruikt hij die kop. Bij gelijke sleutels emitteert
hij de nieuwere rij en verbruikt hij beide koppen. Bij één uitgeputte invoer
loopt de andere door. Meld EOF pas wanneer beide uitgeput zijn. Gebruik de
bestaande typed codecs met hun roundtrip- en orderegel. Een bytevergelijking
is equivalent als de gedeelde codec diezelfde orde draagt. De WAL-codering
is een afzonderlijke codec.

De cursorinvariant koppelt iedere kop en cursor aan het exacte nog
onverbruikte suffix van zijn geopende tabel. De al uitgegeven sleutels zijn
strikt stijgend en kleiner dan elke resterende kop. Voor elke uitgegeven
sleutel is precies de eerste mutatie in manifestvolgorde uitgegeven. Geen
uitgegeven sleutel komt in de rest terug. De som van de ongelezen en
gebufferde rijen daalt bij elke succesvolle uitvoerrij. Een succesvolle
volledige drain levert dus exact één rij per sleutel in de unie, in strikte
orde, inclusief winnende tombstones. Een succesvolle `next` levert de rij
op die index met opvolger, of EOF bij een uitgeputte cursor. Lees-, codec- en
buildfouten breken af met het bereikte cursor-, writer- en naambezit. Een
fout blijft een fout, ook bij het uitlezen van het oudere duplicaat. Er
volgt geen succesvol EOF of manifestvoorstel uit een gedeeltelijke stream.

De writer neemt de callback van de producent. De eindstelling moet de
werkelijk geconsumeerde stroom en het exacte EOF aan de bytes van de
originele gesyncte outputdescriptor koppelen. Een sorteerbewijs of
rijtelling alleen sluit een verkeerd geïnstalleerde waarde of een
stil afgebroken stream niet uit. Dezelfde grens laat een gematerialiseerde
of blok-gecachete producer toe zonder wijziging van het manifestbewijs.
[SSTable typed next](../../lean/Alvoki/Experiments/SSTable/Core.lean) ·
[Native writer en checked open](../../lean/Alvoki/Experiments/SSTable/Proofs/UnifiedNativeEndToEnd.lean) ·
[Foutpaden](../../lean/Alvoki/Experiments/SSTable/Proofs/UnifiedReadErrors.lean)

## Publicatie, onderbreking en herstel

De L0-coördinator houdt de geïnstalleerde versie en exclusieve
namespace-authoriteit vast van plan tot resultaat. Hij leent de
inputdescriptors aan de merge en blijft verantwoordelijk voor hun
sluiting. De writer bezit de nieuwe outputnaam en descriptor na geslaagde
exclusieve creatie. Hij draagt bewijs van de exacte gesyncte inode over.
Een succesvolle directorybarrière levert de duurzame koppeling
`output-ID → naam → inode → rows`. Pas dan mag de coördinator het
manifestvoorstel indienen. Houd de naam van iedere tabel uit beide versies
beschikbaar. Bij succesvolle publicatie installeert de engine de nieuwe
versie met dezelfde memtable. Een verloren reply vraagt om reopen.

| Bereikte grens | Toegelaten gevolgen en vervolg |
| --- | --- |
| Lezen, creëren, schrijven, flushen of file-fsync faalt of wordt onderbroken | Alleen oud manifest. Een tijdelijke of exclusief geopende output kan gedeeltelijk, volledig of afwezig zijn op reboot. Sluit verkregen resources. Verwijder op dit pad alleen een naam met bewezen eigenaarschap en onbereikbaarheid. |
| SSTable-directorysync faalt of wordt onderbroken | Alleen oud manifest. De naam kan al duurzaam zijn. Bewaar de bereikte toestand en publiceer op dit pad geen voorstel. |
| Manifest publish gestart, resultaat onzeker | Behoud catalogus voor oud én voorstel, ook bij fout rond rename of de directorybarrière. De live naam kan al nieuw zijn. Stop de betreffende sessie en gebruik de bestaande reopen-discipline. |
| Geslaagde publish met verloren reply | Nieuw is duurzaam en reopen haalt die versie terug. |
| Reopen faalt | Retourneer geen ready sessie. Als manifest-reopen al succesvol was, kan een latere WAL- of tabelfout de keuze niet terugdraaien. Neem het bereikte beeld mee naar de retry. |

De publicatie heeft twee verschillende directoryverplichtingen. De
SSTable-directory moet de naam van het nieuwe immutable bestand eerst
duurzaam maken. DurableBlob schrijft en synct zijn staging inode, vervangt
de actieve manifestnaam atomair en synct de parent van die naam. Houd die
volgorde ook bij één gedeelde directory aan. Processtop behoudt het bereikte
zichtbare beeld. Power loss kiest een gezamenlijk overlevend beeld van
bindings en inhoud. Na de eerste outputbarrière moet daarin iedere
tabelnaam die een toegelaten manifest kan selecteren duurzaam aan de juiste
inode gebonden blijven. Na rename en vóór de laatste barrière kan een
processtop de nieuwe manifestnaam laten zien terwijl een power loss nog
oud of nieuw mag kiezen. Manifest-reopen leest de actieve versie en zet
een directorybarrière vóór terugkeer. Een tweede reopen na stop of power
loss ziet daardoor dezelfde keuze, zolang er geen nieuwe publicatie is.

Voor beide manifestkeuzes construeert L0 een `Durable`-bewijs met
dezelfde geschiedenis, dezelfde flushed/pending-splitsing en dezelfde WAL.
De tabeloverlay dekt dezelfde `latest flushed`. Met `b = view.base`,
`t = view.tail` en `w = flushedThrough.toNat` geldt nog `b ≤ w ≤ t`.
Reopen laat precies de eerste `w - b` behouden batches vallen en decodeert
dezelfde pending mutaties. Bestaande WAL-retentie kan alleen posities
vrijgeven waarvoor de ingestelde en duurzaam geselecteerde watermark dat
toestaat. Deze operatie vraagt geen `discardThrough` aan en geeft geen
nieuwe retentierechten. Begin uit ready zodat er geen eerder onbesliste
append of flush met dit voorstel concurreert.

De geldende externe aannames omvatten dezelfde-descriptor flush/sync,
immutability, stabiele exclusieve namespace, intacte manifestkeuzes en
betrouwbare sync van beschikbare bytes en bindings. Een fout kan een
uitgevoerd effect rapporteren. Een later succesvolle fsync is volgens de
bestaande aannames geen reparatiebewijs voor bytes verloren bij eerdere
writeback. Een proces-kill-fixture test reached-state gedrag. De power-loss
garantie volgt uit het model onder de filesystempremissen.
[Manifestcontract](../../lean/Alvoki/Experiments/Manifest/README.md) ·
[DurableBlob](../../lean/Alvoki/Experiments/DurableBlob/README.md) ·
[Filesystempremissen](filesystem-assumptions.md)

## Reclamation en toekomstige versies

De eerste compaction doet zelf geen unlink van ingevoerde tabellen.
Ruimtegebruik kan daardoor stijgen. Een latere collector werkt onder
namespace-eigenaarschap en gebruikt de union van alle mogelijk
herstelbare en geïnstalleerde versies, live reader- of snapshotpins en
in-flight outputnamen als beschermde set. Tijdens onzekere publicatie
beschermt die zowel inputs als output. Na succesvolle settlement en
installatie mag een oude naam pas vrijgegeven worden wanneer geen
toekomstige open via een pin die naam nog kan gebruiken. Een open
descriptor houdt op Linux een inode vast, maar beschermt een toekomstige
pathname-open door een reader met een versiepin niet.

Een collector beschouwt uitsluitend herkenbare table artifacts bij een
volledige, foutgecontroleerde listing of aantoonbaar eigen kandidaten.
Een prefix van een mislukte listing levert geen complete inventaris.
Unlink met onzeker effect en een mislukte directorysync mogen hoogstens een
onbereikbare naam laten bestaan of terugbrengen. Voor bestendige
terugwinning van ruimte is een directorybarrière nodig. Vermijd ID-hergebruik
in deze mijlpaal en gebruik exclusieve creatie tegen achtergebleven namen.
Leid allocatiebevoegdheid en uitputting af van de aanvaarde L0-namespace.
Leid globale ID-freshness niet af van alleen een manifestmaximum na
reclamation.

Voor concurrent background maintenance kan een taak de inputs pinnen,
buiten de publicatielock bouwen en bij de commit de basisversie of een
bewezen compatibele splice opnieuw valideren. Zonder zo'n bewijs faalt
een stale voorstel zonder publicatie. Met versie-gebaseerde snapshots
houdt de snapshot zijn versie plus passende memtable/WAL-view vast. Voor
sequence-gebaseerde snapshots is per sleutel één mutatie onvoldoende.
De interne recordorde, zichtbaarheid per snapshot en voorwaarden voor
plaatsen of verwijderen van tombstones worden dan nieuwe contracten.
Stel levelmetadata, overlapselectie, automatische scheduling,
outputsplitsing, tombstone-eliminatie en snapshotrepresentatie uit.

## Stellingen en premissen

| Stelling | Consumptie en huidige producent |
| --- | --- |
| `drain_merge`: volledige healthy drain geeft ordered output en voor elke sleutel `lookupRows out k = (lookupRows newer k).or (lookupRows older k)`. Elke fout levert het bereikte state en geen publish-bevoegdheid. | De referentie heeft `mergeReference_ordered` en `mergeReference_lookup`. Typed `next`, `TypedTable.represents_of_bytes` en de fallible reader leveren cursor- en foutfeiten. Het streamingbewijs en diens callback-frame ontbreken. |
| `replace_span`: bij dezelfde prioriteit en een exacte merge behoudt replacement de overlay onder iedere prefix en suffix. | `overlay_replace` is bewezen voor de bestaande L0-overlay. De concrete manifestsplice van het nieuwste paar en de catalogusbindings staan in `publicationChoices`. |
| `output_ready`: succesvolle build plus directorybarrière geeft `Catalog.Created` voor exacte rows en bewaart alle bestaande bindings. Op fouten blijven bestaande bindings intact. | `buildFileWith_refines` en `buildFileWith_open_represents` leveren de file-sync en bytes/reader-keten. De producer van het directorybewijs, het eindpunt van de supplier op de werkelijke writerstate en de overdracht van naambezit moeten in de geaccepteerde L0-adapter worden aangesloten. |
| `compact_refines`: bij success blijft `Installed` gelden voor dezelfde geschiedenis. Ieder toegelaten offline beeld is `Durable` voor dezelfde geschiedenis. | Geconstrueerd voor beide keuzes op een aangeleverde gemeenschappelijke catalogus door `publicationChoices`. `install_compacted` behoudt de geïnstalleerde sessie met dezelfde memtable en geschiedenis. `flushPublicationChoices` is het bestaande compositiepatroon, met een andere watermarktransitie. Het argument voor de echte compactionschedule en fysieke catalogus/WAL-frame ontbreekt. |
| `recover_compacted`: healthy recovery installeert dezelfde logische database; fouten behouden de nog toegelaten keuzes op de bereikte toestand. | `merge_recovery` gebruikt `Retry.afterPublish` en `Durable.replay_pending`. `manifest_effect_recovery` haalt zijn selectie uit het bestaande DurableBlob-effectmodel en gebruikt de echte manifestcodec. `recover_refines`, `recover_progress`, `get_refines`, `Retry.narrows` en `LinuxEffects.reopenAgain` zijn herbruikbare vervolgstappen. Native compaction, SSTable-name- en WAL-persistentie onder een gezamenlijk crashbeeld blijven bewijsverplichtingen. |
| `collect_preserves`: iedere gekozen verwijdering behoudt alle views in de beschermde set, ook na een fout, stop of power loss. | Later los bewijzen. WAL `reopen_nativeRoot` en directorycollectie zijn voorbeelden voor foutdiscipline en bereikt beeld. SSTable-lifetimes hebben eigen autoriteit. |

[Gecheckt L0-refinement](../../lean/Alvoki/Experiments/L0/Refinement.lean) ·
[Retrykeuzes](../../lean/Alvoki/Experiments/L0/RecoveryChoices.lean) ·
[WAL-retentiebewijs](../../lean/Alvoki/Experiments/WAL/Segmented/Proofs/Retention.lean) ·
[Manifesttrace](../../lean/Alvoki/Experiments/Manifest/Proofs.lean) ·
[DurableBlob-effecten](../../lean/Alvoki/Experiments/DurableBlob/Proofs.lean)

## Gefaseerde uitvoering

1. Accepteer de native L0-baseline en pin de commit. Laat een onafhankelijke
   reviewer de voorgestelde producer/consumer-grens en het crashcontract
   toetsen. Controleer concreet hoe ready sessie, inputversie,
   tabelnaam/descriptor en reached state in de geaccepteerde API doorgegeven
   worden. Laat de L0-adapter de concrete authority dragen en houd
   verificatiegeschiedenis uit het runtimepad.
2. Bouw één verticale route via de echte typed reader en bestaande synced
   writer. Gebruik twee overlappende runs met een tombstone, één oudere
   ongemoeid gelaten tabel en resterende WAL-batches. Laat get, manifest en
   reopen hetzelfde producerbewijs consumeren. Voeg vroeg een vereiste
   `next`-fout ná een uitgegeven rij toe en controleer dat die fout vanaf de
   bereikte toestand doorloopt zonder voorstel. Gebruik de TreeMap-referentie
   als differentieel orakel.
3. Sluit directorybinding en manifestpublicatie aan onder de bestaande
   serializer. Oefen pre-/post-effect fouten rond outputsync, outputbarrière,
   rename en manifestbarrière. Oefen processtop, power-loss-keuzes, verloren
   reply en een reopen-fout na succesvolle manifestsettlement, gevolgd door
   twee heropens. Bewijs healthy progress voor representabele invoer onder
   gezonde primitives. Auditeer afzonderlijk model, native fixtures en
   correspondentie van dezelfde schedules met de primitive-effectbewijzen.
4. Voeg pas daarna reclamation toe met expliciete lifetime-authoriteit.
   Meet leesversterking, root- en buffergebruik en tijdelijke schijfruimte.
   Gebruik die resultaten om verdere selectie, outputsplitsing of
   blok-caching te kiezen voordat background workers of levels worden
   ingevoerd.

Draai vanuit de repository `bash scripts/check-compaction-experiment.sh`
voor kernelreplay en de axiom-policy. Met een extern geïnstalleerde
toolchain accepteert de runner `ALVOKI_TOOLCHAINS`. De proef gebruikt
Lean 4.36.0. Zij bewijst een referentiemerge, manifestsplice en
recoverycompositie binnen de bestaande L0- en DurableBlob-modellen.
Een native compactionpad, een streamingimplementatie en een collector
vallen buiten deze onderzoekswijziging.
