# Correctie van het native acceptatieoordeel

De onafhankelijke correctnessreviewer rapporteerde dat PhaseMemory onbewoonbaar is. Voor deze publicatie is dat resultaat opnieuw afgeleid uit de definitie op de **exacte** auditcommit. De meegeleverde Lean-proef importeert de echte interface en bewijst `(heap : PhaseMemory) → False`. Lean 4.36.0, leanchecker en de transitive-axiomcontrole van de repository accepteren de proef. Het is een zelfstandige reproductie; de broncode van de reviewer is hiervoor niet nodig. De definitie is tussen `335bbff0` en de bekeken integratiestand `13a655ea` gelijk. [Controleerbare proef](../../../tests/architecture-audit/PhaseMemory.lean) · [Interface](../../../lean/Alvoki/Experiments/WAL/Segmented/Native.lean#L494)

## Waar de tegenspraak ontstaat

Neem W = Void IO.RealWorld. Lean geeft Nonempty W. Kies één startwereld en één vaste IO.Ref met als elementtype W → Bool. Voor elke wereld t is observe(t) de functie die get op die ref in t retourneert. De wet set garandeert voor **iedere** functie f dat diezelfde ref f bevat in de wereld na set. De wet read geeft daar observe(t) = f. Daarmee zouden alle Bool-predicaten op W vanuit W uitleesbaar zijn. Kies nu f(t) = !observe(t)(t). Evalueren van de verkregen gelijkheid op de wereld na die set geeft een Bool die zijn eigen negatie is.

Dit gebruikt uitsluitend de set- en read-wetten van de interface. De ref is verkregen uit de waardeprojectie van mkRef; er is geen beroep op een allocatorwet, gedeelde alias, ongeldige byte, crash, simultane mutatie of native uitvoering. De tegenspraak vereist evenmin dat W een singleton is. Een lock, extra framewet of betere bind-tactiek verandert deze afleiding niet.

## Gevolgen per soort bewijs

| Claim | Gevolg op deze pin |
|---|---|
| WithOpenReads.withOpen, NativeFlush.withOpen, MutationAllCuts.interrupted/committed en gezonde routes zoals NativeFlush.healthyRead met een heap-premisse | Er bestaat geen instantie van hun gezamenlijk vereiste input. De conditionele stellingen blijven Lean-stellingen, maar leveren nul native uitvoeringen als getuige. Ook positieve syscallrapporten kunnen geen heap leveren. |
| Native open/registration/append-authority die PhaseMemory direct of via een record gebruikt | De stap van kernel-gecheckte compositie naar een native guarantee is open. Traceer aliases zoals WithOpenReads.Heap en velden van producers. Een afleiding van Registered uit een onmogelijke heap kan een volgende consumer niet legitimeren. |
| Zuivere modelbewijzen, exacte executable schedule-equalities en lokale cut-inducties zonder zo'n premise | De tegenproef weerlegt deze stellingen niet. Controleer hun eigen kwantoren en de premissen van de concrete toepassing. Specifiek blijft ChunkPrefix.remaining gevoelig voor een verkeerde uitgelezen primitive. |
| Werkelijke Linux-foutfixture en exacte writertransportstelling | De fixture voert de native code uit zonder PhaseMemory. De transportstelling gebruikt effect_bind en BuilderRelation, zonder PhaseMemory. Beide bevindingen blijven rechtstreeks reproduceerbaar. Voor een bredere consumer met andere heappremissen is een afzonderlijke beoordeling nodig. |

Een groene kernel- of axiomacheck controleert de afleiding van het type, inclusief een implicatie met onmogelijke antecedent. Dit is een fout in de specificatie van de omgeving. Dezelfde diagnose volgt niet automatisch voor bijvoorbeeld ChildMemory.cursor: dat contract spreekt over concrete child-fasen en rollen. Daar moet juist worden nagegaan of een productiewaardige Owned-toestand samen met de primitieve rapporten bereikbaar is. Een instantie met overal lege ownership-predicaten volstaat ook niet.

## Kleinste zinvolle herstelproef

1. Kies de twee echte celrollen bij segmented open, de phase-cell en de active-child-slot. Beschrijf per rol precies de toegestane eerste waarde en de overdrachten door install, borrow, poison en close. Verwijder de universele set/read-belofte voor willekeurige Lean-typen uit het consumerpad. Alleen het woord “polymorf” uit de definitie halen bewijst nog geen realiseerbaarheid.
2. Bouw een kleine interpreter met een expliciete, getypeerde toestand en bereikbare uitkomsten. Eis een **geconstrueerde** legale initiële toestand, aantoonbare acquire/install/read/swap en een framerelatie op de andere cel. Laat de publieksconsumer na een mislukte overdracht precies de resterende slot sluiten. Een onafhankelijk ghostregister moet via dezelfde overgangen bewegen als de uitvoering.
3. Houd de stap naar native afzonderlijk controleerbaar. Leg per werkelijk uitgegeven mkRef/get/set/swap vast welke handle de producer levert en op welke bereikte toestand het lokale rapport geldt. Een witness voor een modelschedule bewijst het gedrag van Lean-runtimeprimitieven nog niet. Leg een eventuele resterende FFI- of operationele aanname precies vast en toets specifiek identiteitsverwisseling en cleanup na fout.
4. Heracceptatie vereist één positieve native route van geselecteerde open tot tweede append op dezelfde registratie, en één fout-/retryroute vanaf het werkelijk overblijvende disk- en slotbezit. Laat het bewijs een opzettelijke verkeerde child weigeren. Breng daarna pas public mutation, flush en healthy-read terug onder de nieuwe grens.

Begin met deze ene producent en zijn consumer. De bestaande lokale postcondities, erase, omgekeerde cutclassificatie en survivorwetten kunnen eromheen blijven staan. Een algemene heap voor alle IO.Ref-typen of een nieuwe globale WP-infrastructuur vergroot hier juist het deel waarvan realiseerbaarheid moet worden aangetoond.

## Reproductie

Gebruik de Lean-toolchain op PATH in een checkout van de rapportbranch (de engine-tree is die van de pin). Het gegenereerde object hoort in een tijdelijke directory.

```bash
cd lean
lake build +Alvoki.Experiments.WAL.Segmented.Native +Alvoki.Checks.Audit.AxiomPolicy
out=$(mktemp -d)
lake env lean --root=../tests/architecture-audit -o "$out/PhaseMemory.olean" ../tests/architecture-audit/PhaseMemory.lean
LEAN_PATH="$out:$PWD/.lake/build/lib/lean" leanchecker PhaseMemory
```
