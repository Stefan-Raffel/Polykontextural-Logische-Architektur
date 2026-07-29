# Setzungsregister

Fuehrt jede Setzung des Korpus mit Klasse, Reichweite und Exit-Kriterium
beziehungsweise Begruendung, warum sie keines hat. Die Zweiklassigkeit steht in
`CLAUDE.md` §10; dieses Register schreibt sie nur auf.

Stand: Commit `26a65a3`, Branch `rev2`, 29. Juli 2026. Jede Zahl haengt am
Commit und an einer Route; die Routen stehen in §5.

**Bau- und Targetstatus gehoeren nicht hierher.** Welches Modul in welchem
Target liegt und was ein gruener Bau je Target zusichert, steht in
`docs/build-targets.md`. Welcher Definitionen-Begriff welchen Lean-Traeger hat,
steht in `docs/definition-ledger.md`. Dieses Register beantwortet eine dritte
Frage: wo im Korpus etwas gesetzt statt bewiesen ist.

---

## 0 — Was eine Setzung ist, und was hier steht

Eine Setzung ist ein Strukturdatum, das nicht bewiesen wird. Im Korpus tritt sie
in genau einer Form auf: als Strukturfeld vom Typ `True`. Ein solches Feld kann
in keinen Beweis eingehen — das ist das Schutzziel aus `CLAUDE.md` §10, und es
ist nicht durch die Zahl der Felder gefaehrdet, sondern durch ihre
Unauffaelligkeit. Darum werden sie hier gefuehrt.

Zwei Klassen, die nicht dasselbe sagen:

- **Platzhalter** — eine verschobene Beweisschuld. Braucht ein Exit-Kriterium:
  was muesste vorliegen, damit er faellt.
- **Konstitutiv** — kein Beweis-Soll. Braucht keine Exit-Bedingung, wohl aber
  eine Begruendung, warum sie keine hat.

Dazu kommt eine dritte Rubrik, die keine Setzung ist, aber hierher gehoert:
**gestrichene Deklarationen**, deren Aussage `True` war und deren Name Gehalt
behauptete. Sie sind keine Setzungen — eine Setzung markiert, ein Satz mit der
Aussage `True` behauptet. Genau darum wurden sie gestrichen und nicht
umklassiert. Sie stehen hier, damit die Streichung auffindbar bleibt.

| Rubrik | Zeilen | Zahl |
|---|---|---:|
| `True`-Felder im Aggregat | `S01`–`S32` | 32 |
| `True`-Feld ausserhalb des Aggregats | `S33` | 1 |
| gestrichene Saetze | `S34`–`S42` | 9 |
| gestrichene `def` | `S43`–`S48` | 6 |
| gestrichener Satz in `PathC` | `S49` | 1 |

Die IDs `S01`–`S32` folgen der alphabetischen Ordnung der vollen Lean-Namen.
Das ist keine Rangfolge, sondern eine reproduzierbare Vergaberegel: wer die
Messroute aus §5 laufen laesst, bekommt dieselbe Reihenfolge.

---

## 1 — `True`-Felder im Aggregat

Alle 32 liegen im Importbaum von `Reformulation` und werden vom AxiomGate
mitgezaehlt. Klasse und Exit stehen seit Commit `a66514f` auch im Feld-Doc
selbst; dieses Register und die Feld-Docs sind zwei Ansichten derselben Angabe,
und bei Widerspruch gilt der Feld-Doc, weil der Bau ihn traegt.

| ID | Traeger | Ort | Klasse | Exit-Kriterium |
|---|---|---|---|---|
| S01 | `F1.D2.ConsensusGeneral.HardConsensusOps.isHardLayer` | `F1/D2/ConsensusGeneral.lean` | Platzhalter | Der harte Layer wird durch seine Modaloperatoren charakterisiert statt markiert: `isHardLayer` faellt, sobald `HardConsensusOps` eine Bedingung an die Operatoren traegt, die ein weicher Layer verletzt. |
| S02 | `F1.D2.ConsensusGeneral.SoftConsensusOps.isSoftLayer` | `F1/D2/ConsensusGeneral.lean` | Platzhalter | Wie `S01`, mit vertauschten Rollen. Beide zusammen: eine Trennung, die an einem konkreten Paar scheitern kann. |
| S03 | `F1.D2.Ethereum.Checkpoint.isEpochBoundary` | `F1/D2/Ethereum.lean` | Platzhalter | `slotsPerEpoch` modellieren; dann ist die Bedingung `block.slot % slotsPerEpoch = 0` und beweisbar oder widerlegbar. |
| S04 | `F1.D2.Ethereum.GasperCompatibility.pullBackCompatibility` | `F1/D2/Ethereum.lean` | Platzhalter | Die Doppelfaserung `𝒯 → 𝒞 × 𝒪` als Datum, gegen das Pull-back-Vertraeglichkeit eine Gleichung ist (T11 IV). |
| S05 | `F1.D2.Hybrid.HybridConsensus.interLayerCompat` | `F1/D2/Hybrid.lean` | Platzhalter | Eine Vertraeglichkeit zwischen hartem und weichem Layer, die scheitern kann — der Gehalt, den `S42` behauptet hat, ohne ihn zu tragen. |
| S06 | `F1.D2.Rollups.DoubleValuation.RollupCompatibility.beckChevalleyHolds` | `F1/D2/Rollups/DoubleValuation.lean` | Platzhalter | Wie `S14`: das Zielfeld braucht eine 2-Iso. Solange es `True` ist, ist auch dieses Feld nicht fuellbar-mit-Widerstand. |
| S07 | `F1.D2.Rollups.RollupGeneral.Layer2Rollup.inheritedGenesis` | `F1/D2/Rollups/RollupGeneral.lean` | Platzhalter | Genesis-Vererbung als Gleichung ueber den Genesis-Hashes von Layer 1 und Layer 2 statt als Marke. |
| S08 | `F1.D5.IBC.CrossChainCompatibility.beckChevalleyHolds` | `F1/D5/IBC.lean` | Platzhalter | Wie `S14`. Lokales Material fuer eine echte Konstruktion: `Header` mit `height`/`blockHash` und `replayProtection`. |
| S09 | `F1.D5.MultiChainGeneral.Connection.isEstablished` | `F1/D5/MultiChainGeneral.lean` | Platzhalter | Den Verbindungs-Lebenszyklus modellieren; dann ist „etabliert" das Praedikat, dass der offene Zustand erreicht ist. |
| S10 | `F1.D5.MultiChainGeneral.MultiChain.bicategoryStructure` | `F1/D5/MultiChainGeneral.lean` | Platzhalter | Eine `Bicategory`-Instanz mit Chains als Objekten und Connections als 1-Zellen, gegen die das Feld eingeloest wird. |
| S11 | `F1.D5.Polkadot.PolkadotGeneral.Parachain.isIncluded` | `F1/D5/Polkadot/PolkadotGeneral.lean` | Platzhalter | Inklusion als Relation zur Relay-Chain statt als Marke — beweisbar aus derselben Struktur, die `polkadot_doubleValuation_asymmetric` schon benutzt. |
| S12 | `F1.D5.Polkadot.XCM.XCMBridge.isRelaySound` | `F1/D5/Polkadot/XCM.lean` | Platzhalter | Relay-Chain-Konsens modellieren und Soundness daraus ableiten, statt sie zu delegieren. |
| S13 | `F1.D5.Polkadot.XCM.XCMCompatibility.beckChevalleyHolds` | `F1/D5/Polkadot/XCM.lean` | Platzhalter | Wie `S14`. Lokales Material: `relayMediation`, beweisbar aus `XCMMessage.sameRelay`. |
| S14 | `F3a.DesignativeRestriction.beckChevalley` | `F3a/Endofunctor.lean` | Platzhalter | Das Feld traegt eine wirkliche 2-Iso statt `True` — der Schritt, den F3.e mit `ModalTwoCategoryWithPullbacks.pullBackCommute` vollzogen hat. **Schluesselzeile:** an diesem Feld haengen `S06`, `S08`, `S13` und die drei gestrichenen `def` `S44`, `S45`, `S48`. |
| S15 | `F3a.DoubleValuation.compatibility` | `F3a/DoubleValuation.lean` | Platzhalter | Eine 2-Zelle, die scheitern kann; die konkrete „Beck-Chevalley-verwandte" Form aus Klaerung 1 §IV.1. **Schluesselzeile:** an diesem Feld haengen die gestrichenen `def` `S43`, `S46`, `S47`. |
| S16 | `F3a.OuterBalance.isFunctorial` | `F3a/Endofunctor.lean` | Platzhalter | Die explizite Kolimes-Konstruktion ueber die Auslassungsmodulationen; ihre Funktorialitaet ist dann ein Beweis und kein Feld. |
| S17 | `F3a.Skeleton.isUnique` | `F3a/Endofunctor.lean` | Platzhalter | Eine Determinationsbedingung an `skeletonFun`, gegen die Eindeutigkeit diskriminieren kann. Leere Felder diskriminieren nicht — dieselbe Diagnose wie bei `beckChevalley_unique`. |
| S18 | `F3c.BeckChevalleyCompatibility.exists_compatibility` | `F3c/TwoCategory.lean` | Platzhalter | Die konstruktive Form: die 2-Iso selbst als Datum. |
| S19 | `F3d.Hypostatization.brokenVerschraenkung` | `F3d/Hypostasis.lean` | Platzhalter | Die zyklische Verschraenkung als Kompositionsbedingung ueber `IsSmooth`/`IsRough`, die bei Absolutsetzung einer Negation scheitert. Traegt zugleich das Exit von `S38`. |
| S20 | `F3d.ModalTwoCategoryWithNegations.modalKinshipDelta` | `F3d/Negations.lean` | Platzhalter | Die konkrete `NatTrans` zwischen ¬_δ und δ; die syntaktische Form liegt in `IsSmooth.modalCompanion_delta_*` bereits vor. |
| S21 | `F3d.ModalTwoCategoryWithNegations.modalKinshipOmega` | `F3d/Negations.lean` | Platzhalter | Wie `S20`, fuer ¬_ω und ω. |
| S22 | `F3d.ModalTwoCategoryWithNegations.modalKinshipTau` | `F3d/Negations.lean` | Platzhalter | Wie `S20`, fuer ¬_τ und τ. |
| S23 | `F3d.ModalTwoCategoryWithNegations.negTau_trivial_at_K1` | `F3d/Negations.lean` | Platzhalter | ¬_τ als `NatTrans`, damit „trivial an K1" die Gleichung mit der Identitaet ist und an anderen Konfigurationen scheitern kann. Traegt zugleich das Exit von `S39`. |
| S24 | `F3e.BeckChevalleyAxioms.modalCompatible` | `F3e/BeckChevalleyAxioms.lean` | Platzhalter | Vertraeglichkeit als Gleichung natuerlicher Transformationen je Modaloperator. Traegt zugleich das Exit von `S40`. |
| S25 | `F3e.BeckChevalleyAxioms.pentagon` | `F3e/BeckChevalleyAxioms.lean` | Platzhalter | Die Pentagon-Identitaet ausgeschrieben und bewiesen. Solange sie `True` ist, erfuellt sie jeder Isomorphismus — das ist der Grund, aus dem `beckChevalley_unique` in seiner Signatur nicht haltbar war. |
| S26 | `F3e.BeckChevalleyAxioms.triangle` | `F3e/BeckChevalleyAxioms.lean` | Platzhalter | Wie `S25`, fuer die Dreiecks-Identitaet. |
| S27 | `F3f.Stage.noAlgebraExtension` | `F3f/Stage.lean` | Platzhalter | Ein Nicht-Existenz-Satz: kein globaler Stapeloperator setzt die stufenlokalen Endenfunktoren kohaerent ueber die Stufen hinweg fort. Siehe §3 — die Zuordnung ist strittig und hier bewusst konservativ. |
| S28 | `Proemial.Discontextural.DiscontexturalStratification.discontextural_posited` | `Proemial/DiscontexturalStratification.lean` | **konstitutiv** | Kein Exit. Begruendung: Diskontexturalitaet ist intra-kontextural nicht beweisbar — ein Beweis waere ein Selbstwiderspruch. Das Feld markiert die Setzung, statt sie zu verbergen; ein Sorry an dieser Stelle waere ein Befund gegen die Form. In `CLAUDE.md` §10 namentlich gefuehrt. |
| S29 | `Proemial.ProemialBeckChevalleyVerschraenkung.naturality_C` | `Proemial/AlphaGamma.lean` | Platzhalter | Die konkrete Form der ψ*-Rueckzugs-Vertraeglichkeit auf der 𝒞-Achse; belegungsspezifisch (F1). |
| S30 | `Proemial.ProemialBeckChevalleyVerschraenkung.naturality_O` | `Proemial/AlphaGamma.lean` | Platzhalter | Wie `S29`, fuer die 𝒪-Achse. |
| S31 | `Proemial.Substantial.ProemialGammaMorphismSubstantial.bc_compat` | `Proemial/AlphaGammaSubstantial.lean` | Platzhalter | Aufloesung des B-2-Befunds: Architektur-Mismatch zwischen F3e-BC (Endofunktor) und F-3 (S ≠ K). Bis dahin ist die volle BC-Integration belegungsspezifisch. |
| S32 | `Proemial.Transjunction.CharacterizedPosit.contexturePartitionGenuine` | `Proemial/ContexturalTransjunction.lean` | **konstitutiv** | Kein Exit. Begruendung: die Echtheit der Kontextur-Partition ist der gesetzte Rand (Grenze 4), Daten-Charakter analog Beck-Chevalley. Der Kern derselben Struktur ist bewiesen (`not_S_internal`); die Grenze zwischen beiden ist die Pointe und kein Mangel. In `CLAUDE.md` §10 namentlich gefuehrt. |

30 Platzhalter, 2 konstitutiv. Die beiden konstitutiven sind `S28` und `S32`,
und sie tragen ihre Klasse, weil sie kein Beweis-Soll haben — nicht, weil eine
Zahl es vorschreibt. `CLAUDE.md` §10 nennt dieselben zwei; das ist ein Messwert
am Commit `284995b` und stimmt mit dieser Einordnung ueberein. Eine Obergrenze
ist er nicht: wer ein drittes Feld ohne Beweis-Soll findet, fuehrt es
konstitutiv und misst §10 neu.

---

## 2 — `True`-Feld ausserhalb des Aggregats

| ID | Traeger | Ort | Klasse | Reichweite | Begruendung |
|---|---|---|---|---|---|
| S33 | `Proemial.AsymmetricTransition.AsymmetricDiscontexturalTransition.contextureCrossing` | `Proemial/AsymmetricDiscontexturalTransition.lean` | **konstitutiv** | Target `Probes`, nicht im Aggregat | Kein Exit. Die Identifikation „Stufenwechsel = Kontexturwechsel" ist Definitionswahl, nicht Satz. Sie ist der Grund, aus dem die Datei standalone liegt (`CLAUDE.md` §10, Ablagekonvention): setzungstragend bedeutet standalone, bis ein Aggregat-Satz sie konsumiert. |

Genau ein Feld ausserhalb — die Turm-Linie traegt ihre Setzung an dieser einen
Stelle und hat sie nicht ueber mehrere Felder verteilt.

---

## 3 — Eine strittige Zuordnung, ausdruecklich

`S27` (`F3f.Stage.noAlgebraExtension`) liest sich der Sache nach **konstitutiv**:
das Verbot der Algebra-Lesart ist eine Architekturentscheidung (T1a V), kein
verschobener Beweis. Es steht hier gleichwohl als **Platzhalter**, und zwar aus
dem Grund, der eine Zeile tiefer steht: es gibt ein formulierbares und
beweisbares Exit-Kriterium. Eine konstitutive Setzung ist eine ohne Beweis-Soll;
wo ein Beweis-Soll benannt ist, liegt ein Platzhalter vor. Architektur und
Beweis schliessen einander nicht aus - eine Architekturentscheidung darf einen
Satz hinter sich haben.

Das dabei entstehende Exit-Kriterium ist kein Notbehelf: der Nicht-Existenz-Satz
ueber einen globalen Stapeloperator ist formulierbar und waere beweisbar.
Wer die Zuordnung umdrehen will, muss zeigen, dass das Exit-Kriterium nicht traegt.

---

## 4 — Gestrichene Deklarationen

Streichung am 29. Juli 2026, nach Entscheidung des Projektinhabers: fuenfzehn
Deklarationen mit Commit `4e5bbf7`, die sechzehnte (`S49`, in `PathC`) mit
Commit `997037f` beim Einfrieren des Zweiges. Ihr Name behauptete Gehalt, ihre
Aussage war `True`. Jede traegt am Ende ihres Moduls einen Memorial-Block mit
zitierter Signatur und Exit-Kriterium; die Spalte „Ort" nennt das Modul, in dem
er steht.

Warum ueberhaupt gestrichen und nicht als Setzung gefuehrt: ein Feld vom Typ
`True` markiert, ein Satz vom Typ `True` behauptet. Der Unterschied liegt nicht
im Typ, sondern im Namen und im Leseeindruck — `resDes_not_invertible` liest sich
als Nicht-Existenz-Ergebnis und war `trivial`.

### 4.1 Gestrichene Saetze

| ID | Traeger (gestrichen) | Ort des Memorial-Blocks | Was ein tragfaehiger Satz braeuchte |
|---|---|---|---|
| S34 | `F3a.resDes_functorial` (EA1) | `F3a/Endofunctor.lean` | Nichts war zu beweisen: `resDes` ist bereits ein Mathlib-Funktor. Gehalt haette Natuerlichkeit im Stufenindex — dazu muss `DesignativeRestriction` funktoriell ueber `Stage` indiziert sein. |
| S35 | `F3a.skeleton_unique` (EA2) | `F3a/Endofunctor.lean` | Siehe `S17`. Eindeutigkeit gegen ein leeres Feld ist nicht formulierbar. |
| S36 | `F3a.resDes_beckChevalley` (EA3) | `F3a/Endofunctor.lean` | Siehe `S14`. Der Satz las das Feld ab; das Feld ist `True`. |
| S37 | `F3a.resDes_not_invertible` (NEA1) | `F3a/Endofunctor.lean` | Ein Zeuge, keine Abwesenheit: ein konkretes Kategorienpaar samt Beweis, dass kein Funktor zurueck zur Identitaet komponiert. Beachte `CLAUDE.md` §5.2 — `¬ ∃ f` ist in diesem Korpus die falsche Form; tragfaehig ist Nicht-Erzeugbarkeit im Termklon. |
| S38 | `F3d.hypostatization_breaks_cyclic_verschraenkung` | `F3d/Hypostasis.lean` | Siehe `S19`. Die Verschraenkung muss scheitern koennen. |
| S39 | `F3d.EnM2_negTau_trivial_at_K1` | `F3d/Theorems.lean` | Siehe `S23`. Die Hypothese `k = .k1` war im gestrichenen Satz bereits ungenutzt — das deutlichste Zeichen, dass die Konfiguration nichts entschied. |
| S40 | `F3e.beckChevalley_modalCompat` | `F3e/Theorems.lean` | Siehe `S24`. Der Satz nahm sein Argument nicht einmal entgegen (`_`). |
| S41 | `F3g.continuing_not_in_stage_transition` | `F3g/Classification.lean` | Eine klassifizierende Funktion `StageTransitionWithB6Trace n → ClassIVSubtype`, die nie `continuing` liefert. Ueber Mengenzugehoerigkeit geht es nicht: `classIVSubtype (n+1)` enthaelt beide Subtypen. |
| S42 | `F1.D2.Ethereum.gasper_inter_layer_compatible` | `F1/D2/Ethereum.lean` | Eine Ableitung aus `noConflictingVotes`, das eine echte universelle Bedingung ist — etwa die Nicht-Umschliessung zweier Stimmen desselben Validators ueber eine Epochengrenze. Siehe auch `S05`. |

### 4.2 Gestrichene `def`

Alle sechs waren Verbindungsfunktionen nach `True`. Ihr gemeinsames
Exit-Kriterium ist dasselbe und steht bei `S14` und `S15`: **eine Funktion nach
`True` stellt keine Verbindung her, weil jeder Term jedes Typs auf `trivial`
abbildet.** Erst mit Inhalt im Zielfeld wird das Fuellen eine Konstruktion, die
scheitern kann.

| ID | Traeger (gestrichen) | Ort des Memorial-Blocks | Zielfeld |
|---|---|---|---|
| S43 | `F1.D2.Ethereum.GasperCompatibility.toDoubleValuationCompat` | `F1/D2/Ethereum.lean` | `S15` |
| S44 | `F1.D5.IBC.CrossChainCompatibility.toBeckChevalley` | `F1/D5/IBC.lean` | `S14` |
| S45 | `F1.D5.Polkadot.XCM.XCMCompatibility.toBeckChevalley` | `F1/D5/Polkadot/XCM.lean` | `S14` |
| S46 | `F1.D5.Polkadot.DoubleValuation.PolkadotDoubleValuation.toDoubleValuationCompat` | `F1/D5/Polkadot/DoubleValuation.lean` | `S15` |
| S47 | `F1.D2.Rollups.DoubleValuation.RollupDoubleValuation.toDoubleValuationCompat` | `F1/D2/Rollups/DoubleValuation.lean` | `S15` |
| S48 | `F1.D2.Rollups.DoubleValuation.RollupCompatibility.toBeckChevalley` | `F1/D2/Rollups/DoubleValuation.lean` | `S14` |

**Die Serien-Beobachtung.** Die Doc-Strings der sechs lasen sich als Reihe: jedes
der beiden Zielfelder wurde dreimal belegt, und die drei Belegungen unterscheiden
sich in ihrer strukturellen Form — bei `S15` symmetrisch (Ethereum, FFG-Lock
innerhalb einer Chain), raeumlich asymmetrisch (Polkadot, Relay-Inklusion
zwischen Chains), vertikal asymmetrisch (Rollups, Stufeniteration zwischen
Layer 1 und Layer 2); bei `S14` Light-Client-Pull-back (IBC),
Relay-Chain-Vermittlung (XCM), Stufenverifikations-Pull-back (Rollups).

Die Reihe ist eine wirkliche Beobachtung, und sie ist eine Beobachtung **ueber
die Modellierung, nicht ueber den Kalkuel**. Sie sagt, dass drei
Ingenieurmechanismen sichtbar verschiedener Gestalt sich je als Fuellung
derselben F3.a-Form ausdruecken liessen. Sie sagt nicht, dass die F3.a-Form in
einem tragfaehigen Sinn mehrfach erfuellbar ist — bei `True` als Feldtyp steht
Erfuellbarkeit nicht auf dem Spiel, und keine der drei Fuellungen haette
scheitern koennen. Die frueheren Wortlaute („multiply multi-belegbar, not only
doubly") behaupteten das Zweite aus einem Beleg fuer das Erste.

Der Absatz steht hier und im Memorial-Block von
`F1/D2/Rollups/DoubleValuation.lean` — an zwei Stellen, weil Register und Code
zwei Leserkreise haben, und an keiner dritten. Er wurde aus sechs Modulen
zusammengezogen, in denen er in Varianten stand.

### 4.3 Gestrichener Satz in `PathC`

| ID | Traeger (gestrichen) | Ort des Memorial-Blocks | Was ein tragfaehiger Satz braeuchte |
|---|---|---|---|
| S49 | `PathC.Classifying.Model.toPresheafFunctor_jt_continuous` | `PathC/Classifying/ClassifyingEquivalence.lean` | Die Aussage, die der eigene Doc-String schon nannte: `(Model.toFunctor M).IsContinuous (geometricTopology T) K`, aus `geometricCoverage.pullback` und `CoverPreserving`, bewiesen aus `M.satisfies`. Stetigkeit kann scheitern — das ist der Unterschied zu `True`. |

**Gestrichen am 29. Juli 2026, Commit `997037f`**, im selben Zug, der `PathC`
eingefroren hat. Die Zeile stand zuvor offen, weil `PathC` Gegenstand einer
eigenen Entscheidung war (Plan §12, Vorgang 2). Sie ging mit dem Einfrieren,
nicht danach: ein Zweig, den man einfriert, wird vorher aufgeraeumt.

Der Zweig ist seit demselben Tag eingefroren; die Streichung ist die letzte
Aenderung an ihm. Bedingungen fuer ein Auftauen: `docs/build-targets.md`,
Abschnitt `PathC`.

---

## 5 — Messrouten

Jede Zahl dieses Registers ist an `a66514f` gemessen. Die Routen, damit sie
nachgefahren werden koennen:

**R-1 — `True`-Felder.** Umgebungsabfrage ueber `env.constants`, gefiltert auf
Praefix `Reformulation`, ohne `Name.isInternalDetail`, Projektion nach
`env.getProjectionFnInfo?`, Schluss des Typs nach `forallTelescope` gleich
`True`. Ergebnis: 32 im Aggregat, 33 mit `AsymmetricDiscontexturalTransition`
importiert. **Nicht per `grep`** — und nicht ueber `forallTelescopeReducing`,
das `Set X = X → Prop` faelschlich als `Prop`-Feld zaehlt (`CLAUDE.md` §10).

**R-2 — Nicht-Projektionen mit Schluss `True`.** Dieselbe Route, Projektion
verneint. Ergebnis nach der Streichung: **0** (vorher 15). Das ist die
eigentliche Abnahme der Streichung: die Route reproduzierte vorher unabhaengig
genau die fuenfzehn Ziele, und sie meldet einen eingeschleusten
`theorem probe_x : True` sofort.

**R-3 — Konsumenten.** Fuer jede Konstante des Aggregats werden die benutzten
Konstanten aus Typ **und** Beweisterm gesammelt und gegen die Zielmenge
geprueft. Der Beweisterm wird per explizitem Muster geholt:

```lean
match ci with
| .thmInfo v => some v.value
| .defnInfo v => some v.value
| .opaqueInfo v => some v.value
| _ => none
```

**`ConstantInfo.value?` ist im Korpus nicht zu verwenden.** In Lean
`4.30.0-rc2` liefert es fuer `thmInfo` `none`; Beweisterme sind fuer eine Route
ueber `value?` unsichtbar, und „null Konsumenten" kommt dann auch dann heraus,
wenn es welche gibt. Gegengerechnet an `gasper_inter_layer_compatible`:
`value?.isSome = false`, Muster-Route sehend.

Ergebnis vor der Streichung: genau **ein** Konsument im gesamten Aggregat —
`S42` auf `S43`. Beide gestrichen, das Paar ging gemeinsam. Alle uebrigen
dreizehn Ziele und beide konstitutiven Felder: null.

**R-4 — Klassenangabe im Feld-Doc.** Ein Feld-Doc gibt eine Klasse an genau
dann, wenn es eines der Worte `Platzhalter`, `placeholder`, `konstitutiv`,
`constitutive` fuehrt, **schreibungsunabhaengig** gelesen. Ergebnis an
`a66514f`: 33 mit, 0 ohne.

Zur Schreibungsunabhaengigkeit: ohne sie zaehlt `S32` als unklassiert, weil sein
Doc `Konstitutives` gross schreibt. Das ist ein Falsch-Negativ, das eine
schreibungsabhaengige Route still erzeugt. Gegengerechnet in der anderen
Richtung: unter allen als klassiert gezaehlten Feldern nennt jedes seine eigene
Klasse, keines nur die eines anderen Feldes — kein Falsch-Positiv.

Diese Route loest zwei aeltere ab, die verschiedene Zahlen lieferten: 19
(`Phase1_Abschluss.md` §8.1) und 12 (Empirie-Befund). Sie widersprachen einander
nicht, sie massen mit verschiedenen Wortsaetzen ueber verschiedenen
Textbereichen. Fortzuschreiben ist ab jetzt allein R-4.

---

## 6 — Was dieses Register nicht leistet

- **Es prueft sich nicht selbst.** `docs/definition-ledger.md` hat mit R7 und R8
  einen Lint, der Tabelle und Referenzdatei gegeneinander haelt. Dieses Register
  hat das nicht: die Traegernamen sind Text und werden vom Bau nicht geprueft.
  Ein Traeger, der umbenannt wird, hinterlaesst hier eine tote Zeile. Der
  Anschluss an denselben Mechanismus — eine Referenzdatei mit `#register_feld`
  nach dem Muster von `#ledger_setzung` — ist der naechstliegende Ausbau und
  hier ausdruecklich als offen vermerkt.
- **Es entscheidet nichts.** Klasse und Exit sind Angaben, keine Beweise. Ob ein
  Exit-Kriterium das richtige ist, entscheidet der Zug, der es einloest.
- **Es sagt nichts ueber Bau und Targets.** Siehe `docs/build-targets.md`.
