# Reformulation - Polykontexturale Logik in Lean 4

###### *English introduction*

This repository contains a formal reformulation of Gotthard Guenther's polycontextural
logic in Lean 4 with Mathlib. It separates, machine-checkably, what is proved from what is
named, interpreted or posited, and it carries a counting route for every figure it states.

The project works with one definition. The German wording below is the binding one; this is
a translation of it:

> A structure is **formally operative polycontextural** if it carries several local
> contextures - regions closed under the admitted signature, which may overlap - and if
> there is an operation on it that acts on each of these contextures like one of the
> classical connectives and is nonetheless not generable from the intra-contextural term
> calculus.
>
> **Formally operative** means: this non-generability is not asserted but machine-checked
> as a theorem.

This is narrower than Guenther's world-picture notion of polycontexturality, which is not
implemented and is carried as open.

- Working paper, edition Rev7, in English: `docs/en.html` (Part A the shape, Part B the apparatus)
- Concept-to-carrier assignment, compiler-checked: `docs/definition-ledger.md`
- What a green build assures, per target: `docs/build-targets.md`
- Current figures with their counting routes: the German section below

Contributions are not accepted at present and issues are switched off; the reporting
channel is named at the end of this file.

---

Dieses Repository arbeitet mit einer Projektdefinition, und sie steht vorneweg:

> Eine Struktur ist **formal-operativ polykontextural**, wenn sie mehrere lokale
> Kontexturen traegt - unter der zugelassenen Signatur abgeschlossene Bereiche, die
> einander ueberlappen duerfen - und wenn es auf ihr eine Operation gibt, die auf jeder
> dieser Kontexturen wie eine der klassischen Verknuepfungen wirkt und dennoch aus dem
> intra-kontexturellen Termkalkuel nicht erzeugbar ist.
>
> **Formal-operativ** heisst: diese Nicht-Erzeugbarkeit ist nicht behauptet, sondern als
> Theorem maschinell geprueft.

Als Arbeitsformel:

```text
Kontexturpluralitaet mit Ueberlappung
lokale Klassizitaet
maschinell gepruefte Nicht-Erzeugbarkeit
```

Diese Definition ist enger als Guenthers weltbildhafter Begriff der Poly-Kontexturalitaet
und staerker als blosse Mehrwertigkeit oder Rollenpluralitaet. Alles Weitere in diesem README
ist an ihr zu messen.

Formale Begleitung des Projekts zur Reformulierung der polykontexturalen Logik
Gotthard Guenthers. Der Code ist kein Beweis der Theorie, sondern ein Pruefwerkzeug:
er trennt, was aus klassischen Mitteln erzeugbar ist, von dem, was es nicht ist -
und macht die Grenze zwischen Beweis, Setzung und Deutung maschinell nachpruefbar.

Lean `4.30.0-rc2`, Mathlib. Bau mit `lake build`.

**Arbeitspapier zur Fassung PKL Rev7** (deutsch und englisch, zwei Teile in einem Dokument,
acht Figuren und Zaehlrouten): <https://stefan-raffel.github.io/Polykontextural-Logische-Architektur/> -
und im Bestand unter `docs/de.html` und `docs/en.html`.

Vorgeschichte, weil sie datiert ist und nicht geloescht wird: bis zur Umstellung auf
oeffentlich lieferte die frueher hier genannte Adresse
<https://stefan-raffel.github.io/PKLrev1/> ohne Anmeldung HTTP 404 - gemessen am
29. Juli 2026, wie es bei privatem Repositorium zu erwarten ist. Seit dem 1. August 2026
loest <https://stefan-raffel.github.io/Polykontextural-Logische-Architektur/> auf; die
alte Adresse loest nicht auf (gemessen, HTTP 404) - Pages folgt der Umbenennung nicht.

---

## Was hat man davon?

Drei Saetze fuer den eiligen Leser, in der Reihenfolge Entwurf, Pruefung, Grenze.

**Die Entwurfsregel.** Wer eine Stufenskala so bauen will, dass jede gemischte Politik eine
eigene, nicht wegkompilierbare Vermittlungsinstanz erzwingt, braucht **mindestens vier
Stufen**: ab vier ist jede echt gemischte, lokal klassische Politik unkomponierbar
(`GeneralCloneBound.locally_classical_in_clone_iff`), darunter nicht - bei drei Stufen ist
die Haelfte der Mischungen sehr wohl aus lokalen Pruefern zusammensetzbar
(`NonUniformCloneBound.four_of_eight_generatable`).

**Und die zweite Bedingung ist die schwierigere.** *Lokal klassisch* heisst: die Politik
wirkt auf **jedem** Stufenpaar wie das Minimum oder wie das Maximum - auch auf den nicht
benachbarten. Bei vier Stufen sind das **sechs** Paare, nicht drei (allgemein `m(m-1)/2`).
Genau hier bricht der naheliegende Entwurf: eine Eskalationsregel bei Konflikt der
Randstufen - *gesperrt und privilegiert treffen zusammen, also zur Pruefung* - ist auf
diesem Paar weder das Minimum noch das Maximum, und der Satz greift nicht mehr. Dass
gerade der durchdachte Entwurf die Voraussetzung verlaesst, ist die nuetzlichste Auskunft
dieses Absatzes.

**Das Pruefkriterium.** Ist die Voraussetzung erfuellt, so ist eine unkomponierbare Politik
an ihrer Wertetafel erkennbar: es gibt **zwei Stufenpaare**, auf denen sie entgegengesetzt
wirkt - auf dem einen wie das Maximum, auf dem anderen wie das Minimum
(`PairwiseMixture.not_in_clone_pair_mixture`). Der Satz garantiert zwei Paare; er
garantiert nicht, dass sie benachbart oder disjunkt sind. Und die Schranke haelt auch dann,
wenn man **fest verdrahtete Pruefer** als Bausteine hinzunimmt - den Allowlist-Eintrag, die
Ausnahme fuer ein einzelnes Werkzeug (`PolicyCheck.freigabe_nicht_erzeugbar_konstanten`).

**Die Grenze.** Vorausgesetzt ist eine **lineare** Stufenskala. Mehrere Rollen, mehrere
Perspektiven, mehrere Agenten genuegen nicht, und auf nicht-linearen Verbaenden faellt die
Charakterisierung nachweislich. Und was bewiesen ist, ist nicht mehr als das - im Wortlaut
der Modulkoepfe: *keine Sicherheits-, Rechts-, Wahrheits- oder Retrievalgarantie. Bewiesen
ist, was aus lokalen, kontextur-blinden Pruefern nicht zusammensetzbar ist.*

Eine Wertetafel zum Ansehen steht auf der Projektseite, im Abschnitt *Woran man es sieht*.

---

## Was implementiert ist, und was nicht

Dieses Repository implementiert **nicht** die volle weltbildhafte Poly-Kontexturalitaet aus
§6 der Definitionen-Fassung: das System sich unendlich erweiternder Kontexturen mit
wachsendem strukturellem Reichtum. Implementiert ist die formal-operative Fassung, die oben
steht - und nur sie.

**Der Name PKL bezeichnet den formalisierten Architekturkern und seine
Reduzierbarkeitsbrueche, nicht den abgeschlossenen Beweis der gesamten philosophischen
Theorie.**

Welcher Begriff welchen Lean-Traeger hat, welchen Status er traegt und wo seine Grenze
liegt, fuehrt `docs/definition-ledger.md` fuer alle neunzehn Paragraphen der
Definitionen-Fassung - einschliesslich der Zeilen, die offen sind und es bleiben.

---

## Stand

| Kennzahl | Wert |
|---|---:|
| geprueft (AxiomGate) | 3622 Konstanten |
| Axiom-Wachen | 638 ueber 91 Dateien |
| Saetze gesamt | 912 |
| Build-Jobs | 1326 |
| ausgewiesene Luecken | 0 (Whitelist leer) |

Kennzahlen gezaehlt am gruenen Build. **Erzeugt von `./kennzahlen.sh --bau`** — das Skript
gibt jede Zahl mit ihrer Route aus und prueft Gleichungen zwischen ihnen mit; faellt eine, sind die
Werte nicht zu verwenden. Von Hand abgeschriebene Zaehlkommandos gehoeren nicht mehr in
Dokumente (`CLAUDE.md` §13).

Was das AxiomGate zusichert, und was nicht. Das zertifizierte Aggregat zieht kein
`sorryAx`, die Whitelist ist leer, und jede neue Luecke bricht den Bau. Diese Zusicherung
gilt fuer das Aggregat und fuer keinen anderen Bereich. Der Zweig `PathC` ist eingefroren,
liegt ausserhalb der Default-Targets und traegt offene Stellen; ein Modul darin uebersetzt
nicht. Wer im Baum nach `sorry` sucht, findet drei verschiedene Zahlen, und jede beantwortet
eine andere Frage: 158 rohe Treffer ueber den ganzen verfolgten Bestand, 114 in den
Lean-Quellen, 27 betroffene Deklarationen. Die dritte ist die tragende; was ein gruener
Bau je Target zusichert, steht in `docs/build-targets.md`.

Die erste Zahl zaehlt sich selbst mit: bis zur dritten Fassung standen je drei ihrer Treffer
in `docs/de.html` und `docs/en.html`, weil das Arbeitspapier den Wortlaut dieser Suche zitierte;
seit der vierten stehen sie in `docs/rev3/`, weil die vierte Fassung die Marke benennt statt sie
zu zitieren. Am Stand
`e5ef3d7` waren es 123, mit der deutschen Fassung Rev2 126, mit der englischen 129, und mit
dem Absatz zu dieser Zahl in `CLAUDE.md` §3 dann 130 - der Absatz nennt den Suchbegriff mit
Bindestrich, und ein Bindestrich ist eine Wortgrenze. Diese drei Zuege liessen die zweite
und die dritte Zahl unberuehrt, weil keiner von ihnen eine `.lean`-Datei anfasste.

Seither bewegen Bauzuege beide Zahlen, und jeder nennt seine Rechnung je Datei. Der
M3-Zug: 130 -> 131 und 95 -> 96, ein neues Vorkommen im Dateikopf von
`Reformulation/Proemial/M3CloneWitness.lean`. Der Morphogramm-Zug: 131 -> 132 und
96 -> 97, ein neues Vorkommen im Dateikopf von
`Reformulation/Kenogram/Fillability.lean`. Beide Male traegt die Ablage-Zeile den
Suchbegriff mit angehaengtem Bindestrich - und ein Bindestrich ist eine Wortgrenze.
Sonst aendert keiner der beiden Zuege an einer Datei ein Vorkommen. Die dritte Zahl
bleibt 27: keine der neuen Dateien traegt eine offene Stelle.

Die Papierausgabe Rev3: 132 -> 138. Die Rechnung je Datei: die beiden laufenden Fassungen
`docs/de.html` und `docs/en.html` tragen den Begriff unveraendert je dreimal, und die
Archivierung der Rev2-Fassungen unter `docs/rev2/de.html` und `docs/rev2/en.html` bringt
dieselben zweimal drei Vorkommen ein zweites Mal in den verfolgten Bestand - 6 = 132 -> 138.
Die zweite und die dritte Zahl bleiben unberuehrt, weil der Zug keine `.lean`-Datei
anfasst. Gemessen ist die Zahl NACH dem Verfolgen der neuen Dateien: davor liefert
dieselbe Route den unveraenderten Vorwert, und ein unbewegter Wert sieht aus wie eine
gute Nachricht.

Der Fallstrick-13-Zug: 138 -> 140, und die zwei Schritte gehoeren beide dazu. Die
Rechnung je Datei: `CLAUDE.md` §8 2 -> 3, weil der neue Eintrag die `sorry`-Zahl als
Vergleichsfall nennt; und **dieser Absatz selbst** 1 -> 2, weil er den Begriff ein
zweites Mal nennt, um die Bewegung zu erklaeren. Sonst keine Datei bewegt. Die zweite
und die dritte Zahl bleiben unberuehrt, weil der Zug keine `.lean`-Datei anfasst.

Die Papierausgabe Rev4: 140 -> 140, und der Stillstand ist eine Rechnung und kein Ausbleiben.

Der Klammer-Zug: 142 -> 144 und 99 -> 101, je ein neues Vorkommen in den Dateikoepfen
von `Reformulation/Kenogram/Descent.lean` und `Reformulation/Proemial/RetractionBracket.lean`,
beide in der Zusicherung, dass die Datei keine offene Stelle traegt. Sonst keine Datei
bewegt; die dritte Zahl bleibt 27. Gemessen NACH dem Verfolgen.

Der Ordnungswechsel-Zug: 141 -> 142 und 98 -> 99, ein neues Vorkommen im Dateikopf von
`Reformulation/Proemial/ArrowAscent.lean`, in der Zusicherung, dass die Datei keine offene
Stelle traegt. Sonst keine Datei bewegt; die dritte Zahl bleibt 27. Gemessen NACH dem
Verfolgen.

Der Stellen-Tausch-Zug: 140 -> 141 und 97 -> 98. Die Rechnung je Datei: ein neues Vorkommen
im Dateikopf von `Reformulation/Kenogram/PlaceSwap.lean`, in der Zusicherung, dass die Datei
keine offene Stelle traegt. Sonst keine Datei bewegt. Die dritte Zahl bleibt 27: die neue
Datei traegt keine offene Stelle - was der Satz, der die Zahl bewegt, gerade sagt. Gemessen
NACH dem Verfolgen der Datei; davor lieferte dieselbe Route den unveraenderten Vorwert.
Je Datei: die Archivierung der Rev3-Fassungen unter `docs/rev3/de.html` und `docs/rev3/en.html`
bringt zweimal drei Vorkommen neu in den verfolgten Bestand (+6); die beiden laufenden Fassungen
verlieren dieselben zweimal drei (-6), weil die vierte Fassung die Marke benennt statt ihren
Wortlaut zu zitieren. Die zweite und die dritte Zahl bleiben unberuehrt, weil der Zug keine
`.lean`-Datei anfasst. Gemessen ist die Zahl NACH dem Verfolgen der neuen Dateien.

**Die Nachfuehrung einer selbstzaehlenden Zahl bewegt sie ein zweites Mal.** Der Commit
`23104c9` traegt darum an dieser Stelle 139 und war damit an seinem eigenen Stand schon
falsch: gemessen waren 140, weil die erklaerende Zeile mitzaehlt. Das Einsetzen der
**Ziffer** ist ein Fixpunkt, das Schreiben des **Satzes** ist es nicht - und wer eine
solche Zahl nachfuehrt, misst darum NACH dem Schreiben und nicht davor.

Die Route ist genau anzugeben, weil zwei nahe Routen verschiedene Zahlen liefern: gezaehlt
werden **Wortvorkommen** (140 / 97), nicht Zeilen mit mindestens einem Vorkommen (137 / 94).
Die Differenz sind zwei Zeilen in `Reformulation/PathC/Classifying/ModelFunctor.lean` und
eine in `Reformulation/F3f.lean`, die den Begriff zweimal tragen.

Jede Zahl laeuft ueber einen Bereich, und es ist nicht fuer alle derselbe. Darum steht er
dabei:

| Kennzahl | Bereich, ueber den sie laeuft |
|---|---|
| geprueft (AxiomGate) | Konstanten aus dem Importbaum von `Reformulation`, namensgefiltert auf `Reformulation.*` — nicht der Dateibaum |
| Axiom-Wachen | `Reformulation/` **und** `Foreign/` |
| Saetze gesamt | `Reformulation/` **allein**; Route seit dem Satzrouten-Zug geweitet, siehe `CLAUDE.md` §3 |
| Build-Jobs | die Default-Targets (`Reformulation`, `AxiomGate`, `DefinitionLedger`, `Probes`, `F1Coalgebraic`); `Diagnostics`, `MathlibExtensions`, `PreC`, `PathC` und `ForeignPeresMermin` laufen nur auf eigenen Ruf — siehe `docs/build-targets.md` |
| Quellbestand (Dateien) | `Reformulation/` und `Foreign/` |

Die Bereiche werden **benannt, nicht vereinheitlicht**: sie unterscheiden sich, weil die
Zahlen verschiedene Fragen beantworten. Was sie gemeinsam haben, ist der Commit.

---

## Struktur

**Dateien** zaehlt die Dateien *im Verzeichnis*, ohne das gleichnamige Sammelmodul daneben
(`Reformulation/Proemial.lean`, `F1.lean`, `PreC.lean`); jene tragen null Saetze. Ohne dieses
Kriterium hat die Spalte zwei Routen mit zwei Ergebnissen.

| Bereich | Dateien | Saetze | Gegenstand |
|---|---:|---:|---|
| `Proemial/` | 72 | 535 | Klon-Schranken und ihre Anwendungen · Stufenaufstieg und Paritaet · Zeit- und Stellen-Reihe · Transjunktion und ihre Setzung · die α+γ-Form · Kontextur-Zeugnis · Sonden |
| `PathC/` | 18 | 102 | Weg C - iterative Doppelbeschreibung |
| `Kenogram/` | 16 | 175 | Kenogrammatik: RGS, Normalform, Operationssemantik, Musterrelation, Besetzbarkeit, Wertvorrat, Stellen-Tausch, Abstieg, gemeinsame Abgeschlossenheit, Belegung zweier Stellen, Stufenschranke der Paare, Verkettung unter Identifikation, Zahl der Mengenpartitionen, Kanonisierung und Umkehrung |
| `F1/` | 20 | 20 | Belegungen, Faserungen, Cross-Chain-Anschluss |
| `F3a`-`F3g/` | 38 | 63 | Stufen, Modaloperatoren, Uebergangsklassen |
| `PreC/`, `Diagnostics/`, `MathlibExtensions/` | 16 | 17 | Vorbereitung, Messung, Zusatzlemmata |
| `Foreign/` | 1 | 10 | fremd gestellter Fall (Peres-Mermin) |

**Die Summe dieser Tafel ist groesser als die Gesamtzahl oben**, und das ist kein
Widerspruch, sondern der Bereich: die 912 laufen ueber `Reformulation/` allein, die Tafel
weist `Foreign/` mit seinen 10 Saetzen eigens aus; 912 + 10 = 922 ist die Tafelsumme. Der
fremd gestellte Fall liegt ausserhalb des Aggregats und wird darum in der Gesamtzahl nicht
mitgezaehlt.

Zwei Module tragen die schaerfsten Aussagen des Korpus:

* **`Proemial/TransjunctionCloneBound.lean`** - eine konkrete Transjunktion auf `Fin 3`
  liegt nicht im Klon der intra-kontexturalen Junktoren `{min, max, neg}`. Die Schranke
  laeuft ueber die Elementarkontextur `{0,2}` als Invariante; die Operation verlaesst sie.
* **`Proemial/NonUniformCloneBound.lean`** - ein zweiter Zeuge, der **keine** Kontextur
  verlaesst: er erhaelt alle drei, wirkt auf jeder klassisch, und liegt trotzdem nicht im
  Klon, weil er in verschiedenen Kontexturen verschiedene klassische Operationen waehlt.
  Dazu die vollstaendige Klassifikation: von den acht Wahlmustern sind genau vier
  erzeugbar und genau vier nicht.

---

## AxiomGate

`Reformulation/AxiomGate.lean` prueft beim Bau das gesamte Aggregat auf `sorryAx` und
bricht bei jeder Luecke. Seit der Whitelist-Aufloesung (Commit `c576b57`) ist die
**Whitelist leer**: das Aggregat zieht **kein** `sorryAx`, jede `sorryAx`-Konstante
ist ein Verstoss. Die vier vormaligen Klasse-D-Luecken sind:

* geschlossen -- `F3e.beckChevalleyFromData` (und das erbende `beckChevalley_exists`):
  die Beck-Chevalley-2-Iso ist jetzt das Strukturdatum
  `ModalTwoCategoryWithPullbacks.pullBackCommute`, direkt gelesen;
* gestrichen -- `F3e.beckChevalley_unique` (uneindeutig gegen die `True`-Axiome) und
  `Proemial.belegung_specialization_cognitive` (ueber alle Belegungen quantifiziert,
  Zielhom ggf. leer); in ihrer Signatur nicht haltbar, Memorial-Vermerke im Code.

Zusaetzlich frieren 568 `#guard_msgs`-Wachen die gemessenen Axiom-Profile ein: aendert
ein Satz sein Profil, bricht der Bau. `Classical.choice` ist auf wenige Dateien begrenzt
und dort ausgewiesen.

Zu lesen mit einer Einschraenkung: von den 568 geschriebenen Wachen erzwingt `lake build`
**558** (in 75 Dateien). Die uebrigen 10 stehen in `Foreign/PeresMermin.lean`, das ueber
`lake build ForeignPeresMermin` laeuft, aber nicht ueber den Default-Bau. Der fremd
gestellte Fall liegt ausserhalb des Aggregats; seine Wachen sind geschrieben und pruefbar,
nur nicht vom Default-Bau erzwungen. Das gehoert ausdruecklich dorthin.

Bis zum Buildabdeckungs-Zug C2 waren es 23 unerzwungene: dreizehn davon standen in drei
Modulen, die von keinem Target erfasst wurden und darum ueberhaupt nicht liefen
(`Proemial/AsymmetricDiscontexturality.lean` 7, `Proemial/TowerAsymmetryProbe.lean` 4,
`Proemial/AsymmetricDiscontexturalTransition.lean` 2). Seit C2 liegen sie im Target
`Probes` und werden bei jedem Bau ausgefuehrt; beim Anschalten hielt jede von ihnen.

568 ist die Zahl der geschriebenen Wachen - Route `grep -rE '#guard_msgs.*in #print axioms'`
ueber `Reformulation/` und `Foreign/` -, 558 die der erzwungenen: dieselbe Route,
eingeschraenkt auf die Import-Huelle der Default-Targets. Die Gleichung
568 = 558 + 10 geht auf; die 10 sind unveraendert `Foreign/PeresMermin.lean`.

Die siebzehn juengsten stehen am alpha+gamma-Strang. Stufe 1 der Wachenspitze setzte vier:
je eine in `AlphaGammaRelPullback`, `AlphaGammaTransport`, `AlphaGammaStratification` und
`AlphaGammaRounding`, gesetzt auf den im jeweiligen Dateikopf benannten Kern. Stufe 2 setzte
dreizehn weitere ueber alle neun Module des Strangs: acht auf Saetze, die der Doc-Index von
`Reformulation/Proemial.lean` beim Namen fuehrt, und fuenf auf die Saetze, die die Begriffe
ihrer Datei benennen - diese fuenf als Ermessensauswahl, im Wachen-Block als solche
markiert. Damit tragen alle neun Module des Strangs mindestens eine Wache; 22 seiner
43 Saetze liegen weiterhin ausserhalb jeder Wachen-Huelle.

Die vierzehn juengsten stehen an den vier Sonden, die sich im Dateikopf gleichlautend als
*vor dem proemialen Entwurf ρ stehend* ausweisen: `A1DescentProbe` (4), `A3CoarseningProbe`
(3), `K3CouplingProbe` (3), `ProemialInversionProbe` (4). Bis dahin trugen sie null Wachen;
zehn ihrer Saetze standen unter einem blossen `#print axioms`, das druckt und nichts
sichert, vier unter gar nichts - darunter `split_epi_not_iso`, der von
`AsymmetricDiscontexturality` und vom Sonden-Register namentlich als Zeuge zitiert wird.
Alle vierzehn Wachen sind **erzwungen**: die vier Module sind Wurzeln des Targets `Probes`
und laufen bei jedem `lake build`. Was sie **nicht** sind: gegatet. Das AxiomGate misst den
Importbaum von `Reformulation`, und alle vier liegen ausserhalb davon - gemessen ueber
`env.allImportedModuleNames` unter `import Reformulation` (3405 Module, keines der vier
darunter). Die Wachen sichern damit das Profil, das Gate die `sorryAx`-Freiheit; fuer die
vier Sonden gilt das erste und nicht das zweite.

Die **29 juengsten** stammen aus einem Zug, der eine dritte Stufe unter der Unterscheidung
*geschrieben/erzwungen* geschlossen hat: **gedruckt gegen gewacht.** Ein blosses
`#print axioms` ohne `#guard_msgs` druckt ein Profil in die Bauausgabe und sichert nichts -
aendert der Satz sein Profil, druckt es das neue und der Bau bleibt gruen. Gemessen am
Stand `4c263ee`: **39** solcher Aufrufe in 9 Dateien, davon **28** in Modulen, die bei
jedem Bau mitlaufen und auf einen Satz der eigenen Datei zeigen. Diese 28 sind jetzt
Wachen, dazu ein 29. nach einem zweiten Kriterium - `F3g.classI_iff_stage_1`, ohne Aufruf,
aber im Beweisterm von `F3g.Quine` konsumiert und ausserhalb jeder Huelle.

**Die elf uebrigen bleiben nackt, und das ist kein Rest.** Sie stehen in
`Diagnostics/AxiomProbe.lean` und `Diagnostics/SwapSatzProbe.lean`; dort ist der nackte
Aufruf die Bauform, weil ein Werkzeug, das Profile *anzeigen* soll, sie nicht einfrieren
darf. Die Zahl 39 = 28 + 1 (anderes Kriterium, ohne Aufruf) + 11 (Werkzeuge) geht damit
auf, wobei der 29. nicht unter den 39 steht - die Gleichung der Wachen lautet
501 + 29 = 530.

Nebenwirkung, gemessen statt gerechnet: die **Saetze in Aggregat-Modulen, die keine Wache
tragen**, gehen von **71 in 23 Modulen** auf **66 in 22** zurueck.

**Die Beschreibung ist genau zu nehmen, und zwar an dieser Stelle mehr als anderswo.**
Gezaehlt werden Saetze, deren **Modul** keine einzige Wache traegt - nicht Saetze ohne
eigene Wache. Das sind zwei verschiedene Groessen, und die Verwechslung ist in diesem
Projekt zweimal aufgetreten. Hier ist die Folge: der Rueckgang ist **5 und nicht 1**,
obwohl nur eine Wache hinzukam. Mit ihr faellt `F3g/Availability.lean` als ganze Datei aus
der Zaehlung, mit allen fuenf Saetzen. Neue Gleichung: F3a-F3g 56 + F1-Belegungen 10 = 66
in 13 + 9 = 22 Modulen.

---

## Reichweite

Was hier steht, ist schmaler als die Theorie, auf die es sich bezieht - absichtlich:

* **Diskontexturalitaet** erscheint als *Nicht-Erzeugbarkeit im Termklon*, nicht als
  Nichtexistenz einer Abbildung. Guenthers Grundfall (Sein und Nichts) ist isomorph und
  trotzdem diskontextural; eine Formalisierung ueber fehlende Abbildungen waere am
  Gegenstand falsch.
* **Die philosophische Deutung wird nicht bewiesen.** Ob kontextur-relative
  Operationswahl Guenthers *Vermittlung* ist, entscheidet kein Modul. Darum heisst die
  Datei `NonUniformCloneBound` und nicht `Mediation`.
* **Zaehlungen ausserhalb des Korpus** (Klon-Groessen, Aufzaehlungen ueber alle
  Operationen) bleiben ausserhalb. Im Korpus stehen sie nur in Bijektions- oder Iff-Form.

---

## Bauen und pruefen

```sh
lake build                 # Default-Targets; AxiomGate laeuft mit
```

`lake build` baut das Aggregat, das AxiomGate, den Definition-Ledger sowie die Targets
`Probes` und `F1Coalgebraic`. Vier weitere Targets (`Diagnostics`, `MathlibExtensions`,
`PreC`, `PathC`) und `ForeignPeresMermin` laufen nur auf eigenen Ruf. **Was ein gruener
Bau je Target zusichert - und was nicht -, steht in `docs/build-targets.md`.** Ein Modul
(`PathC/Classifying/Universal.lean`) uebersetzt nicht und liegt darum in keinem Target;
es wird dort mit Fehlermeldung und Messdatum gefuehrt.

Axiom-Profile einzelner Saetze ohne Neubau:

```sh
echo 'import Reformulation.Proemial.NonUniformCloneBound' > /tmp/a.lean
echo '#print axioms Reformulation.Proemial.NonUniformCloneBound.W_not_in_clone' >> /tmp/a.lean
lake env lean /tmp/a.lean
```

`.lake/` umfasst rund 7,5 GB und ist ausgeschlossen; der Quellbestand sind ~166 Dateien
unter 1 MB.

Bau-Konventionen fuer beitragende Instanzen: siehe `CLAUDE.md`.

---

## Lizenz, Zitate und Beitraege

Der Lean-Bestand steht unter Apache-2.0 (`LICENSE`), die Dokumente unter `docs/` unter
CC-BY-4.0 (`docs/LICENSE`). Beide Lizenzdateien tragen den Volltext der amtlichen Fassung.

Keine der beiden Lizenzen erstreckt sich auf woertlich zitierte Passagen Dritter. Der
Korpus enthaelt Zitate aus den Schriften Gotthard Guenthers; sie sind an ihren Fundstellen
als Zitat gekennzeichnet, stehen unter dem Zitatrecht und verbleiben bei den jeweiligen
Rechteinhabern. Wer Teile dieses Werks weiterverwendet, prueft die Zitate eigenstaendig.

Zitierangabe: `CITATION.cff`.

Der Spezifikations- und Befundkorpus, auf den Doc-Strings und Dokumente an vielen Stellen
verweisen, liegt ausserhalb dieses Repositoriums und ist nicht veroeffentlicht.

Dieses Projekt arbeitet mit einer spezifizierenden und einer bauenden Instanz; Beitraege
werden derzeit nicht angenommen, und Issues sind abgeschaltet. Wer einen Fehler findet -
eine falsche Zahl, eine Route, die nicht traegt, eine Behauptung ohne Traeger -, melde ihn
auf X an @PolyContextual.
