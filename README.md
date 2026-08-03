# Reformulation - Polykontexturale Logik in Lean 4

###### *English introduction*

This repository contains a formal reformulation of Gotthard Guenther's polycontextural
logic in Lean 4 with Mathlib. It separates, machine-checkably, what is proved from what is
named, interpreted or posited, and it carries a counting route for every figure it states.

The project works with one definition. The German wording below is the binding one; this is
a translation of it:

> A structure is **formally operative polycontextural** if it carries a family of local
> contextures on which the relevant operations act classically or locally classically, and
> if in addition a machine-checked theorem shows that the global interplay of these local
> operations is not generable by any single intra-contextural term calculus.

This is narrower than Guenther's world-picture notion of polycontexturality, which is not
implemented and is carried as open.

- Working paper, edition Rev2, in English: `docs/en.html`
- Concept-to-carrier assignment, compiler-checked: `docs/definition-ledger.md`
- What a green build assures, per target: `docs/build-targets.md`
- Current figures with their counting routes: the German section below

Contributions are not accepted at present and issues are switched off; the reporting
channel is named at the end of this file.

---

Dieses Repository arbeitet mit einer Projektdefinition, und sie steht vorneweg:

> Eine Struktur ist **formal-operativ polykontextural**, wenn sie eine Familie lokaler
> Kontexturen traegt, auf denen die relevanten Operationen jeweils klassisch oder lokal
> klassisch wirken, und wenn zusaetzlich ein maschinell gepruefter Satz zeigt, dass das
> globale Zusammenspiel dieser lokalen Operationen nicht durch einen einheitlichen
> intra-kontexturellen Termkalkuel erzeugbar ist.

Als Arbeitsformel:

```text
lokale Klassizitaet + Kontexturpluralitaet + beweisbarer globaler Reduzierbarkeitsbruch
```

Diese Definition ist enger als die philosophische Definition 6 und staerker als blosse
Mehrwertigkeit oder Rollenpluralitaet. Alles Weitere in diesem README ist an ihr zu messen.

Formale Begleitung des Projekts zur Reformulierung der polykontexturalen Logik
Gotthard Guenthers. Der Code ist kein Beweis der Theorie, sondern ein Pruefwerkzeug:
er trennt, was aus klassischen Mitteln erzeugbar ist, von dem, was es nicht ist -
und macht die Grenze zwischen Beweis, Setzung und Deutung maschinell nachpruefbar.

Lean `4.30.0-rc2`, Mathlib. Bau mit `lake build`.

**Arbeitspapier zur Fassung PKL Rev1** (deutsch und englisch, mit Figuren und
Zaehlrouten): <https://stefan-raffel.github.io/Polykontextural-Logische-Architektur/> -
und im Bestand unter `docs/de.html` und `docs/en.html`.

Vorgeschichte, weil sie datiert ist und nicht geloescht wird: bis zur Umstellung auf
oeffentlich lieferte die frueher hier genannte Adresse
<https://stefan-raffel.github.io/PKLrev1/> ohne Anmeldung HTTP 404 - gemessen am
29. Juli 2026, wie es bei privatem Repositorium zu erwarten ist. Seit dem 1. August 2026
loest <https://stefan-raffel.github.io/Polykontextural-Logische-Architektur/> auf; die
alte Adresse loest nicht auf (gemessen, HTTP 404) - Pages folgt der Umbenennung nicht.

---

## Was implementiert ist, und was nicht

Dieses Repository implementiert **nicht** die volle weltbildhafte Poly-Kontexturalitaet aus
Definition 6 der Definitionen-Fassung: das System sich unendlich erweiternder Kontexturen mit
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
| geprueft (AxiomGate) | 3199 Konstanten |
| Axiom-Wachen | 440 ueber 49 Dateien |
| Saetze gesamt | 772 |
| Build-Jobs | 1305 |
| ausgewiesene Luecken | 0 (Whitelist leer) |

Kennzahlen gezaehlt am gruenen Build, Stand Commit `990077b`.

Was das AxiomGate zusichert, und was nicht. Das zertifizierte Aggregat zieht kein
`sorryAx`, die Whitelist ist leer, und jede neue Luecke bricht den Bau. Diese Zusicherung
gilt fuer das Aggregat und fuer keinen anderen Bereich. Der Zweig `PathC` ist eingefroren,
liegt ausserhalb der Default-Targets und traegt offene Stellen; ein Modul darin uebersetzt
nicht. Wer im Baum nach `sorry` sucht, findet drei verschiedene Zahlen, und jede beantwortet
eine andere Frage: 132 rohe Treffer ueber den ganzen verfolgten Bestand, 97 in den
Lean-Quellen, 27 betroffene Deklarationen. Die dritte ist die tragende; was ein gruener
Bau je Target zusichert, steht in `docs/build-targets.md`.

Die erste Zahl zaehlt sich selbst mit: je drei ihrer Treffer stehen in `docs/de.html` und
`docs/en.html`, weil das Arbeitspapier den Wortlaut dieser Suche zitiert. Am Stand
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

Die Route ist genau anzugeben, weil zwei nahe Routen verschiedene Zahlen liefern: gezaehlt
werden **Wortvorkommen** (132 / 97), nicht Zeilen mit mindestens einem Vorkommen (129 / 94).
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

| Bereich | Dateien | Saetze | Gegenstand |
|---|---:|---:|---|
| `Proemial/` | 61 | 463 | Proemialrelation, Transjunktion, Klon-Schranken |
| `PathC/` | 18 | 102 | Weg C - iterative Doppelbeschreibung |
| `Kenogram/` | 6 | 106 | Kenogrammatik: RGS, Normalform, Operationssemantik, Musterrelation, Besetzbarkeit |
| `F1/` | 20 | 21 | Belegungen, Faserungen, Cross-Chain-Anschluss |
| `F3a`-`F3g/` | 38 | 63 | Stufen, Modaloperatoren, Uebergangsklassen |
| `PreC/`, `Diagnostics/`, `MathlibExtensions/` | 16 | 17 | Vorbereitung, Messung, Zusatzlemmata |
| `Foreign/` | 1 | 10 | fremd gestellter Fall (Peres-Mermin) |

**Die Summe dieser Tafel ist groesser als die Gesamtzahl oben**, und das ist kein
Widerspruch, sondern der Bereich: die 772 laufen ueber `Reformulation/` allein, die Tafel
weist `Foreign/` mit seinen 10 Saetzen eigens aus. Der fremd gestellte Fall liegt ausserhalb
des Aggregats und wird darum in der Gesamtzahl nicht mitgezaehlt.

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

Zusaetzlich frieren 440 `#guard_msgs`-Wachen die gemessenen Axiom-Profile ein: aendert
ein Satz sein Profil, bricht der Bau. `Classical.choice` ist auf wenige Dateien begrenzt
und dort ausgewiesen.

Zu lesen mit einer Einschraenkung: von den 440 geschriebenen Wachen erzwingt `lake build`
**430** (in 48 Dateien). Die uebrigen 10 stehen in `Foreign/PeresMermin.lean`, das ueber
`lake build ForeignPeresMermin` laeuft, aber nicht ueber den Default-Bau. Der fremd
gestellte Fall liegt ausserhalb des Aggregats; seine Wachen sind geschrieben und pruefbar,
nur nicht vom Default-Bau erzwungen. Das gehoert ausdruecklich dorthin.

Bis zum Buildabdeckungs-Zug C2 waren es 23 unerzwungene: dreizehn davon standen in drei
Modulen, die von keinem Target erfasst wurden und darum ueberhaupt nicht liefen
(`Proemial/AsymmetricDiscontexturality.lean` 7, `Proemial/TowerAsymmetryProbe.lean` 4,
`Proemial/AsymmetricDiscontexturalTransition.lean` 2). Seit C2 liegen sie im Target
`Probes` und werden bei jedem Bau ausgefuehrt; beim Anschalten hielt jede von ihnen.

440 ist die Zahl der geschriebenen Wachen - Route `grep -rE '#guard_msgs.*in #print axioms'`
ueber `Reformulation/` und `Foreign/` -, 430 die der erzwungenen: dieselbe Route,
eingeschraenkt auf die Import-Huelle der Default-Targets.

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

`.lake/` umfasst rund 7,5 GB und ist ausgeschlossen; der Quellbestand sind ~164 Dateien
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
