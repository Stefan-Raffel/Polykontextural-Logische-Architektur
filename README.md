# Reformulation - Polykontexturale Logik in Lean 4

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

**Arbeitspapier zur Fassung PKL Rev1** (deutsch und englisch, mit Figuren und Zaehlrouten):
`docs/de.html` und `docs/en.html`. Die frueher hier genannte Pages-Adresse
<https://stefan-raffel.github.io/PKLrev1/> loest nicht auf - gemessen am 29. Juli 2026 gibt
sie ohne Anmeldung HTTP 404 zurueck, wie es bei privatem Repository zu erwarten ist.

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
| geprueft (AxiomGate) | 2998 Konstanten |
| Axiom-Wachen | 385 ueber 43 Dateien |
| Saetze gesamt | 715 |
| Build-Jobs | 1299 |
| ausgewiesene Luecken | 0 (Whitelist leer) |

Kennzahlen gezaehlt am gruenen Build, Stand Commit `997037f`.

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
| `Proemial/` | 57 | 421 | Proemialrelation, Transjunktion, Klon-Schranken |
| `PathC/` | 18 | 102 | Weg C - iterative Doppelbeschreibung |
| `Kenogram/` | 4 | 91 | Kenogrammatik: RGS, Normalform, Operationssemantik |
| `F1/` | 20 | 21 | Belegungen, Faserungen, Cross-Chain-Anschluss |
| `F3a`-`F3g/` | 38 | 63 | Stufen, Modaloperatoren, Uebergangsklassen |
| `PreC/`, `Diagnostics/`, `MathlibExtensions/` | 16 | 17 | Vorbereitung, Messung, Zusatzlemmata |
| `Foreign/` | 1 | 10 | fremd gestellter Fall (Peres-Mermin) |

**Die Summe dieser Tafel ist groesser als die Gesamtzahl oben**, und das ist kein
Widerspruch, sondern der Bereich: die 715 laufen ueber `Reformulation/` allein, die Tafel
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

Zusaetzlich frieren 385 `#guard_msgs`-Wachen die gemessenen Axiom-Profile ein: aendert
ein Satz sein Profil, bricht der Bau. `Classical.choice` ist auf wenige Dateien begrenzt
und dort ausgewiesen.

Zu lesen mit einer Einschraenkung: von den 385 geschriebenen Wachen erzwingt `lake build`
**375** (in 42 Dateien). Die uebrigen 10 stehen in `Foreign/PeresMermin.lean`, das ueber
`lake build ForeignPeresMermin` laeuft, aber nicht ueber den Default-Bau. Der fremd
gestellte Fall liegt ausserhalb des Aggregats; seine Wachen sind geschrieben und pruefbar,
nur nicht vom Default-Bau erzwungen. Das gehoert ausdruecklich dorthin.

Bis zum Buildabdeckungs-Zug C2 waren es 23 unerzwungene: dreizehn davon standen in drei
Modulen, die von keinem Target erfasst wurden und darum ueberhaupt nicht liefen
(`Proemial/AsymmetricDiscontexturality.lean` 7, `Proemial/TowerAsymmetryProbe.lean` 4,
`Proemial/AsymmetricDiscontexturalTransition.lean` 2). Seit C2 liegen sie im Target
`Probes` und werden bei jedem Bau ausgefuehrt; beim Anschalten hielt jede von ihnen.

385 ist die Zahl der geschriebenen Wachen - Route `grep -rE '#guard_msgs.*in #print axioms'`
ueber `Reformulation/` und `Foreign/` -, 375 die der erzwungenen: dieselbe Route,
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

`.lake/` umfasst rund 7,5 GB und ist ausgeschlossen; der Quellbestand sind ~158 Dateien
unter 1 MB.

Bau-Konventionen fuer beitragende Instanzen: siehe `CLAUDE.md`.
