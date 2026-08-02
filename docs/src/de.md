---
lang: de
pagetitle: "Die mathematische Gestalt der Architektur — PKL Rev2"
title: "Die mathematische Gestalt der Architektur"
subtitle: "Polykontexturale Logik in Lean 4 und Mathlib — Fassung PKL Rev2"
dateline: "1. August 2026 · Stand aller Kennzahlen: Commit `e5ef3d7` · Fassung Rev2"
description: "Polykontexturale Logik in Lean 4 und Mathlib. Fassung PKL Rev2: zwei Achsen je Aussage, die Schrankenreihe D–E4, die Anwendungsschicht mit gemessenem Konsum, Ledger und Setzungsregister, Bereichstrennung."
toc-title: "Inhalt"
toc-label: "Inhaltsverzeichnis"
---

---

## Wovon dieses Papier handelt {#wovon}

Es handelt von einer Formalisierung, die ihre eigenen Ansprüche etikettiert, und von einer
Prüfpraxis, die übertragbar sein soll. Gegenstand ist die Reformulierung der
polykontexturalen Logik Gotthard Günthers in einer typentheoretischen Beweisumgebung.

Das Projekt arbeitet mit einer Definition, und sie steht vorneweg — zitiert aus `README.md`,
Stand `e5ef3d7`, und dort und nicht hier zu Hause:

::: callout
Eine Struktur ist **formal-operativ polykontextural**, wenn sie eine Familie lokaler
Kontexturen trägt, auf denen die relevanten Operationen jeweils klassisch oder lokal
klassisch wirken, und wenn zusätzlich ein maschinell geprüfter Satz zeigt, dass das
globale Zusammenspiel dieser lokalen Operationen nicht durch einen einheitlichen
intra-kontexturellen Termkalkül erzeugbar ist.
:::

Diese Definition ist enger als die weltbildhafte Definition 6 der Quelle und stärker als
blosse Mehrwertigkeit oder Rollenpluralität. Sie ist der Massstab, an dem alles Weitere zu
messen ist.

## Zwei Achsen je Aussage {#achsen}

Die vorige Ausgabe etikettierte jede Behauptung nach ihrer **Art**. Das genügt nicht mehr.

**Erste Achse — die Art:**

- **bewiesen** — maschinell verifiziertes Theorem
- **gemessen** — maschinell gezählte Kenngrösse
- **gerechnet** — exakte Rechnung ausserhalb des Korpus
- **gesetzt** — ausdrückliche Prämisse
- **quellen-fest** — wörtlich bei Günther, mit Fundstelle
- **Deutung** — Zuordnung von Formalem zu Begrifflichem
- **Programm** — benannt, nicht gebaut

**Zweite Achse — der Bereich**, gemessen an den Import-Hüllen und nicht am Verzeichnis:

- **Aggregat** — in der Hülle der fünf Default-Targets; das AxiomGate prüft es beim Bau
- **Rufe-Target** — ausserhalb davon, aber von mindestens einem Rufe-Target erreicht; kein
  Gate, keine Lückenfreiheitszusage
- **von keinem Target erfasst** — im Baum, von keiner Hülle erreicht; kein Bau fasst es an

Quer dazu steht eine Marke, die kein Hüllenwert ist: **eingefroren** bezeichnet den Zweig
`PathC/`, der mit ausdrücklichen Auftaubedingungen stillgelegt ist. Ein eingefrorenes Modul
kann trotzdem gebaut werden — zwei von achtzehn werden über ein Rufe-Target erreicht.

Das Wort *standalone* ist hier bewusst vermieden. Die Ablagekonvention des Korpus nennt so
eine Datei, die eine Setzung trägt und von keinem Aggregat-Satz konsumiert wird; das ist
eine andere Frage, und drei solche Dateien werden heute gebaut.

Der Grund für die zweite Achse ist nicht Ordnungsliebe. **Bewiesen** heisst im Aggregat
etwas anderes als in einem Rufe-Target: dort greift eine maschinelle Schranke, hier nicht.
Ein Papier, das Sätze beider Bereiche ohne Unterschied führt, beansprucht für die einen
eine Zusicherung, die nur die anderen haben.

Die zwei Spalten des Definition-Ledgers — Trägerstatus und Zuordnungsstatus — sind eine
dritte Sache: sie klassifizieren **Träger**, während die Etiketten hier **Aussagen im
Fliesstext** klassifizieren. Die Ledger-Tabelle steht in `docs/definition-ledger.md` und
wird hier nicht wiederholt.

---

## Was diese Ausgabe gegenüber der ersten ändert {#ändert}

Die erste Ausgabe datiert vom 24. Juli 2026 und misst alle Zahlen am Commit `e89ab47`. Sie
bleibt unter `docs/rev1/` erreichbar und wird nicht nachgeführt.

| | Fassung Rev1 (24. Juli) | diese Fassung (1. August) |
|---|---|---|
| Etikettierung | eine Achse (Art) | **zwei Achsen** (Art und Bereich) |
| Begriffszuordnung | im Fliesstext verteilt | **compilergeprüfter Ledger**, 19 von 19 Paragraphen |
| Setzungen | benannt | **registriert**, mit Klasse und Exit-Kriterium |
| Bereichstrennung | nicht geführt | **Default-Targets, Rufe-Targets, eingefroren, von keinem Target erfasst** |
| Anwendungen | keine | **zwei**, Konsum am Beweisterm gemessen |
| Morphogramm-Brücke | Programm | **drei Sätze, zwei Definitionen, eine offene Zeile** |
| Replizierbarkeit | Bau auf einer Maschine | **Bau aus frischem, anmeldungsfreiem Klon** |
| Zugang | privat | **öffentlich, Apache-2.0 und CC-BY-4.0** |

**Was nicht dazugekommen ist, und es steht hier, damit es nicht gesucht werden muss:** die
proemiale Relation ist nicht formalisiert; die Verbundkontextur ist als Zahlenfolge
vorhanden und nicht als Begriff gebaut; die starke Definition 6 ist offen und wird als
offen geführt (Ledger-Zeile L06-1, Trägerstatus `Offen`).

---

## I · Der Grund: eine Kombinatorik vor der Logik {#i}

Zuunterst liegt eine Struktur, die noch keine Logik ist: die kenogrammatische Schicht, eine
Kombinatorik leerer Stellen. Endliche Folgen werden allein danach klassifiziert, welche
Stellen welche wiederholen. Keine Werte, keine Negation, keine Wahrheit; nur
Unterscheidbarkeit und Wiederholung. Alles Spätere ist eine Belegung auf diesen Mustern.

Günther unterscheidet drei Feinheiten (**quellen-fest**). Die **Proto**-Struktur zählt nur,
wie viele verschiedene Marken vorkommen. Die **Deutero**-Struktur hält das
Wiederholungsprofil fest. Die **Trito**-Struktur behält das stellengenaue Muster. Nur die
dritte ist fein genug, um Grund einer Logik zu sein: eine Belegung muss sagen können,
welche Stellen denselben Wert tragen.

<figure class="fig wide">
<div class="fig-scroll">
<svg viewBox="0 0 700 250" role="img" aria-label="Dieselbe Folge in drei Feinheiten">
  <defs><marker id="ah1" markerWidth="8" markerHeight="8" refX="7" refY="4" orient="auto">
    <path d="M0,0 L8,4 L0,8 z" fill="var(--stroke)"/></marker></defs>

  <text class="txs mut" x="112" y="30" text-anchor="end">Folge 1</text>
  <text class="txs mut" x="112" y="70" text-anchor="end">Folge 2</text>
  <text class="txs mut" x="112" y="110" text-anchor="end">Normalform</text>

  <g class="box" fill="var(--f03)">
    <rect x="130" y="8"  width="42" height="32"/><rect x="180" y="8"  width="42" height="32"/>
    <rect x="230" y="8"  width="42" height="32"/><rect x="280" y="8"  width="42" height="32"/>
    <rect x="330" y="8"  width="42" height="32"/>
    <rect x="130" y="48" width="42" height="32"/><rect x="180" y="48" width="42" height="32"/>
    <rect x="230" y="48" width="42" height="32"/><rect x="280" y="48" width="42" height="32"/>
    <rect x="330" y="48" width="42" height="32"/>
  </g>
  <g class="box" fill="var(--f12)">
    <rect x="130" y="88" width="42" height="32"/><rect x="180" y="88" width="42" height="32"/>
    <rect x="230" y="88" width="42" height="32"/><rect x="280" y="88" width="42" height="32"/>
    <rect x="330" y="88" width="42" height="32"/>
  </g>
  <g class="t i" text-anchor="middle">
    <text x="151" y="30">a</text><text x="201" y="30">b</text><text x="251" y="30">b</text>
    <text x="301" y="30">a</text><text x="351" y="30">c</text>
    <text x="151" y="70">x</text><text x="201" y="70">y</text><text x="251" y="70">y</text>
    <text x="301" y="70">x</text><text x="351" y="70">z</text>
  </g>
  <g class="t" text-anchor="middle">
    <text x="151" y="110">0</text><text x="201" y="110">1</text><text x="251" y="110">1</text>
    <text x="301" y="110">0</text><text x="351" y="110">2</text>
  </g>

  <rect class="box" x="110" y="150" width="160" height="46" rx="5" fill="var(--f03)"/>
  <rect class="box" x="285" y="150" width="160" height="46" rx="5" fill="var(--f08)"/>
  <rect class="box" x="460" y="150" width="180" height="46" rx="5" fill="var(--f16)"/>
  <g text-anchor="middle">
    <text class="ts b" x="190" y="169">Proto</text><text class="txs" x="190" y="185">3 Marken</text>
    <text class="ts b" x="365" y="169">Deutero</text><text class="txs" x="365" y="185">2, 2, 1</text>
    <text class="ts b" x="550" y="169">Trito</text><text class="txs" x="550" y="185">0, 1, 1, 0, 2</text>
  </g>
  <line class="ln" x1="200" y1="222" x2="545" y2="222" marker-end="url(#ah1)"/>
  <text class="txs mut" x="372" y="240" text-anchor="middle">gröber → feiner</text>
</svg>
</div>
<figcaption><span class="fignum">Figur 1</span> — Dieselbe Folge in drei Feinheiten: Proto,
Deutero und Trito als zunehmend feine Klassifikation. Die gröberen sind Quotienten der feinsten;
nur die feinste kann sagen, welche Stellen denselben Wert tragen.</figcaption>
</figure>

Formal wird die Trito-Struktur durch eine Normalform vertreten: eine Folge natürlicher
Zahlen, die mit `0` beginnt und in der jede neue Marke das bisherige Maximum um genau eins
übersteigt — in der Kombinatorik als *restricted growth string* bekannt. Das Prädikat ist
entscheidbar, und die Kanonisierung ist als Prozedur gebaut, nicht behauptet
(**bewiesen · Aggregat**; Ledger-Zeile L16-1, `K.relabel`, axiomfreies Profil).

### Die eingebaute Richtungsasymmetrie

Die Abbildungen zwischen Mustern sind nicht symmetrisch. Ein Muster mit grösster Marke `k`
hat genau `k+2` Verlängerungen — es wiederholt eine der vorhandenen Marken oder führt eine
neue ein. **Die Rücknahme ist dagegen eindeutig**: streiche die letzte Stelle, und genau ein
Muster bleibt (**gerechnet**).

Das ist keine Schreibweise, sondern die Sache selbst: **der Aufstieg wählt, der Abstieg
rechnet.** Zwischen beiden Richtungen liegt kein Vorzeichenwechsel, sondern ein Unterschied
in der Art der Bestimmtheit. Günther nennt die eine Richtung *evolutiv*, die andere
*emanativ* (**quellen-fest**).

<figure class="fig wide">
<div class="fig-scroll">
<svg viewBox="0 0 700 260" role="img" aria-label="Rücknahme eindeutig, Verlängerung verzweigt">
  <defs><marker id="ah2" markerWidth="8" markerHeight="8" refX="7" refY="4" orient="auto">
    <path d="M0,0 L8,4 L0,8 z" fill="var(--stroke)"/></marker></defs>

  <g class="box" fill="var(--f03)">
    <rect x="20" y="116" width="30" height="28"/><rect x="54" y="116" width="30" height="28"/>
    <rect x="88" y="116" width="30" height="28"/>
  </g>
  <g class="ts" text-anchor="middle">
    <text x="35" y="135">0</text><text x="69" y="135">1</text><text x="103" y="135">1</text>
  </g>

  <line class="ln" x1="270" y1="130" x2="135" y2="130" marker-end="url(#ah2)"/>
  <text class="txs" x="203" y="121" text-anchor="middle">emanativ</text>
  <text class="txs i mut" x="203" y="146" text-anchor="middle">eindeutig</text>

  <text class="txs mut" x="278" y="103" text-anchor="start">Muster</text>
  <g class="box" fill="var(--f12)">
    <rect x="280" y="116" width="30" height="28"/><rect x="314" y="116" width="30" height="28"/>
    <rect x="348" y="116" width="30" height="28"/><rect x="382" y="116" width="30" height="28"/>
  </g>
  <g class="ts" text-anchor="middle">
    <text x="295" y="135">0</text><text x="329" y="135">1</text>
    <text x="363" y="135">1</text><text x="397" y="135">0</text>
  </g>

  <path class="ln" d="M418,130 C470,130 470,40 520,40"   marker-end="url(#ah2)"/>
  <path class="ln" d="M418,130 L520,130"                  marker-end="url(#ah2)"/>
  <path class="ln" d="M418,130 C470,130 470,220 520,220"  marker-end="url(#ah2)"/>

  <g class="box" fill="var(--f03)">
    <rect x="533" y="26"  width="26" height="28"/><rect x="562" y="26"  width="26" height="28"/>
    <rect x="591" y="26"  width="26" height="28"/><rect x="620" y="26"  width="26" height="28"/>
    <rect x="533" y="116" width="26" height="28"/><rect x="562" y="116" width="26" height="28"/>
    <rect x="591" y="116" width="26" height="28"/><rect x="620" y="116" width="26" height="28"/>
    <rect x="533" y="206" width="26" height="28"/><rect x="562" y="206" width="26" height="28"/>
    <rect x="591" y="206" width="26" height="28"/><rect x="620" y="206" width="26" height="28"/>
  </g>
  <g class="box" fill="var(--f20)">
    <rect x="649" y="26"  width="26" height="28"/>
    <rect x="649" y="116" width="26" height="28"/>
    <rect x="649" y="206" width="26" height="28"/>
  </g>
  <g class="txs" text-anchor="middle">
    <text x="546" y="45">0</text><text x="575" y="45">1</text><text x="604" y="45">1</text>
    <text x="633" y="45">0</text><text x="662" y="45">0</text>
    <text x="546" y="135">0</text><text x="575" y="135">1</text><text x="604" y="135">1</text>
    <text x="633" y="135">0</text><text x="662" y="135">1</text>
    <text x="546" y="225">0</text><text x="575" y="225">1</text><text x="604" y="225">1</text>
    <text x="633" y="225">0</text><text x="662" y="225">2</text>
  </g>

  <text class="txs" x="466" y="14" text-anchor="middle">evolutiv</text>
  <text class="txs i mut" x="466" y="27" text-anchor="middle">verzweigt</text>
</svg>
</div>
<figcaption><span class="fignum">Figur 2</span> — Rücknahme eindeutig, Verlängerung verzweigt.
Ein Muster mit grösster Marke <em>k</em> hat <em>k</em> + 2 Verlängerungen — jede vorhandene
Marke oder eine neue — und genau eine Rücknahme (<strong>gerechnet</strong>).</figcaption>
</figure>

### Die Morphogramm-Brücke

Auf der Normalform sitzt die Musteridentität: zwei Folgen tragen dasselbe Morphogramm,
wenn ihre Normalformen übereinstimmen. Der Korpus führt dazu sechs Ledger-Zeilen zu
Paragraph 16, drei davon mit Satzcharakter (**bewiesen · Aggregat**):

| Zeile | Träger | Art | Profil |
|---|---|---|---|
| L16-1 | `K.relabel` | Definition | axiomfrei |
| L16-2 | `K.rgs_unique_of_pattern` | Theorem | `[propext, Quot.sound]` |
| L16-3 | `KM.SamePattern` | Definition | — |
| L16-4 | `KM.samePattern_iff_pattern` | Theorem | `[propext, Classical.choice, Quot.sound]` |
| L16-5 | `KM.samePattern_iff_common_nf` | Theorem | `[propext, Classical.choice, Quot.sound]` |
| L16-6 | — | **Offen** | Wertbesetzung der Morphogramme nicht formalisiert |

**Kein Quotiententyp.** Die Brücke ist als Normalformsemantik gebaut, nicht als Quotient;
das war eine Bauentscheidung und keine Verlegenheit. L16-5 trägt den Vermerk, dass die
Charakterisierung über die gemeinsame Normalform an `List ℕ` hängt, während L16-4
typübergreifend ist. Die offene Zeile L16-6 bleibt offen und steht in [§X](#x).

---

## II · Kontexturen: zwei Diskontexturalitäten, eine davon bewiesen {#ii}

Eine Kontextur ist eine Belegung auf dem Grund mit dem Rang einer eigenen Logik.

### 1 · Was Diskontexturalität nicht ist

Günthers elementarster Fall von Diskontexturalität ist der Gegensatz von Sein und Nichts —
und diese beiden sind bei ihm **isomorph** (**quellen-fest**). Zwischen ihnen besteht eine
vollständige, strukturerhaltende Abbildung, und sie sind trotzdem diskontextural.

Daraus folgt die Formalisierungsentscheidung, die dieses Papier trägt: Diskontexturalität
erscheint **nicht** als Nichtexistenz einer Abbildung, sondern als **Nicht-Erzeugbarkeit im
Termklon** — als Unmöglichkeit, eine vermittelnde Operation aus intra-kontexturellen Mitteln
zusammenzusetzen. Was fehlt, ist nicht die Abbildung, sondern der Weg zu ihr von innen.

Zwei Kurzformen sind darum ausgeschlossen und werden im Korpus als Bauverbot geführt:
`Disjoint K₁ K₂` scheitert daran, dass die Elementarkontexturen paarweise in genau einem
Wert überlappen und diese Überlappung die Beweise trägt; `¬ ∃ f : K₁ → K₂` scheitert am
Grundfall Sein/Nichts.

### 2 · Die erste Relation: symmetrisch, und bewiesen

Günther nennt zwei Grundrelationen. Die erste ist das **Umtauschverhältnis** zwischen
Elementarkontexturen: ungeordnetes Paar, symmetrisch, ohne Richtungssinn (**quellen-fest**).

::: theorem
[Satz (E3).]{.label} Für jedes `m ≥ 4` liegt eine kontexturerhaltende, lokal klassische
Operation auf `m` Werten genau dann im Klon der intra-kontexturellen Junktoren, wenn sie
das Minimum oder das Maximum ist.
(**bewiesen · Aggregat**; `GeneralCloneBound.locally_classical_in_clone_iff`)
:::

Das ist eine **Charakterisierung**, keine Existenzaussage: die Menge der nicht
zusammensetzbaren Operationen ist nicht bloss nichtleer, sondern vollständig bestimmt.

### 3 · Die zweite Relation: asymmetrisch, und geteilt

Die zweite Relation besteht zwischen Kontextur und Transkontexturalität. Ihr Stand ist ein
geteiltes Ergebnis: der **strukturelle** Teil liegt als Satz vor, der **begriffliche** bleibt
Modellierung — dass ein Stufenwechsel ein Kontexturwechsel ist, schliesst kein Theorem. Eine
Kontexturgrenze schliesst nie durch Satz allein, sondern durch Definition plus Satz
(**gesetzt**, im Korpus als solches markiert).

### 4 · Wo die Setzung sitzt

::: callout
Eine zweielementige Menge benachbarter Werte ist eine Elementarkontextur in Günthers Sinn.
(**gesetzt** — die tragende Wahl der ganzen Schrankenreihe)
:::

Für diese Wahl gibt es einen sachlichen Grund, und er ist nicht nachträglich zugeschnitten:
eine zweielementige Menge ist unter den lokalen Operationen genau dann abgeschlossen, wenn
ihre beiden Elemente vergleichbar sind. Bei unvergleichbaren Paaren verlässt das Minimum die
Menge — dann ist sie kein in sich geschlossener Zusammenhang und keine Kontextur im Sinne der
Definitionen. **Die Grenze der Formalisierung liegt im Begriff, nicht im Beweis.**

---

## III · Die Beweisform: das Differential {#iii}

Wie beweist man, was einer Struktur unveräusserlich fehlt, ohne den Selbstwiderspruch eines
Systems, das seine eigene Grenze von innen bescheinigt? Nicht positiv innerhalb eines
Systems, sondern **differentiell zwischen zweien**. Zu jedem Strukturmerkmal wird eine arme
Klasse benannt und ein Paar vorgezeigt: über alle Instanzen der armen Klasse ist das Merkmal
unmöglich — als allquantifizierter Satz —, und ein reicher Zeuge trägt es.

| die schwere Hälfte | die leichte Hälfte |
|---|---|
| `X` ist unmöglich — allquantifiziert | `X` wird vorgezeigt — eine Konstruktion |
| alle strikten Ordnungen, der erzeugte Klon | eine konkrete Struktur, intern gebaut |

Drei Marken disziplinieren die Form. **Erstens** wird das arme Modell intern gebaut, nicht in
der Metasprache behauptet. **Zweitens** ist das Ergebnis relativ zu den gesetzten Prämissen
bedingt; es symmetrisiert den Skeptiker, es zwingt ihn nicht. **Drittens** ist bewiesen die
Form, nie die Benennung — dass eine kontexturrelative Operationswahl aus lokalen Mitteln
unerreichbar ist, ist ein Satz; dass diese Wahl *Vermittlung* heisst, bleibt **Deutung**. Die
Datei im Korpus heisst darum `NonUniformCloneBound` und nicht `Mediation`.

<figure class="fig wide">
<div class="fig-scroll">
<svg viewBox="0 0 700 170" role="img" aria-label="Arme Klasse und reicher Zeuge">
  <defs><marker id="ah3" markerWidth="9" markerHeight="9" refX="8" refY="4.5" orient="auto">
    <path d="M0,0 L9,4.5 L0,9 z" fill="var(--stroke)"/></marker></defs>

  <rect class="box" x="15" y="18" width="290" height="134" rx="6" fill="var(--f12)"/>
  <text class="t b" x="160" y="45" text-anchor="middle">arme Klasse</text>
  <text class="ts mut" x="160" y="66" text-anchor="middle">alle strikten Ordnungen,</text>
  <text class="ts mut" x="160" y="81" text-anchor="middle">der erzeugte Klon</text>
  <text class="ts" x="160" y="112" text-anchor="middle"><tspan class="i">X</tspan> ist unmöglich — allquantifiziert</text>
  <text class="ts b" x="160" y="132" text-anchor="middle">die schwere Hälfte</text>

  <line class="ln" x1="315" y1="85" x2="385" y2="85" stroke-width="1.8" marker-end="url(#ah3)"/>
  <text class="t" x="350" y="74" text-anchor="middle">⊢</text>

  <rect class="box" x="395" y="18" width="290" height="134" rx="6" fill="var(--f03)"/>
  <text class="t b" x="540" y="45" text-anchor="middle">reicher Zeuge</text>
  <text class="ts mut" x="540" y="66" text-anchor="middle">eine konkrete Struktur,</text>
  <text class="ts mut" x="540" y="81" text-anchor="middle">intern gebaut</text>
  <text class="ts" x="540" y="112" text-anchor="middle"><tspan class="i">X</tspan> wird vorgezeigt — Konstruktion</text>
  <text class="ts mut" x="540" y="132" text-anchor="middle">die leichte Hälfte</text>
</svg>
</div>
<figcaption><span class="fignum">Figur 3</span> — Das Differential und seine ungleich schweren
Hälften. Erbracht ist es erst mit der negativen.</figcaption>
</figure>

---

## IV · Die Zeugen: die Reihe der Schranken {#iv}

| | Satz | Art der Nicht-Internalität | Reichweite |
|---|---|---|---|
| **D** | Rejektion liegt nicht im Klon | **Transzendenz** — sie verlässt die Kontextur | `m = 3` |
| **E1** | vollständige Klassifikation | **Nicht-Uniformität** — sie bleibt und wählt verschieden | `m = 3` |
| **E2** | Charakterisierung | genau Minimum und Maximum | `m = 4` |
| **E3** | Charakterisierung | genau Minimum und Maximum | **alle `m ≥ 4`** |
| **E4** | Stufenaggregation | Anwendungsgesicht | `m = 4` |

Alle fünf: **bewiesen · Aggregat**.

### 1 · D — die erste Schranke verorten

Die Rejektionsoperation weist ein angebotenes Wertepaar als Ganzes zurück und liegt nicht im
Klon über drei Werten (**bewiesen · Aggregat**; der Beweis ist stelligkeitsblind und läuft
über Kontexturerhaltung).

Ausserhalb eines Klons zu liegen ist für sich genommen billig: im binären Fragment umfasst
der Klon **82 von 19 683** Operationen, 0,42 Prozent (**gerechnet**). Die Aussage ruht nicht
darauf. Die Basis erhält drei Invarianten, und jeder Term über ihr erhält alle drei — nicht
nur die Erzeuger (**bewiesen · Aggregat**, durch Terminduktion). Die Rejektion verletzt genau
eine davon und erhält die beiden anderen. Sie liegt also nicht irgendwo ausserhalb, sondern
**an einer bestimmten Stelle**.

Eine Randbemerkung, die beim Nachrechnen dieser Ausgabe anfiel und in Rev1 fehlt: das binäre
Klonfragment hat **bei drei, vier, fünf und sechs Werten dieselbe Grösse 82**
(**gerechnet**). Die Zahl 82 ist keine Eigenschaft der Dreiwertigkeit, sondern der Signatur.

<figure class="fig wide">
<div class="fig-scroll">
<svg viewBox="0 0 700 300" role="img" aria-label="Der erzeugte Klon innerhalb aller binären Operationen">
  <rect class="box" x="120" y="8" width="460" height="188" rx="8" fill="var(--f05)"/>
  <text class="ts" x="350" y="34" text-anchor="middle">alle binären Operationen über drei Werten: 19 683</text>

  <circle class="box" cx="300" cy="118" r="66" fill="var(--f16)"/>
  <text class="ts" x="300" y="108" text-anchor="middle">erzeugter</text>
  <text class="ts" x="300" y="124" text-anchor="middle">Klon</text>
  <text class="ts b" x="300" y="142" text-anchor="middle">82</text>

  <circle class="box" cx="470" cy="72" r="13" fill="var(--f35)"/>
  <text class="ts" x="492" y="76" text-anchor="start">Rejektion</text>

  <text class="txs" x="120" y="228" text-anchor="start">drei Invarianten erhält <tspan class="i">jeder</tspan> Term (<tspan class="b">bewiesen · Aggregat</tspan>):</text>
  <text class="txs" x="120" y="245" text-anchor="start">zweiwertige Einbettung · Fixpunkt · Toleranz-Relation</text>
  <text class="txs" x="120" y="266" text-anchor="start">die Rejektion verletzt <tspan class="b">genau eine</tspan> und erhält die beiden anderen</text>
  <text class="txs mut" x="120" y="288" text-anchor="start">die Klongrösse 82 gilt ebenso bei vier, fünf und sechs Werten — sie hängt an der Signatur, nicht an der Wertzahl</text>
</svg>
</div>
<figcaption><span class="fignum">Figur 4</span> — Die Verortung: nicht irgendwo ausserhalb,
sondern jenseits genau einer von drei erhaltenen Invarianten. Klonzahlen
<strong>gerechnet</strong>, ausserhalb des Korpus; die Grösse 82 ist eine Eigenschaft der
Signatur und nicht der Dreiwertigkeit.</figcaption>
</figure>

### 2 · E1 — der zweite Grund, und die vollständige Teilung

Eine Operation kann aus **zwei verschiedenen Gründen** nicht zusammensetzbar sein: durch
**Transzendenz** — sie verlässt die Elementarkontextur (das ist D) — oder durch
**Nicht-Uniformität** — sie erhält jede Kontextur, wirkt auf jeder klassisch, und wählt auf
verschiedenen Kontexturen verschiedene klassische Operationen.

Der zweite Grund hat einen Zeugen, und zwar vollständig: von den acht Wahlmustern über drei
Werten sind genau vier zusammensetzbar und genau vier nicht (**bewiesen · Aggregat**; die
Teilung ist unter Negationskonjugation abgeschlossen — ein Transportlemma ersetzt drei Kopien
eines Beweises durch einen Satz).

**Die vier erreichbaren Muster sind keine beliebigen vier** (**gerechnet**). Ordnet man die
drei Elementarkontexturen als `{0,1}`, `{0,2}`, `{1,2}`, so sind sie
`(min,min,min)`, `(max,min,min)`, `(max,max,min)`, `(max,max,max)` — eine Kette von
Schwellen und keine verstreute Auswahl.

### 3 · E2 und E3 — von der Existenz zur Charakterisierung

Bei vier Werten kippt das Bild: von den 64 lokal klassischen Operationen bleiben **zwei**
zusammensetzbar, nämlich Minimum und Maximum selbst (**bewiesen · Aggregat**; **gerechnet**
nachgeprüft). Bei fünf Werten sind es 2 von 1024, bei sechs 2 von 32 768 (**gerechnet**).

Die Musterzahlen sind kein Zufall: es sind `2^C(m,2)` Muster, und `C(m,2) = m(m-1)/2` ist die
Zahl der Elementarkontexturen eines `m`-wertigen Systems. Die Dreieckszahlen, die Günther
für Verbundkontexturen und für die Hierarchie der Ontologien führt, stehen hier als
Exponent.

<p class="formula"><span class="name">E3</span> <code>m ≥ 4</code> &nbsp;⟹&nbsp;
(<code>f</code> im Klon &nbsp;⟺&nbsp; <code>f = min</code> oder <code>f = max</code>)</p>

E3 hängt an keiner festen Wertzahl — D und E1 stehen bei drei Werten, E2 bei vier. Der
Beweis verwendet kein `decide` und keine Fallunterscheidung über `m`; er läuft über sechs
Kantenfamilien mit geschlossenen Bruchstellen und eine Induktion über die Weglänge.

::: callout
**Die Schwelle liegt bei vier, und das ist kein Artefakt.** Bei drei Werten ist die Aussage
*falsch* — dort sind vier von acht Mustern zusammensetzbar. Bei zwei Werten gibt es
überhaupt keinen Zeugen, weil es nur eine Kontextur gibt. Das trifft Günthers eigene
Schwelle: das klassische zweiwertige System stellt noch keine Verbundkontextur dar, der
zweite Wert liefert nichts Neues und steht dem ersten unvermittelt gegenüber
(**quellen-fest**). Vermittlung beginnt bei drei — hier als gezählte Null, nicht als These.
:::

### 4 · Robustheit: wieviel jede Schranke beansprucht

Eine Nicht-Erzeugbarkeitsschranke hängt an ihrer Invariante. Wird die Signatur um Konstanten
erweitert, überlebt die Schranke genau dann, wenn die Invariante reflexiv ist.

| Zeuge | Invariante | überlebt Konstanten |
|---|---|---|
| D | eine Elementarkontextur | **nein** |
| E2, E3, E4 | Nachbarschaft mit gebrochenen Kanten | **ja** |

Eine Schranke, die an einer hinzugefügten Konstante fällt, beansprucht weniger, als sie zu
beanspruchen scheint. Die Prüfung ist im Korpus als Pflicht vor jedem neuen Zeugen
festgeschrieben.

---

## V · Die Anwendungsschicht, und was an ihr gemessen ist {#v}

Zwei Anwendungen liegen vor: eine Freigabepolitik über vier Autorisierungsstufen und eine
Quellenautorität über vier Evidenzstufen. Beide sind **Aggregat**.

**Die tragende Behauptung ist nicht, dass es sie gibt.** Sie lautet: die Anwendungen
**konsumieren** den generischen Satz, statt seinen Beweis nachzubilden. Das ist am Beweisterm
messbar und sonst nirgends, und es ist gemessen (**gemessen · Aggregat**):

| Satz | referenziert im Term | |
|---|---|---|
| `PolicyCheck.freigabe_nicht_erzeugbar` | `GCB.locally_classical_in_clone_iff` | **ja** |
| `RAGAuthority.autoritaet_nicht_erzeugbar` | `GCB.locally_classical_in_clone_iff` | **ja** |
| `PolicyCheck.freigabe_nicht_erzeugbar_konstanten` | `GCB.constant_clone_min_or_max` | **ja** |
| `RAGAuthority.autoritaet_nicht_erzeugbar_konstanten` | `GCB.constant_clone_min_or_max` | **ja** |
| `PolicyCheck.freigabe_lokal` (Gegenprobe) | dasselbe Ziel | **nein** |
| `RAGAuthority.autoritaet_lokal` (Gegenprobe) | dasselbe Ziel | **nein** |

**Die Gegenprobe ist der Punkt.** Eine Route, die überall *ja* meldet, misst nichts. Diese
unterscheidet, und zwar an den Voraussetzungslemmata derselben Dateien — am nächstliegenden
Nicht-Treffer und nicht an einem beliebig entfernten Gegenstück.

### Die Grenze im selben Atemzug

Die Schranke beisst auf linear geordneten Stufenträgern ab vier Stufen. Aus
Nicht-Erzeugbarkeit folgt **keine** Sicherheits-, Rechts-, Wahrheits- oder Retrievalgarantie.
Was der Satz sagt, ist: eine gemischte Politik ist nicht aus lokalen, kontexturblinden
Prüfern zusammensetzbar — in welcher Verschaltung und bis zu welcher Tiefe auch immer. Was
er nicht sagt, ist, dass die Politik richtig sei.

**Auf einem Verband gleichrangiger Rollen fällt die Schranke.** Auf dem kleinsten
nicht-distributiven Verband `M₃` — unten, drei unvergleichbare Elemente, oben — umfasst das
binäre Klonfragment 166 Operationen, davon sind bei sieben vergleichbaren Paaren **zehn lokal
klassisch, und acht davon sind weder Infimum noch Supremum** (**gerechnet**). Ein Zeuge ist
hinzuschreiben: die Operation, die auf den unteren Kanten das Supremum und auf den oberen das
Infimum wählt. Genau das Muster, das E3 auf linearen Skalen ausschliesst, ist hier
zusammensetzbar.

Ein Übergangsgraph benannter Rollen ohne Stufung wird von dieser Schranke **nicht** getragen;
was dort beweisbar bleibt, ist Erreichbarkeit, und die leistet ein Typsystem auch.

---

## VI · Der Ledger und das Register: die Begriffe und ihre Träger {#vi}

Günthers Begriffe stehen in einer Definitionenfassung mit neunzehn Paragraphen. Die Frage,
welcher Begriff welchen Lean-Träger hat, ist in dieser Ausgabe nicht mehr über den
Fliesstext verteilt, sondern **maschinell geprüft**.

Der Ledger führt **79 Zeilen**, davon **63 mit Träger** über 55 verschiedene Trägernamen,
und deckt **19 von 19 Paragraphen** ab (**gemessen**). Die Trägerstatus verteilen sich auf
45 Theoreme, 17 Definitionen, eine Setzung und **16 offene Zeilen**.

**Das Papier stellt diese Zuordnung nicht selbst her.** Es zeigt den Mechanismus, der sie
hält; die Tabelle steht in `docs/definition-ledger.md` und dort allein. Acht Regeln prüfen
sie, sechs davon beim Doc-Lint und zwei beim Bau:

- **R1, R2** (Bau): jeder genannte Träger löst in der Umgebung auf, und sein Trägerstatus
  stimmt mit der Deklarationsart überein.
- **R3** kein Zuordnungsstatus `Theorem` — ein Zuordnungsstatus ist redaktionell und nie
  compilergeprüft, und darf sich nicht so nennen.
- **R4** Trägerstatus `Offen` erzwingt eine leere Trägerspalte.
- **R5** alle neunzehn Paragraphen vertreten.
- **R6** Trägerstatus `Theorem` erzwingt eine Wachenangabe.
- **R7** jede Trägerzeile hat genau eine passende Referenz in der Referenzdatei, und
  umgekehrt; eine verwaiste Referenz ist ebenso ein Verstoss wie eine fehlende.
- **R8** jede Zeilen-ID kommt in beiden Dateien genau einmal vor.

R3 bis R8 setzen den Exit-Code des Lints; ein Verstoss macht den Lauf rot. **16 offene
Zeilen bleiben offen** — darunter die starke Definition 6 (L06-1) und die Wertbesetzung der
Morphogramme (L16-6). Eine offene Zeile ist kein Mangel des Ledgers, sondern seine Leistung.

### Das Setzungsregister

Setzungen verschwinden nicht, sie werden registriert. Gemessen trägt das Aggregat **32
Strukturfelder vom Typ `True`** (**gemessen · Aggregat**), gezählt per Umgebungsabfrage und
nicht per Textsuche. Sie zerfallen in zwei Klassen, die nicht dasselbe sagen:

- **30 Platzhalter** — eine verschobene Beweisschuld. Jeder braucht ein Exit-Kriterium: was
  müsste vorliegen, damit er fällt.
- **2 konstitutive Setzungen** — kein Beweis-Soll, dafür eine Begründung, warum keines
  besteht.

Die tragende Regel lautet nicht „das Aggregat enthält keine Setzung", sondern **kein Satz des
Aggregats hängt an einer Setzung**. Ein Feld vom Typ `True` kann in keinen Beweis eingehen;
warum es dennoch markiert sein muss, ist ein epistemisches und kein logisches Argument: was im
Aggregat steht, liest sich als zertifizierter Bestand.

Dazu eine stehende Probe: **keine Nicht-Projektion des Aggregats hat den Schluss `True`**
(**gemessen · Aggregat**, Wert 0). Sie verhindert Deklarationen, deren Name mehr behauptet als
ihre Aussage. Die Probe trägt ihre eigene Gegenrechnung: dieselbe Route meldet auf der
Projektionsseite 32 — einen Wert, dessen Antwort bekannt ist.

---

## VII · Bewegung und Zeit {#vii}

Über dem Gewebe liegt eine modale Trias als Bewegungsvorrat: **Verschiebung** — dieselbe
Struktur an anderer Stelle; **Umordnung** — dieselben Teile in anderer Ordnung;
**irreversible Setzung** — der Schritt, der nicht zurückgenommen wird. Ihre Kompositionen
sind in genau einer Richtung glatt; einen kanonischen Richtungstausch gibt es nicht.

Davor lohnt der Blick auf die Stelle, an der Günther der Sache zuerst begegnet ist. 1937
stellt er drei Sätze über Mächtigkeit nebeneinander, jeder für sich unmittelbar plausibel:
die Zeit ist mächtiger als der Wille; das Denken ist mächtiger als die Zeit; der Wille ist
mächtiger als das Denken. Nimmt man die ersten beiden zusammen, folgt, dass das Denken
mächtiger ist als der Wille — der dritte sagt das Gegenteil. Die drei schliessen sich zum
Kreis (**quellen-fest**, *Wahrheit, Wirklichkeit und Zeit*, Paris 1937).

**Was die Architektur daraus macht, ist ein Differential und keine These.** Bewiesen ist die
arme Seite: in jeder transitiven, irreflexiven Relation — auf jedem Träger, ohne Ausnahme —
ist ein Dreierzyklus unmöglich, und es gibt ebensowenig ein relationserhaltendes Bild eines
solchen Zyklus in eine strikte Ordnung. Dass Denken, Wille und Zeit sich so verhalten, wird
nicht behauptet; behauptet wird: **wenn** sie es tun, ist keine lineare Ordnung ihr Mass — und
zwar nicht, weil bisher keine gefunden wurde, sondern weil keine existieren kann.

<figure class="fig wide">
<div class="fig-scroll">
<svg viewBox="0 0 700 370" role="img" aria-label="Die drei Mächtigkeitssätze als intransitiver Zyklus">
  <defs><marker id="ah5" markerWidth="8" markerHeight="8" refX="7" refY="4" orient="auto">
    <path d="M0,0 L8,4 L0,8 z" fill="var(--stroke)"/></marker></defs>

  <circle class="box" cx="350" cy="62"  r="42" fill="var(--f05)"/>
  <circle class="box" cx="212" cy="222" r="42" fill="var(--f05)"/>
  <circle class="box" cx="488" cy="222" r="42" fill="var(--f05)"/>
  <g class="ts" text-anchor="middle">
    <text x="350" y="67">Denken</text><text x="212" y="227">Zeit</text><text x="488" y="227">Wille</text>
  </g>

  <line class="ln" x1="323" y1="95"  x2="239" y2="189" marker-end="url(#ah5)"/>
  <line class="ln" x1="255" y1="222" x2="443" y2="222" marker-end="url(#ah5)"/>
  <line class="ln" x1="461" y1="189" x2="377" y2="95"  marker-end="url(#ah5)"/>

  <g class="txs mut" text-anchor="end">
    <text x="248" y="128">die Erinnerung geht</text>
    <text x="248" y="142">zurück bis zum Anfang</text>
  </g>
  <g class="txs mut" text-anchor="middle">
    <text x="349" y="246">Entscheidungen fallen</text>
    <text x="349" y="260"><tspan class="i">in</tspan> der Zeit</text>
  </g>
  <g class="txs mut" text-anchor="start">
    <text x="452" y="128">„dass ich denke“ ruht auf</text>
    <text x="452" y="142">„dass ich denken <tspan class="i">will</tspan>“</text>
  </g>

  <text class="txs" x="350" y="172" text-anchor="middle">≻ heisst</text>
  <text class="txs i" x="350" y="186" text-anchor="middle">mächtiger als</text>

  <rect class="box" x="110" y="298" width="480" height="52" rx="5" fill="var(--f08)"/>
  <text class="txs" x="350" y="320" text-anchor="middle">Verkettet man die ersten beiden, folgt <tspan class="b">Denken ≻ Wille</tspan> —</text>
  <text class="txs" x="350" y="337" text-anchor="middle">die dritte sagt das Gegenteil. <tspan class="b">Der Zyklus schliesst sich.</tspan></text>
</svg>
</div>
<figcaption><span class="fignum">Figur 5</span> — Die drei Mächtigkeitssätze von 1937 und ihr
intransitiver Kreis. Bewiesen ist nicht der Kreis, sondern seine Unmöglichkeit in jeder
transitiven, irreflexiven Relation (<strong>bewiesen · Aggregat</strong>).</figcaption>
</figure>

### Die Träger dieses Abschnitts

Der tragende Satz des Mächtigkeitszyklus ist
`Proemial.IntransitivityDifferential.no_cycle_in_strict_order`
(**bewiesen · Aggregat**, Profil **axiomfrei**): in jeder transitiven, irreflexiven Relation
ist ein Dreierzyklus unmöglich. Dass ein solcher Zyklus auch kein relationserhaltendes Bild
in eine strikte Ordnung hat, trägt `cyc3_not_representable` (**bewiesen · Aggregat**,
`[propext]`); dass der Zyklus selbst besteht, tragen `cyc3_holds`, `cyc3_irrefl` und
`cyc3_not_transitive` (dieselben Marken). Alle sechs Sätze sind gewacht.

Der fehlende Richtungstausch ist `Proemial.NoUniformSwap.no_uniform_swap`
(**bewiesen · Aggregat**, `[propext, Classical.choice, Quot.sound]`, gewacht; der Aufruf von
`Classical.choice` stammt aus der Kategorien-Maschinerie und nicht aus eigener
Beweisführung). **Der volle Name mit Modul ist hier keine Pedanterie:** ein Satz gleichen
Namens liegt in `Diagnostics.SwapSatzProbe` — Bereich **Rufe-Target**, ungewacht, im Korpus
als historischer Beleg geführt. Wer den Namen ohne Modul nennt, lässt offen, welchen der
beiden er meint, und die zweite Achse läuft leer.

Die modale Trias liegt an zwei Orten. Dieser Abschnitt stützt sich auf
`F3e.ModalTwoCategoryWithPullbacks` (**Aggregat**); eine Fassung im eingefrorenen Zweig
(`PathC.ModalTwoCategory`, `PathC.ModalTwoCategoryNegation`) bleibt ausserhalb der
Default-Targets und trägt hier nichts.

---

## VIII · Die Sicherungen: Wachen, Profile, Bereiche {#viii}

Eine Architektur, die Unmöglichkeiten behauptet, muss sagen können, worauf ihre Beweise
ruhen — und verhindern, dass sich das still ändert.

### Der Stand

::: stand
| Kenngrösse | Wert | Bereich |
|---|---:|---|
| geprüft (AxiomGate) | **3018** Konstanten | Importbaum von `Reformulation`, namensgefiltert |
| Axiom-Wachen, geschrieben | **396** in 45 Dateien | `Reformulation/` **und** `Foreign/` |
| Axiom-Wachen, erzwungen | **386** in 44 Dateien | Import-Hülle der fünf Default-Targets |
| Statement-Pins | **44** | `Reformulation/` |
| Sätze | **726** | `Reformulation/` allein |
| `def` | **318** | `Reformulation/` |
| Build-Jobs | **1301** | die fünf Default-Targets zusammen |
| Dateien | **163**, davon 160 `.lean` | `Reformulation/` und `Foreign/` |
| **ausgewiesene Lücken** | **0** | Whitelist leer |
:::

**Zur Satzzahl gehört eine Warnung.** Sie vergleicht sich nicht mit der Zahl der vorigen
Ausgabe: dort stand eine Zahl über einen anderen Bereich, und die Zählroute ist seither
geweitet worden — sie verfehlte zuvor dreizehn `private`-Deklarationen und sechs mit Attribut
und zählte drei Zitate mit. Zwischen den beiden Zahlen liegen zwei Änderungen, und ein
Nebeneinander zeigte einen Zuwachs, den keine von beiden behauptet.

### Die vier Mechanismen

**Erstens, die Axiomwachen.** Zu jedem tragenden Satz wird das Axiomprofil gemessen und als
Erwartung eingefroren; verschiebt sich die Beweisbasis still, bricht der Bau. Die Wache
sichert die Basis, nicht den Wortlaut. Die Profilverteilung über alle 396 geschriebenen
Wachen (**gemessen**):

| Profil | Wachen |
|---|---:|
| `[propext, Quot.sound]` | 183 |
| `[propext]` | 84 |
| **axiomfrei** | **66** |
| `[propext, Classical.choice, Quot.sound]` | 61 |
| `[Quot.sound]` | 2 |

Die **66** beantwortet „wie viele der gewachten Profile sind axiomfrei" und nicht „wie viele
Sätze des Korpus sind axiomfrei"; die Bezugsgrösse 396 gehört daneben. `Classical.choice`
erscheint in 61 Profilen — nicht verboten, aber ausgewiesen.

**Zweitens, die Statement-Pins.** Wachen sichern die Basis, nicht die Formulierung; ein
geschwächter Satz mit gleichem Profil käme durch. Pins nageln den vollen Wortlaut fest und
brechen den Bau bei Definitionsdrift.

**Drittens, das globale Gate.** Es meldet:

```text
AXIOM-GATE GRÜN — Aggregat Reformulation (3018 geprüfte Konstanten)
zieht kein sorryAx. Whitelist leer.
```

**Viertens, und in dieser Ausgabe neu: die Bereichstrennung.** Fünf Targets bauen auf
`lake build`; fünf weitere laufen nur auf eigenen Ruf. Die Zusicherung des Gates gilt für
das Aggregat und für keinen anderen Bereich.

| Target | Jobs | Default |
|---|---:|---|
| `Reformulation` | 1274 | ja |
| `AxiomGate` | 1275 | ja |
| `DefinitionLedger` | 1275 | ja |
| `Probes` | 1212 | ja |
| `F1Coalgebraic` | 671 | ja |
| `ForeignPeresMermin` | 677 | nein |
| `Diagnostics` | 1506 | nein |
| `MathlibExtensions` | 1289 | nein |
| `PreC` | 1242 | nein |
| `PathC` | 1388 | nein |
| **`lake build` ohne Argument** | **1301** | die fünf zusammen |

**Diese Tafel ist nicht zu addieren, und sie zeigt selbst, warum.** Die fünf Default-Targets
summieren sich auf 5707 Jobs; der gemeinsame Bau braucht 1301. Der Faktor 4,4 ist die
Überlappung der Import-Hüllen. Wer Bauausgaben mehrerer Targets summiert, zählt Module
mehrfach.

### Was ein fremder `grep` findet

Wer im Baum nach `sorry` sucht, findet drei Zahlen, und jede beantwortet eine andere Frage
(**gemessen**): **123** rohe Wortvorkommen über den ganzen verfolgten Bestand, **95** in den
Lean-Quellen, **27** betroffene Deklarationen in acht Dateien. Die dritte ist die tragende;
die ersten beiden zählen Prosa mit — Einfriervermerke, Doc-Strings, die Wendung „sorry-frei".

Innerhalb der Lean-Quellen verteilen sich die 95 auf `PathC/` 53, `Proemial/` 27,
`Reformulation/` 5, `Diagnostics/` 5, `F3e/` 4, `F3f/` 1.

**Zum eingefrorenen Zweig gehören zwei Sätze, und beide sind wahr.** Das Target `PathC`
baut grün, 1388 Jobs — und genau ein Modul des Zweiges liegt in keiner Target-Wurzel und
übersetzt nicht. **Keine der beiden Aussagen ist eine Lückenfreiheitszusage:** grün heisst
hier *übersetzt*, nicht *lückenfrei*, und für ein Rufe-Target gibt es kein AxiomGate.
Derselbe Zweig trägt 53 der 95 Vorkommen.

### Replizierbarkeit

Ein grüner Bau im Arbeitsverzeichnis sagt „grün bei mir". Gemessen ist mehr: aus einem
frischen, anmeldungsfreien Klon des öffentlichen Standes baut der Baum in 39 Sekunden grün
durch, **126 Module gebaut und 0 wiedereingespielt**, mit derselben Gate-Zeile und leerer
Whitelist (**gemessen**). Es ist ein wirklicher Bau und kein Abspielen eines Zwischenstands.

Die Zahl 126 ist zugleich der Umfang der Import-Hülle der fünf Default-Targets, aus den
`import`-Zeilen gerechnet. **Beide Listen sind als Menge verglichen und gleich** — der `diff`
der sortierten Modulnamen ist leer (**gemessen**). Die zwei Wege teilen keinen Schritt: der
eine liest Quelltext und folgt `import`-Zeilen transitiv, der andere liest die Bauausgabe
eines frischen Klons.

Die Bereichskarte über alle 161 Projektmodule (**gemessen**):

| Bereich | Module |
|---|---:|
| Aggregat | 126 |
| Rufe-Target | 34 |
| von keinem Target erfasst | 1 |

Quer dazu liegen 18 Module im eingefrorenen Zweig; zwei davon werden über ein Rufe-Target
gebaut, und eines wird von keinem Target erreicht — es ist dasselbe Modul, das nicht
übersetzt. **Der Bereich ist nicht am Verzeichnis abzulesen:** das Target des eingefrorenen
Zweiges erreicht sechs Module unter `MathlibExtensions/`, die über ihr eigenes Target grün
bauen und nicht eingefroren sind.

Dass die zehn nicht erzwungenen Wachen sämtlich in einer Datei ausserhalb der Hülle liegen,
ist der Grund, warum „erzwungen = 386" über die **Hüllenroute** und nicht über die
Verzeichnisgrenze begründet wird: dass beide heute denselben Wert liefern, ist eine
Koinzidenz und keine Identität.

---

## IX · Die Instrumente als eigener Gegenstand {#ix}

Neben den Theoremen ist etwas entstanden, das von Günther nichts weiss und weiterreisen
könnte: eine Prüfpraxis für die Formalisierung philosophischer Texte. Wer einen Denker
formalisiert, hat ein Problem, das die reine Mathematik nicht kennt — **die Deutung
überholt den Term**. Ein Theorem wird gebaut, sein Name gewählt, und der Name beansprucht
mehr als das Theorem. Gegen dieses Gefälle helfen keine Vorsätze, nur Mechanismen.

### Regeln, jede aus einem Fehlgriff

1. **Zuerst den Satz suchen, dann nur so viel Träger bauen, wie der Satz verlangt.** Eine
   Grundschicht, die kein Satz anfordert, ist eine Umbenennung der Bibliothek.
2. **Ein Probebau vor jeder Spezifikation, in der Zielumgebung.**
3. **Die Spezifikation nennt Ziel, Auflagen und Fallstricke — nicht die Verschaltung.**
4. **Spezifikationen werden ebenfalls begutachtet, nicht nur Baue.**
5. **Eine Zählroute, die Prosa als Kriterium nimmt, ist eine Zeitbombe.**
6. **Aggregat heisst setzungsfrei.** Eine Datei kommt in den zertifizierten Bestand, wenn sie
   keine Setzung trägt — nicht, wenn der Aufwand klein ist.
7. **Der Titel überholt das Theorem.**
8. **Eine Route wird gegengerechnet, bevor ihr Ergebnis in ein Dokument geht** — an einem
   Fall, dessen Antwort aus dem Quelltext bekannt ist.
9. **Eine Messprobe prüft eine Gleichung, nicht eine Zahl.**
10. **Wertgleichheit zweier Routen ist kein Beleg für Mengengleichheit.** Gemessen: zwei
    Routen lieferten beide 49 und hatten keine Zeile gemeinsam.
11. **Bauausgaben mehrerer Targets werden nicht summiert.**

### Der Lint

Ein Doc-Lint prüft drei Gruppen über Markdown und Lean-Quellen. Gruppe (A) sucht
Rangansprüche und **meldet** — derzeit 38 Treffer, jeder einzeln beurteilt, keiner mit einer
Bezugsmenge ausserhalb des eigenen Bestands. Gruppe (B) sucht einen bestimmten
begrifflichen Rückfall in der Nähe von Mengenlehre-Stichworten und meldet 0. Gruppe (C)
prüft die Ledger-Regeln R3 bis R8 und **setzt den Exit-Code**.

::: callout
**Nachtrag vom 2. August 2026.** Die hier genannten Lintzahlen sind am Commit
`e5ef3d7` gemessen und mit der damals geltenden Route exakt reproduzierbar. Die
Route ist seither in drei Punkten korrigiert worden: sie war fallempfindlich, ihre deutschen
Stichwörter trafen keine transliterierten Schreibweisen, und sie las die HTML-Fassungen nicht.
Die Trefferzahl der Gruppe (A) ist darum eine untere Schranke und keine Zählung gewesen. Die
Null der Gruppe (B) war ein Artefakt der Route; seit der Korrektur ist sie eine Zählung, und
ihr Grund lässt sich nennen: im gesamten Prüfbereich steht genau eine Zeile, in der das
bewachte Stichwort überhaupt vorkommt, und es ist die Zeile, die den Lint beschreibt. Gruppe
(B) ist damit eine Wache ohne Gegenstand. Das ist ihre Arbeit, aber es ist kein Beleg.
:::

Die Aufteilung ist Absicht: ein Ranganspruch will gelesen und nicht erzwungen werden — ein
brechender Lint wird umgangen, ein meldender wird gelesen. Ein Widerspruch zwischen Tabelle
und Referenzdatei dagegen ist objektiv falsch, und wer ihn stehen lässt, veröffentlicht
eine ungeprüfte Tabelle.

### Die Fehlerliste

**Der Beleg dafür, dass die Prüfschichten beissen, ist die Fehlerliste** — und sie wird
fortgeschrieben, nicht gekürzt. Aus dem Block, der zu dieser Ausgabe führte:

- Eine Route mit `\b` in einer Werkzeugbetriebsart, die Wortgrenzen nicht führt: Ergebnis
  0 statt 153. Kein falsches Ergebnis, sondern ein leeres — und ein leeres sieht aus wie
  eine gute Nachricht.
- Eine Zählung mit `grep -c`, die Zeilen statt Vorkommen zählt: ein über einen
  Zeilenumbruch laufender Treffer fiel heraus, fünf statt sechs.
- Eine Anleitung im Imperativ, gelesen als Zustandsbeschreibung: „geht ohne weiteres Zutun
  live" stand unter der Überschrift „Einschalten".
- Eine Route, die vor und nach einem Zustandswechsel dasselbe meldet und den Wechsel darum
  nicht misst — ihr Ergebnis war zufällig richtig. Getragen hat den Befund die zweite
  Route. Wer zwei Routen führt, überlebt den Ausfall einer.
- Eine Herkunftsangabe für zwei Zahlen, die auf das falsche Dokument zeigte.
- Fünf geschätzte statt sechzehn gezählte Vorkommen eines Namens.

**Keiner dieser Fehler wurde von der Instanz gefunden, die ihn gemacht hat.**

---

## X · Reichweite und Grenze {#x}

Was diese Architektur behauptet, ist bedingt und wird als bedingt geführt. Sie verspricht
nicht, den Skeptiker zur Anerkennung einer Irreduzibilität zu zwingen; sie verspricht, ihn
zu **symmetrisieren** — von der bequemen Position *das reduziert sich auf Bekanntes* zur
ausdrücklichen Position *ich setze die eine umfassende Logik*, die selbst eine Setzung ist
und als solche keinen Vorrang mehr hat.

### Die drei Grenzen

**Erstens, mathematisch: `M₃`.** Die Charakterisierung lebt auf linear gestuften Trägern und
fällt auf Verbänden gleichrangiger Elemente. Das ist keine Beweislücke, sondern ein
Gegenbeispiel — und die Bruchstelle ist genau die Verbandsform, die eine Architektur
gleichrangiger Rollen hätte.

**Zweitens, hermeneutisch: die Identifikation.** Dass die zweielementige Wertmenge Günthers
Elementarkontextur *ist*, entscheidet kein Theorem. Die Setzung steht auf begründetem Boden
— Abgeschlossenheit unter den lokalen Operationen ist ein sachlicher Grund — bleibt aber eine
Wahl.

**Drittens, grundsätzlich: die Spontaneität des Vollzugs.** Nicht der Wille als Funktion,
sondern allein das *Dass* des Vollzugs ist kein Strukturmerkmal; es gibt kein ärmeres
Modell, in dem es als Position fehlt, weil es keine Position ist.

### Was nicht gebaut ist

Die **proemiale Relation** — der Kern von Günthers Theorie — ist nicht formalisiert. Die
**Verbundkontextur** liegt als Zahlenfolge vor und ist nicht als Begriff gebaut. Die starke
**Definition 6** ist offen und wird als offen geführt. Die **Wertbesetzung der
Morphogramme** ist eine offene Ledger-Zeile. **Sechzehn Ledger-Zeilen** stehen auf `Offen`,
und sie sollen dort stehen bleiben, solange kein Träger sie trägt.

Eine Anmerkung, die in der Sache selbst liegt: die Definitionenfassung gibt für
Verbundkontexturen die Formel `n(n+1)/2` und die Folge `1, 3, 6, 10, …` und sagt zugleich,
eine Verbundkontextur brauche mindestens drei Werte. Beides stimmt nicht zusammen; die erste
Verbundkontextur ist die dreiwertige, die `1` gehört zur Ontologienfolge. Die Architektur
zählt die Elementarkontexturen eines `m`-wertigen Systems als `m(m-1)/2`; das ist mit
Günthers Reihe verträglich, aber eine **Festlegung** und keine Ableitung.

### Das Bild

Ein Grund, der Wiederholung zählt und dessen Normalisierung als Prozedur gebaut ist; Logiken,
deren Trennung nicht gesetzt, sondern bewiesen ist — in einer Form, die Günthers Grundfall
standhält; eine Beweisform, die ihre schwere Hälfte kennt und trägt; eine Zeugenreihe, die
von einer Existenzbehauptung zu einer Charakterisierung ohne feste Wertzahl gewachsen ist;
eine Anwendungsschicht, deren Konsum am Term gemessen ist; ein Ledger, der neunzehn
Paragraphen compilergeprüft hält und sechzehn Zeilen offen lässt; ein Gate ohne `sorryAx`;
und drei Grenzen, von denen keine eine Niederlage ist.

::: callout
**Was gesetzt ist, steht am Anfang; was bewiesen ist, ist gezählt; was Deutung ist, heisst
so.**
:::

---

## Anhang · Zählrouten {#anhang}

Damit die Zahlen nachrechenbar und nicht bloss glaubhaft sind, trägt jede ihre Route. Alle
Angaben gelten am Commit `e5ef3d7`; jeder Bauzug macht jede ausgestellte Zahl still veraltet,
weshalb sie ihren Stand mitführt.

| Grösse | Wert | Route |
|---|---:|---|
| geprüfte Konstanten | 3018 | Bauausgabe des AxiomGate |
| Wachen geschrieben | 396 / 45 Dateien | `grep -rE '#guard_msgs.*in #print axioms'` über `Reformulation/` und `Foreign/` |
| Wachen erzwungen | 386 / 44 Dateien | dieselbe Route, eingeschränkt auf die Import-Hülle der fünf Default-Targets |
| Import-Hülle | 126 von 161 Modulen | `import`-Zeilen ab den 21 Target-Wurzeln transitiv verfolgt |
| axiomfreie Profile | 66 von 396 Wachen | `grep -rc 'does not depend on any axioms'` |
| Profilverteilung | 183 / 84 / 66 / 61 / 2 | jede Wache einzeln gelesen; Summe 396 als Gleichung geprüft |
| Sätze | 726 | <code>grep -rhE '^((private&#124;protected&#124;nonrec) +)?(@\\[[^]]*\\] +)?(theorem&#124;lemma) '</code> über `Reformulation/` |
| `def` | 318 | dieselbe Weitung für `def` |
| Statement-Pins | 44 | `grep -rc '^-- STATEMENT-PIN'` |
| Build-Jobs | 1301 gemeinsam | Bauausgabe je Target, **nicht summiert**; je Target siehe oben |
| Dateien | 163 / 160 `.lean` | Dateizählung über `Reformulation/` und `Foreign/` |
| `sorry`-Vorkommen | 123 / 95 / 27 | Wortgrenze `\bsorry\b`, Vorkommen (nicht Zeilen), über `git ls-files` |
| Setzungsfelder | 32 = 30 + 2 | Umgebungsabfrage über Strukturfelder und Projektionen |
| Nicht-Projektionen mit Schluss `True` | 0 | dieselbe Route, Projektion verneint; Gegenprobe liefert 32 |
| Ledger | 79 Zeilen / 63 Paare / 19 von 19 | Doc-Lint Gruppe (C) |
| Lint | (A) 38, (B) 0, (C) 0, Exit 0 | ein Lauf |
| Konsum der Anwendungen | 4 Treffer / 2 Nicht-Treffer | Umgebungsabfrage mit expliziter `ConstantInfo`-Musterung über Typ und Beweisterm |
| Klonbau | 1301 Jobs, 126 gebaut / 0 wiedereingespielt | `git clone`, `lake exe cache get`, `lake build`, anmeldungsfrei |
| Klonfragment `{min,max,neg}` | 82 bei `m` = 3, 4, 5, 6 | Abschluss von `{p₁,p₂}` unter punktweisem Min, Max, Ordnungsumkehr |
| lokal klassisch im Klon | 4 von 8 · 2 von 64 · 2 von 1024 · 2 von 32 768 | dieselbe Aufzählung, gefiltert auf lokale Klassizität |
| `M₃` | 166 Klonglieder, 10 lokal klassisch, 8 davon weder Infimum noch Supremum | Abschluss unter Infimum, Supremum, Ordnungsumkehr auf dem fünfelementigen Verband |

**Drei Regeln zum Zählen.** Erstens: gezählt wird über die Schale, nicht mit einer
Bibliotheksfunktion, die Leerzeilen überspringt. Zweitens: **Aggregat- und Korpuszahlen
werden getrennt geführt**; das Aggregat ist der zertifizierte Importbaum, der Korpus umfasst
zusätzlich die Sonden, die eine markierte Setzung tragen. Drittens: **Bauausgaben mehrerer
Targets werden nicht summiert** — die 5707 aus §VIII steht dort, damit sie nirgends sonst
steht.

### Zwei Punkte, die diese Ausgabe geschlossen hat

**Die Gleichheit der beiden Modullisten ist als Menge geprüft**, nicht nur als Zahl: die
sortierten Modulnamen der Import-Hülle und der Built-Zeilen des Klonbaus wurden verglichen,
der `diff` ist leer. Damit trägt die Zeile „Wachen erzwungen" — die Route schränkt auf
genau die Menge ein, die der Bau anfasst.

**Die Bereichsangaben in §VII liegen vor** und stehen dort. Die Träger sind mit vollem Namen
und Modul genannt, weil ein Satzname des Abschnitts zweimal im Baum vorkommt — einmal im
Aggregat und gewacht, einmal in einem Rufe-Target und ungewacht.

---
