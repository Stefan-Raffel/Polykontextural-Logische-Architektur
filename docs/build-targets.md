# Build-Targets — was ein gruener Bau je Target zusichert

`lake build` erfasst die Import-Huelle der `defaultTargets`. Alles andere wird nur auf
ausdruecklichen Aufruf uebersetzt. Diese Datei sagt fuer jedes Target, **was gruen
heisst — und was es nicht heisst**.

Bis zum Buildabdeckungs-Zug C2 lagen 52 Module in gar keinem Target: ein Bruch dort fiel
bei keinem Bau auf, und eines von ihnen war unbemerkt rot. C2 legt sechs Targets an und
nimmt zwei davon in die Defaults — genau die beiden, die Aggregat-konsumierende Module
tragen.

Alle Zahlen dieser Datei haengen an Commit und Zaehlroute; sie sind am gruenen Bau
gemessen, nicht geschaetzt. Stand: Commit `f2aac24` zuzueglich dieses Zuges, gemessen am
28. Juli 2026.

---

## Tafel

| Target | Mitglieder | in `defaultTargets` | Bauzeit |
|---|---:|:--:|---:|
| `Reformulation` | 103 | ja | nicht kalt gemessen |
| `AxiomGate` | 1 | ja | nicht kalt gemessen |
| `DefinitionLedger` | 1 | ja | nicht kalt gemessen |
| `Probes` | 16 | **ja** | 7,7 s |
| `F1Coalgebraic` | 2 | **ja** | 3,0 s |
| `Diagnostics` | 2 | nein | 2,6 s |
| `MathlibExtensions` | 8 | nein | 6,3 s |
| `PreC` | 6 | nein | 4,6 s |
| `PathC` | 17 | nein | 12,0 s |
| `ForeignPeresMermin` | 1 | nein | nicht kalt gemessen |
| *(von keinem Target erfasst)* | 1 | — | — |

**Zur Bauzeit.** Gemessen wurde je Target so: die Bauartefakte der Target-Mitglieder
entfernen, dann `lake build <Target>` als Ganzes. Mathlib und das Aggregat lagen dabei
gebaut vor; die Werte sind also die Kosten des Targets **oberhalb** eines warmen Standes,
nicht die eines Kaltbaus. Die drei Aggregat-Targets sind nicht kalt gemessen — C2 misst
die sechs neuen. `lake build` als Ganzes: **1298 Jobs**; mit kalten `Probes` und
`F1Coalgebraic` 8,1 s, vollstaendig warm 1,0 s. Die Aufnahme der beiden Targets in die
Defaults kostet also einmalig rund sieben Sekunden und danach nahezu nichts, weil Lake
repliziert.

---

## Zusicherung je Target

### `Reformulation` — das Aggregat, 103 Module

*Gruen heisst:* der zertifizierte Bestand uebersetzt.

Die eigentliche Zusicherung dieses Targets ist nicht der gruene Bau, sondern die
AxiomGate-Zeile (siehe unten). Sie bleibt die einzige Zusicherungszeile des Baus; die
uebrigen Targets melden nur Erfolg oder Bruch.

### `AxiomGate` — 1 Modul

*Gruen heisst:* der Axiom-Abschluss des Aggregats zieht kein `sorryAx`, und die Whitelist
ist leer. Das Gate meldet die Zahl der geprueften Konstanten in einer Zeile des Bau-Logs.

### `DefinitionLedger` — 1 Modul

*Gruen heisst:* die Traegerspalte von `docs/definition-ledger.md` stimmt mit der
Aggregatumgebung ueberein (R1), und der Traegerstatus passt zur Deklarationsart (R2).
Die Datei traegt keinen Satz.

### `Probes` — 16 Sonden und Zeugenregister

15 Module unter `Proemial/` plus `Diagnostics/HeteroreferenzProbe.lean`.

*Gruen heisst:* die Sonden uebersetzen gegen den aktuellen Aggregatstand, und ihre
13 Axiom-Wachen halten.

*Gruen heisst nicht:* dass sie setzungsfrei sind — `AsymmetricDiscontexturalTransition`
traegt `contextureCrossing : True`; und nicht, dass eine Sonde einen Satz belegt, den das
Aggregat traegt. Sondierungen bleiben Sondierungen.

*Warum in den Defaults:* 13 der 16 konsumieren Aggregatmodule und koennen durch eine
Aenderung *am Aggregat* brechen. `HeteroreferenzProbe` liegt seinem Gegenstand nach hier
und nicht bei den Messwerkzeugen; ohne diesen Wechsel waeren
`Proemial.InteractiveTransjunction` und `Proemial.SubstantialTransjunction` die einzigen
beiden Aggregatmodule, deren Bruch von keinem default-gebauten Modul bemerkt wuerde.

Die 13 Wachen dieses Targets standen seit ihrer Niederlegung geschrieben, wurden aber nie
ausgefuehrt: `AsymmetricDiscontexturality` 7, `TowerAsymmetryProbe` 4,
`AsymmetricDiscontexturalTransition` 2. Seit C2 erzwingt der Bau sie.

### `F1Coalgebraic` — 2 Substanzstudien

`F1/D2/Rollups/Coalgebraic/Substantial.lean` und `…/SubstantialRev2.lean`.

*Gruen heisst:* uebersetzt gegen den aktuellen F1/F3-Stand.

*Warum in den Defaults:* beide konsumieren Aggregatmodule.

### `Diagnostics` — 2 Messwerkzeuge

`AxiomProbe` und `SwapSatzProbe`.

*Gruen heisst:* die Messsonden laufen. Sie erzeugen Messwerte, keine Saetze; ein gruener
Bau sagt ueber den Korpus nichts, nur ueber die Messbarkeit.

*Warum nicht in den Defaults:* keines der beiden konsumiert eine Aggregatkonstante, keines
kann also durch eine Aenderung am Aggregat brechen. `SwapSatzProbe` zieht dabei ueber
tausend Mathlib-Module nach, die im Aggregat nicht vorkommen. Die Aufnahme kaufte Bauzeit
fuer null Regressionsschutz.

### `MathlibExtensions` — 8 Zusatzlemmata

*Gruen heisst:* uebersetzt und sorry-frei. Bibliothekscharakter, kein PKL-Gehalt; die
Gruppe ist der Kandidat fuer einen spaeteren Mathlib-Beitrag.

### `PreC` — 6 Module des Vorbereitungszweigs

*Gruen heisst:* uebersetzt und sorry-frei.

*Nicht:* dass der Zweig noch aktuell ist — er ist der Stand vor Weg C und wird nicht
fortgeschrieben.

### `PathC` — 17 der 18 Module, ohne `Classifying/Universal`

***Gruen heisst ausschliesslich: es uebersetzt.***

Der Zweig traegt **25 `sorry` in 8 Dateien** und null Wachen; ein gruener Bau sagt darueber
nichts. Diese Zeile ist die wichtigste der ganzen Datei, weil `PathC` der Zweig ist, bei
dem die Verwechslung von „gruen" mit „bewiesen" schon einmal vorgekommen ist.

Verteilung der 25: `ClassifyingEquivalence` 8, `TermSemantics` 5, `ModelFunctor` 3,
`Soundness` 3, `Formula` 2, `ModalTwoCategoryNegation` 2, `ClassifyingTopos` 1,
`GeometricTopology` 1.

### `ForeignPeresMermin` — 1 Modul

*Gruen heisst:* der fremd gestellte Fall (Peres-Mermin) uebersetzt und seine 10
Axiom-Wachen halten.

*Warum nicht in den Defaults:* das Modul liegt ausserhalb des Aggregats, wird von
`Reformulation` nicht importiert und vom AxiomGate (Namensfilter `Reformulation.*`) nicht
gefasst; es zieht 677 Jobs. Es laeuft ueber `lake build ForeignPeresMermin`. Seine 10
Wachen sind darum geschrieben und pruefbar, aber vom Default-Bau nicht erzwungen — das ist
die verbleibende Differenz zwischen geschriebenen (382) und erzwungenen (372) Wachen, und
sie gehoert ausdruecklich dorthin.

---

## Von keinem Target erfasst

### `Reformulation/PathC/Classifying/Universal.lean`

Das Modul uebersetzt nicht. Gemessen am 28. Juli 2026, Commit `f2aac24`, Exit 1 nach 2,3 s.
Erste Fehlermeldung verbatim:

```
error: Reformulation/PathC/Classifying/Universal.lean:49:4: failed to synthesize instance of type class
  Limits.HasColimitsOfShape (Discrete PEmpty.{1}) E
```

Es liegt in **keinem** Target, und das ist eine Entscheidung, keine Nachlaessigkeit: naehme
man es in `PathC` auf, waere `lake build PathC` dauerhaft rot und als Regressionsprobe
wertlos — es koennte keinen *neuen* Bruch mehr anzeigen.

Drei Beobachtungen, keine davon eine Reparatur:

* Das Modul traegt **null `sorry`**. Der Bruch ist kein markierter Rest, sondern ein
  fehlender Instanzenschluss — vermutlich Folge einer Mathlib-Verschiebung, die niemand
  bemerkt hat, weil das Modul nie gebaut wurde.
* **Niemand importiert es.** `Universal.lean` ist ein Blatt; kein anderes Modul im Korpus
  haengt daran. Der Bruch hat sich nirgends fortgepflanzt.
* Von den 52 Modulen ohne Targetzugehoerigkeit uebersetzen 51; dieses nicht. Die
  Nachmessung in C2 hat gegenueber C1 kein zweites rotes Modul gefunden.

Die Reparatur gehoert zu Phase 2 (PathC-Status), zusammen mit der Entscheidung ueber den
Zweig als ganzen. Bis dahin wird das Modul hier gefuehrt, mit Fehlermeldung und Messdatum.

---

## Zaehlrouten

* **Modulinventar:** Import-Huelle ueber `^import <Modul>` der Quelldateien, eingeschraenkt
  auf `Reformulation.*` und `Foreign.*`; Targetzugehoerigkeit aus `lakefile.toml`. Kein
  `lean_lib` traegt eine `globs`-Angabe, also gilt ueberall der Default `Glob.one`: erfasst
  wird jede angegebene Wurzel samt ihrer transitiven Import-Huelle, sonst nichts.
* **Kopplung an das Aggregat:** auf Konstanten-Ebene, nicht auf Import-Ebene — ein Modul
  gilt als gekoppelt, wenn eine seiner Deklarationen eine Konstante aus einem Aggregatmodul
  referenziert. Gemessen per Umgebungsabfrage ueber `getUsedConstants` und
  `env.getModuleIdxFor?`. Ein blosser `import` ohne Referenz zaehlt nicht.
* **Wachen erzwungen:** `grep -rE '#guard_msgs.*in #print axioms'` ueber `Reformulation/`
  und `Foreign/`, eingeschraenkt auf die Import-Huelle der `defaultTargets`. Die Anwesenheit
  einer `.olean` ist **kein** Nachweis, dass ein Modul vom Bau erfasst wird — Waisen tragen
  `.olean`-Dateien aus frueheren Einzelbauten.
