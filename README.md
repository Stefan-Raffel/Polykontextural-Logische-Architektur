# Reformulation - Polykontexturale Logik in Lean 4

Formale Begleitung des Projekts zur Reformulierung der polykontexturalen Logik
Gotthard Guenthers. Der Code ist kein Beweis der Theorie, sondern ein Pruefwerkzeug:
er trennt, was aus klassischen Mitteln erzeugbar ist, von dem, was es nicht ist -
und macht die Grenze zwischen Beweis, Setzung und Deutung maschinell nachpruefbar.

Lean `4.30.0-rc2`, Mathlib. Bau mit `lake build`.

---

## Stand

| Kennzahl | Wert |
|---|---:|
| geprueft (AxiomGate) | 2697 Konstanten |
| Axiom-Wachen | 221 ueber 25 Dateien |
| Saetze gesamt | 621 |
| Build-Jobs | 1262 |
| ausgewiesene Luecken | 4 (gewhitelistet) |

Kennzahlen gezaehlt am gruenen Build, Stand Commit `4c46257`.

---

## Struktur

| Bereich | Dateien | Saetze | Gegenstand |
|---|---:|---:|---|
| `Proemial/` | 45 | 328 | Proemialrelation, Transjunktion, Klon-Schranken |
| `PathC/` | 18 | 94 | Weg C - iterative Doppelbeschreibung |
| `Kenogram/` | 4 | 88 | Kenogrammatik: RGS, Normalform, Operationssemantik |
| `F1/` | 20 | 22 | Belegungen, Faserungen, Cross-Chain-Anschluss |
| `F3a`-`F3g/` | 32 | 72 | Stufen, Modaloperatoren, Uebergangsklassen |
| `PreC/`, `Diagnostics/`, `MathlibExtensions/` | 16 | 17 | Vorbereitung, Messung, Zusatzlemmata |
| `Foreign/` | 1 | - | fremd gestellter Fall (Peres-Mermin) |

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
bricht bei jeder nicht gewhitelisteten Luecke. Die vier bekannten Klasse-D-Luecken sind:

```
F3e.beckChevalleyFromData
F3e.beckChevalley_exists
F3e.beckChevalley_unique
Proemial.belegung_specialization_cognitive
```

Zusaetzlich frieren 221 `#guard_msgs`-Wachen die gemessenen Axiom-Profile ein: aendert
ein Satz sein Profil, bricht der Bau. `Classical.choice` ist auf wenige Dateien begrenzt
und dort ausgewiesen.

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
lake build                 # vollstaendig; AxiomGate laeuft mit
```

Axiom-Profile einzelner Saetze ohne Neubau:

```sh
echo 'import Reformulation.Proemial.NonUniformCloneBound' > /tmp/a.lean
echo '#print axioms Reformulation.Proemial.NonUniformCloneBound.W_not_in_clone' >> /tmp/a.lean
lake env lean /tmp/a.lean
```

`.lake/` umfasst rund 7,5 GB und ist ausgeschlossen; der Quellbestand sind ~155 Dateien
unter 1 MB.

Bau-Konventionen fuer beitragende Instanzen: siehe `CLAUDE.md`.
