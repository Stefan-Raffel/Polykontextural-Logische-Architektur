import Reformulation.Proemial.NegationCycle

/-!
# Proemial.NegationCycleTable — die Tafel der vierwertigen Vollkreise: mindestens vierundvierzig (Stufe 2a)

**ERTRAG mit benannter Grenze.** Gebaut auf Anordnung des Architekten vom 21. September 2026
nach `KorpusRev2/Spec_NegationCycle_Stufe2.md` (Mathematiker), Stufe **2a**. Günther zählt
die vierwertigen Vollkreise: *„Von diesen Kreisen gibt es, wenn man Drehsinn und
Gegen-Drehsinn als einen Kreis rechnet, 44 Exemplare"* (1980, S. 20; ebenso IGN S. 41: „44
Totaläquivalenzen der Negativität"). Dieses Modul zeigt die **untere Hälfte** seiner Zahl:
es schreibt 44 Folgen aus und beweist von ihnen, dass sie Vollkreise und paarweise
verschieden sind — auch als Kreise, nicht nur als Folgen.

**Die obere Hälfte — dass es nicht mehr als 44 sind — ist nicht gebaut** und ist Stufe 2b
der Spec. Der Kopf sagt darum **mindestens 44**, nie „genau 44".

Die Sätze:

* `alleKreise_length`, `alleKreise_full`, `alleKreise_nodup`, `alleKreise_no_reverse` —
  zusammen die Aussage: **44 Vollkreise, paarweise verschieden modulo Drehsinn**. Der letzte
  ist der tragende: zwei Folgen, die dieselbe Kreisfigur in verschiedenem Drehsinn
  durchlaufen, wären zwei Folgen und ein Kreis; hier ist keine die Umkehrung einer anderen.
* `alleKreise_families` — jede der 44 trägt eine von Günthers vier Verteilungen
  (10-9-5, 5-9-10, 6-12-6, 9-6-9; er rechnet die ersten beiden zu einer Familie, IGN S. 43).
* `alleKreise_no_888` — **keine der 44 verteilt 8-8-8.** Das ist Günthers „alle drei
  Operatoren dürfen sich niemals gleich oft wiederholen" (IGN S. 43) **an diesen 44**, nicht
  als Unmöglichkeitssatz; siehe die Grenze unten.
* `guenthers_mem` — Günthers drei ausgeschriebene Kreise sind unter den 44.
* `gerichtet_length`, `gerichtet_full`, `gerichtet_nodup` — **die 88 gerichteten**: mit jedem
  Kreis sein Gegen-Drehsinn, und alle 88 Folgen sind verschieden. `gerichtet_full` ist
  bewiesen, nicht entschieden — es konsumiert `NegationCycle.reverse_full`.

## Woher die 44 kommen — und was daran gerechnet ist

```text
kreis1, kreis2, kreis3   GÜNTHER-EIGEN, aus IGN S. 44-45 (kreis2 emendiert, siehe dort)
die übrigen 41           GERECHNET, ausserhalb des Korpus (erschöpfende Tiefensuche
                         über die 24 Wertfolgen, Quelltext in
                         KorpusRev2/Vollzug_NegationCycle_Stufe2a_Impl.md)
```

Die Trennung steht **in der Definition**, nicht nur im Kopf: `alleKreise = guenthers ++
gerechnet`. Günther schreibt nur drei aus und sagt von den übrigen, sie seien „später von
Computer errechnet worden" (1980, S. 20) — die 41 hier sind nicht seine, sondern unsere,
und sie stimmen mit seiner **Zahl** überein, nicht nachweislich mit seiner **Liste**.

## Was dieses Modul NICHT sagt

* **Nicht „genau 44".** Die Vollständigkeit ist Stufe 2b, ungebaut. Alles hier ist eine
  untere Schranke.
* **Nicht Günthers Unmöglichkeitssatz.** `alleKreise_no_888` spricht über diese 44. Günthers
  „niemals" spricht über alle Vollkreise und folgt erst aus 2b. *Der Mathematiker hat am
  21. September gemessen, dass ein Paritätsargument ihn nicht liefern kann: 8-8-8-Folgen
  kehren durchaus zum Ausgang zurück (12,6 % einer Stichprobe von 200 000), sie sind nur
  nicht vollständig.*
* **Nicht Tafel XX** (IGN S. 50, die Kreiszahlen je Umfang) — ausserhalb nachgerechnet und
  richtig, hier kein Satz; Stufe 2c, nicht empfohlen vor 2b.
* **Nicht, dass die 44 Folgen Günthers 44 sind.** Gleich ist die Zahl; über die Liste sagt
  die Quelle nichts.
* **Kein `§20`-Anspruch, keine Ledger-Zeile.**

## Zur Äquivalenz: Drehsinn ja, Rotation nein

Die Spec spricht von „modulo Rotation und Drehsinn". **Bei festem Ausgang gibt es keine
Rotations-Freiheit zu quotientieren**, und quotierte man doch, bliebe von den 44 nichts
übrig: gemessen (ausserhalb) zerfallen die 44 unter Rotation in **sechs** Bahnen, unter
Rotation und Drehsinn in **fünf**. Der Grund: die Rotation einer geschlossenen Folge ist
wieder eine geschlossene Folge vom selben Ausgang, aber ein **anderer** Kreis — die
Rotations-Aktion bildet die 88 auf sich ab, statt Vertreter zu identifizieren. Günthers
Wortlaut nennt darum auch nur den Drehsinn. Die Tafel ist modulo **Drehsinn allein**
gebildet, und `alleKreise_no_reverse` ist genau diese Aussage.

## Axiomprofil

Gemessen und am Dateiende gewacht. Die `decide`-Sätze tragen `[propext]`; `gerichtet_full`
trägt, was `reverse_full` trägt (`[propext, Quot.sound]`). **Kein `Classical.choice`.**

**Bauzeit:** rund 11 s — die 44 `IsFullCycle`-Entscheidungen sind der Posten. Gemessen an
zehn Kreisen vor dem Bau (Spec §6 P2: ~2 s für zehn), die Hochrechnung traf.
-/

namespace Reformulation.Proemial.NegationCycleTable

open Reformulation.Proemial.NegationCycle

-- ============================================================
-- Die Tafel
-- ============================================================

/-- Die drei Kreise, die Günther ausschreibt (IGN S. 44-45). -/
def guenthers : List (List (Fin 3)) := [kreis1, kreis2, kreis3]

/-- Die übrigen einundvierzig — **gerechnet, nicht bei Günther**. -/
def gerechnet : List (List (Fin 3)) := [
  [0, 1, 0, 1, 0, 2, 0, 1, 2, 1, 0, 1, 0, 1, 2, 1, 0, 2, 0, 1, 0, 1, 0, 2],
  [0, 1, 0, 1, 2, 1, 0, 1, 2, 1, 2, 1, 0, 1, 0, 1, 2, 1, 0, 1, 2, 1, 2, 1],
  [0, 1, 0, 1, 2, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 2, 1],
  [0, 1, 0, 1, 2, 1, 2, 1, 0, 1, 0, 1, 2, 1, 2, 1, 0, 1, 0, 1, 2, 1, 2, 1],
  [0, 1, 0, 1, 2, 1, 2, 1, 0, 1, 2, 1, 0, 1, 0, 1, 2, 1, 2, 1, 0, 1, 2, 1],
  [0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 2, 1, 0, 1, 0, 1, 2, 1, 0, 2, 0, 1],
  [0, 1, 0, 2, 0, 1, 2, 1, 0, 1, 0, 1, 2, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 1],
  [0, 1, 2, 0, 2, 1, 2, 1, 2, 0, 2, 1, 2, 1, 2, 0, 2, 1, 0, 1, 2, 1, 2, 1],
  [0, 1, 2, 1, 0, 1, 0, 1, 2, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2],
  [0, 1, 2, 1, 0, 1, 0, 1, 2, 1, 2, 1, 0, 1, 2, 1, 0, 1, 0, 1, 2, 1, 2, 1],
  [0, 1, 2, 1, 0, 1, 2, 1, 2, 1, 0, 1, 0, 1, 2, 1, 0, 1, 2, 1, 2, 1, 0, 1],
  [0, 1, 2, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 2, 1, 0, 1],
  [0, 1, 2, 1, 2, 1, 0, 1, 0, 1, 2, 1, 0, 1, 2, 1, 2, 1, 0, 1, 0, 1, 2, 1],
  [0, 1, 2, 1, 2, 1, 0, 1, 2, 0, 2, 1, 2, 1, 2, 0, 2, 1, 2, 1, 2, 0, 2, 1],
  [0, 1, 2, 1, 2, 1, 0, 1, 2, 1, 0, 1, 0, 1, 2, 1, 2, 1, 0, 1, 2, 1, 0, 1],
  [0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 2, 1, 0, 1, 0, 1, 2, 1],
  [0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 2, 1, 0, 1, 0, 1, 2, 1, 0, 2, 0, 1, 0, 1],
  [0, 2, 0, 1, 2, 0, 2, 1, 0, 2, 0, 1, 2, 0, 2, 1, 0, 2, 0, 1, 2, 0, 2, 1],
  [0, 2, 0, 1, 2, 1, 0, 1, 0, 1, 2, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 0, 1],
  [0, 2, 1, 0, 1, 2, 1, 2, 1, 0, 1, 2, 0, 2, 1, 2, 1, 2, 0, 2, 1, 2, 1, 2],
  [0, 2, 1, 0, 2, 0, 1, 2, 0, 2, 1, 0, 2, 0, 1, 2, 0, 2, 1, 0, 2, 0, 1, 2],
  [0, 2, 1, 2, 1, 2, 0, 2, 1, 0, 1, 2, 1, 2, 1, 0, 1, 2, 0, 2, 1, 2, 1, 2],
  [0, 2, 1, 2, 1, 2, 0, 2, 1, 2, 1, 2, 0, 2, 1, 0, 1, 2, 1, 2, 1, 0, 1, 2],
  [1, 0, 1, 0, 1, 2, 1, 0, 1, 2, 1, 2, 1, 0, 1, 0, 1, 2, 1, 0, 1, 2, 1, 2],
  [1, 0, 1, 0, 1, 2, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 2],
  [1, 0, 1, 0, 1, 2, 1, 2, 1, 0, 1, 0, 1, 2, 1, 2, 1, 0, 1, 0, 1, 2, 1, 2],
  [1, 0, 1, 0, 1, 2, 1, 2, 1, 0, 1, 2, 1, 0, 1, 0, 1, 2, 1, 2, 1, 0, 1, 2],
  [1, 0, 1, 2, 0, 2, 1, 2, 1, 2, 0, 2, 1, 2, 1, 2, 0, 2, 1, 0, 1, 2, 1, 2],
  [1, 0, 1, 2, 1, 0, 1, 0, 1, 2, 1, 2, 1, 0, 1, 2, 1, 0, 1, 0, 1, 2, 1, 2],
  [1, 0, 1, 2, 1, 2, 1, 0, 1, 0, 1, 2, 1, 0, 1, 2, 1, 2, 1, 0, 1, 0, 1, 2],
  [1, 0, 1, 2, 1, 2, 1, 0, 1, 2, 0, 2, 1, 2, 1, 2, 0, 2, 1, 2, 1, 2, 0, 2],
  [1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 2, 1, 0, 1, 0, 1, 2],
  [1, 0, 2, 0, 1, 2, 0, 2, 1, 0, 2, 0, 1, 2, 0, 2, 1, 0, 2, 0, 1, 2, 0, 2],
  [1, 2, 0, 2, 1, 0, 1, 2, 1, 2, 1, 0, 1, 2, 0, 2, 1, 2, 1, 2, 0, 2, 1, 2],
  [1, 2, 0, 2, 1, 2, 1, 2, 0, 2, 1, 0, 1, 2, 1, 2, 1, 0, 1, 2, 0, 2, 1, 2],
  [1, 2, 1, 0, 1, 0, 1, 2, 1, 0, 1, 2, 1, 2, 1, 0, 1, 0, 1, 2, 1, 0, 1, 2],
  [1, 2, 1, 0, 1, 0, 1, 2, 1, 2, 1, 0, 1, 0, 1, 2, 1, 2, 1, 0, 1, 0, 1, 2],
  [1, 2, 1, 0, 1, 2, 0, 2, 1, 2, 1, 2, 0, 2, 1, 2, 1, 2, 0, 2, 1, 0, 1, 2],
  [1, 2, 1, 0, 1, 2, 1, 0, 1, 0, 1, 2, 1, 2, 1, 0, 1, 2, 1, 0, 1, 0, 1, 2],
  [1, 2, 1, 2, 0, 2, 1, 0, 1, 2, 1, 2, 1, 0, 1, 2, 0, 2, 1, 2, 1, 2, 0, 2],
  [1, 2, 1, 2, 0, 2, 1, 2, 1, 2, 0, 2, 1, 0, 1, 2, 1, 2, 1, 0, 1, 2, 0, 2]]

/-- Die Tafel: 44 Vollkreise, einer je Drehsinn-Paar. -/
def alleKreise : List (List (Fin 3)) := guenthers ++ gerechnet

-- ============================================================
-- Mindestens vierundvierzig
-- ============================================================

theorem alleKreise_length : alleKreise.length = 44 := by decide

set_option maxRecDepth 4000000 in
/-- Jede der 44 ist ein Vollkreis. -/
theorem alleKreise_full : ∀ s ∈ alleKreise, IsFullCycle s := by decide

set_option maxRecDepth 1000000 in
/-- Keine zwei sind dieselbe Folge. -/
theorem alleKreise_nodup : alleKreise.Nodup := by decide

set_option maxRecDepth 1000000 in
/-- **Und keine ist die Umkehrung einer anderen** — die 44 sind 44 *Kreise*, nicht 44
Folgen, die 22 Kreise doppelt zählen. -/
theorem alleKreise_no_reverse : ∀ s ∈ alleKreise, ∀ t ∈ alleKreise, s ≠ t.reverse := by
  decide

set_option maxRecDepth 1000000 in
/-- Jede trägt eine von Günthers vier Verteilungen (IGN S. 43). -/
theorem alleKreise_families : ∀ s ∈ alleKreise,
    (s.count 0 = 10 ∧ s.count 1 = 9 ∧ s.count 2 = 5) ∨
    (s.count 0 = 5 ∧ s.count 1 = 9 ∧ s.count 2 = 10) ∨
    (s.count 0 = 6 ∧ s.count 1 = 12 ∧ s.count 2 = 6) ∨
    (s.count 0 = 9 ∧ s.count 1 = 6 ∧ s.count 2 = 9) := by decide

set_option maxRecDepth 1000000 in
/-- **Keine der 44 verteilt 8-8-8** — Günthers „niemals gleich oft", an diesen 44. -/
theorem alleKreise_no_888 :
    ∀ s ∈ alleKreise, ¬(s.count 0 = 8 ∧ s.count 1 = 8 ∧ s.count 2 = 8) := by decide

/-- Günthers drei sind unter den 44. -/
theorem guenthers_mem : kreis1 ∈ alleKreise ∧ kreis2 ∈ alleKreise ∧ kreis3 ∈ alleKreise := by
  decide

-- ============================================================
-- Die achtundachtzig gerichteten
-- ============================================================

/-- Mit jedem Kreis sein Gegen-Drehsinn. -/
def gerichtet : List (List (Fin 3)) := alleKreise ++ alleKreise.map List.reverse

theorem gerichtet_length : gerichtet.length = 88 := by decide

/-- **Bewiesen, nicht entschieden**: die zweite Hälfte über `reverse_full`. -/
theorem gerichtet_full : ∀ s ∈ gerichtet, IsFullCycle s := by
  intro s hs
  rcases List.mem_append.mp hs with h | h
  · exact alleKreise_full s h
  · obtain ⟨t, ht, rfl⟩ := List.mem_map.mp h
    exact reverse_full (alleKreise_full t ht)

set_option maxRecDepth 2000000 in
theorem gerichtet_nodup : gerichtet.Nodup := by decide

-- ============================================================
-- Wachen
-- ============================================================

/-- info: 'Reformulation.Proemial.NegationCycleTable.alleKreise_length' depends on axioms: [propext] -/
#guard_msgs in #print axioms alleKreise_length

/-- info: 'Reformulation.Proemial.NegationCycleTable.alleKreise_full' depends on axioms: [propext] -/
#guard_msgs in #print axioms alleKreise_full

/-- info: 'Reformulation.Proemial.NegationCycleTable.alleKreise_nodup' depends on axioms: [propext] -/
#guard_msgs in #print axioms alleKreise_nodup

/-- info: 'Reformulation.Proemial.NegationCycleTable.alleKreise_no_reverse' depends on axioms: [propext] -/
#guard_msgs in #print axioms alleKreise_no_reverse

/-- info: 'Reformulation.Proemial.NegationCycleTable.alleKreise_families' depends on axioms: [propext] -/
#guard_msgs in #print axioms alleKreise_families

/-- info: 'Reformulation.Proemial.NegationCycleTable.alleKreise_no_888' depends on axioms: [propext] -/
#guard_msgs in #print axioms alleKreise_no_888

/-- info: 'Reformulation.Proemial.NegationCycleTable.guenthers_mem' depends on axioms: [propext] -/
#guard_msgs in #print axioms guenthers_mem

/-- info: 'Reformulation.Proemial.NegationCycleTable.gerichtet_length' depends on axioms: [propext] -/
#guard_msgs in #print axioms gerichtet_length

/-- info: 'Reformulation.Proemial.NegationCycleTable.gerichtet_full' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms gerichtet_full

/-- info: 'Reformulation.Proemial.NegationCycleTable.gerichtet_nodup' depends on axioms: [propext] -/
#guard_msgs in #print axioms gerichtet_nodup

end Reformulation.Proemial.NegationCycleTable
