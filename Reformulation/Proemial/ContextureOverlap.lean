import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Card

/-!
# Proemial.ContextureOverlap — die Überlappung der Elementarkontexturen als Satz

**Ertrag** (klein, aber eigenständig). Diese Datei macht die konstitutive
Überlappungsrelation des Kontexturengitters **satzförmig**, die im Korpus bisher
nur als Prosa stand (CLAUDE.md §5.1: „Die Elementarkontexturen überlappen
paarweise in genau einem Wert, `{0,1} ∩ {1,2} = {1}` usw."). Sie schließt damit
die **Kontexturgrenze-Spalte** der KA-Matrix auf dem *etablierten* wertbasierten
Kontextur-Begriff — dem, den die Schranken-Reihe D/E ohnehin benutzt
(`GeneralCloneBound.LocallyClassical`: „über jede Elementarkontextur `{x,y}`").

Anders als der Längen-Turm (`TowerAsymmetryProbe`) braucht diese Datei **keine**
Setzung „Stufe = Kontextur": die Elementarkontextur *ist* hier die Wert-Zweiermenge,
und die Überlappung ist ein Kardinalitäts-Satz, keine Deutung.

## Die zwei Gestalten des Satzes

- `elem_contexture_overlap_le_one` — der **allgemeine** Kern über `Finset (Fin m)`:
  je zwei *verschiedene* Elementarkontexturen (Zweiermengen) überlappen in
  **höchstens einem** Wert. Trägt die Kardinalitäts-Substanz.
- `three_contextures_overlap` — der **konkrete** günthersche Fall über `Fin 3`,
  **prädikativ** gefasst (`a = x ∨ a = y`, wie `LocallyClassical`): die drei
  Elementarkontexturen `{0,1}`, `{1,2}`, `{0,2}` überlappen paarweise in **genau**
  dem geteilten Wert. Die prädikative Form ist zugleich korpus-näher (der
  Kontextur-Begriff der D-Reihe ist die Disjunktion, nicht der `Finset`) und
  `Classical`-frei (die `Finset`-Entscheidung zöge `Classical.choice`, gemessen).

## Aggregat-Reife

Diese Datei konsumiert **nur** Mathlib, keine Sonde und keine Setzung. Sie ist
damit — anders als Turm und Transition — ohne Kern/Rand-Bruch aggregatfähig.
Der Anschluss bleibt dennoch eine eigene Entscheidung (Eichwerte).

Kein `sorry`, kein `axiom`, kein `: True`-Feld.
-/

open Finset

namespace Reformulation.Proemial.ContextureOverlap

/-- Eine **Elementarkontextur** über `Fin m`: eine Zwei-Werte-Menge. Das ist der
wertbasierte Kontextur-Begriff des Korpus (`{x, y}`, `x ≠ y`), hier als
`Finset` für die Kardinalitäts-Aussage. -/
abbrev IsElemContexture {m : ℕ} (K : Finset (Fin m)) : Prop := K.card = 2

/-- **Der allgemeine Überlappungs-Satz.** Zwei *verschiedene* Elementarkontexturen
über `Fin m` teilen höchstens einen Wert. Denn teilten sie zwei, so umfasste ihr
Schnitt bereits jede der beiden (Kardinalität 2, Teilmenge von Kardinalität 2),
und sie wären gleich. -/
theorem elem_contexture_overlap_le_one {m : ℕ} {A B : Finset (Fin m)}
    (hA : IsElemContexture A) (hB : IsElemContexture B) (hAB : A ≠ B) :
    (A ∩ B).card ≤ 1 := by
  by_contra h
  have hle : (A ∩ B).card ≤ A.card := card_le_card inter_subset_left
  rw [hA] at hle
  have h2 : (A ∩ B).card = 2 := by omega
  have hIA : A ∩ B = A := eq_of_subset_of_card_le inter_subset_left (by rw [hA, h2])
  have hIB : A ∩ B = B := eq_of_subset_of_card_le inter_subset_right (by rw [hB, h2])
  exact hAB (hIA ▸ hIB)

/-- **Der konkrete günthersche Fall (prädikativ).** Die drei Elementarkontexturen
über `Fin 3` überlappen paarweise in genau dem geteilten Wert: `{0,1} ∩ {1,2}`
ist genau `{1}`, `{1,2} ∩ {0,2}` genau `{2}`, `{0,1} ∩ {0,2}` genau `{0}`. In
prädikativer Fassung `a ∈ K ↔ a = x ∨ a = y` — die Relationsgestalt des
Kontexturengitters, satzförmig statt als Prosa. -/
theorem three_contextures_overlap :
    (∀ a : Fin 3, ((a = 0 ∨ a = 1) ∧ (a = 1 ∨ a = 2)) ↔ a = 1)
    ∧ (∀ a : Fin 3, ((a = 1 ∨ a = 2) ∧ (a = 0 ∨ a = 2)) ↔ a = 2)
    ∧ (∀ a : Fin 3, ((a = 0 ∨ a = 1) ∧ (a = 0 ∨ a = 2)) ↔ a = 0) := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

-- ============================================================
-- Wachen — Axiom-Profile
-- ============================================================

/-! **Wachen.** Ist-Ausgabe des grünen Builds (v4.30.0-rc2). Der allgemeine Satz
zieht `Quot.sound` (Finset über Multiset-Quotient); der konkrete prädikative Satz
ist `Classical`-frei (nur `propext`), weil er die `Finset`-Entscheidung meidet. -/

/-- info: 'Reformulation.Proemial.ContextureOverlap.elem_contexture_overlap_le_one' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms elem_contexture_overlap_le_one

/-- info: 'Reformulation.Proemial.ContextureOverlap.three_contextures_overlap' depends on axioms: [propext] -/
#guard_msgs in #print axioms three_contextures_overlap

end Reformulation.Proemial.ContextureOverlap
