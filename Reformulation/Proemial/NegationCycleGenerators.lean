import Reformulation.Proemial.NegationCycle
import Mathlib.GroupTheory.Perm.Sign

/-!
# Proemial.NegationCycleGenerators — das Negationssystem ist der Inbegriff aller Permutationen

**HEBUNG und FOLGERUNG.** Gebaut auf Anordnung des Architekten vom 25. September 2026 nach
`KorpusRev2/Spec_Zug3_Negationssystem.md` (Fassung 2, Mathematiker), Teil A; begutachtet in
`KorpusRev2/Begutachtung_Spec_Zug3_Impl.md`. Eigenes Modul, weil
`Mathlib.GroupTheory.Perm.Sign` nicht in der Importhülle von `NegationCycle` liegt: Dort
hiesse Teil A, allen Konsumenten die Gruppentheorie nachzuladen.

* **K1 — Günthers Satz.** Das Negationssystem ist *„der Inbegriff aller Permutationen"*
  (tml S. 10). `negators_generate_all`: Die Negatoren des Bestandes erzeugen jede
  Permutation, **für jedes `m`**. Definitionen §7 führte das als „gemessen bis `m = 7`".
* **K2 — das Choice sitzt an zwei Stellen.** In der Definition `Equiv.swap` (ihr Kern
  `Equiv.swapCore` ist axiomfrei) und in jeder Aussage über Mitgliedschaft im
  Submonoid-Abschluss: Schon `1 ∈ Submonoid.closure …` trägt es, ganz ohne `swap`. Eine
  Aussage über den Abschluss ist darum nie choice-frei, auch mit einer Brücke ohne `swap`.
  Die Gruppe `Perm` selbst ist frei (`negPerm i * negPerm i = 1` trägt
  `[propext, Quot.sound]`, gemessen in der Begutachtung). **Nicht heilbar, solange die
  Aussage über den Abschluss spricht**; eine Heilung wurde darum nicht versucht.
* **K3 — der Beweis ist Mathlibs.** `Equiv.Perm.mclosure_swap_castSucc_succ`. Eigener Gehalt
  ist die Brücke `sw_eq_swap` / `negPerm_eq_swap` (**HEBUNG**: der Negator des Bestandes ist
  Mathlibs Nachbartransposition). `negators_generate_all` sagt über die Negatoren des
  Bestandes, was Mathlib über `swap` sagt (**FOLGERUNG**). Den Satz der Voranalyse, der
  wörtlich Mathlibs Satz wäre, baut dieses Modul nicht; er wäre eine UMBENENNUNG.
* **K4 — nicht konstruktiv.** Der Satz sagt, *dass* jede Permutation erzeugt wird, nicht
  durch welches Wort. Das leistet die Listen-Fassung: `NegationCycleSJT.reach_all`, für
  jedes `m`, konstruktiv und choice-frei, aus dem Vollkreis `sjt_full` (Steinhaus–Johnson–
  Trotter).
* **K5 — nicht die zweite Negation.** Das Negationssystem ist die ganze Gruppe; Günthers
  zweite Negation ist ein Bereich darin (`NegationCycle`, Teil 6 und 7).

## Axiomprofil

Gemessen nach grünem Bau und am Dateiende gewacht: `sw_eq_swap`, `negPerm_eq_swap` und
`negators_generate_all` tragen `[propext, Classical.choice, Quot.sound]`; die Herkunft steht
unter K2.
-/

namespace Reformulation.Proemial.NegationCycleGenerators

open Equiv Reformulation.Proemial.NegationCycle

/-- **Die Brücke**: Günthers Negator `N_{i+1}` ist Mathlibs Nachbartransposition. Der Beweis
zeigt über `sw_val`, wo beide übereinstimmen. -/
theorem sw_eq_swap {m : ℕ} (i : Fin m) : sw i = ⇑(swap i.castSucc i.succ) := by
  funext v
  have hc : i.castSucc.val = i.val := Fin.val_castSucc i
  have hs : i.succ.val = i.val + 1 := Fin.val_succ i
  apply Fin.ext
  rw [sw_val]
  by_cases h1 : v = i.castSucc
  · rw [h1, swap_apply_left, hc, hs, if_pos rfl]
  · have n1 : v.val ≠ i.val := fun h => h1 (Fin.ext (by rw [hc]; exact h))
    by_cases h2 : v = i.succ
    · rw [h2, swap_apply_right, hc, hs, if_neg (by omega), if_pos rfl]
    · have n2 : v.val ≠ i.val + 1 := fun h => h2 (Fin.ext (by rw [hs]; exact h))
      rw [swap_apply_of_ne_of_ne h1 h2, if_neg n1, if_neg n2]

/-- Der Negator des Bestandes als Permutation; er ist seine eigene Umkehrung. -/
def negPerm {m : ℕ} (i : Fin m) : Perm (Fin (m + 1)) := ⟨sw i, sw i, sw_sw i, sw_sw i⟩

/-- Die Brücke auf der Ebene der Permutationen. -/
theorem negPerm_eq_swap {m : ℕ} (i : Fin m) : negPerm i = swap i.castSucc i.succ :=
  Equiv.ext (fun v => congrFun (sw_eq_swap i) v)

/-- **Günthers „Inbegriff aller Permutationen"** (tml S. 10): die Negatoren erzeugen jede
Permutation, für jedes `m`. -/
theorem negators_generate_all (m : ℕ) :
    Submonoid.closure (Set.range (negPerm (m := m))) = ⊤ := by
  have : (negPerm (m := m)) = fun i => swap i.castSucc i.succ := funext negPerm_eq_swap
  rw [this]; exact Perm.mclosure_swap_castSucc_succ m

-- ============================================================
-- Wachen
-- ============================================================

/-- info: 'Reformulation.Proemial.NegationCycleGenerators.sw_eq_swap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms sw_eq_swap

/--
info: 'Reformulation.Proemial.NegationCycleGenerators.negPerm_eq_swap' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms negPerm_eq_swap

/--
info: 'Reformulation.Proemial.NegationCycleGenerators.negators_generate_all' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms negators_generate_all

end Reformulation.Proemial.NegationCycleGenerators
