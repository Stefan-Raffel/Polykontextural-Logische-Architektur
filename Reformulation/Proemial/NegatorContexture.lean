import Reformulation.Proemial.NegationCycleThreeCycle
import Reformulation.Proemial.ContextureOverlap

/-!
# Proemial.NegatorContexture — die Negatoren und ihre Elementarkontexturen

Gebaut auf Anordnung des Architekten vom 26. September 2026 nach
`KorpusRev2/Antwort_Verbund_und_Kreise_Mathematiker.md` (Fassung 2, als Spec; §2, §3, §6),
hervorgegangen aus `KorpusRev2/Verbund_und_Kreise_an_Mathematiker_Impl.md`. Das Modul verbindet
zwei Stränge, die einander nicht importierten: die Negatoren (`NegationCycle`,
`NegationCycleThreeCycle`) und die Elementarkontexturen (`ContextureOverlap`).

* **K1 — Umtauschbereich und Elementarkontextur.** Der Negator `N_{i+1}` (`sw i`) tauscht die
  Werte `i` und `i + 1`; sein Umtauschbereich ist das Wertpaar `{i, i + 1}` (`InE`, als Menge
  `E`), eine Elementarkontextur (`isElemContexture_E`). Zwei verschiedene Negatoren ergeben
  genau dann die Kreisrelation (einen Dreierzyklus), wenn ihre Paare sich **überlappen**
  (`overlap_iff_three`), und sie vertauschen genau dann, wenn die Paare **disjunkt** sind
  (`disjoint_iff_comm`); disjunkte Paare gibt es erst ab vier Werten
  (`CompoundContexture.disjoint_elem_contextures_iff`). Für jede Wertzahl.
* **K2 — der vermittelte Umtausch.** `N_{i+1} N_{i+2} N_{i+1}` tauscht `i` und `i + 2` und lässt
  alle anderen Werte, für jede Wertzahl (`mediated_swap`). Die nicht benachbarte Zweiermenge
  `{i, i + 2}` hat keinen eigenen Negator; ihr Umtausch geht über den gemeinsamen Wert
  `i + 1`. Bei drei Werten ist er Günthers Relationsart O des Katalogs (`mediated_swap_is_O`,
  IGN S. 26 f.). Dass dies das „vermittelt" von IGN S. 17 f. ist („das zwischen P und N 2 ist
  durch die andern beiden vermittelt"), ist **LESART**; ob Günthers Vermittlung der
  Verbundkontextur (Definitionen §3) dieselbe ist, ist offen (Hermeneutes).
* **K3 — die Stufen, je Satz am Beweis bestimmt** (CLAUDE.md §4):
  - `overlap_iff` — FOLGERUNG (dünn) — die Arithmetik des Schnitts zweier Paare.
  - `overlap_iff_three` — ZUSAMMENSTELLUNG — `overlap_iff` und `three_iff_adj`.
  - `adj_not_comm` — FOLGERUNG (dünn) — Nachbarn vertauschen nicht, am Wert `i`.
  - `disjoint_iff_comm` — ZUSAMMENSTELLUNG — `overlap_iff`, `comm_far`, `adj_not_comm`.
  - `mediated_swap` — FOLGERUNG (dünn) — die Konjugation einer Transposition, für jedes `m`.
  - `mediated_swap_is_O` — EICHUNG — an Günthers Katalog.
  - `isElemContexture_E` — INSTANZIIERUNG — `Finset.card_pair` am Paar.
  - `E_inter_nonempty_iff_three`, `E_inter_empty_iff_comm` — ZUSAMMENSTELLUNG — die Hauptsätze
    über `mem_E` in die `Finset`-Sprache übersetzt. `mem_E` ist der Hilfssatz dazu.
  Keine Entdeckung: der Wert der Sätze ist, dass sie die zwei Stränge verbinden.
* **K4 — das Profil, gemessen.** Die Hauptsätze über das Prädikat `InE` sind choice-frei, und
  von den `Finset`-Korollaren auch `mem_E`, `E_inter_nonempty_iff_three` und
  `E_inter_empty_iff_comm`. Nur `isElemContexture_E` trägt `Classical.choice`, aus
  `Finset.card_pair` (gemessen, Mathlib 83a5988). Die erste Fassung des B3-Korollars über
  `Disjoint (E i) (E j)` trug es ebenfalls, aus `Finset.disjoint_left`; die Fassung mit
  `E i ∩ E j = ∅` (die Form von `CompoundContexture`, und CLAUDE.md §5 verbietet `Disjoint` auf
  Kontextur-Trägermengen) ist frei. Das Choice gehört also nicht der Sache, sondern einzelnen
  Mengensätzen der Sprache, in der die Kontextur-Seite gebaut ist.
* **K5 — nicht:** kein Verbund-Objekt (der Verbund wäre die Familie der Paare mit ihrem
  Überlappungsgraphen, eine Benennung); keine Aussage über Vollkreise als „Durchlauf des
  Verbunds"; Werte und Wertabbildungen, nicht Kenogramme (A20-1 unberührt); keine
  Ledger-Zeile.
-/

namespace Reformulation.Proemial.NegatorContexture

open Reformulation.Proemial.NegationCycle Reformulation.Proemial.NegationCycleThreeCycle
  Reformulation.Proemial.NegationCycleCatalog Reformulation.Proemial.ContextureOverlap

variable {m : ℕ}

-- ============================================================
-- Teil 1 — die Hauptsätze, über das Prädikat (choice-frei)
-- ============================================================

/-- Der Wert `v` liegt im Umtauschbereich des Negators `N_{i+1}`: er ist `i` oder `i + 1`. -/
def InE (i : Fin m) (v : Fin (m + 1)) : Prop := v.val = i.val ∨ v.val = i.val + 1

/-- **Die Arithmetik des Schnitts:** zwei verschiedene Umtauschbereiche haben genau dann einen
gemeinsamen Wert, wenn ihre Negatoren Nachbarn sind. -/
theorem overlap_iff (i j : Fin m) (hij : i ≠ j) :
    (∃ v, InE i v ∧ InE j v) ↔ (j.val = i.val + 1 ∨ i.val = j.val + 1) := by
  constructor
  · rintro ⟨x, h1 | h1, h2 | h2⟩
    · exact absurd (Fin.ext (h1.symm.trans h2)) hij
    · right; omega
    · left; omega
    · have : i.val = j.val := by omega
      exact absurd (Fin.ext this) hij
  · rintro (h | h)
    · exact ⟨j.castSucc, Or.inr (by simp only [Fin.val_castSucc]; omega),
        Or.inl (by simp only [Fin.val_castSucc])⟩
    · exact ⟨i.castSucc, Or.inl (by simp only [Fin.val_castSucc]),
        Or.inr (by simp only [Fin.val_castSucc]; omega)⟩

/-- **B2 — Überlappung ist Kreisrelation:** zwei verschiedene Negatoren ergeben genau dann einen
Dreierzyklus, wenn ihre Umtauschbereiche einen Wert teilen. -/
theorem overlap_iff_three (i j : Fin m) (hij : i ≠ j) :
    (∃ v, InE i v ∧ InE j v) ↔ IsThree (fun v => sw j (sw i v)) := by
  rw [overlap_iff i j hij, three_iff_adj i j hij]

/-- **Nachbarn vertauschen nicht:** am Wert `i` unterscheiden sich `N_{i+1} N_{i+2}` und
`N_{i+2} N_{i+1}`. -/
theorem adj_not_comm (i j : Fin m) (h : j.val = i.val + 1) :
    sw i (sw j i.castSucc) ≠ sw j (sw i i.castSucc) := by
  intro heq
  have := congrArg Fin.val heq
  rw [sw_val, sw_val, sw_val, sw_val] at this
  simp only [Fin.val_castSucc] at this
  split_ifs at this <;> omega

/-- **B3 — Disjunktheit ist Vertauschung:** zwei verschiedene Negatoren vertauschen genau dann,
wenn ihre Umtauschbereiche keinen Wert teilen. -/
theorem disjoint_iff_comm (i j : Fin m) (hij : i ≠ j) :
    (¬ ∃ v, InE i v ∧ InE j v) ↔ ∀ v, sw i (sw j v) = sw j (sw i v) := by
  rw [overlap_iff i j hij]
  constructor
  · intro hn v
    have hv : i.val ≠ j.val := fun e => hij (Fin.ext e)
    rcases Nat.lt_or_gt_of_ne hv with hl | hl
    · exact comm_far i j (by omega) v
    · exact (comm_far j i (by omega) v).symm
  · rintro hc (h | h)
    · exact adj_not_comm i j h (hc _)
    · exact adj_not_comm j i h (hc _).symm

/-- **B4 — der vermittelte Umtausch:** `N_{i+1} N_{i+2} N_{i+1}` tauscht die Werte `i` und
`i + 2` und lässt alle anderen, für jede Wertzahl. Die nicht benachbarte Zweiermenge
`{i, i + 2}` hat keinen eigenen Negator; ihr Umtausch geht über den gemeinsamen Wert `i + 1`. -/
theorem mediated_swap (i j : Fin m) (hj : j.val = i.val + 1) (v : Fin (m + 1)) :
    (sw i (sw j (sw i v))).val =
      if v.val = i.val then i.val + 2 else if v.val = i.val + 2 then i.val else v.val := by
  simp only [sw_val]
  split_ifs <;> omega

/-- **Eichung an Günthers O:** bei drei Werten ist der vermittelte Umtausch `N1·2·1` genau die
Relationsart O des Katalogs (IGN S. 26 f.; `NegationCycleCatalog.kat`). -/
theorem mediated_swap_is_O :
    kat (fun v => sw (0 : Fin 2) (sw 1 (sw 0 v))) = some .O := by
  decide

-- ============================================================
-- Teil 2 — die Korollare, in der Sprache der Kontextur-Seite (Finset)
-- ============================================================

/-- Der Umtauschbereich des Negators `N_{i+1}` als Wertmenge. -/
def E (i : Fin m) : Finset (Fin (m + 1)) := {i.castSucc, i.succ}

theorem mem_E (i : Fin m) (v : Fin (m + 1)) : v ∈ E i ↔ InE i v := by
  simp only [E, Finset.mem_insert, Finset.mem_singleton, InE, Fin.ext_iff, Fin.val_castSucc,
    Fin.val_succ]

/-- **B1:** der Umtauschbereich eines Negators ist eine Elementarkontextur. -/
theorem isElemContexture_E (i : Fin m) : IsElemContexture (E i) := by
  unfold IsElemContexture E
  exact Finset.card_pair (Fin.ne_of_lt Fin.castSucc_lt_succ)

/-- B2 in der Sprache der Kontextur-Seite. -/
theorem E_inter_nonempty_iff_three (i j : Fin m) (hij : i ≠ j) :
    (E i ∩ E j).Nonempty ↔ IsThree (fun v => sw j (sw i v)) := by
  rw [← overlap_iff_three i j hij]
  constructor
  · rintro ⟨v, hv⟩
    rw [Finset.mem_inter, mem_E, mem_E] at hv
    exact ⟨v, hv⟩
  · rintro ⟨v, hv⟩
    exact ⟨v, by rw [Finset.mem_inter, mem_E, mem_E]; exact hv⟩

/-- B3 in der Sprache der Kontextur-Seite, in der Form von
`CompoundContexture.disjoint_elem_contextures_iff` (`A ∩ B = ∅`, nicht `Disjoint`; CLAUDE.md §5). -/
theorem E_inter_empty_iff_comm (i j : Fin m) (hij : i ≠ j) :
    E i ∩ E j = ∅ ↔ ∀ v, sw i (sw j v) = sw j (sw i v) := by
  rw [← disjoint_iff_comm i j hij]
  constructor
  · rintro h ⟨v, hi, hj⟩
    have hv : v ∈ E i ∩ E j := by
      rw [Finset.mem_inter, mem_E, mem_E]; exact ⟨hi, hj⟩
    rw [h] at hv
    exact Finset.notMem_empty v hv
  · intro h
    ext v
    rw [Finset.mem_inter, mem_E, mem_E]
    exact ⟨fun hv => absurd ⟨v, hv⟩ h, fun hv => absurd hv (Finset.notMem_empty v)⟩

-- ============================================================
-- Wachen
-- ============================================================

/-- info: 'Reformulation.Proemial.NegatorContexture.overlap_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms overlap_iff

/-- info: 'Reformulation.Proemial.NegatorContexture.overlap_iff_three' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms overlap_iff_three

/-- info: 'Reformulation.Proemial.NegatorContexture.adj_not_comm' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms adj_not_comm

/-- info: 'Reformulation.Proemial.NegatorContexture.disjoint_iff_comm' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms disjoint_iff_comm

/-- info: 'Reformulation.Proemial.NegatorContexture.mediated_swap' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms mediated_swap

/-- info: 'Reformulation.Proemial.NegatorContexture.mediated_swap_is_O' depends on axioms: [propext] -/
#guard_msgs in #print axioms mediated_swap_is_O

/-- info: 'Reformulation.Proemial.NegatorContexture.mem_E' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms mem_E

/-- info: 'Reformulation.Proemial.NegatorContexture.isElemContexture_E' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms isElemContexture_E

/-- info: 'Reformulation.Proemial.NegatorContexture.E_inter_nonempty_iff_three' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms E_inter_nonempty_iff_three

/-- info: 'Reformulation.Proemial.NegatorContexture.E_inter_empty_iff_comm' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms E_inter_empty_iff_comm

end Reformulation.Proemial.NegatorContexture
