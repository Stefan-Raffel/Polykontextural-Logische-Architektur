import Reformulation.Proemial.IrreversibleAdvance

/-!
# Proemial.TimeMeasure — das gegenständliche Zeitmass: zwei gegenläufige Zeiten haben kein gemeinsames

**FOLGERUNG.** Gebaut auf Anordnung des Architekten vom 25. September 2026 nach
`KorpusRev2/Spec_TimeMeasure.md` (Mathematiker). Vorgänge: `Optionen_Willensproblem_Impl.md`,
`Begutachtung_Optionen_Willensproblem.md`, `Antwort_Begutachtung_Optionen_Willensproblem_Impl.md`.

* **K-M1 — die Quelle.** Günther, *Wahrheit, Wirklichkeit und Zeit* (1937), S. 3: „die
  transzendente Zeit und die Zeit der Erinnerung besitzen kein gemeinsames, objektives
  (gegenständliches) Zeitmaß". `no_common_measure_inverse` ist dieser Satz, in der Lesart von
  K-M2: zwei gegenläufige Zeiten haben jede ihr Mass und kein gemeinsames — für **jeden**
  Träger, und der Satz verbraucht **beide** Zeiten.
* **K-M2 — die Lesart.** Die zwei Zeiten sind **gegenläufig**: die eine kehrt um, was die
  andere tut. **LESART** — sie liegt in den Wörtern Zukunft und Vergangenheit nahe, steht aber
  nicht als Satz bei Günther; ob WWZ S. 3 die Richtungen nennt, ist eine Frage an Hermeneutes.
  Die schwächere Lesart „Erinnerung ↦ reversibel" ist darin die **Diagonale**
  (`reversible_no_measureZ`, `g = f`): unter ihr hätte eine Zeit gar kein Mass, und „kein
  gemeinsames" folgte aus einer Zeit allein.
* **K-M3 — das Mass über `ℤ`, nicht über `ℕ`.** Ein strikt wachsender `ℕ`-Rang setzt ein
  Unten voraus: die Verschiebung auf `ℤ` hat keinen (M4, `no_nat_rank_on_int`, 21.9.). Mit
  einem `ℕ`-Mass entschiede die Definition über die Lage der Zeitachse — dieselbe Frage, an der
  Phase 2 entfallen ist.
* **K-M4 — Mass ⇒ Ordnung.** `measure_noreturn`: wer ein gegenständliches Mass hat, kehrt nicht
  zurück (`IrreversibleAdvance.NoReturn`); es verallgemeinert `noreturn_of_strict_rank` vom
  `ℕ`- auf den `ℤ`-Rang. Unter der Gegenläufigkeit sind darum **beide** Zeiten Ordnungen,
  gegeneinander gerichtet. Das steht quer zu E&W S. 21 (kognitiv ↦ Umtausch, volitiv ↦
  Ordnung) und zu *Als Wille* S. 3 (Denken hierarchisch, Wille zyklisch); **genannt, nicht
  entschieden**.
* **K-M5 — nicht gebaut.** Die Wahl selbst: WWZ S. 6, Logik und „Lehre von den
  Entscheidungen" können „unmöglich … in einem geschlossenen, streng finitistischen System
  vereinigt werden"; nach Hauslesart (27.6.) liegt der Akt jenseits von Lean. Keine
  Wahlfunktion (sie wäre Setzung, Gattung `directionChoice`). Keine Deckung: eine Definition,
  die jede Struktur trivial erfüllt, trägt nichts; eine nichttriviale ist ungemessen.
* **K-M6 — nicht die Genese.** Zwei Wege zum selben Punkt (`NegationCycle`, Teil 5) sind nicht
  das Trennen oder Decken zweier Masse.

Kein Paragraph-Anspruch, keine Ledger-Zeile: der Wille hat in `Definitionen.md` keinen eigenen
Paragraphen. Der Bezeichner nennt den Willen nicht — der Wille ist, was nicht gebaut wird.

## Axiomprofil

Gemessen nach grünem Bau und am Dateiende gewacht: alle fünf Sätze tragen
`[propext, Quot.sound]`, **kein `Classical.choice`**.
-/

namespace Reformulation.Proemial.TimeMeasure

open Reformulation.Proemial.ReversibleExchange Reformulation.Proemial.IrreversibleAdvance

/-- Ein **gegenständliches Zeitmass** für einen Prozess: ein Rang in `ℤ`, der mit jedem Schritt
strikt wächst. Über `ℤ`, weil ein `ℕ`-Rang ein Unten voraussetzte (K-M3). -/
def IsMeasureZ {α : Type*} (f : α → α) (rank : α → ℤ) : Prop := ∀ x, rank x < rank (f x)

/-- **Zwei gegenläufige Zeiten haben kein gemeinsames Mass** (WWZ S. 3, Lesart K-M2) — für
jeden Träger. -/
theorem no_common_measure_inverse {α : Type*} [Nonempty α] {f g : α → α}
    (h : ∀ x, g (f x) = x) : ¬ ∃ r : α → ℤ, IsMeasureZ f r ∧ IsMeasureZ g r := by
  rintro ⟨r, hf, hg⟩
  obtain ⟨x⟩ := ‹Nonempty α›
  have h1 := hf x
  have h2 := hg (f x)
  rw [h x] at h2
  omega

/-- Die Diagonale: ein Umtausch, der sich selbst umkehrt, hat überhaupt kein Mass. -/
theorem reversible_no_measureZ {α : Type*} [Nonempty α] {f : α → α} (hr : Reversible f) :
    ¬ ∃ r : α → ℤ, IsMeasureZ f r := fun ⟨r, hf⟩ =>
  no_common_measure_inverse (f := f) (g := f) hr ⟨r, hf, hf⟩

/-- **Mass ⇒ Ordnung:** wer ein gegenständliches Mass hat, kehrt nicht zurück. -/
theorem measure_noreturn {α : Type*} {f : α → α} {r : α → ℤ} (h : IsMeasureZ f r) :
    NoReturn f := by
  have key : ∀ n x, r x + n ≤ r (f^[n] x) := by
    intro n; induction n with
    | zero => intro x; simp
    | succ k ih =>
      intro x
      rw [Function.iterate_succ_apply]
      have := ih (f x); have := h x; omega
  intro x n hn hx
  have := key n x
  rw [hx] at this
  omega

/-- Eichung: jede der zwei gegenläufigen Zeiten auf `ℤ` hat ihr Mass. -/
theorem opposite_each_measured :
    IsMeasureZ (fun z : ℤ => z + 1) id ∧ IsMeasureZ (fun z : ℤ => z - 1) (fun z => -z) :=
  ⟨fun z => by show z < z + 1; omega, fun z => by show -z < -(z - 1); omega⟩

/-- Eichung: … und keinen gemeinsamen. -/
theorem opposite_no_common :
    ¬ ∃ r : ℤ → ℤ, IsMeasureZ (fun z : ℤ => z + 1) r ∧ IsMeasureZ (fun z : ℤ => z - 1) r :=
  no_common_measure_inverse (fun z => by omega)

-- ============================================================
-- Wachen
-- ============================================================

/-- info: 'Reformulation.Proemial.TimeMeasure.no_common_measure_inverse' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms no_common_measure_inverse

/-- info: 'Reformulation.Proemial.TimeMeasure.reversible_no_measureZ' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms reversible_no_measureZ

/-- info: 'Reformulation.Proemial.TimeMeasure.measure_noreturn' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms measure_noreturn

/-- info: 'Reformulation.Proemial.TimeMeasure.opposite_each_measured' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms opposite_each_measured

/-- info: 'Reformulation.Proemial.TimeMeasure.opposite_no_common' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms opposite_no_common

end Reformulation.Proemial.TimeMeasure
