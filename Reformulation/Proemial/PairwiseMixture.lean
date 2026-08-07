import Mathlib.Data.Finset.Card
import Reformulation.Proemial.StageAscent
import Reformulation.Proemial.ChoiceVectors
import Reformulation.Proemial.ContextureOverlap

/-!
# Proemial.PairwiseMixture — nicht erzeugbar heisst: wählt auf zwei Paaren verschieden

**Ertrag, dreifach geschnitten.** Der Bestand führt an mehreren Stellen die Wendung, eine
lokal klassische Operation sei „gemischt" — sie wirke auf einer Elementarkontextur wie das
Maximum und auf einer anderen wie das Minimum. Als **Satz** stand das bisher nur an den
konkreten `m = 3`-Mustern (`NonUniformCloneBound`). Diese Datei macht daraus die uniforme
Aussage und schliesst sie an die Klon-Schranke an.

- **Satz** — `pair_mixture_of_ne_min_ne_max`: eine lokal klassische Operation, die weder
  global `min` noch global `max` ist, wirkt auf einem Paar als Maximum und auf einem
  **anderen** Paar als Minimum. Uniform in `f` und `m`.
- **Konsum** — `not_in_clone_pair_mixture`: mit der Klon-Charakterisierung (E3) wird
  daraus *Nicht-Erzeugbarkeit impliziert Paarmischung*. Reine Kontraposition; kein
  eigenes Argument.
- **Verortung am gewählten Zeugen** — `w_differs_on_disjoint`: beim Bestandszeugen `w`
  liegt die Mischung auf zwei **disjunkten** Elementarkontexturen. Das ist Benennung an
  einem Zeugen und kein Gattungssatz, und der nächste Abschnitt sagt, warum das der
  Unterschied ist.

## Die Grenze, und sie ist der Gehalt dieser Datei

**Die Disjunkt-Verschärfung des allgemeinen Satzes ist falsch.** Man könnte vermuten,
eine gemischte Operation müsse auf zwei *disjunkten* Elementarkontexturen verschieden
wirken. Gegenbeispiel bei `m = 4` (gerechnet, ausserhalb des Korpus; Route: Auswertung
der drei disjunkten Paar-Partitionen von `Fin 4` gegen den Wahlvektor): die Operation mit
`min` auf `{0,1}` und `{2,3}` und `max` auf den vier Kreuzpaaren ist lokal klassisch
(Bauplan `ChoiceVectors.ofChoices`), gemischt, nach E3 also **nicht** im Klon — und wirkt
auf **jeder** der drei disjunkten Partitionen von `Fin 4` gleich (min/min, max/max,
max/max).

**Damit ist die Disjunktheit in `w_differs_on_disjoint` eine Eigenschaft des Zeugen und
nicht der Gemischtheit.** Die Datei hat die Hausgestalt des Differentials: eine arme
Klasse — alle gemischten `f`, für die nur Paar-Verschiedenheit gesichert ist — und ein
reicher Zeuge, bei dem die Mischung disjunkt liegt.

## Anschluss, in Prosa und nicht als Satz

`CompoundContexture.disjoint_elem_contextures_iff` sagt, dass disjunkte
Elementarkontexturen genau ab vier Werten existieren; `RegimeThreshold.regime_threshold_at_four`
kippt an derselben Zahl. `w_differs_on_disjoint` **zeigt** dort eine solche Konfiguration,
statt ihre Existenz zu zitieren. Ein gemeinsamer Satz wird nicht gebaut, und
`SAsc.w_not_in_clone` wird **nicht** in den Zeugensatz hineinkonjugiert — Verpackung
ersetzt keinen Gehalt.

## Was hier ausdrücklich nicht steht

Dass Paarmischung „Vermittlung" oder „zweite Negation" wäre, steht hier **nicht einmal
als Deutung**. Diese Deutung hat einen Ort — die Ledger-Zeile L07-2, die
`TCB.T_not_in_clone` als Proxy der zweiten Negation führt und als Deutung markiert —, und
dieser Zug lässt sie dort. Kein Deklarationsname dieser Datei trägt „Vermittlung",
„Mediation" oder „SecondNegation".

## Die Herkunft des Choice-Anteils, gemessen

Der allgemeine Satz ist **nicht** axiomfrei, obwohl er rein prädikativ gehalten ist. Der
Choice-Anteil sitzt **in der Gestalt der Voraussetzung** und nicht im Argument. Gemessen
an zwei Fassungen, die sich in genau einer Grösse unterscheiden:

- aus `f ≠ fun a b => min a b` einen Punkt zu gewinnen, an dem `f` nicht das Minimum ist,
  ist ein Schritt von `¬∀` nach `∃` — `[propext, Classical.choice, Quot.sound]`;
- mit `∃ a b, f a b ≠ min a b` als Voraussetzung fällt derselbe Schluss weg —
  `[propext]`.

**Der Preis ist für den Konsum bezahlt, nicht für die Mischung.** Die Ungleichungsform
ist gewählt, weil die rechte Seite der Klon-Charakterisierung genau
`f = min ∨ f = max` lautet; eine Existenzform hier zwänge den Konsumenten, sie erst
wieder herzustellen — mit demselben Schritt und demselben Axiom, nur eine Stelle später.

## Randlage kleiner Wertzahl

Für `m ≤ 2` sind die Voraussetzungen von `pair_mixture_of_ne_min_ne_max` unerfüllbar: bei
höchstens zwei Werten fallen `min` und `max` mit jeder lokal klassischen Operation
zusammen, `f ≠ min ∧ f ≠ max` ist also leer. Der Satz braucht dafür **keine**
Fallunterscheidung — er läuft über die Voraussetzung und nicht über `m`.

## Aggregat-Reife

Konsumiert `StageAscent`, `ChoiceVectors`, `ContextureOverlap` — alle Aggregat — sowie
Mathlib. Keine Sonde, keine Setzung.

Kein `sorry`, kein `axiom`, kein `: True`-Feld.
-/

open FirstOrder Language

namespace Reformulation.Proemial.PairwiseMixture

open Reformulation.Proemial.TransjunctionCloneBound (L)
open Reformulation.Proemial.GeneralCloneBound
open Reformulation.Proemial.StageAscent (w)
open Reformulation.Proemial.ChoiceVectors (min_ne_max_of_ne)
open Reformulation.Proemial.ContextureOverlap (IsElemContexture)

/-! ## Teil 1 — die Diagonale, erzwungen

Nachgebaut nach der Präzedenz in `ChoiceVectors.locallyClassicalEquiv`, wo dasselbe
Argument in einem Beweis steckt und nicht als Lemma exportiert ist. Kein eigener Posten;
`private`, darum nach dem Wachen-Wortlaut ohne eigene Wache. -/

private theorem diag_of_locallyClassical {m : ℕ} {f : Fin m → Fin m → Fin m}
    (hf : LocallyClassical f) (a : Fin m) : f a a = a := by
  rcases Nat.lt_or_ge m 2 with hm | hm
  · have : Subsingleton (Fin m) := Fin.subsingleton_iff_le_one.mpr (by omega)
    exact Subsingleton.elim _ _
  · have hne : ∃ y : Fin m, y ≠ a := by
      by_cases h0 : a.val = 0
      · refine ⟨⟨1, by omega⟩, fun hc => ?_⟩
        have h1 : (1 : ℕ) = a.val := congrArg Fin.val hc
        omega
      · refine ⟨⟨0, by omega⟩, fun hc => ?_⟩
        have h1 : (0 : ℕ) = a.val := congrArg Fin.val hc
        omega
    obtain ⟨y, hy⟩ := hne
    rcases hf y a hy with h1 | h2
    · exact (h1 a a (Or.inr rfl) (Or.inr rfl)).trans (min_self a)
    · exact (h2 a a (Or.inr rfl) (Or.inr rfl)).trans (max_self a)

/-! ## Teil 2 — die allgemeine Hälfte: Mischung am Paar -/

/-- **Mischung am Paar.** Eine lokal klassische Operation, die weder global `min` noch
global `max` ist, wirkt auf einem Paar als Maximum und auf einem **anderen** Paar als
Minimum.

Die letzte Konjunkte sagt die Paar-Verschiedenheit prädikativ, ohne `Finset`: das
Minimum-Paar liegt nicht in der Zweiermenge des Maximum-Paars. Sie steht im Satz, weil
„auf zwei verschiedenen Paaren" der Gehalt ist und nicht ein Zusatz.

**Nicht verschärfbar auf Disjunktheit** — siehe die Grenznotiz im Modul-Kopf. -/
theorem pair_mixture_of_ne_min_ne_max {m : ℕ}
    (f : Fin m → Fin m → Fin m) (hf : LocallyClassical f)
    (hmin : f ≠ fun a b => min a b) (hmax : f ≠ fun a b => max a b) :
    ∃ x y u v : Fin m, x ≠ y ∧ u ≠ v ∧
      ActsAsMax f x y ∧ ActsAsMin f u v ∧
      ¬ ((u = x ∨ u = y) ∧ (v = x ∨ v = y)) := by
  -- Aus `f ≠ min` ein Paar, auf dem `f` als Maximum wirkt.
  obtain ⟨x, y, hxy, hmaxxy⟩ :
      ∃ x y : Fin m, x ≠ y ∧ ActsAsMax f x y := by
    by_contra hc
    push_neg at hc
    apply hmin
    funext a b
    rcases eq_or_ne a b with rfl | hab
    · rw [diag_of_locallyClassical hf a, min_self]
    · rcases hf a b hab with h | h
      · exact h a b (Or.inl rfl) (Or.inr rfl)
      · exact absurd h (hc a b hab)
  -- Aus `f ≠ max` ein Paar, auf dem `f` als Minimum wirkt.
  obtain ⟨u, v, huv, hminuv⟩ :
      ∃ u v : Fin m, u ≠ v ∧ ActsAsMin f u v := by
    by_contra hc
    push_neg at hc
    apply hmax
    funext a b
    rcases eq_or_ne a b with rfl | hab
    · rw [diag_of_locallyClassical hf a, max_self]
    · rcases hf a b hab with h | h
      · exact absurd h (hc a b hab)
      · exact h a b (Or.inl rfl) (Or.inr rfl)
  refine ⟨x, y, u, v, hxy, huv, hmaxxy, hminuv, ?_⟩
  -- Lägen `u`, `v` in `{x, y}`, so wirkte `f` dort zugleich als `min` und als `max`.
  rintro ⟨hu, hv⟩
  exact min_ne_max_of_ne huv ((hminuv u v (Or.inl rfl) (Or.inr rfl)).symm.trans
    (hmaxxy u v hu hv))

/-- **Der Konsum-Korollar: Nicht-Erzeugbarkeit impliziert Paarmischung.**

Kontraposition der Klon-Charakterisierung (E3) und dann der Satz darüber. Kein eigenes
Argument; die Arbeit steckt in `GeneralCloneBound.locally_classical_in_clone_iff`. -/
theorem not_in_clone_pair_mixture {m : ℕ} (hm : 4 ≤ m)
    (f : Fin m → Fin m → Fin m) (hf : LocallyClassical f)
    (hnc : ¬ ∃ t : L.Term (Fin 2),
        ∀ v : Fin 2 → Fin m, t.realize v = f (v 0) (v 1)) :
    ∃ x y u v : Fin m, x ≠ y ∧ u ≠ v ∧
      ActsAsMax f x y ∧ ActsAsMin f u v ∧
      ¬ ((u = x ∨ u = y) ∧ (v = x ∨ v = y)) := by
  have hne : ¬ ((f = fun a b => min a b) ∨ (f = fun a b => max a b)) := fun h =>
    hnc ((locally_classical_in_clone_iff hm f hf).mpr h)
  push_neg at hne
  exact pair_mixture_of_ne_min_ne_max f hf hne.1 hne.2

/-! ## Teil 3 — der reiche Zeuge: bei `w` liegt die Mischung disjunkt -/

private theorem w_max_on_zero_one {m : ℕ} {a b : Fin m}
    (ha : a.val = 0 ∨ a.val = 1) (hb : b.val = 0 ∨ b.val = 1) :
    w m a b = max a b := by
  unfold w
  by_cases h : (a.val = 0 ∧ b.val = 1) ∨ (a.val = 1 ∧ b.val = 0)
  · rw [if_pos h]
  · rw [if_neg h]
    have hab : a = b := Fin.ext (by omega)
    subst hab
    exact (min_self a).trans (max_self a).symm

private theorem w_min_on_two_three {m : ℕ} {a b : Fin m}
    (_ha : a.val = 2 ∨ a.val = 3) (hb : b.val = 2 ∨ b.val = 3) :
    w m a b = min a b := by
  unfold w
  rw [if_neg (by omega)]

/-- **Verortung am gewählten Zeugen.** Beim Bestandszeugen `w` liegt die Mischung auf
zwei **disjunkten** Elementarkontexturen: auf `{0,1}` wirkt er als Maximum, auf `{2,3}`
als Minimum.

**Ertragsklasse: Benennung an einem Zeugen, kein Gattungssatz.** Dass eine gemischte
Operation ihre Mischung disjunkt trägt, ist im Allgemeinen **falsch** — die Grenznotiz im
Modul-Kopf führt das Gegenbeispiel. Der Wert dieses Satzes liegt darin, dass er am
Bestandszeugen genau die Konfiguration zeigt, die ab vier Werten möglich wird. -/
theorem w_differs_on_disjoint {m : ℕ} (hm : 4 ≤ m) :
    ∃ A B : Finset (Fin m), IsElemContexture A ∧ IsElemContexture B ∧
      A ∩ B = ∅ ∧
      (∃ x y : Fin m, A = {x, y} ∧ ActsAsMax (w m) x y) ∧
      (∃ u v : Fin m, B = {u, v} ∧ ActsAsMin (w m) u v) := by
  refine ⟨{⟨0, by omega⟩, ⟨1, by omega⟩}, {⟨2, by omega⟩, ⟨3, by omega⟩}, ?_, ?_, ?_, ?_, ?_⟩
  · rw [IsElemContexture, Finset.card_insert_of_notMem (by simp [Fin.ext_iff]),
      Finset.card_singleton]
  · rw [IsElemContexture, Finset.card_insert_of_notMem (by simp [Fin.ext_iff]),
      Finset.card_singleton]
  · ext z
    simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton,
      Finset.notMem_empty, iff_false, not_and, Fin.ext_iff]
    omega
  · refine ⟨⟨0, by omega⟩, ⟨1, by omega⟩, rfl, ?_⟩
    intro a b ha hb
    exact w_max_on_zero_one
      (by rcases ha with rfl | rfl <;> simp) (by rcases hb with rfl | rfl <;> simp)
  · refine ⟨⟨2, by omega⟩, ⟨3, by omega⟩, rfl, ?_⟩
    intro a b ha hb
    exact w_min_on_two_three
      (by rcases ha with rfl | rfl <;> simp) (by rcases hb with rfl | rfl <;> simp)

/-! ## Teil 4 — Statement-Pins

Ein Pin nagelt den vollen Wortlaut fest: ein geschwächter Satz mit gleichem Axiomprofil
käme durch eine Wache hindurch, aber nicht hier vorbei. Namenlose `example`s, keine
Axiom-Wache. -/

-- STATEMENT-PIN
example {m : ℕ} (f : Fin m → Fin m → Fin m) (hf : LocallyClassical f)
    (hmin : f ≠ fun a b => min a b) (hmax : f ≠ fun a b => max a b) :
    ∃ x y u v : Fin m, x ≠ y ∧ u ≠ v ∧
      ActsAsMax f x y ∧ ActsAsMin f u v ∧
      ¬ ((u = x ∨ u = y) ∧ (v = x ∨ v = y)) :=
  pair_mixture_of_ne_min_ne_max f hf hmin hmax
-- STATEMENT-PIN
example {m : ℕ} (hm : 4 ≤ m) (f : Fin m → Fin m → Fin m) (hf : LocallyClassical f)
    (hnc : ¬ ∃ t : L.Term (Fin 2),
        ∀ v : Fin 2 → Fin m, t.realize v = f (v 0) (v 1)) :
    ∃ x y u v : Fin m, x ≠ y ∧ u ≠ v ∧
      ActsAsMax f x y ∧ ActsAsMin f u v ∧
      ¬ ((u = x ∨ u = y) ∧ (v = x ∨ v = y)) :=
  not_in_clone_pair_mixture hm f hf hnc
-- STATEMENT-PIN
example {m : ℕ} (hm : 4 ≤ m) :
    ∃ A B : Finset (Fin m), IsElemContexture A ∧ IsElemContexture B ∧
      A ∩ B = ∅ ∧
      (∃ x y : Fin m, A = {x, y} ∧ ActsAsMax (w m) x y) ∧
      (∃ u v : Fin m, B = {u, v} ∧ ActsAsMin (w m) u v) :=
  w_differs_on_disjoint hm

/-! ## Teil 5 — die Axiom-Wachen (Ist-gebunden)

Ist-Ausgabe des grünen Builds (v4.30.0-rc2), je nicht-private Deklaration eingefroren;
die privaten Hilfslemmata tragen nach der Präzedenz des Trakts keine eigene Wache — ihr
Profil liegt im Axiomabschluss ihrer Konsumenten. -/

/--
info: 'Reformulation.Proemial.PairwiseMixture.pair_mixture_of_ne_min_ne_max' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms pair_mixture_of_ne_min_ne_max

/--
info: 'Reformulation.Proemial.PairwiseMixture.not_in_clone_pair_mixture' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms not_in_clone_pair_mixture

/--
info: 'Reformulation.Proemial.PairwiseMixture.w_differs_on_disjoint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms w_differs_on_disjoint

end Reformulation.Proemial.PairwiseMixture
