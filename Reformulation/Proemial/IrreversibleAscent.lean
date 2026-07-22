import Mathlib.Logic.Function.Iterate
import Mathlib.Data.Set.Basic

/-!
# Reformulation.Proemial.IrreversibleAscent — der irreversible Aufstieg (sechzehnte Schicht)

Das zweite Zeit-Differential in Zeugen-Fassung — dual zur vierzehnten Schicht:
dort lebt der Zyklus in keiner strikten Ordnung, hier lebt der strikte Aufstieg
in keiner Periodik. Eine Sprache für beide Hälften: die Iterations-Sprache
(`Function.iterate`, Gleichheit). Selbsttragend: kein Kenogramm-, F3- oder
PathC-Import.

## (1) Quellen-fest

Günther, Vorwort *Beiträge zur Grundlegung einer operationsfähigen Dialektik III*
(1980, S. XI): „Und zwar muß die Asymmetrie im Prinzip liegen." — hier
ausdrücklich als **behauptete** negative Richtung markiert: behauptet ≠ bewiesen.
Der Satz dieser Schicht ist nicht die Einlösung jener Stelle, sondern die
*bewiesene* negative Richtung des Iterations-Differentials. Ebd. der
„symmetrische Idealfall als Maßstab für den Grad der Abweichung".

## (2) Bauform-Identität (Zusammenlesung, Deutung)

Die arme Klasse `PointwisePeriodic` formalisiert Günthers Maßstab-Grenzfall — den
symmetrischen Idealfall, gegen den das konkrete, asymmetrische Geschehen gemessen
wird. Diese Identifikation ist Zusammenlesung, Deutung. Ihre Symmetrie aber ist
Satz (`reach_returns`), nicht Definitions-Zutat: gefordert wird allein die
Periodizität, die Reversibilität wird bewiesen.

## (3) Term-fest werden hiermit

* die **Symmetrie der armen Klasse** (`reach_returns`, Hilfssatz
  `iterate_mul_apply_self`);
* die **Nicht-Darstellbarkeit des injektiven Aufstiegs**
  (`no_injective_trajectory`, Hilfssatz `trajectory_eq_iterate`);
* der **rückkehrfreie Zeuge** `Nat.succ` samt Ehrlichkeits-Sätzen
  (`succ_iterate'`, `succ_no_return`, `succ_not_pointwise_periodic`);
* die **Rang-Reduktion** (`no_return_of_strict_rank` samt Korollar
  `not_pointwise_periodic_of_strict_rank`, Hilfssatz `rank_add_le_iterate`).

## (4) Marken

Der Zeuge trägt die Stufen-Zahl, nicht die Kontextur-Substanz — die Lesart „in
keiner periodisch-reversiblen Ein-Kontextur-Iteration" ist Architektur-Deutung.
An der Zeugen-Fassung ist nichts gesetzt und nichts konditional; die
Fixpunkt-Freiheits-Setzung betrifft allein die Architektur-Anbindung und
reduziert sich per Rang-Lemma (`no_return_of_strict_rank`) auf eine prüfbare
Term-Eigenschaft der künftigen Stufen-Hebung (Kandidaten: Präfixlänge,
`numDistinct`-Wachstum). Der Zeuge M4 ist die Instanz `rank = id` des Rang-Lemmas.

## (5) Abgrenzung

Dual zur vierzehnten Schicht (`IntransitivityDifferential`): Zyklus↔strikte
Ordnung / Aufstieg↔Periodik — die Kontextur-Zahl trennt die zwei
Zeit-Differentiale, die Beweis-Idee verbindet sie. Die Kenogramm-Anwendung (16b,
F3-abhängig) und die Inversion 1976 (4b) sind eigene Züge.

## (6) Sorry-Bilanz und Axiom-Stand

0 Sorries. Axiom-Stand (Ist, per `#print axioms` am Datei-Ende): `propext`
(foundationaler Lean-Kern) in allen Sätzen; in den ℕ-arithmetik-tragenden
Sätzen zusätzlich `Quot.sound` (über `omega` und die Nat-Lemma-Ketten);
`reach_returns` hängt nur an `propext`. Kein `Classical`, kein `decide`,
kein `sorryAx`. Der leere Axiom-Satz ist für arithmetiktragende Sätze nicht
ohne Preisgabe des Gegenstands (Iteration über ℕ-Schrittzahlen) erreichbar.
-/

namespace Reformulation.Proemial.IrreversibleAscent

/-- Die arme Klasse: punktweise periodische Selbstabbildungen — jeder Punkt
    kehrt in endlich vielen Schritten zu sich zurück. Formalisierung von
    Günthers „symmetrischem Idealfall als Maßstab" (Vorwort Beiträge III,
    S. XI — Zusammenlesung, Deutung). Nur die Periodizität wird gefordert;
    die Reversibilität ist SATZ (`reach_returns`), nicht Definitions-Zutat. -/
def PointwisePeriodic {α : Type*} (f : α → α) : Prop :=
  ∀ x, ∃ n > 0, f^[n] x = x

/-- Hilfssatz: Perioden vervielfachen sich. -/
theorem iterate_mul_apply_self {α : Type*} {f : α → α} {x : α} {n : ℕ}
    (h : f^[n] x = x) : ∀ a : ℕ, f^[a * n] x = x := by
  intro a
  induction a with
  | zero => simp
  | succ a ih =>
      rw [Nat.succ_mul, Function.iterate_add_apply, h]
      exact ih

/-- SYMMETRIE-SATZ der armen Klasse: jede Erreichbarkeit ist umkehrbar —
    was in k Schritten erreicht wurde, findet in m Schritten zurück.
    „Periodisch-reversibel" ehrlich gemacht: die Reversibilität des
    Maßstab-Grenzfalls als bewiesene Eigenschaft. -/
theorem reach_returns {α : Type*} {f : α → α} (hf : PointwisePeriodic f)
    (x : α) (k : ℕ) : ∃ m : ℕ, f^[m] (f^[k] x) = x := by
  obtain ⟨n, hn, hx⟩ := hf x
  refine ⟨k * n - k, ?_⟩
  rw [← Function.iterate_add_apply]
  have hkn : k ≤ k * n := Nat.le_mul_of_pos_right k hn
  rw [Nat.sub_add_cancel hkn]
  exact iterate_mul_apply_self hx k

/-- Hilfssatz: eine Trajektorie ist die Iterierten-Folge ihres Anfangs. -/
theorem trajectory_eq_iterate {α : Type*} {f : α → α} {φ : ℕ → α}
    (hstep : ∀ k, φ (k + 1) = f (φ k)) : ∀ k, φ k = f^[k] (φ 0) := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih => rw [hstep, ih, ← Function.iterate_succ_apply' f k (φ 0)]

/-- NEGATIVE HÄLFTE (Darstellbarkeit): kein injektiver Trajektorien-Morphismus
    von der Stufen-Kette in irgendein Mitglied der armen Klasse — jede
    Trajektorie kehrt wieder, und die Wiederkehr bricht die Injektivität.
    Instanz-Quantifikation über alle Träger und alle punktweise periodischen f. -/
theorem no_injective_trajectory {α : Type*} {f : α → α} (hf : PointwisePeriodic f) :
    ¬ ∃ φ : ℕ → α, Function.Injective φ ∧ ∀ k, φ (k + 1) = f (φ k) := by
  rintro ⟨φ, hinj, hstep⟩
  obtain ⟨n, hn, hper⟩ := hf (φ 0)
  have h : φ n = φ 0 := by
    rw [trajectory_eq_iterate hstep n, hper]
  exact hn.ne' (hinj h)

/-- Iterierte des Nachfolgers (Mathlib stellt kein `Nat.succ_iterate` bereit —
    Teil 0 (2)). -/
theorem succ_iterate' (n k : ℕ) : Nat.succ^[k] n = n + k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', ih]; omega

/-- POSITIVE HÄLFTE: der minimale Zeuge — die Nachfolger-Iteration kehrt
    nie zurück. (Zugleich die Instanz `rank = id` des Rang-Lemmas, Teil 4.) -/
theorem succ_no_return (n k : ℕ) (hk : 0 < k) : Nat.succ^[k] n ≠ n := by
  rw [succ_iterate']
  omega

/-- EHRLICHKEIT: der Zeuge verlässt die arme Klasse exakt an der
    Periodizität — an JEDEM Punkt (die Negation der Klassen-Bedingung selbst). -/
theorem succ_not_pointwise_periodic : ¬ PointwisePeriodic Nat.succ := by
  intro hf
  obtain ⟨n, hn, h⟩ := hf 0
  exact succ_no_return 0 n hn h

/-- Ein strikt wachsender Rang treibt die Iterierten unbeschränkt. -/
theorem rank_add_le_iterate {α : Type*} (f : α → α) (rank : α → ℕ)
    (hr : ∀ x, rank x < rank (f x)) (x : α) :
    ∀ k, rank x + k ≤ rank (f^[k] x) := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      have := hr (f^[k] x)
      omega

/-- RANG-LEMMA (die Reduktion der Setzung): trägt eine Iteration einen strikt
    wachsenden ℕ-Rang, ist sie rückkehrfrei. Die Fixpunkt-Freiheits-Setzung
    der Architektur reduziert sich damit auf eine prüfbare Term-Eigenschaft
    der künftigen Stufen-Hebung (Kandidaten: Präfixlänge, numDistinct). -/
theorem no_return_of_strict_rank {α : Type*} (f : α → α) (rank : α → ℕ)
    (hr : ∀ x, rank x < rank (f x)) (x : α) (k : ℕ) (hk : 0 < k) :
    f^[k] x ≠ x := by
  intro h
  have := rank_add_le_iterate f rank hr x k
  rw [h] at this
  omega

/-- Korollar: strikt berangte Iterationen liegen außerhalb der armen Klasse. -/
theorem not_pointwise_periodic_of_strict_rank {α : Type*} [Nonempty α]
    (f : α → α) (rank : α → ℕ) (hr : ∀ x, rank x < rank (f x)) :
    ¬ PointwisePeriodic f := by
  intro hf
  obtain ⟨x⟩ := ‹Nonempty α›
  obtain ⟨n, hn, hx⟩ := hf x
  exact no_return_of_strict_rank f rank hr x n hn hx

/-- KÜR — die „reversibel"-Hälfte des Namens als Satz: in der armen Klasse
    hat jeder Orbit-Punkt einen Orbit-Vorgänger. -/
theorem orbit_pred_exists {α : Type*} {f : α → α} (hf : PointwisePeriodic f)
    (x : α) :
    ∀ y ∈ Set.range (fun k => f^[k] x),
      ∃ z ∈ Set.range (fun k => f^[k] x), f z = y := by
  rintro y ⟨k, rfl⟩
  cases k with
  | zero =>
      obtain ⟨n, hn, hx⟩ := hf x
      refine ⟨f^[n - 1] x, ⟨n - 1, rfl⟩, ?_⟩
      show f (f^[n - 1] x) = x
      rw [← Function.iterate_succ_apply' f (n - 1) x, Nat.succ_eq_add_one,
        Nat.sub_add_cancel hn]
      exact hx
  | succ k =>
      exact ⟨f^[k] x, ⟨k, rfl⟩, (Function.iterate_succ_apply' f k x).symm⟩

end Reformulation.Proemial.IrreversibleAscent

-- #print axioms (Abnahme-Checkliste Punkt 2) — als Regressions-Wachen gesetzt.
-- Ist-Ausgabe des grünen Builds (v4.30.0-rc2), pro Satz eingefroren; ab hier bricht
-- jede Axiom-Drift den Build.
open Reformulation.Proemial.IrreversibleAscent in
section

/-- info: 'Reformulation.Proemial.IrreversibleAscent.iterate_mul_apply_self' depends on axioms: [propext] -/
#guard_msgs in #print axioms iterate_mul_apply_self

/-- info: 'Reformulation.Proemial.IrreversibleAscent.reach_returns' depends on axioms: [propext] -/
#guard_msgs in #print axioms reach_returns

/-- info: 'Reformulation.Proemial.IrreversibleAscent.trajectory_eq_iterate' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms trajectory_eq_iterate

/-- info: 'Reformulation.Proemial.IrreversibleAscent.no_injective_trajectory' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms no_injective_trajectory

/-- info: 'Reformulation.Proemial.IrreversibleAscent.succ_iterate'' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms succ_iterate'

/-- info: 'Reformulation.Proemial.IrreversibleAscent.succ_no_return' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms succ_no_return

/-- info: 'Reformulation.Proemial.IrreversibleAscent.succ_not_pointwise_periodic' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms succ_not_pointwise_periodic

/-- info: 'Reformulation.Proemial.IrreversibleAscent.rank_add_le_iterate' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms rank_add_le_iterate

/-- info: 'Reformulation.Proemial.IrreversibleAscent.no_return_of_strict_rank' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms no_return_of_strict_rank

/-- info: 'Reformulation.Proemial.IrreversibleAscent.not_pointwise_periodic_of_strict_rank' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in #print axioms not_pointwise_periodic_of_strict_rank

/-- info: 'Reformulation.Proemial.IrreversibleAscent.orbit_pred_exists' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms orbit_pred_exists
end
