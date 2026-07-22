import Reformulation.Proemial.SubstantialTransjunction

/-!
# Reformulation.Proemial.InteractiveTransjunction — der Interaktions-Zeuge

Dreizehnte Niederlegungs-Schicht. Sie präzisiert die Erzählung der zwölften
Schicht (`SubstantialTransjunction.lean`, unangetastet) und legt den echten
Interaktions-Zeugen nieder.

## (1) Die Korrektur der Zwölfte-Schicht-Erzählung

Die zwölfte Schicht nennt ihren Zeugen `exTransjectA` „binär-interaktiv". Am Term
zeigt sich präziser: sein Rejektions-Ziel `φ_b = fun n => decide (n = b)` hängt
ALLEIN am ZWEITEN Argument. `exTransjectA` entgeht der Erst-Argument-Familie
`InExtendedUnary` also durch Argument-*Asymmetrie*, nicht durch Interaktion. Diese
Schicht bucht den Loop-Befund als Theorem: die gespiegelte Zweit-Argument-Familie
`InExtendedUnarySnd` FÄNGT `exTransjectA` ein (`exTransjectA_inside_snd`).
`exTransjectA` ist damit der ASYMMETRISCHE Zeuge — kein interaktiver. Die zwölfte
Schicht bleibt unverändert; ihre Beweise stehen; ihre „binär-interaktiv"-Prosa ist
hiermit am Term präzisiert.

## (2) Der Interaktions-Zeuge

`exTransjectI` rejiziert bei `a ≠ b` zur charakteristischen Funktion von `{a + b}`
— das Ziel hängt an BEIDEN Argumenten. Er sitzt außerhalb der Erst-Argument-Familie
(`exTransjectI_outside_fst`) UND außerhalb der Zweit-Argument-Familie
(`exTransjectI_outside_snd`), also außerhalb BEIDER unärer Familien
(`exTransjectI_outside_either`). Kür: außerhalb der punktweise GEMISCHTEN Familie
(`exTransjectI_outside_mixed`, Taubenschlag über der Injektivität) — das Ziel ist an
KEINER punktweisen Ein-Argument-Wahl festmachbar. Damit wird der Ausschluss im
*unären Regime* unbedingt.

## (3) Reichweite (unverändert konditional)

`binary_captures_all` (zwölfte Schicht) bleibt wahr — die Unär-Lesart von
„kanonisch" bleibt gesetzte Prämisse. Der Zeuge beseitigt das Asymmetrie-*Artefakt*,
nicht die *Setzung*: Symmetrisierung, nicht Zwang (Marke 2). „Interaktion =
Akkretion / Neues" bleibt Deutung (Marke 3); term-fest ist allein die Form (Ziel an
keiner Ein-Argument-Wahl festmachbar). `exTransjectA` wird nicht entwertet: sein
`exTransjectA_outside` bleibt bewiesen; der Interaktions-Zeuge tritt NEBEN ihn.

## Sorry-Bilanz / „ruht auf"-Audit

* Teil 1 (`InExtendedUnarySnd`, `exTransjectA_inside_snd`): 0 Sorries. Konsumenten
  wie die zwölfte Schicht: Sum-Maschinerie, `decide`, `cond`.
* Teil 2 (`exTransjectI`, `exTransjectI_rejects`, beide Ausschlüsse + Korollar):
  0 Sorries. Instanzgebunden (`(0,1)/(0,2)` bzw. `(1,0)/(2,0)`), kein Form α;
  `congrFun` für die Ziel-Unterscheidung.
* Teil 3 (Kür 1, `InExtendedUnaryMixed`, `exTransjectI_outside_mixed`): 0 Sorries.
  Zusätzlich Taubenschlag über `1,2 × 5,6,7` (Injektivität der Ziel-Familie).
* Teil 4 (Kür 2, `exLiftedI`, `exLiftedI_transject_eq`): 0 Sorries. Zusätzlich
  `Discrete`/`Sum.map`/`LiftedTransjunctiveC` (elfte/zwölfte Schicht).
* Gesamt: 0 Sorries. Erwarteter Axiom-Rahmen: `propext` (ggf. `Quot.sound`).
-/

namespace Reformulation.Proemial.InteractiveTransjunction

open CategoryTheory
open Reformulation.Proemial.RealizedTransjunction
open Reformulation.Proemial.SubstantialTransjunction

-- ============================================================
-- Teil 1 — Die gespiegelte Familie und die ehrliche Buchung
-- ============================================================

/-- Die gespiegelte unäre Familie: die Rejektion ist vom ZWEITEN Argument
    allein bestimmt (`g b` statt `g a`). Wortgleich zu `InExtendedUnary`
    bis auf die Argument-Stelle. -/
def InExtendedUnarySnd {S K : Type*} (t : S → S → (S ⊕ K)) : Prop :=
  ∃ (op : S → S → S) (sel : S → S → Bool) (g : S → K),
    ∀ a b, t a b = cond (sel a b) (Sum.inl (op a b)) (Sum.inr (g b))

/-- DIE EHRLICHE BUCHUNG (der Loop-Befund als Theorem): `exTransjectA` liegt
    IN der gespiegelten Familie — sein Rejektions-Ziel `φ_b` ist eine
    Ein-Argument-Funktion des zweiten Arguments. `exTransjectA` ist damit ein
    ASYMMETRISCHER Zeuge (entgeht der Erst-Argument-Familie, gefangen von der
    Zweit-Argument-Familie), kein interaktiver. -/
theorem exTransjectA_inside_snd : InExtendedUnarySnd exTransjectA := by
  refine ⟨fun a _ => a, fun a b => decide (a = b),
          fun b => (fun n => decide (n = b)), ?_⟩
  intro a b
  by_cases hab : a = b
  · simp [exTransjectA, hab]
  · simp [exTransjectA, hab]

-- ============================================================
-- Teil 2 — Der Interaktions-Zeuge
-- ============================================================

/-- DER INTERAKTIONS-ZEUGE: bei `a ≠ b` Rejektion zur charakteristischen
    Funktion von `{a + b}` — das Ziel hängt an BEIDEN Argumenten (an keiner
    Ein-Argument-Wahl festmachbar, Teil 2/3). -/
def exTransjectI : ℕ → ℕ → (ℕ ⊕ (ℕ → Bool)) :=
  fun a b => if a = b then Sum.inl a else Sum.inr (fun n => decide (n = a + b))

/-- Rejektions-Zeuge (die Operation überschreitet wirklich). -/
theorem exTransjectI_rejects :
    exTransjectI 0 1 = Sum.inr (fun n => decide (n = 1)) := by
  simp [exTransjectI]

/-- AUSSCHLUSS AUS DER ERST-ARGUMENT-FAMILIE: Zeugen `(0,1)/(0,2)` — gleiches
    erstes Argument, Ziele `φ_1 ≠ φ_2`. Instanzgebunden, kein Form α.
    Beweis-Template: `exTransjectA_outside` (zwölfte Schicht) wörtlich,
    mit `0 + 1 = 1` / `0 + 2 = 2` in den e1/e2-Gleichungen. -/
theorem exTransjectI_outside_fst : ¬ InExtendedUnary exTransjectI := by
  rintro ⟨op, sel, g, h⟩
  have h1 := h 0 1
  have h2 := h 0 2
  have e1 : exTransjectI 0 1 = Sum.inr (fun n => decide (n = 1)) := by
    simp [exTransjectI]
  have e2 : exTransjectI 0 2 = Sum.inr (fun n => decide (n = 2)) := by
    simp [exTransjectI]
  rw [e1] at h1
  rw [e2] at h2
  have hg1 : g 0 = (fun n => decide (n = 1)) := by
    cases hs : sel 0 1 with
    | true => rw [hs, cond_true] at h1; exact absurd h1 (by simp)
    | false => rw [hs, cond_false] at h1; simpa using h1.symm
  have hg2 : g 0 = (fun n => decide (n = 2)) := by
    cases hs : sel 0 2 with
    | true => rw [hs, cond_true] at h2; exact absurd h2 (by simp)
    | false => rw [hs, cond_false] at h2; simpa using h2.symm
  rw [hg1] at hg2
  have := congrFun hg2 1
  simp at this

/-- AUSSCHLUSS AUS DER ZWEIT-ARGUMENT-FAMILIE: Zeugen `(1,0)/(2,0)` — gleiches
    ZWEITES Argument, Ziele `φ_1 ≠ φ_2`. Spiegelbildlich zu `outside_fst`
    (`g 0` jetzt aus der Zweit-Stelle; `1 + 0 = 1` / `2 + 0 = 2`). -/
theorem exTransjectI_outside_snd : ¬ InExtendedUnarySnd exTransjectI := by
  rintro ⟨op, sel, g, h⟩
  have h1 := h 1 0
  have h2 := h 2 0
  have e1 : exTransjectI 1 0 = Sum.inr (fun n => decide (n = 1)) := by
    simp [exTransjectI]
  have e2 : exTransjectI 2 0 = Sum.inr (fun n => decide (n = 2)) := by
    simp [exTransjectI]
  rw [e1] at h1
  rw [e2] at h2
  have hg1 : g 0 = (fun n => decide (n = 1)) := by
    cases hs : sel 1 0 with
    | true => rw [hs, cond_true] at h1; exact absurd h1 (by simp)
    | false => rw [hs, cond_false] at h1; simpa using h1.symm
  have hg2 : g 0 = (fun n => decide (n = 2)) := by
    cases hs : sel 2 0 with
    | true => rw [hs, cond_true] at h2; exact absurd h2 (by simp)
    | false => rw [hs, cond_false] at h2; simpa using h2.symm
  rw [hg1] at hg2
  have := congrFun hg2 1
  simp at this

/-- Korollar: außerhalb BEIDER unärer Familien. -/
theorem exTransjectI_outside_either :
    ¬ (InExtendedUnary exTransjectI ∨ InExtendedUnarySnd exTransjectI) := by
  rintro (h | h)
  · exact exTransjectI_outside_fst h
  · exact exTransjectI_outside_snd h

-- ============================================================
-- Teil 3 — Kür 1: die gemischte Familie
-- ============================================================

/-- Die punktweise GEMISCHTE Familie: pro Stelle darf zwischen Erst- und
    Zweit-Argument-Kanonizität gewählt werden. Der maximale unäre Rahmen. -/
def InExtendedUnaryMixed {S K : Type*} (t : S → S → (S ⊕ K)) : Prop :=
  ∃ (op : S → S → S) (sel : S → S → Bool) (g h : S → K) (sw : S → S → Bool),
    ∀ a b, t a b = cond (sel a b) (Sum.inl (op a b))
                        (Sum.inr (cond (sw a b) (g a) (h b)))

/-- KÜR 1 (Taubenschlag über der Injektivität): auch aus der punktweise
    gemischten Familie sitzt `exTransjectI` außerhalb. Für jedes rejizierende
    Paar `(a,b)` (`a ≠ b`) ist `sel a b = false` erzwungen und `φ_{a+b}` gleich
    `g a` ODER `h b`. Für festes `a` ist `b ↦ φ_{a+b}` injektiv, also gilt
    `φ_{a+b} = g a` für höchstens ein `b`; über den Spalten `{5,6,7}` sind je Zeile
    (`a = 1`, `a = 2`) mindestens zwei Spalten `h`-gedeckt. Zwei Zwei-Teilmengen
    von `{5,6,7}` schneiden sich: ein `b*` mit `h b* = φ_{1+b*}` und `h b* = φ_{2+b*}`,
    also `φ_{1+b*} = φ_{2+b*}` — Auswertung bei `1+b*` gibt `true = false`. -/
theorem exTransjectI_outside_mixed : ¬ InExtendedUnaryMixed exTransjectI := by
  rintro ⟨op, sel, g, h, sw, H⟩
  -- Die Ziel-Familie ist injektiv: verschiedene Summen ⇒ verschiedene Ziele.
  have phi_ne : ∀ {i j : ℕ}, i ≠ j →
      (fun n => decide (n = i)) ≠ (fun n => decide (n = j)) := by
    intro i j hij hcon
    have hh : decide (i = i) = decide (i = j) := congrFun hcon i
    rw [decide_eq_decide] at hh
    exact hij (hh.mp rfl)
  -- Die zentrale Disjunktion: für `a ≠ b` ist `φ_{a+b}` = `g a` oder `h b`.
  have key : ∀ a b : ℕ, a ≠ b →
      g a = (fun n => decide (n = a + b)) ∨ h b = (fun n => decide (n = a + b)) := by
    intro a b hab
    have he : exTransjectI a b = Sum.inr (fun n => decide (n = a + b)) := by
      simp [exTransjectI, hab]
    have hH := H a b
    rw [he] at hH
    cases hsel : sel a b with
    | true => rw [hsel, cond_true] at hH; exact absurd hH (by simp)
    | false =>
      rw [hsel, cond_false] at hH
      have hcond : (fun n => decide (n = a + b)) = cond (sw a b) (g a) (h b) := by
        simpa using hH
      cases hsw : sw a b with
      | true => left; rw [hsw, cond_true] at hcond; exact hcond.symm
      | false => right; rw [hsw, cond_false] at hcond; exact hcond.symm
  have d15 := key 1 5 (by decide)
  have d16 := key 1 6 (by decide)
  have d17 := key 1 7 (by decide)
  have d25 := key 2 5 (by decide)
  have d26 := key 2 6 (by decide)
  have d27 := key 2 7 (by decide)
  rcases d15 with g15 | h15 <;> rcases d16 with g16 | h16 <;>
    rcases d17 with g17 | h17 <;> rcases d25 with g25 | h25 <;>
    rcases d26 with g26 | h26 <;> rcases d27 with g27 | h27 <;>
  first
    | exact absurd (g15.symm.trans g16) (phi_ne (by decide))
    | exact absurd (g15.symm.trans g17) (phi_ne (by decide))
    | exact absurd (g16.symm.trans g17) (phi_ne (by decide))
    | exact absurd (g25.symm.trans g26) (phi_ne (by decide))
    | exact absurd (g25.symm.trans g27) (phi_ne (by decide))
    | exact absurd (g26.symm.trans g27) (phi_ne (by decide))
    | exact absurd (h15.symm.trans h25) (phi_ne (by decide))
    | exact absurd (h16.symm.trans h26) (phi_ne (by decide))
    | exact absurd (h17.symm.trans h27) (phi_ne (by decide))

-- ============================================================
-- Teil 4 — Kür 2: die Naht
-- ============================================================

/-- Die Naht über substantiellem K mit dem INTERAKTIVEN transject-Feld. -/
def exLiftedI : LiftedTransjunctiveC (Discrete ℕ) (Discrete (ℕ → Bool)) where
  transition := Discrete.functor (fun n => ⟨fun m => decide (m = n)⟩)
  transject  := liftToDiscrete exTransjectI
  rejects    := ⟨⟨0⟩, ⟨1⟩, ⟨fun n => decide (n = 1)⟩, by
    simp [liftToDiscrete, exTransjectI]⟩

/-- Der Anschluss explizit: das `transject`-Feld der Naht ist punktweise die
    gehobene `exTransjectI`. -/
theorem exLiftedI_transject_eq (a b : ℕ) :
    exLiftedI.transject ⟨a⟩ ⟨b⟩ = (exTransjectI a b).map Discrete.mk Discrete.mk :=
  rfl

-- ============================================================
-- Axiom-Sauberkeit der Kerne (kein `sorryAx`) — als Regressions-Wachen gesetzt.
-- Ist-Ausgabe des grünen Builds (v4.30.0-rc2), pro Satz eingefroren; ab hier bricht
-- jede Axiom-Drift den Build.
-- ============================================================

/-- info: 'Reformulation.Proemial.InteractiveTransjunction.exTransjectA_inside_snd' depends on axioms: [propext] -/
#guard_msgs in #print axioms exTransjectA_inside_snd

/-- info: 'Reformulation.Proemial.InteractiveTransjunction.exTransjectI_outside_fst' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms exTransjectI_outside_fst

/-- info: 'Reformulation.Proemial.InteractiveTransjunction.exTransjectI_outside_snd' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms exTransjectI_outside_snd

/-- info: 'Reformulation.Proemial.InteractiveTransjunction.exTransjectI_outside_either' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms exTransjectI_outside_either

/-- info: 'Reformulation.Proemial.InteractiveTransjunction.exTransjectI_outside_mixed' depends on axioms: [propext] -/
#guard_msgs in #print axioms exTransjectI_outside_mixed

/-- info: 'Reformulation.Proemial.InteractiveTransjunction.exLiftedI_transject_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms exLiftedI_transject_eq

end Reformulation.Proemial.InteractiveTransjunction
