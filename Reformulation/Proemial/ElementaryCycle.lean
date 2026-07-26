import Reformulation.Proemial.ContextureOverlap
import Mathlib.Dynamics.PeriodicPts.Defs

/-!
# Proemial.ElementaryCycle — die Elementarkontextur als Zweierbahn einer Involution

**Ertrag.** Diese Datei baut die Brücke zwischen dem Zyklusbegriff
(`Definitionen.md` §2, §14: die Elementarkontextur ist ein Selbstzyklus **oder**
ein Zweierzyklus) und dem im Korpus etablierten wertbasierten Kontextur-Begriff
`ContextureOverlap.IsElemContexture`. Der Zielsatz in einem Satz:

> Für eine Involution hat jede Bahn Größe 1 oder 2, und die Bahnen der Größe 2
> sind genau die Elementarkontexturen.

Kein freistehender Zyklusbegriff und keine allgemeine Zyklenzerlegung: der Satz
dockt an einen Träger an, den der Bestand schon führt.

## Was Benennung ist und was Ertrag

- **Benennung** ist `minimalPeriod_dvd_two` — eine dreizeilige Spezialisierung
  von `Function.isPeriodicPt_iff_minimalPeriod_dvd` aus Mathlib. Sie tritt hier
  als Hilfslemma auf, nicht als ausgewiesener Ertrag. Ebenso ist die erste Hälfte
  des Zielsatzes (`card_orb_le_two`) in dieser Darstellung im Wesentlichen
  Bibliotheks-Spezialisierung.
- **Ertrag** sitzt in den beiden Kontextur-Sätzen. `isElemContexture_orb_iff`
  identifiziert die Zweierbahnen mit den Elementarkontexturen; die tragende
  Richtung ist `exists_involutive_orb_eq`: **jede** Elementarkontextur ist als
  Bahn realisiert, an der Transposition. Ohne sie hieße der Satz nur „Bahnen der
  Größe 2 haben die Größe 2". Mathlib führt zu Bahnen von Involutionen als
  solchen nichts.

## Der Typschnitt

`orb`, `card_orb_le_two` und `orb_eq_pair` gelten über beliebigem `α` mit
`[DecidableEq α]`; erst die beiden Kontextur-Sätze sind an `Fin m` gebunden, weil
`IsElemContexture` es ist. Der Schnitt zeigt am Code, wo allgemeine Kombinatorik
aufhört und der Korpusbegriff anfängt.

## Der Selbstzyklus

Der einwertige Fall trägt hier keinen eigenen Satz. Er ist der Zweig, der die
Dichotomie erschöpfend macht — als Bahn der Größe 1 und damit formal trivial;
`Function.minimalPeriod_eq_one_iff_isFixedPt` steht wörtlich in Mathlib. Die
Ledger-Zeile zum Selbstzyklus bleibt darum offen, nicht geschlossen.

## Axiom-Lage

Das Profil `[propext, Classical.choice, Quot.sound]` ist durchgängig und wird
gemessen, nicht bekämpft: `Function.minimalPeriod` ist `noncomputable` und zieht
`Classical.choice`. Vermeidung hieße den Bahnbegriff selbst ersetzen — externer
Träger, kein vermeidbarer Griff. Die Grenze ist am Term abgelesen:
`isPeriodicPt_two`, die Involutionsaussage vor jedem Bahnbegriff, zieht nur
`Quot.sound`.

Kein `sorry`, kein `axiom`, kein Feld vom Typ `True`.
-/

open Function Finset Reformulation.Proemial.ContextureOverlap

namespace Reformulation.Proemial.ElementaryCycle

variable {α : Type*}

/-- Die **Bahn** von `x` unter `f`: das Bild der Iterierten bis zur Minimalperiode.
Die Definition erwähnt kein Paar; dass sie für eine Involution `{x, f x}` ist,
bleibt ein Satz (`orb_eq_pair`). -/
noncomputable def orb [DecidableEq α] (f : α → α) (x : α) : Finset α :=
  (range (minimalPeriod f x)).image (fun i => f^[i] x)

/-- Jeder Punkt einer Involution ist periodisch mit Periode 2. -/
theorem isPeriodicPt_two (f : α → α) (hf : Involutive f) (x : α) :
    IsPeriodicPt f 2 x := by
  show f^[2] x = x
  simpa using hf x

/-- **Benennung**, kein Ertrag: für eine Involution teilt die Minimalperiode die 2.
Spezialisierung von `Function.isPeriodicPt_iff_minimalPeriod_dvd`. -/
theorem minimalPeriod_dvd_two (f : α → α) (hf : Involutive f) (x : α) :
    minimalPeriod f x ∣ 2 :=
  isPeriodicPt_iff_minimalPeriod_dvd.mp (isPeriodicPt_two f hf x)

/-- Die Minimalperiode einer Involution ist 1 oder 2 — die Dichotomie
„Selbstzyklus oder Zweierzyklus" auf der Ebene der Periode. -/
theorem minimalPeriod_eq_one_or_two (f : α → α) (hf : Involutive f) (x : α) :
    minimalPeriod f x = 1 ∨ minimalPeriod f x = 2 := by
  have hle : minimalPeriod f x ≤ 2 :=
    Nat.le_of_dvd (by omega) (minimalPeriod_dvd_two f hf x)
  have hpos : 0 < minimalPeriod f x := (isPeriodicPt_two f hf x).minimalPeriod_pos (by omega)
  omega

/-- **Erste Hälfte des Zielsatzes.** Jede Bahn einer Involution hat höchstens
zwei Elemente. -/
theorem card_orb_le_two [DecidableEq α] (f : α → α) (hf : Involutive f) (x : α) :
    #(orb f x) ≤ 2 := by
  refine le_trans (card_image_le.trans_eq (card_range _)) ?_
  exact Nat.le_of_dvd (by omega) (minimalPeriod_dvd_two f hf x)

/-- Am Fixpunkt ist die Bahn der Selbstzyklus: `{x}`. -/
theorem orb_of_fixed [DecidableEq α] (f : α → α) {x : α}
    (hx : f x = x) : orb f x = {x} := by
  have h1 : minimalPeriod f x = 1 := minimalPeriod_eq_one_iff_isFixedPt.mpr hx
  rw [orb, h1]
  simp

/-- **Die Brücke, allgemein.** Ist `x` kein Fixpunkt der Involution `f`, so ist
die Bahn genau das Paar `{x, f x}`. -/
theorem orb_eq_pair [DecidableEq α] (f : α → α) (hf : Involutive f) {x : α}
    (hx : f x ≠ x) : orb f x = {x, f x} := by
  have h2 : minimalPeriod f x = 2 := by
    rcases minimalPeriod_eq_one_or_two f hf x with h | h
    · exact absurd (minimalPeriod_eq_one_iff_isFixedPt.mp h) hx
    · exact h
  rw [orb, h2]
  ext y
  simp only [mem_image, mem_range, mem_insert, mem_singleton]
  constructor
  · rintro ⟨i, hi, rfl⟩
    match i, hi with
    | 0, _ => exact Or.inl rfl
    | 1, _ => exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact ⟨0, by omega, rfl⟩
    · exact ⟨1, by omega, rfl⟩

/-- **Zweite Hälfte, Hinrichtung.** Die Bahn durch `x` ist genau dann eine
Elementarkontextur, wenn `x` kein Fixpunkt ist. -/
theorem isElemContexture_orb_iff {m : ℕ} (f : Fin m → Fin m) (hf : Involutive f)
    (x : Fin m) : IsElemContexture (orb f x) ↔ f x ≠ x := by
  constructor
  · intro h hfx
    rw [orb_of_fixed f hfx] at h
    simp [IsElemContexture] at h
  · intro hx
    rw [IsElemContexture, orb_eq_pair f hf hx, card_insert_of_notMem (by simpa using fun h => hx h.symm)]
    simp

/-- **Zweite Hälfte, Umkehrung — der tragende Teil.** Jede Elementarkontextur
*ist* eine Zweierbahn: zu jedem `K` mit `#K = 2` gibt es eine Involution und einen
Punkt, deren Bahn genau `K` ist. Realisiert an der Transposition. -/
theorem exists_involutive_orb_eq {m : ℕ} {K : Finset (Fin m)} (hK : IsElemContexture K) :
    ∃ (f : Fin m → Fin m) (x : Fin m), Involutive f ∧ orb f x = K := by
  obtain ⟨a, b, hab, rfl⟩ := card_eq_two.mp hK
  refine ⟨Equiv.swap a b, a, Equiv.swap_apply_self a b, ?_⟩
  have hx : Equiv.swap a b a ≠ a := by rw [Equiv.swap_apply_left]; exact fun h => hab h.symm
  rw [orb_eq_pair _ (Equiv.swap_apply_self a b) hx, Equiv.swap_apply_left]

-- ============================================================
-- Wachen — Axiom-Profile
-- ============================================================

/-! **Wachen.** Ist-Ausgabe des grünen Builds (v4.30.0-rc2). Das Profil ist
durchgängig `[propext, Classical.choice, Quot.sound]`, und die Stelle, an der die
Klassik hereinkommt, ist gemessen: `isPeriodicPt_two` — die Involutionsaussage
selbst — zieht nur `Quot.sound`; erst `Function.minimalPeriod`, `noncomputable`,
bringt `Classical.choice` mit. Das ist ein externer Träger: vermeiden hieße den
Bahnbegriff ersetzen. -/

/-- info: 'Reformulation.Proemial.ElementaryCycle.orb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms orb

/-- info: 'Reformulation.Proemial.ElementaryCycle.isPeriodicPt_two' depends on axioms: [Quot.sound] -/
#guard_msgs in #print axioms isPeriodicPt_two

/--
info: 'Reformulation.Proemial.ElementaryCycle.minimalPeriod_dvd_two' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms minimalPeriod_dvd_two

/-- info: 'Reformulation.Proemial.ElementaryCycle.card_orb_le_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms card_orb_le_two

/-- info: 'Reformulation.Proemial.ElementaryCycle.orb_eq_pair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms orb_eq_pair

/--
info: 'Reformulation.Proemial.ElementaryCycle.isElemContexture_orb_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms isElemContexture_orb_iff

/--
info: 'Reformulation.Proemial.ElementaryCycle.exists_involutive_orb_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms exists_involutive_orb_eq

end Reformulation.Proemial.ElementaryCycle
