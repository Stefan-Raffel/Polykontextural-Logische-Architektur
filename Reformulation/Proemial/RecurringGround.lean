import Reformulation.Proemial.ExhaustionTransition
import Mathlib.Data.Fin.VecNotation

/-!
# Reformulation.Proemial.RecurringGround — der wiederkehrende Grund (zwanzigste Schicht)

Die **erste Stelle** der achtfachen Thematik in Zeugen-Fassung: der Grund als
Fixpunkt, der Anker-Satz als Wiederkehr-Lemma, die Stufung ohne Sein als arme
Klasse, der Bogen-Satz zur achten Stelle — die Rand-Klammer der 1+3+3+1 in einer
Sprache, am geteilten Zeugen `collapse`. Die zwei dünnsten Sätze der Phase liegen
in dieser Schicht; ihre Docs sprechen das aus.

Zweite Schicht-zu-Schicht-Abhängigkeit (erste Kette 16→19→20): die Schicht
importiert `ExhaustionTransition` und konsumiert `Exhausts`, `collapse` und
transitiv `PointwisePeriodic` **term-identisch** — nichts wird dupliziert.

## (1) Quellen

Der Anker-Satz im vollen Wortlaut: „Das erste Thema ist selbstverständlich das
reflexionslose Sein des ersten Intervalls, das in allen folgenden
Reflexionsstufen immer wiederkehrt." — Marke: **druck-verifiziert (Beiträge III,
S. 160 = vordenker Z. 1018–1032; Doppel-Abgleich 13. Juli, Mathematiker-
Vorprüfung + volles Hermeneutes-Siegel)** — erste Schicht mit druck-verifiziertem
Anker in der Quellen-Rubrik. Kontext derselben Seite: die achte Thematik fügt die
„Ur-Designation, die Einwertigkeit" hinzu; „Die Subjektivität geht, wie Hegel
sagen würde, in ihren Grund, d.h. in das Sein zurück."

## (2) Stellen-Marke

Die Zuordnung „diese Formalisierung ist Stelle 1" ist strukturanalytisch;
**Fixpunkt ↔ reflexionslos ist Deutung**; die Einwertigkeits-Lesart ist benannter
Folge-Posten **St.1b** (nicht versprochen). Benennung ist kein Satz — term-fest
sind Fixpunkt-Eigenschaft, Wiederkehr, Fixpunktfreiheit.

## (3) Term-fest werden hiermit

`ground_recurs`, `no_ground_in_fixpointfree`, `collapse_ground` /
`collapse_not_ground_zero`, `exhausts_ground`, `exhausts_ground_recurs`, Kür
(`swap_*`, `classes_differ`).

## (4) Bauform und Stufen-Disziplin

Die **Rand-Klammer** der 1+3+3+1 als Bauform-Deutung — die beiden Rand-Stellen
sind die zwei Rollen desselben Fixpunkts (Anfangs-Invariante /
Erschöpfungs-Ziel), in einer Sprache, am geteilten Zeugen. **Ketten-Import
16→19→20** (geteilte arme Klassen und Zeugen per Import, Plan-Bindung). Die
Schicht trägt die zwei dünnsten Sätze der Phase (`no_ground_in_fixpointfree`
definitorisch, `exhausts_ground` eine Projektion) — strengste Wort-Kontrolle: die
Substanz liegt im Anker-Lemma, der Wiederkehr-Folge und der benannten Klammer,
und nirgends erzählt ein Doc es größer.

## (5) Abgrenzung

Designation ≠ Denotation gilt fort; keine Einwertigkeits- /
Boolesche-Algebra-Formalisierung (St.1b); die Mittelstellen (2–7) sind eigene
Pakete hinter dem Umriss-Gate.

## (6) Sorry-Bilanz und Axiom-Ist

0 Sorries. Axiom-Ist (je Kern-Satz `#guard_msgs`-verwacht, Datei-Ende) — der
erwartete Bereich war `propext`/`Quot.sound`, **kein `Classical`** (die Wiederkehr
rechnet nur); das Ist **unterschreitet** ihn durchweg: **kein `Quot.sound`**
tritt auf, mehrere Kern-Sätze sind axiom-frei — eine Verschärfung. Ist:
`ground_recurs` **axiom-frei** (via `Function.iterate_fixed`-Konsum, Teil 0 (1) —
schärfer als die induktive Route); `no_ground_in_fixpointfree` axiom-frei;
`collapse_ground` `[propext]` (`rfl`); `exhausts_ground` axiom-frei (Projektion);
`exhausts_ground_recurs` axiom-frei; Kür `swap_no_exhaustion` `[propext]`,
`classes_differ` `[propext]`. Dritter Datenpunkt der Spiegel-Asymmetrie auf der
Rechen-Seite: `Classical` bleibt aus.
-/

namespace Reformulation.Proemial.RecurringGround

open Reformulation.Proemial.IrreversibleAscent
open Reformulation.Proemial.ExhaustionTransition

-- ============================================================
-- Teil 1 — Merkmal und Anker-Lemma (M1)
-- ============================================================

/-- Der Grund: was unter f es selbst bleibt. Die Zuordnung zum „reflexionslosen
    Sein" (Stelle 1) ist Deutung; term-fest ist die Fixpunkt-Eigenschaft. -/
def Ground {α : Type*} (f : α → α) (a : α) : Prop := f a = a

/-- DER ANKER ALS LEMMA (druck-verifiziert, Beiträge III S. 160): was Grund
    ist, „kehrt in allen folgenden Reflexionsstufen immer wieder" — die
    Wiederkehr durch alle Iterations-Stufen. Teil 0 (1): `Function.iterate_fixed`
    existiert in v4.30 mit Signatur `(h : f a = a) (n : ℕ) : f^[n] a = a` —
    Konsum schlägt Neubeweis. -/
theorem ground_recurs {α : Type*} {f : α → α} {a : α}
    (h : Ground f a) : ∀ n, f^[n] a = a :=
  fun n => Function.iterate_fixed h n

-- ============================================================
-- Teil 2 — Arme Klasse und negative Hälfte (M2)
-- ============================================================

/-- Die Stufung ohne Sein: fixpunktfreie Iterationen — nichts bleibt durch
    alle Stufen hindurch es selbst. -/
def FixpointFree {α : Type*} (f : α → α) : Prop := ∀ x, f x ≠ x

/-- NEGATIVE HÄLFTE: in der fixpunktfreien Welt gibt es keinen Grund.
    Definitorisch dünn — die benannte Kontraposition der Definitionen;
    Doc-Rubrik (4) trägt die Stufen-Disziplin ausdrücklich. -/
theorem no_ground_in_fixpointfree {α : Type*} {f : α → α}
    (hf : FixpointFree f) : ∀ a, ¬ Ground f a :=
  fun a h => hf a h

-- ============================================================
-- Teil 3 — Geteilte Zeugen (M3)
-- ============================================================

/-- Der geteilte Zeuge: `collapse` (19.) hat den Grund 1 … -/
theorem collapse_ground : Ground collapse 1 := rfl

/-- … und 0 ist kein Grund — dieselbe Funktion bedient beide Rand-Stellen. -/
theorem collapse_not_ground_zero : ¬ Ground collapse 0 := by
  show (1 : Fin 2) ≠ 0
  decide

-- ============================================================
-- Teil 4 — Der Bogen-Satz (M4)
-- ============================================================

/-- BOGEN-SATZ: was die Erschöpfung erreicht, trägt die St.1-Invarianz — der
    gesiegelte Wortlaut „die Subjektivität geht in ihren Grund, d.h. in das
    Sein zurück" als Theorem, quell-treu. EHRLICHKEIT: beweistechnisch eine
    Projektion (h.1) — der dünnste Satz der Phase; seine Substanz ist die
    benannte Identität der Invariante über die Stellen hinweg. Zusammen mit
    `exhausts_ne` (19.) stehen beide Seiten der Quell-Spannung am Term:
    das Erreichte ist Neues (b ≠ x) UND es ist Grund. -/
theorem exhausts_ground {α : Type*} {f : α → α} {x b : α}
    (h : Exhausts f x b) : Ground f b := h.1

/-- Die Wiederkehr-Folge des Bogens: der erreichte Grund kehrt in allen
    weiteren Stufen wieder. -/
theorem exhausts_ground_recurs {α : Type*} {f : α → α} {x b : α}
    (h : Exhausts f x b) : ∀ n, f^[n] b = b :=
  ground_recurs h.1

-- ============================================================
-- Teil 5 — Kür (K1/K2)
-- ============================================================

/-- KÜR — der symmetrische Fall in Kleinstform: swap ist fixpunktfrei UND
    punktweise periodisch — weder Grund noch Erschöpfung. -/
def swap : Fin 2 → Fin 2 := ![1, 0]

theorem swap_fixpointfree : FixpointFree swap := by
  show ∀ x : Fin 2, swap x ≠ x
  decide

theorem swap_pointwise_periodic : PointwisePeriodic swap := by
  have h2 : ∀ x : Fin 2, swap^[2] x = x := by decide
  intro x
  exact ⟨2, by decide, h2 x⟩

theorem swap_no_ground : ∀ a, ¬ Ground swap a :=
  no_ground_in_fixpointfree swap_fixpointfree

theorem swap_no_exhaustion : ∀ x b, ¬ Exhausts swap x b :=
  no_exhaustion_in_periodic swap_pointwise_periodic

/-- KÜR — Klassen-Verschiedenheit: id liegt in der Periodik, nicht in der
    Fixpunktfreiheit. -/
theorem classes_differ : ∃ f : Fin 2 → Fin 2, PointwisePeriodic f ∧ ¬ FixpointFree f := by
  refine ⟨id, fun x => ⟨1, Nat.one_pos, rfl⟩, ?_⟩
  intro hf
  exact hf 0 rfl

end Reformulation.Proemial.RecurringGround

-- ============================================================
-- Teil 6 — Die `#guard_msgs`-Wachen (M6; Ist-gebunden)
-- ============================================================

-- Ist-Ausgabe des ersten grünen Builds (v4.30.0-rc2), pro Kern-Satz als Wache.
open Reformulation.Proemial.RecurringGround in
section

/-- info: 'Reformulation.Proemial.RecurringGround.ground_recurs' does not depend on any axioms -/
#guard_msgs in #print axioms ground_recurs

/-- info: 'Reformulation.Proemial.RecurringGround.no_ground_in_fixpointfree' does not depend on any axioms -/
#guard_msgs in #print axioms no_ground_in_fixpointfree

/-- info: 'Reformulation.Proemial.RecurringGround.collapse_ground' depends on axioms: [propext] -/
#guard_msgs in #print axioms collapse_ground

/-- info: 'Reformulation.Proemial.RecurringGround.exhausts_ground' does not depend on any axioms -/
#guard_msgs in #print axioms exhausts_ground

/-- info: 'Reformulation.Proemial.RecurringGround.exhausts_ground_recurs' does not depend on any axioms -/
#guard_msgs in #print axioms exhausts_ground_recurs

/-- info: 'Reformulation.Proemial.RecurringGround.swap_no_exhaustion' depends on axioms: [propext] -/
#guard_msgs in #print axioms swap_no_exhaustion

/-- info: 'Reformulation.Proemial.RecurringGround.classes_differ' depends on axioms: [propext] -/
#guard_msgs in #print axioms classes_differ

end
