import Reformulation.Proemial.BranchingCoalgebra

/-!
# Reformulation.Proemial.FlowIteration — der Iterations-Fluss (neunundzwanzigste Schicht)

**AP6-Zug-2, reiner Term-Zug.** Auf dem Fundament der 28. macht die
n-Schritt-Möglichkeits-Menge `reachSet c n a := (flow c)^[n] {a}` das
Langzeit-Verhalten der Verzweigung messbar. **Bahn gegen Sättigung:** ohne Gabel
bleibt die Möglichkeit Einer für alle Zeit (`det_reach`), die Gabel sättigt in
einem Schritt und die Sättigung bleibt (`fork_reach`) — die **iterierte Fassung
der Miniatur** der 28.: was dort Operator-Vergleich war, ist hier Langzeit-
Verhalten; die Miniatur bleibt Miniatur, kein neuer Differential-Anspruch.

**Ein Import** (`BranchingCoalgebra`, transitiv die gesamte Kette und das
Substrat); die Kette wird 16→…→28→29. Term-identisch konsumiert werden
`Branching`, `det`, `flow`, `fork`, `flow_det`, `flow_singleton`, `flow_monotone`
(28.), `reflect_iterate` (25.), `reflect_singleton` (26.). Nichts wird dupliziert;
**kein Mathlib-Import über die transitive Hülle hinaus**.

## (1) Bestands-Lage

Reiner Term-Zug, keine neue Quellen-Berührung; kein Stellen-Bau (kein Intervall,
keine Marken-Trias); AP6-Zug-2 auf dem Fundament der 28.

## (2) NAMENS-MARKE (Pflicht)

`reachSet` ist die **Erreichbarkeits-Menge der Koalgebra** und hat **keine
Beziehung zur Reichweiten-Disziplin** des Projekts — Struktur-Begriff der
Koalgebra, nicht Methoden-Begriff. Die Namensgleichheit ist zufällig und hier
entschärft.

## (3) Deutungs-Marken

„Bahn" und „Sättigung" sind **markierte Struktur-Aussagen** (Projekt-Rede); der
Kontrast `det_reach` gegen `fork_reach` ist die **iterierte Miniatur** der 28. —
**kein neuer Differential-Anspruch**; kein Physik-Anspruch; Designation ist nicht
Denotation.

## (4) Term-fest werden hiermit

Die fünf Sätze `flow_iterate_det`, `det_reach`, `fork_flow_full`, `fork_reach`,
Kür `flow_iterate_monotone`.

**KONSUM-EHRLICHKEIT:** `flow_iterate_det` (M2) ist Umschreibung via `flow_det`
plus Konsum des Iterations-Gesetzes der 25.; `det_reach` (M3) ist Konsum-Kette
(`flow_det` rückwärts auf `reflect_singleton`); eigener Beweis-Gehalt liegt in
`fork_flow_full`/`fork_reach` (M4) und der Induktions-Führung.

## (5) Abgrenzung

Der **Ketten-Satz** (`reachSet`-Mitgliedschaft als n-Schritt-Kollaps-Kette) ist
**benannt, nicht gebaut** — er braucht ein Ketten-Prädikat (Kandidat Zug 3).
Koalgebra-Morphismen und Kontextur-Faserung bleiben Folge-Pakete. Konditional ist
nichts; gesetzt ist nichts (`Set.Nonempty` in `fork_flow_full` ist
Voraussetzungs-Ehrlichkeit).

## (6) Sorry-Bilanz und Axiom-Ist — mit Vormessung und Rechnungs-Abgleich

**0 Sorries.** Axiom-Ist (erster grüner Build, v4.30.0-rc2), je Satz
`#guard_msgs`-verwacht am Datei-Ende (fünf Wachen): **alle fünf**
`[propext, Quot.sound]`.

**Vormessungs-Posten (Teil 0 (1)):** `Function.iterate_succ_apply'` ist **nicht
axiom-frei**, sondern `[propext, Quot.sound]` (gemessen) — die Spec-Erwartung
„axiom-frei" trifft **nicht** zu. Damit erbt die Kür `flow_iterate_monotone`
`[propext, Quot.sound]` (Basisfall `zero` axiom-frei, aber der `succ`-Schritt zieht
`iterate_succ_apply'`); die von der Rechnung als „potenziell axiom-frei" markierte
Kür liegt also im propext-Bereich. Ehrliche Abweichung nach oben, keine
Verschärfung.

**Abgleich gegen die Profil-Rechnung (M5(6), R2 = Erwartung):** M2/M3 erben
`[propext, Quot.sound]` (Konsum `flow_det`) — getroffen; M4a Set-ext
`[propext, Quot.sound]` — getroffen; M4b erbt M4a plus die `iterate_succ_apply'`-
und Insert-Anteile, gleiches Niveau — getroffen; **Kür `[propext, Quot.sound]`
statt axiom-frei** — die einzige Abweichung, Grund ist die `iterate_succ_apply'`-
Vormessung. **Kein `Classical`** an keiner der fünf Stellen.
-/

namespace Reformulation.Proemial.FlowIteration

open Reformulation.Proemial.BranchingCoalgebra
open Reformulation.Proemial.ContentReflexivity
open Reformulation.Proemial.MediationProcess

-- ============================================================
-- Teil 1 — Die Konstruktion (M1)
-- ============================================================

/-- Die n-Schritt-Möglichkeits-Menge (Erreichbarkeits-Menge der Koalgebra).
    NAMENS-MARKE: `reachSet` hat keine Beziehung zur Reichweiten-Disziplin
    des Projekts — Struktur-Begriff der Koalgebra, nicht Methoden-Begriff. -/
def reachSet {α : Type*} (c : Branching α) (n : ℕ) (a : α) : Set α :=
  (flow c)^[n] {a}

-- ============================================================
-- Teil 2 — Iterierter Anschluss und Bahn (M2/M3)
-- ============================================================

/-- Der iterierte deterministische Fluss IST die iterierte Hebung. -/
theorem flow_iterate_det {α : Type*} (f : α → α) (n : ℕ) (S : Set α) :
    (flow (det f))^[n] S = f^[n] '' S := by
  rw [flow_det]; exact reflect_iterate f n S

/-- „OHNE GABEL BLEIBT DIE MÖGLICHKEIT BAHN": Einer, für alle Zeit
    (markierte Struktur-Aussage). -/
theorem det_reach {α : Type*} (f : α → α) (n : ℕ) (a : α) :
    reachSet (det f) n a = {f^[n] a} := by
  show (flow (det f))^[n] {a} = {f^[n] a}
  rw [flow_det]
  exact reflect_singleton f n a

-- ============================================================
-- Teil 3 — Sättigung (M4)
-- ============================================================

/-- Das Sättigungs-Lemma: auf bewohntem Inhalt füllt die Gabel den Raum
    in einem Schritt. -/
theorem fork_flow_full (S : Set (Fin 2)) (h : S.Nonempty) :
    flow fork S = {0, 1} := by
  apply Set.ext
  intro y
  constructor
  · rintro ⟨a, _, hy⟩
    exact hy
  · intro hy
    obtain ⟨a, ha⟩ := h
    exact ⟨a, ha, hy⟩

/-- „DIE GABEL SÄTTIGT, UND DIE SÄTTIGUNG BLEIBT" (markierte
    Struktur-Aussage): mit `det_reach` die ITERIERTE MINIATUR — Bahn gegen
    Vollraum; kein neuer Differential-Anspruch. -/
theorem fork_reach (a : Fin 2) (n : ℕ) (h : 0 < n) :
    reachSet fork n a = {0, 1} := by
  induction n with
  | zero => exact absurd h (by decide)
  | succ m ih =>
      rcases Nat.eq_zero_or_pos m with hm | hm
      · subst hm
        show flow fork {a} = {0, 1}
        exact flow_singleton fork a
      · have hm2 : (flow fork)^[m] {a} = {0, 1} := ih hm
        show (flow fork)^[m + 1] {a} = {0, 1}
        rw [Function.iterate_succ_apply', hm2]
        exact fork_flow_full {0, 1} ⟨0, Or.inl rfl⟩

-- ============================================================
-- Teil 4 — Kür (K1)
-- ============================================================

/-- KÜR: der iterierte Fluss achtet die Inhalts-Ordnung — Induktion über die
    (axiom-freie) Kür der 28. Ist-Profil `[propext, Quot.sound]`: der
    `succ`-Schritt zieht `Function.iterate_succ_apply'` (Vormessung Modul-Doc (6):
    nicht axiom-frei). -/
theorem flow_iterate_monotone {α : Type*} (c : Branching α) (n : ℕ)
    {S T : Set α} (h : S ⊆ T) : (flow c)^[n] S ⊆ (flow c)^[n] T := by
  induction n with
  | zero => exact h
  | succ n ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      exact flow_monotone c ih

end Reformulation.Proemial.FlowIteration

-- ============================================================
-- Teil 5 — Die `#guard_msgs`-Wachen (M7; Ist-gebunden)
-- ============================================================

-- Ist-Ausgabe des ersten grünen Builds (v4.30.0-rc2), pro Satz als Wache.
open Reformulation.Proemial.FlowIteration in
section

/-- info: 'Reformulation.Proemial.FlowIteration.flow_iterate_det' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms flow_iterate_det

/-- info: 'Reformulation.Proemial.FlowIteration.det_reach' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms det_reach

/-- info: 'Reformulation.Proemial.FlowIteration.fork_flow_full' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms fork_flow_full

/-- info: 'Reformulation.Proemial.FlowIteration.fork_reach' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms fork_reach

/-- info: 'Reformulation.Proemial.FlowIteration.flow_iterate_monotone' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms flow_iterate_monotone

end
