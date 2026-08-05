import Mathlib.Data.Finset.Basic
import Reformulation.F3g.TransitionClass

/-!
# F3.g.Availability — class availability per stage and ClassIV sub-differentiation

Defines `availableClasses` (four classes in stage 1; three in stages n ≥ 2)
and `classIVSubtype` (none in stages 0–1; {initialising, continuing} in
stages n ≥ 2).

Carries Theorems 1–3:
- Theorem 1: `class_availability_stage_1` / `class_availability_stage_succ`.
- Theorem 2: `classI_iff_stage_1` (class I available ↔ n = 1).
- Theorem 3: `classIV_subtype_stage_1` / `classIV_subtype_stage_succ`.

Klasse-B adaptation: explicit `_ + 2` pattern instead of wildcard `_` for the
n ≥ 2 case of both `availableClasses` and `classIVSubtype`, to ensure Lean's
pattern-match engine maps the third branch exactly to n ≥ 2. Proof tactics
follow the spec's prescribed strategies (rfl, cases + omega, simp).

Architecture reference: F3g_Spec §III.
-/

namespace Reformulation.F3g

open Finset

/-- Available transition classes per stage index.

- Stage 0: ∅ (no PKL stage with index 0).
- Stage 1: {I, II, III, IV} (B5-anchored initial stage, all four classes).
- Stage n ≥ 2: {II, III, IV} (class I is stage-1-specific; ω in n ≥ 2 is
  sub-differentiated via `classIVSubtype`).
-/
def availableClasses : ℕ → Finset TransitionClass
  | 0     => ∅
  | 1     => {.classI, .classII, .classIII, .classIV}
  | _ + 2 => {.classII, .classIII, .classIV}

/-- ClassIV sub-differentiation per stage index.

- Stage 0 and stage 1: `none` (no sub-differentiation needed).
- Stage n ≥ 2: `some {initialising, continuing}`.
-/
def classIVSubtype : ℕ → Option (Finset ClassIVSubtype)
  | 0     => none
  | 1     => none
  | _ + 2 => some {.initialising, .continuing}

-- Theorem 1 — class availability per stage

/-- Stage 1 carries all four transition classes (I–IV). -/
theorem class_availability_stage_1 :
    availableClasses 1 = {.classI, .classII, .classIII, .classIV} := rfl

/-- Stages n + 1 ≥ 2 carry exactly classes II–IV (class I is stage-1-specific). -/
theorem class_availability_stage_succ (n : ℕ) (h : n ≥ 1) :
    availableClasses (n + 1) = {.classII, .classIII, .classIV} := by
  cases n with
  | zero  => omega
  | succ k => rfl

-- Theorem 2 — class I stage-1 specificity

/-- Class I is available in stage n (n ≥ 1) if and only if n = 1. -/
theorem classI_iff_stage_1 (n : ℕ) (h : n ≥ 1) :
    TransitionClass.classI ∈ availableClasses n ↔ n = 1 := by
  constructor
  · intro hmem
    cases n with
    | zero   => omega
    | succ m =>
      cases m with
      | zero   => rfl
      | succ k => simp [availableClasses] at hmem
  · intro hn
    subst hn
    simp [availableClasses]

-- Theorem 3 — ClassIV sub-differentiation per stage

/-- Stage 1 has no ClassIV sub-differentiation. -/
theorem classIV_subtype_stage_1 :
    classIVSubtype 1 = none := rfl

/-- Stages n + 1 ≥ 2 carry both ClassIV subtypes (initialising and continuing). -/
theorem classIV_subtype_stage_succ (n : ℕ) (h : n ≥ 1) :
    classIVSubtype (n + 1) = some {.initialising, .continuing} := by
  cases n with
  | zero  => omega
  | succ k => rfl

-- ============================================================
-- Wachen — Axiom-Profile
-- ============================================================

/-! **Wache (Zug B).** Ist-Ausgabe des grünen Builds (v4.30.0-rc2), eingefroren.

Gewacht ist `classI_iff_stage_1`, und zwar nach dem **zweiten** Kriterium des Zuges: er
trug keinen `#print axioms`-Aufruf, wird aber von `Reformulation.F3g.Quine` im
Beweisterm konsumiert und liegt ausserhalb jeder Wachenhülle. Er ist der einzige Satz
des Zuges, der allein über den Zeugen-Konsum hereinkommt — und der erste, den das
Kriterium **im Aggregat** trifft statt im Sondenbereich.

Die übrigen vier Sätze dieser Datei tragen nach der Vorgabe keine Wache: sie werden
modulfremd nicht konsumiert. -/

/-- info: 'Reformulation.F3g.classI_iff_stage_1' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms classI_iff_stage_1

end Reformulation.F3g
