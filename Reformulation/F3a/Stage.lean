import Mathlib.Data.Nat.Basic

/-!
# F3.a.Stage — stage index and ω sub-differentiation

This module introduces:

* `Stage`: type alias for ℕ, indexing the stages of the cumulative
  iteration. Convention: `n = 0` denotes the first stage (Hebdomas in
  the architectural reading); `n + 1` denotes the n+1-th stage. The
  architectural numbering is 1-based, the Lean numbering is 0-based;
  doc-strings respect the architectural convention.
* `IsInitializing`: predicate identifying the initializing ω sub-form
  (available in every stage by B5).
* `IsContinuing`: predicate identifying the continuing ω sub-form
  (available only for stages `n + 1`, i.e. stage 2 and higher).

See F3a_Klaerung_3.md §VII.3 and F3a_Spec.md §0.3, §II.
-/

namespace Reformulation.F3a

/-- Stage index for the cumulative iteration. `Stage = ℕ` with the
convention that `0` denotes the first stage. -/
abbrev Stage : Type := ℕ

/-- The initializing ω sub-form is available in every stage `n`:
in stage `n`, it opens stage `n + 1`. By B5, this is the only ω
form in stage 1 (n = 0). -/
def IsInitializing (_n : Stage) : Prop := True

/-- The continuing ω sub-form is available only for stages `n ≥ 1`
(i.e. `Nat.succ k` for some `k`); in stage `n + 1`, it operates within
the stage on the balance from stage `n`. By B5, stage 1 (n = 0) has
no continuing ω. -/
def IsContinuing : Stage → Prop
  | 0       => False
  | _ + 1   => True

/-- E0 — stage 1 has no continuing ω form (by B5). -/
theorem stage_one_no_continuing : ¬ IsContinuing 0 := by
  intro h
  exact h

/-- Every stage has the initializing ω form (trivially, since
`IsInitializing` is `True` for every stage). -/
theorem every_stage_has_initializing (n : Stage) : IsInitializing n :=
  trivial

end Reformulation.F3a
