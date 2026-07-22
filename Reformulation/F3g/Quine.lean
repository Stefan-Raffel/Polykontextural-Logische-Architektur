import Reformulation.F3g.Availability

/-!
# F3.g.Quine — Quine convergence via the stage-1 combinatorial specificity

This module carries `quine_convergence_protosyntactic_iff_stage_1`, the
second laying-down of `classI_iff_stage_1` from F3.g.Availability.

## Two layings-down, two methodological readings

The theorem is formally identical to `classI_iff_stage_1`. The second
laying-down carries a different doc-string making the Quine reading
explicit: stage 1 is *protosyntactic* (material-free initial singularity,
class I / initial ω available without prior balance); stages n > 1 are
*syntactic* (material-carrying, ω initialised from predecessor balance,
class I unavailable).

This sub-differentiates the stage types and is the reformulation-
convergence with Quine's incompletability result (T1b III–IV):
the protosyntactic stage carries truth formally but non-constructively
(initial singularity, no preceding balance); syntactic stages carry it
constructively (material-carried via predecessor balance).

Proof: replay of `classI_iff_stage_1`.

Architecture reference: F3g_Spec §VI.
-/

namespace Reformulation.F3g

/-- Quine convergence: stage 1 is protosyntactic, stages n > 1 are syntactic.

Formally: class I (initial ω from the singularity) is available in
stage n (n ≥ 1) if and only if n = 1.

The protosyntactic stage 1 carries class I without a preceding balance
(initial singularity, B5-anchored). Syntactic stages n > 1 carry
classes II–IV; class I is unavailable because the ω-transition in
n > 1 is B6-initialised (material-carried from predecessor balance),
not a bare singularity.

This theorem carries T1b III–IV's convergence observation formally.
It is a second laying-down of `classI_iff_stage_1` with an explicit
Quine reading in the doc-string. -/
theorem quine_convergence_protosyntactic_iff_stage_1 (n : ℕ) (h : n ≥ 1) :
    TransitionClass.classI ∈ availableClasses n ↔ n = 1 :=
  classI_iff_stage_1 n h

end Reformulation.F3g
