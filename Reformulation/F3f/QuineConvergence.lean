import Reformulation.F3f.Stage

/-!
# F3.f.QuineConvergence — Quine convergence for stage 1 (Rev2: universe-polymorphic)

This module provides `quine_convergence_stage_1`, formalizing the stage-1
component of the Quine convergence noted in T1b III–IV:

Stage 1 is the material-free (protosyntactic) case — it carries K1
(trivial, constant, absent) as its initial configuration. Higher stages are
material-carrying (syntactic) and obtain their material from previous stages
via the `StageTransition` structure (B6, implicit).

The theorem follows directly from the `initialConfig_at_stage_1` field of
`Stage`, which constrains stage 1 to K1. No sorry is needed.

## Rev2 change: universe polymorphism (F3.f-K4 Möglichkeit α)

`quine_convergence_stage_1.{u}` is now universe-polymorphic in `u`, applying
to `Stage.{u} 1` instances at any universe level. The proof is unchanged.

Architecture references: F3f_Spec §V, F3f_Implementation_Prompt §IV.4.
-/

namespace Reformulation.F3f

universe u

/-- Quine convergence for stage 1: any stage-1 instance carries the
material-free K1 initial configuration.

Universe-polymorphic in `u` (per F3.f-K4 Möglichkeit α): applies to
`Stage.{u} 1` instances at any universe level.

This is the formal expression of the protosyntactic starting point of the
PKL architecture (T1b III–IV): stage 1 is materially blank (K1 =
trivial, constant, absent); all material arises through stage transitions.

Proof: direct application of `Stage.initialConfig_at_stage_1` with `rfl`.
-/
theorem quine_convergence_stage_1 (s : Stage 1) :
    s.initialConfig = Reformulation.F3b.K.k1 :=
  s.initialConfig_at_stage_1 rfl

end Reformulation.F3f
