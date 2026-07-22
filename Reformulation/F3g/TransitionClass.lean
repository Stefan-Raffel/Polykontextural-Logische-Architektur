import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.DeriveFintype

/-!
# F3.g.TransitionClass — the four transition classes and ClassIV sub-differentiation

Introduces `TransitionClass` (classes I–IV) and `ClassIVSubtype`
(initialising / continuing), the inductive types carrying the
combinatorial skeleton of the iteration-stage modulation (Path D:
T1b III, T5 V–VI, T8 III).

No proofs; purely definitional content.

Architecture reference: F3g_Spec §II.
-/

namespace Reformulation.F3g

/-- The four transition classes of the PKL vierfachklassifikation.

* Class I   — initial ω from the reflection-free singularity;
              stage-1-specific (B5-carried).
* Class II  — intra-familial δ (schema change within a family).
* Class III — inter-familial δ (schema change between families;
              wider reach than class II).
* Class IV  — trans-stage ω (stage change); in stages n > 1
              sub-differentiated via `ClassIVSubtype`.
-/
inductive TransitionClass : Type where
  /-- Class I: initial ω from the reflection-free singularity. Stage-1-specific (B5-carried). -/
  | classI   : TransitionClass
  /-- Class II: intra-familial δ (schema change within a family). -/
  | classII  : TransitionClass
  /-- Class III: inter-familial δ (schema change between families; wider reach than II). -/
  | classIII : TransitionClass
  /-- Class IV: trans-stage ω (stage change). Sub-differentiated in stages n > 1. -/
  | classIV  : TransitionClass
  deriving DecidableEq, Repr, Fintype

/-- Sub-differentiation of Class IV in stages n > 1.

* Initialising ω — opens the successor stage (B6-carried).
* Continuing ω   — operates within the stage after initialisation.
-/
inductive ClassIVSubtype : Type where
  /-- Initialising ω: opens the successor stage (B6-carried). -/
  | initialising : ClassIVSubtype
  /-- Continuing ω: operates within the stage after initialisation. -/
  | continuing   : ClassIVSubtype
  deriving DecidableEq, Repr, Fintype

end Reformulation.F3g
