import Reformulation.F3f.Stage
import Reformulation.F3g.Availability
import Reformulation.F3g.Classification

/-!
# F3.g.Anschluss — connection theorems to F3.b, F3.f

This module carries the consistency theorems connecting Path D's
class-availability combinatorics (F3.g.Availability) with:

* F3.b's K-configurations (K1–K8) and their class assignments.
* F3.e's stage-1 special condition (K1 forced at stage 1).
* F3.f's StageTransition as the base of StageTransitionWithB6Trace.

Theorems:

1. `classI_availability_iff_initialConfig_k1`: class I is available in
   stage 1 and any stage-1 instance carries K1 (coherence of class I
   availability and K1-anchoring).
2. `classII_classIII_for_intra_stage_configs`: for any stage n ≥ 1 whose
   initialConfig is intra-stage (K3 or K4), classes II and III are
   available.
3. `stageTransitionWithB6Trace_extends`: `StageTransitionWithB6Trace`
   is an additive extension of `StageTransition` (trivial).

Architecture reference: F3g_Spec §V.
-/

namespace Reformulation.F3g

open Reformulation.F3f Reformulation.F3b

universe u

/-- Class I is available in stage 1, and every stage-1 instance carries K1.

Coherence between Path D's class-I availability (stage-1-specific) and
F3.f's `initialConfig_at_stage_1` field (K1 forced at stage 1 by B5). -/
theorem classI_availability_iff_initialConfig_k1 (s : Stage 1) :
    TransitionClass.classI ∈ availableClasses 1 ∧
    s.initialConfig = K.k1 := by
  refine ⟨?_, ?_⟩
  · simp [availableClasses]
  · exact s.initialConfig_at_stage_1 rfl

/-- For any stage n ≥ 1 with an intra-stage configuration (K3 or K4),
classes II and III are available.

Coherence between F3.b's class assignments (K3 = class II canonical
bearer, K4 = class III canonical bearer) and the availability function. -/
theorem classII_classIII_for_intra_stage_configs
    (n : ℕ) (h : n ≥ 1) (_s : Stage n)
    (_hk : _s.initialConfig = .k3 ∨ _s.initialConfig = .k4) :
    TransitionClass.classII  ∈ availableClasses n ∧
    TransitionClass.classIII ∈ availableClasses n := by
  cases n with
  | zero  => omega
  | succ m =>
    cases m with
    | zero   => simp [availableClasses]
    | succ k => simp [availableClasses]

/-- `StageTransitionWithB6Trace` is an additive extension of `StageTransition`:
every `StageTransitionWithB6Trace` instance yields a `StageTransition` via the
`extends`-generated projection `toStageTransition`. -/
theorem stageTransitionWithB6Trace_extends
    (n : ℕ) (t : StageTransitionWithB6Trace.{u} n) :
    ∃ (t' : StageTransition.{u} n), t.toStageTransition = t' :=
  ⟨t.toStageTransition, rfl⟩

end Reformulation.F3g
