import Reformulation.F1.D2.Rollups.Coalgebraic.Substantial
import Reformulation.F3g.Classification

/-!
# Reformulation.F1.D2.Rollups.Coalgebraic.SubstantialRev2

Additive extension of the Substantial belegung that instantiates F3.g's
`StageTransitionWithB6Trace` class in the Layer-1/Layer-2 Rollup domain.

## What this module carries

- `fromRollupDoubleValuationSubstantialWithB6Trace` — the first substantial
  instantiation of `StageTransitionWithB6Trace`. The trivial demo in
  `F3g/Demo.lean` (`trivialTransition` over `Discrete PUnit`) carries the
  realisability; this instantiation carries the trace in a concrete
  F1-occupancy domain.

- `b6_for_substantial` — direct theorem replay of the trace field.

- `b6_unique_iteration_mode_restored` — the original existential-uniqueness
  form of the B6 theorem, restored via the trace instantiation. Substantive
  recovery of the architectural pointe that the Klasse-D reformulation in
  Substantial-Implementation-Final §IV.D.1 had weakened.

## Methodological note

The extension is additive: the existing `Substantial.lean` is not modified.
SubstantialRev2 is a parallel module that builds on Substantial's components
and instantiates F3.g's `StageTransitionWithB6Trace` class directly.

This module substantiates C13 (formal form of iterated initialisation): the
B6 form, formally carried in F3.g via the trace class, is here instantiated
in a concrete F1-domain.

## Klasse-B adaptations

**B1 — Direct construction**: `fromRollupDoubleValuationSubstantialWithB6Trace`
constructs the `StageTransitionWithB6Trace` directly (not via tuple extraction
from `fromRollupDoubleValuationSubstantial`) to avoid the opaque-product-
selector difficulty documented in Substantial-K3 §II.1.

**B2 — Second-argument form in theorem statements**: `b6_for_substantial` and
`b6_unique_iteration_mode_restored` use `trace.current.stageObj` as the second
argument to `translate` rather than `trace.current.endenFunktor.obj
trace.current.stageObj`. This avoids `Category trace.current.totalSpace`
synthesis at statement-elaboration time (the instance lives in the Stage record
field, not the global typeclass context). The mathematical content is preserved:
in our concrete implementation `translate` ignores its second argument, so both
forms denote `rollupTranslate rdv.layer1 m`.
-/

namespace Reformulation.F1.D2.Rollups.Coalgebraic.Substantial

open CategoryTheory
open Reformulation.F1.D2.Rollups.RollupGeneral
open Reformulation.F1.D2.Rollups.Families
open Reformulation.F3b Reformulation.F3c Reformulation.F3f Reformulation.F3g

/-- B6-Trace extension of the Substantial belegung.

    Constructs a `StageTransitionWithB6Trace.{1} 1` directly from a
    `RollupDoubleValuation`, using the same Stage-1 and Stage-2 data as
    `fromRollupDoubleValuationSubstantial`, plus the `omega_initialises_next`
    trace field that records B6.

    This is the first substantial instantiation of F3.g's
    `StageTransitionWithB6Trace` class. The trivial demo in `F3g.Demo`
    instantiates over `Discrete PUnit`; this instantiation carries the trace
    in the concrete Layer-1/Layer-2 Rollup domain.

    `omega_initialises_next` closes by `rfl`: `translate` ignores its
    second argument (definitionally `fun m _ => rollupTranslate rdv.layer1 m`),
    so both sides reduce to `translateOmegaOp rdv.layer1`. -/
def fromRollupDoubleValuationSubstantialWithB6Trace
    (rdv : RollupDoubleValuation) : StageTransitionWithB6Trace.{1} 1 :=
  let s2obj : Layer2RollupSubstantial :=
    { toLayer2Rollup := defaultLayer2Rollup rdv.layer1, modalAspect := .omega }
  { current := {
      totalSpace               := Layer1Chain
      stageObj                 := rdv.layer1
      endenFunktor             := rollupEndenFunktorL1 rdv.layer1
      γ                        := 𝟙 _
      initialConfig            := K.k1
      initialConfig_at_stage_1 := fun _ => rfl
      noAlgebraExtension       := trivial
    }
    next := {
      totalSpace               := Layer2RollupSubstantial
      stageObj                 := s2obj
      endenFunktor             := rollupEndenFunktorL2 s2obj
      γ                        := 𝟙 _
      initialConfig            := K.k2
      initialConfig_at_stage_1 := fun h => absurd h (by decide)
      noAlgebraExtension       := trivial
    }
    translate             := fun m _ => rollupTranslate rdv.layer1 m
    omega_initialises_next := rfl }

/-- B6 in trace-replay form for the Substantial belegung.

    States that Stage 2's stageObj equals the omega-translation of Stage 1's
    balance. Proof: `rfl` — both sides reduce to `translateOmegaOp rdv.layer1`.

    Klasse-B B2: statement avoids `let trace := ...` wrapper and uses
    `current.stageObj` (not `endenFunktor.obj stageObj`) as translate's second
    argument, sidestepping `Category` synthesis at elaboration time. Equivalent
    since `translate` ignores its second argument in this implementation.

    This theorem makes the B6 equation accessible in the Substantial domain,
    overcoming the Klasse-D weakening of Substantial-Implementation-Final §IV.D.1. -/
theorem b6_for_substantial (rdv : RollupDoubleValuation) :
    (fromRollupDoubleValuationSubstantialWithB6Trace rdv).next.stageObj =
      (fromRollupDoubleValuationSubstantialWithB6Trace rdv).translate
        ModalSymbol.omega
        (fromRollupDoubleValuationSubstantialWithB6Trace rdv).current.stageObj :=
  rfl

/-- B6 uniqueness theorem in the original existential-uniqueness form,
    restored via the trace instantiation.

    Carries two substantive aspects:
    - **Existence**: omega initialises Stage 2; closes by `rfl`.
    - **Uniqueness**: no other modal symbol does so. Proof: extract the
      modalAspect equality from `hm` via `congrArg`, then reduce via
      `dsimp [fromRollupDoubleValuationSubstantialWithB6Trace]` to expose
      a plain `rollupTranslate` equation; close each non-omega case via
      `simp + decide` (mirrors the `b6_unique_iteration_mode` pattern).

    Klasse-B B2: statement avoids `let trace := ...` and uses `current.stageObj`
    as translate's second argument (see B2 note in module header).

    Restores the original §IV B6 form from Substantial-Spec, which the
    Klasse-D adaptation had weakened to a direct `rollupTranslate.modalAspect`
    statement. -/
theorem b6_unique_iteration_mode_restored (rdv : RollupDoubleValuation) :
    ∃! m : ModalSymbol,
      (fromRollupDoubleValuationSubstantialWithB6Trace rdv).translate m
        (fromRollupDoubleValuationSubstantialWithB6Trace rdv).current.stageObj =
      (fromRollupDoubleValuationSubstantialWithB6Trace rdv).next.stageObj := by
  refine ⟨ModalSymbol.omega, rfl, ?_⟩
  intro m hm
  -- Extract modalAspect equality; dsimp concretises fromRollupDoubleValuationSubstantialWithB6Trace
  have hm' : (rollupTranslate rdv.layer1 m).modalAspect = .omega := by
    have h := congrArg (·.modalAspect) hm
    dsimp only [fromRollupDoubleValuationSubstantialWithB6Trace] at h
    exact h
  -- Only omega satisfies (rollupTranslate rdv.layer1 m).modalAspect = .omega
  cases m with
  | omega    => rfl
  | tau      => simp [rollupTranslate, translateTauOp]    at hm'
  | delta    => simp [rollupTranslate, translateDeltaOp]   at hm'
  | negTau   => simp [rollupTranslate, translateNegTauOp]  at hm'
  | negDelta => simp [rollupTranslate, translateNegDeltaOp] at hm'
  | negOmega => simp [rollupTranslate, translateNegOmegaOp] at hm'

end Reformulation.F1.D2.Rollups.Coalgebraic.Substantial
