import Mathlib.CategoryTheory.Discrete.Basic
import Reformulation.F3g.Classification

/-!
# F3.g.Demo — realisability demonstration for StageTransitionWithB6Trace

Demonstrates that `StageTransitionWithB6Trace` is instantiable by
constructing a trivial instance over `Discrete PUnit` (the one-object
discrete category).

This is not an F1 belegung (no domain binding to a concrete mathematical
field). Its purpose is to show the structure class is non-empty.

## Trivial domain: Discrete PUnit

`totalSpace := Discrete PUnit` uses the one-element discrete category
from Mathlib (`CategoryTheory.DiscreteCategory`). The stage object is
`Discrete.mk PUnit.unit`. The end-functor is the identity `𝟭 (Discrete PUnit)`.
The coalgebra structure γ is `𝟙 _` (identity morphism). The translation
function `translate` sends every modal symbol and every element to
`Discrete.mk PUnit.unit`.

## Klasse-B adaptation: universe annotation

`trivialStage` and `trivialTransition` use `Stage.{0}` and
`StageTransitionWithB6Trace.{0}` with universe 0 (totalSpace in `Type`),
since `Discrete PUnit : Type` (universe 0). This matches
`Stage.{u}` with `u = 0`.

Architecture reference: F3g_Spec §VII.
-/

namespace Reformulation.F3g.Demo

open CategoryTheory Reformulation.F3f Reformulation.F3b Reformulation.F3c

/-- Trivial stage over `Discrete PUnit`.

Total space is the one-object discrete category. The end-functor is the
identity; the coalgebra structure γ is the identity morphism. The
`initialConfig` follows the K1/K2 split required by `initialConfig_at_stage_1`.

This carries no substantive PKL domain binding. -/
def trivialStage (n : ℕ) : Stage.{0} n where
  totalSpace             := Discrete PUnit
  stageObj               := Discrete.mk PUnit.unit
  endenFunktor           := 𝟭 (Discrete PUnit)
  γ                      := 𝟙 _
  initialConfig          := if n = 1 then K.k1 else K.k2
  initialConfig_at_stage_1 := by
    intro h; rw [h]; simp
  noAlgebraExtension     := True.intro

/-- Trivial B6-trace transition over `Discrete PUnit`.

Both stages are `trivialStage`. The translation sends every element to
`Discrete.mk PUnit.unit`. The `omega_initialises_next` proof closes by
`rfl`: both sides reduce to `Discrete.mk PUnit.unit` under definitional
unfolding of `trivialStage`, `stageBalance`, and the identity functor. -/
def trivialTransition (n : ℕ) (_h : n ≥ 1) :
    StageTransitionWithB6Trace.{0} n where
  current                := trivialStage n
  next                   := trivialStage (n + 1)
  translate              := fun _ _ => Discrete.mk PUnit.unit
  omega_initialises_next := rfl

/-- Realisability: for every stage n ≥ 1, `StageTransitionWithB6Trace` is
non-empty. Witnessed by `trivialTransition`. -/
theorem stageTransitionWithB6Trace_realisable (n : ℕ) (h : n ≥ 1) :
    Nonempty (StageTransitionWithB6Trace.{0} n) :=
  ⟨trivialTransition n h⟩

end Reformulation.F3g.Demo
