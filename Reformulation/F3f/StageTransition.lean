import Reformulation.F3c.Operators
import Reformulation.F3f.Stage

/-!
# F3.f.StageTransition — the coalgebraic transition structure (Rev2: universe-polymorphic)

This module introduces `StageTransition`, the second structure class of F3.f.
A `StageTransition n` represents the transition from stage n to stage (n+1),
carrying the two-step transition form from T1a V:

1. **Balance formation** (functorial): γ : 𝔖_n ⟶ F_n(𝔖_n) in Stage n.
2. **Translation** (non-functorial): from the balance F_n(𝔖_n) to the initial
   object of stage n+1. This second step is the architectural locus of the
   modal choice (T1b I).

## Rev2 change: universe polymorphism (F3.f-K4 Möglichkeit α)

`StageTransition.{u}` is now universe-polymorphic in `u`, parallel to
`Stage.{u}`. Both `current : Stage.{u} n` and `next : Stage.{u} (n + 1)`
live in the same universe `u`. F1 belegungen with Type-1 domains use
`StageTransition.{1}` directly.

Note: the two-stage form operates within a uniform universe. Stage-typed
variation in universe levels (current in `u`, next in `v`) would require a
two-universe form, deferred to a future Rev3 if needed.

## Architectural invariants

**translate is non-functorial.** `translate` maps between *objects* (terms of
types), not between *categories* (functors). This is the formal expression of
the non-functoriality of the translation step. An algebra extension would
require `translate m` to be a functor between the stage categories, which is
structurally forbidden (T1a V: the next stage is not constructed from the
previous one via a global functor).

**Modal differentiation.** The translate field is indexed by `ModalSymbol`
(τ, δ, ω, ¬_τ, ¬_δ, ¬_ω from F3.c with F3.d extension). This realizes T1b I:
the modal triad structures the choice at the translation point.

**B6 implicitly.** The iterated initialization of higher stages (B6, T5 V–VI)
is implicit in the StageTransition form: γ produces stage n's balance, and
`translate m` maps the balance into stage n+1's total space.

**No self-reference.** StageTransition links two Stage instances (current, next)
without Stage or StageTransition being self-referential (K3-Verfeinerung).

Architecture references: F3f_Spec §IV, F3f_Implementation_Prompt §IV.3.
-/

namespace Reformulation.F3f

open CategoryTheory

universe u

/-- The transition from stage n to stage (n + 1).

`StageTransition.{u} n` is universe-polymorphic in `u` (per F3.f-K4
Möglichkeit α): both `current` and `next` live in `Stage.{u}`, operating
within a uniform universe.

Fields:
- `current`: the current stage (Stage.{u} n).
- `next`: the next stage (Stage.{u} (n + 1)).
- `translate`: the modally differentiated translation from the balance of the
  current stage to the next stage's total space. Indexed by `ModalSymbol`
  (six values: τ, δ, ω, ¬_τ, ¬_δ, ¬_ω). For each modal mode m,
  `translate m` is a function from the current stage's total space to the
  next stage's total space.

  Klasse-B-Anpassung (Lean-4-Semantik): the spec's signature
  `current.endenFunktor.obj current.stageObj → next.totalSpace` requires
  that objects of `current.totalSpace` are themselves types (universe
  constraint). At the invariant layer, the natural well-typed form is
  `current.totalSpace → next.totalSpace`: a function from any object of
  the current stage (including specifically the balance
  `current.endenFunktor.obj current.stageObj`) to an object of the next
  stage. The application
    `translate m (current.endenFunktor.obj current.stageObj) : next.totalSpace`
  expresses the translated balance concretely.

  This is non-functorial: `translate m` is a raw function between types,
  not a functor between categories. The type system does not permit
  promoting `translate m` to a functor without additional structure.
-/
structure StageTransition (n : ℕ) where
  /-- The current stage. -/
  current : Stage.{u} n
  /-- The next stage. -/
  next : Stage.{u} (n + 1)
  /-- Modally differentiated translation from the current stage's balance
  to the next stage's total space. Non-functorial object-level map.
  `translate m (current.endenFunktor.obj current.stageObj)` gives the
  image of the balance under modal translation mode m. -/
  translate : Reformulation.F3c.ModalSymbol → (current.totalSpace → next.totalSpace)

end Reformulation.F3f
