/-
Copyright Reformulierung-Projekt 2026.
Released under PKL-internal license.
-/
import Mathlib.CategoryTheory.Subobject.Lattice
import Reformulation.MathlibExtensions.Topos.Subobject.InitialMonoClass

/-!
# OrderBot (Subobject X) and pullback_bot for ElementaryTopos

## Main results

- `Subobject.orderBot_topos`: `OrderBot (Subobject X)` is available for any `[ElementaryTopos E]`
  via `inferInstance` (the Mathlib standard instance requires `[HasInitial C] [InitialMonoClass C]`,
  both of which are now derived from `ElementaryTopos`).

- `Subobject.pullback_bot`: `(Subobject.pullback f).obj ⊥ = ⊥` for any morphism `f : X ⟶ Y`
  in an elementary topos.

## Mathematical content

For `pullback_bot`: the bottom subobject `⊥ : Subobject Y` is represented by
`initial.to Y : ⊥_ E → Y`. Pulling back along `f : X ⟶ Y` gives a pullback square:
```
P ----fst---→ ⊥_ E
|                 |
snd          initial.to Y
|                 |↓                 ↓
X -----f-----→ Y
```
Since `⊥_ E` is strict initial (`HasStrictInitialObjects E`), the morphism
`fst : P → ⊥_ E` is an isomorphism. Hence `P` is initial, and by `InitialMonoClass E`,
`snd : P → X` is mono. The mono `snd` is uniquely determined (P is initial), giving
`snd = fst ≫ initial.to X`, so `mk snd = mk (initial.to X) = ⊥ : Subobject X`.

## Anschluss (C21-D-5)

- `pullback_bot` closes the `C21-D-5` Klasse-D shift for the `bot` case in
  `Soundness.lean/interpretFormula_subst`.
-/

namespace Reformulation.MathlibExtensions.Topos

open CategoryTheory Limits Subobject Reformulation.PathC

variable {E : Type*} [Category E] [ElementaryTopos E] [HasInitial E]

/-- In an elementary topos, `Subobject X` has a bottom element (the initial-object inclusion).
This follows from `Mathlib.CategoryTheory.Subobject.Lattice.orderBot` which requires
`[HasInitial C] [InitialMonoClass C]`; both hold for `ElementaryTopos`. -/
noncomputable example (X : E) : OrderBot (Subobject X) := inferInstance

/-- Pullback preserves the bottom subobject in an elementary topos.

That is, for any `f : X ⟶ Y`, `(Subobject.pullback f).obj ⊥ = ⊥ : Subobject X`. -/
theorem Subobject.pullback_bot {X Y : E} (f : X ⟶ Y) :
    (Subobject.pullback f).obj ⊥ = ⊥ := by
  -- Use pullback_obj_mk to avoid the `.arrow` normalization issue
  conv_lhs => rw [bot_eq_initial_to]
  rw [pullback_obj_mk (IsPullback.of_hasPullback (initial.to Y) f)]
  -- Goal: mk (pullback.snd (initial.to Y) f) = ⊥
  -- P = pullback (initial.to Y) f; fst : P → ⊥_ E is iso by HasStrictInitialObjects
  have hP : IsInitial (Limits.pullback (initial.to Y) f) :=
    IsInitial.ofStrict (Limits.pullback.fst (initial.to Y) f) initialIsInitial
  -- snd : P → X is mono (P is initial, InitialMonoClass)
  haveI : Mono (Limits.pullback.snd (initial.to Y) f) := by
    have heq : Limits.pullback.snd (initial.to Y) f =
        (hP.uniqueUpToIso initialIsInitial).hom ≫ initial.to X :=
      hP.hom_ext _ _
    rw [heq]; exact mono_comp _ _
  -- mk (pullback.snd) = mk (initial.to X) = ⊥
  rw [bot_eq_initial_to]
  -- Goal: mk (pullback.snd (initial.to Y) f) = mk (initial.to X)
  exact mk_eq_mk_of_comm _ _ (hP.uniqueUpToIso initialIsInitial) (hP.hom_ext _ _)

end Reformulation.MathlibExtensions.Topos
