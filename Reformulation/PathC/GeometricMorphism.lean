import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Mathlib.CategoryTheory.Whiskering
import Reformulation.PathC.ElementaryTopos
import Reformulation.PreC.GeometricMorphismMin

/-!
# Reformulation.PathC.GeometricMorphism

The second gap closure of the full Path-C implementation: the full
`GeometricMorphism` structure that extends `Reformulation.PreC.GeometricMorphismMin`
with composition, identity, and 2-morphisms.

## What this module carries

- `GeometricMorphism E F` — extends `PreC.GeometricMorphismMin E F` with
  `ElementaryTopos` typeclass conditions; no additional data fields.

- `GeometricMorphism.id E` — the identity geometric morphism.

- `GeometricMorphism.comp f g` — composition of geometric morphisms.
  Carries `inverse = g.inverse ⋙ f.inverse`, `direct = f.direct ⋙ g.direct`,
  the composed adjunction via `Adjunction.comp`, and composed finite-limit
  preservation via `comp_preservesFiniteLimits`.

- `TwoMorphism f g` — the type of 2-morphisms between two geometric morphisms
  `f g : E → F`, defined as natural transformations between inverse-image
  functors: `f.inverse ⟶ g.inverse`.

- `TwoMorphism.id`, `TwoMorphism.vcomp` — identity and vertical composition.

- `TwoMorphism.hcomp` — horizontal composition via whiskering.

- Categorical laws (`id_comp`, `comp_id`, `assoc`) stated with proofs deferred
  (see Klasse-B finding B-2/β below).

- `GeometricMorphism.ofMin`, `GeometricMorphism.toMin` — bundling/unbundling
  helpers between PathC and PreC.

## Methodological note

This is the second module of the Path-C subdirectory `Reformulation.PathC`.
It extends Pre-C's minimal geometric morphism with the 2-category machinery
of elementary topoi, without instantiating Mathlib's `Bicategory` typeclass;
that instance is reserved for a follow-up file.

## Klasse-B finding (B-1/δ): struct-inheritance pattern for `ofMin`

The Pre-C `GeometricMorphismMin` fields are: `inverse`, `direct`, `adjunction`,
`inverse_preservesFiniteLimits`. The PathC `GeometricMorphism` adds no new
fields; both `{ m with }` and `{ toGeometricMorphismMin := m }` work for
`ofMin`.

## Klasse-B finding (B-2/β): categorical laws require adjunction transport

The categorical laws `id_comp`, `comp_id`, `assoc` cannot be closed by `rfl`
after `cases` because `Adjunction.comp` with identity adjunctions produces
structurally different (but propositionally equal) proof terms for unit and
counit. Specifically, `adj.comp Adjunction.id` and `adj` have the same type
after `simp [Functor.comp_id, Functor.id_comp]`, but their data (unit/counit
natural transformations) differ. The laws are stated with `sorry`; they would
require proving `adj.comp Adjunction.id = adj` via component-wise unit/counit
equality — a non-trivial but principled calculation.

## Klasse-B finding (B-3/γ): `whiskerLeft`/`whiskerRight` namespace

`whiskerLeft` and `whiskerRight` live in `CategoryTheory.Functor` (in
`Mathlib.CategoryTheory.Whiskering`). The spec's `import Mathlib.CategoryTheory.NatTrans`
is replaced by `import Mathlib.CategoryTheory.Whiskering`, and
`open CategoryTheory.Functor` is needed for the unqualified names.

## References

S. MacLane, I. Moerdijk, *Sheaves in Geometry and Logic*, Springer 1992.
Chapter VII, §1.
-/

namespace Reformulation.PathC

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor

universe v u

/-- A geometric morphism between elementary topoi `E` and `F` extends the
    Pre-C minimal geometric morphism structure with `ElementaryTopos` typeclass
    conditions. No additional fields are added; the extension serves to anchor
    the substance in the PathC namespace and to enable composition and
    2-morphisms as operative definitions.

    The four inherited fields from `PreC.GeometricMorphismMin` are:
    - `inverse : F ⥤ E` — inverse-image functor (left adjoint, left-exact)
    - `direct : E ⥤ F` — direct-image functor (right adjoint)
    - `adjunction : inverse ⊣ direct`
    - `inverse_preservesFiniteLimits : PreservesFiniteLimits inverse` -/
structure GeometricMorphism (E F : Type u) [Category.{v} E] [Category.{v} F]
    [ElementaryTopos E] [ElementaryTopos F]
    extends Reformulation.PreC.GeometricMorphismMin E F where

section Identity

variable (E : Type u) [Category.{v} E] [ElementaryTopos E]

/-- The identity geometric morphism on an elementary topos `E`.
    Both functors are `𝟭 E`, the adjunction is `Adjunction.id`. -/
def GeometricMorphism.id : GeometricMorphism E E where
  inverse := 𝟭 E
  direct := 𝟭 E
  adjunction := Adjunction.id
  inverse_preservesFiniteLimits := inferInstance

end Identity

section Composition

variable {E F G : Type u}
variable [Category.{v} E] [Category.{v} F] [Category.{v} G]
variable [ElementaryTopos E] [ElementaryTopos F] [ElementaryTopos G]

/-- Composition of geometric morphisms. Given `f : E → F` and `g : F → G`,
    constructs `f.comp g : E → G` with:
    - `inverse = g.inverse ⋙ f.inverse` (G ⥤ E)
    - `direct = f.direct ⋙ g.direct` (E ⥤ G)
    - adjunction via `g.adjunction.comp f.adjunction`
    - finite-limit preservation via `comp_preservesFiniteLimits`

    Note on adjunction composition order: `Adjunction.comp (adj₁ : F ⊣ G) (adj₂ : H ⊣ I)`
    produces `F ⋙ H ⊣ I ⋙ G`. For geometric morphisms `f : E → F`, `g : F → G`,
    the composite `g.adjunction.comp f.adjunction` produces
    `g.inverse ⋙ f.inverse ⊣ f.direct ⋙ g.direct` as required. -/
def GeometricMorphism.comp (f : GeometricMorphism E F) (g : GeometricMorphism F G) :
    GeometricMorphism E G where
  inverse := g.inverse ⋙ f.inverse
  direct := f.direct ⋙ g.direct
  adjunction := g.adjunction.comp f.adjunction
  inverse_preservesFiniteLimits := by
    haveI := f.inverse_preservesFiniteLimits
    haveI := g.inverse_preservesFiniteLimits
    exact comp_preservesFiniteLimits g.inverse f.inverse

end Composition

-- Categorical laws (id_comp, comp_id, assoc) are proved in
-- Reformulation.PathC.GeometricMorphismLaws as `*_proof` variants.

section TwoMorphisms

variable {E F : Type u}
variable [Category.{v} E] [Category.{v} F]
variable [ElementaryTopos E] [ElementaryTopos F]

/-- A 2-morphism between two geometric morphisms `f g : E → F` is a natural
    transformation between their inverse-image functors `f.inverse ⟶ g.inverse`.

    Convention follows MacLane-Moerdijk §VII.1: 2-morphisms are in the
    inverse-image direction. The dual choice (direct-image direction) would
    give `g.direct ⟶ f.direct`. -/
def TwoMorphism (f g : GeometricMorphism E F) : Type _ :=
  f.inverse ⟶ g.inverse

/-- Identity 2-morphism on a geometric morphism. -/
def TwoMorphism.id (f : GeometricMorphism E F) : TwoMorphism f f :=
  𝟙 f.inverse

/-- Vertical composition of 2-morphisms: given `α : f ⟶ g` and `β : g ⟶ h`,
    produce `α ≫ᵥ β : f ⟶ h` via natural transformation composition. -/
def TwoMorphism.vcomp {f g h : GeometricMorphism E F}
    (α : TwoMorphism f g) (β : TwoMorphism g h) : TwoMorphism f h :=
  α ≫ β

end TwoMorphisms

section HorizontalComposition

variable {E F G : Type u}
variable [Category.{v} E] [Category.{v} F] [Category.{v} G]
variable [ElementaryTopos E] [ElementaryTopos F] [ElementaryTopos G]

/-- Horizontal composition of 2-morphisms via whiskering.

    Given `α : f₁ ⟶ f₂` (for `f₁ f₂ : E → F`) and `β : g₁ ⟶ g₂`
    (for `g₁ g₂ : F → G`), construct
    `α ∗ β : f₁.comp g₁ ⟶ f₂.comp g₂ : TwoMorphism (f₁.comp g₁) (f₂.comp g₂)`.

    The construction is:
    `whiskerRight β f₁.inverse ≫ whiskerLeft g₂.inverse α`

    which gives the chain:
    `g₁.inverse ⋙ f₁.inverse ⟶ g₂.inverse ⋙ f₁.inverse ⟶ g₂.inverse ⋙ f₂.inverse`.

    Convention matches MacLane-Moerdijk §VII.1. -/
def TwoMorphism.hcomp {f₁ f₂ : GeometricMorphism E F} {g₁ g₂ : GeometricMorphism F G}
    (α : TwoMorphism f₁ f₂) (β : TwoMorphism g₁ g₂) :
    TwoMorphism (f₁.comp g₁) (f₂.comp g₂) :=
  whiskerRight β f₁.inverse ≫ whiskerLeft g₂.inverse α

end HorizontalComposition

section Helpers

variable {E F : Type u}
variable [Category.{v} E] [Category.{v} F]
variable [ElementaryTopos E] [ElementaryTopos F]

/-- Bundling: lift a `PreC.GeometricMorphismMin` to a PathC `GeometricMorphism`
    when the endpoint categories carry `ElementaryTopos` instances.
    Trivial via struct-inheritance (Klasse-B finding B-1/δ). -/
def GeometricMorphism.ofMin (m : Reformulation.PreC.GeometricMorphismMin E F) :
    GeometricMorphism E F :=
  { toGeometricMorphismMin := m }

/-- Unbundling: project a PathC `GeometricMorphism` to the underlying
    `PreC.GeometricMorphismMin`. -/
def GeometricMorphism.toMin (f : GeometricMorphism E F) :
    Reformulation.PreC.GeometricMorphismMin E F :=
  f.toGeometricMorphismMin

end Helpers

end Reformulation.PathC
