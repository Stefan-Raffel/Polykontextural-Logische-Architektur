-- EINGEFROREN (29. Juli 2026): dieser Zweig wird nicht fortgeschrieben.
-- Status, Zahlen und die Bedingungen fuer ein Auftauen: docs/build-targets.md, Abschnitt PathC.
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Functor.Category
import Reformulation.PathC.GeometricMorphism
import Reformulation.PathC.ElementaryTopos

/-!
# Reformulation.PathC.GeometricMorphismLaws

Carries the categorical laws for `GeometricMorphism` composition that were
declared as `sorry` in `Reformulation.PathC.GeometricMorphism`.

## Structure

- Three adjunction-transport helper lemmas (all proofs by `Adjunction.ext` + `simp`):
  - `adj_comp_id_eq` — `adj.comp Adjunction.id = adj`
  - `id_comp_adj_eq` — `Adjunction.id.comp adj = adj`
  - `adj_comp_assoc` — `(adj₁.comp adj₂).comp adj₃ = adj₁.comp (adj₂.comp adj₃)`

- `GeometricMorphism.ext` — extensionality theorem (with `HEq` adjunction field)

- Three categorical law proofs:
  - `GeometricMorphism.id_comp_proof`
  - `GeometricMorphism.comp_id_proof`
  - `GeometricMorphism.assoc_proof`

## Methodological note

`Functor.comp_id`, `Functor.id_comp`, and `Functor.assoc` are all proved by `rfl`
in Mathlib (functor composition is definitionally associative and unital). This
means the adjunction types on both sides of each law are definitionally equal, so
`heq_of_eq` suffices for the HEq adjunction goals — no explicit transport needed.

This is Klasse-B completion (β.2 → β.1, retrospective): three sorry-declared
statements in `GeometricMorphism.lean` are replaced by proofs from this module.

## References

S. MacLane, I. Moerdijk, *Sheaves in Geometry and Logic*, Springer 1992.
Chapter VII, §1.
-/

namespace Reformulation.PathC

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits

universe v u

-- ============================================================
-- Section 1: Adjunction identity and associativity helper lemmas
-- ============================================================
-- Note: Functor.comp_id, Functor.id_comp, Functor.assoc are all rfl in Mathlib,
-- so adjunction types on both sides of these equalities are definitionally equal.

section AdjunctionHelpers

variable {C D : Type u} [Category.{v} C] [Category.{v} D]

/-- `adj.comp Adjunction.id = adj` — right identity for adjunction composition.
    Types are definitionally equal since `Functor.comp_id` is `rfl`. -/
private lemma adj_comp_id_eq {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) :
    adj.comp Adjunction.id = adj :=
  Adjunction.ext (by ext X; simp [Adjunction.comp_unit_app])

/-- `Adjunction.id.comp adj = adj` — left identity for adjunction composition.
    Types are definitionally equal since `Functor.id_comp` is `rfl`. -/
private lemma id_comp_adj_eq {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) :
    Adjunction.id.comp adj = adj :=
  Adjunction.ext (by ext X; simp [Adjunction.comp_unit_app])

end AdjunctionHelpers

section AdjunctionAssoc

variable {C D E E' : Type u}
variable [Category.{v} C] [Category.{v} D] [Category.{v} E] [Category.{v} E']

/-- Associativity of adjunction composition.
    Types are definitionally equal since `Functor.assoc` is `rfl`. -/
private lemma adj_comp_assoc
    {F₁ : C ⥤ D} {G₁ : D ⥤ C} (adj₁ : F₁ ⊣ G₁)
    {F₂ : D ⥤ E} {G₂ : E ⥤ D} (adj₂ : F₂ ⊣ G₂)
    {F₃ : E ⥤ E'} {G₃ : E' ⥤ E} (adj₃ : F₃ ⊣ G₃) :
    (adj₁.comp adj₂).comp adj₃ = adj₁.comp (adj₂.comp adj₃) :=
  Adjunction.ext (by ext X; simp [Adjunction.comp_unit_app, Functor.map_comp, Category.assoc])

end AdjunctionAssoc

-- ============================================================
-- Section 2: Extensionality for GeometricMorphism
-- ============================================================

section GeometricMorphismExt

variable {E F : Type u} [Category.{v} E] [Category.{v} F]
variable [ElementaryTopos E] [ElementaryTopos F]

/-- Extensionality for `GeometricMorphism`: two geometric morphisms are equal
    when their inverse, direct, and adjunction fields agree.
    The `inverse_preservesFiniteLimits` field is `Prop`-valued and uses
    proof irrelevance. The adjunction equality is stated as `HEq` since the
    field type depends on the functor fields (even though functor equalities
    are definitional here). -/
@[ext]
theorem GeometricMorphism.ext {f g : GeometricMorphism E F}
    (h_inv : f.inverse = g.inverse)
    (h_dir : f.direct = g.direct)
    (h_adj : HEq f.adjunction g.adjunction) :
    f = g := by
  obtain ⟨⟨inv₁, dir₁, adj₁, pres₁⟩⟩ := f
  obtain ⟨⟨inv₂, dir₂, adj₂, pres₂⟩⟩ := g
  -- After destructuring, projections reduce definitionally; subst the equalities
  subst h_inv
  subst h_dir
  -- h_adj : HEq adj₁ adj₂ where both have the same type (after subst)
  simp only [heq_iff_eq] at h_adj
  subst h_adj
  -- pres₁ pres₂ : PreservesFiniteLimits inv₁ — equal by Subsingleton (Prop-valued class)
  have h_pres : pres₁ = pres₂ := Subsingleton.elim _ _
  subst h_pres
  rfl

end GeometricMorphismExt

-- ============================================================
-- Section 3: Categorical laws
-- ============================================================

section CategoricalLaws

variable {E F G H : Type u}
variable [Category.{v} E] [Category.{v} F] [Category.{v} G] [Category.{v} H]
variable [ElementaryTopos E] [ElementaryTopos F] [ElementaryTopos G] [ElementaryTopos H]

/-- Left identity law for geometric morphism composition. -/
theorem GeometricMorphism.id_comp_proof (f : GeometricMorphism E F) :
    (GeometricMorphism.id E).comp f = f := by
  apply GeometricMorphism.ext
  · -- inverse: f.inverse ⋙ 𝟭 E = f.inverse
    exact Functor.comp_id f.inverse
  · -- direct: 𝟭 E ⋙ f.direct = f.direct
    exact Functor.id_comp f.direct
  · -- adjunction: HEq (f.adjunction.comp Adjunction.id) f.adjunction
    -- Types definitionally equal (Functor.comp_id, id_comp are rfl)
    exact heq_of_eq (adj_comp_id_eq f.adjunction)

/-- Right identity law for geometric morphism composition. -/
theorem GeometricMorphism.comp_id_proof (f : GeometricMorphism E F) :
    f.comp (GeometricMorphism.id F) = f := by
  apply GeometricMorphism.ext
  · -- inverse: 𝟭 F ⋙ f.inverse = f.inverse
    exact Functor.id_comp f.inverse
  · -- direct: f.direct ⋙ 𝟭 F = f.direct
    exact Functor.comp_id f.direct
  · -- adjunction: HEq (Adjunction.id.comp f.adjunction) f.adjunction
    exact heq_of_eq (id_comp_adj_eq f.adjunction)

/-- Associativity of geometric morphism composition. -/
theorem GeometricMorphism.assoc_proof
    (f : GeometricMorphism E F) (g : GeometricMorphism F G)
    (h : GeometricMorphism G H) :
    (f.comp g).comp h = f.comp (g.comp h) := by
  apply GeometricMorphism.ext
  · -- inverse: h.inverse ⋙ (g.inverse ⋙ f.inverse) = (h.inverse ⋙ g.inverse) ⋙ f.inverse
    -- Functor.assoc is rfl, so this holds by definitional equality
    exact (Functor.assoc h.inverse g.inverse f.inverse).symm
  · -- direct: (f.direct ⋙ g.direct) ⋙ h.direct = f.direct ⋙ (g.direct ⋙ h.direct)
    exact Functor.assoc f.direct g.direct h.direct
  · -- adjunction: HEq (h.adj.comp (g.adj.comp f.adj)) ((h.adj.comp g.adj).comp f.adj)
    exact heq_of_eq (adj_comp_assoc h.adjunction g.adjunction f.adjunction).symm

end CategoricalLaws

end Reformulation.PathC
