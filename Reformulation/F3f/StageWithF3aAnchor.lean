import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Category.Basic
import Reformulation.F3a.Endofunctor
import Reformulation.F3a.SchemaMorphism
import Reformulation.F3f.Stage

/-!
# F3.f Rev3: StageWithF3aAnchor

This module extends F3.f's Stage class with an optional F3.a anchor —
allowing F1 belegungen to track the F3.a three-functor decomposition
of the stage's end-functor.

## Architectural background

F3.a's `EndoFunctor` is a *function* `𝒯 → skeleton.schema.positions`
producing the bilanz as a structural-skeleton-positioned element.
F3.f's `Stage.endenFunktor` is a *functor* `totalSpace ⥤ totalSpace`
producing the bilanz as a stage-immanent element.

These two forms reflect a layer-difference: F3.a operates on the
stage-modulated layer (bilanz as skeleton-schema), F3.f on the
invariant layer (bilanz as stage element).

`StageWithF3aAnchor` carries both readings as compatible forms.
A F1 belegung instantiating it provides:
- the three F3.a structural components
- a schema-to-totalSpace lift function
- a consistency proof that endenFunktor agrees with the F3.a
  three-functor composition modulo the lift.

## Methodological note

This module is the first F-extension in PKL triggered by an
F1 belegungs-anchor need (the F1.D2.Rollups.Coalgebraic.Substantial
extension; see Substantial-K1-Rev2 and F3.f-K5). The extension is
purely additive: existing Stage usages remain unchanged; F1 belegungen
without F3.a anchor instantiate Stage; with anchor they instantiate
StageWithF3aAnchor.

## Related material

- `Reformulation.F3f.Stage`: the base class.
- `Reformulation.F3a.Endofunctor`: DesignativeRestriction, OuterBalance, Skeleton.
- `Reformulation.F3a.SchemaMorphism`: Schema with positions.

## Klasse-B note: schema as explicit field

`Reformulation.F3a.Skeleton` takes `(schema : Schema n)` as a structural
parameter (not an internal field). Consequently `StageWithF3aAnchor` carries
a `schema : Reformulation.F3a.Schema n` field explicitly, before `skeleton`.
This is a Klasse-B adaptation: the Spec assumed `skeleton.schema.positions`
accessible via dot-notation, but the actual F3.a definition requires the
schema to be bound at the call site.
-/

namespace Reformulation.F3f

open CategoryTheory

universe u

/--
Extension of `Stage` carrying a F3.a anchor: three structural components
(restriction, outer balance, skeleton) plus a schema-to-totalSpace lift
function plus a form-consistency proof.

The form-consistency `f3aConsistent` carries the architectural pointe that
the two bilanz readings — F3.a structural-skeleton-oriented and F3.f
stage-immanent — are compatible. The lift function `schemaLift` is the
formal trace of the difference between the readings.

All four type parameters (totalSpace from `Stage`, designativePart, J,
tracesFamily) live in `Type u` per F3.f-K5 Wahl K5.2 (single-universe
form for sparseness; multi-universe extensions can be added as
separate classes if needed).

Additive over `Stage` per F3.f-K5 Wahl K5.3: `StageWithF3aAnchor extends
Stage.{u} n`. F1 belegungen choose Stage or StageWithF3aAnchor based on
whether F3.a anchor is wanted.

Klasse-B adaptation: a `schema : Reformulation.F3a.Schema n` field is added
before `skeleton`, because `Skeleton n tracesFamily schema` requires the
schema at the parameter site. Access via `s.schema.positions` (not
`s.skeleton.schema.positions` as the Spec sketch assumed).
-/
structure StageWithF3aAnchor (n : ℕ) extends Stage.{u} n where
  /-- The designative part — a category onto which totalSpace is restricted. -/
  designativePart : Type u
  [cat_des : Category designativePart]
  /-- The indexing category for omission modulations. -/
  J : Type u
  [cat_J : Category J]
  /-- The traces family — a category receiving the outer balance image. -/
  tracesFamily : Type u
  [cat_traces : Category tracesFamily]
  /-- The schema (V, E, S) for stage n — required as an explicit field because
      `Reformulation.F3a.Skeleton n tracesFamily schema` takes `schema` as a
      structural parameter, not an internal field. -/
  schema : Reformulation.F3a.Schema n
  /-- F3.a's first component: restriction to designative part. -/
  resDes : Reformulation.F3a.DesignativeRestriction n totalSpace designativePart
  /-- F3.a's second component: outer balance via colimit over omission modulations. -/
  outerBalance : Reformulation.F3a.OuterBalance n J designativePart tracesFamily
  /-- F3.a's third component: structural skeleton (schema-parameterized). -/
  skeleton : Reformulation.F3a.Skeleton n tracesFamily schema
  /-- The schema-to-totalSpace lift — connects F3.a's schema.positions output
      to F3.f's totalSpace via a F1-belegungs-specific extraction. -/
  schemaLift : schema.positions → totalSpace
  /-- Form-consistency: the stage's endenFunktor agrees with the F3.a
      three-functor composition modulo the schema-lift. -/
  f3aConsistent : ∀ x : totalSpace,
    endenFunktor.obj x =
      schemaLift (skeleton.skeletonFun
        (outerBalance.outerBalance.obj
          (resDes.resDes.obj x)))

/--
Helper: the F3.a three-functor composition applied to a totalSpace element.
Given a `StageWithF3aAnchor n`, this maps any element of its totalSpace
through the three F3.a components, producing a schema-position element.

The `f3aConsistent` field of `StageWithF3aAnchor` then asserts that the
schemaLift composed with this decomposition equals the stage's endenFunktor.
-/
def f3aDecomposition {n : ℕ} (s : StageWithF3aAnchor.{u} n) (x : s.totalSpace) :
    s.schema.positions :=
  letI := s.cat
  letI := s.cat_des
  letI := s.cat_J
  letI := s.cat_traces
  s.skeleton.skeletonFun (s.outerBalance.outerBalance.obj (s.resDes.resDes.obj x))

end Reformulation.F3f
