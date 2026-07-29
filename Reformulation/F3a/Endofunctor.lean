import Reformulation.F3a.Stage
import Reformulation.F3a.SchemaMorphism
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Functor.Category

/-!
# F3.a.Endofunctor — the endofunctor F as composition of three functors

This module introduces Bestandteil (i) of F3.a:

* `DesignativeRestriction`: structure class for the first operation —
  restriction to the designative part. Carries the restriction functor
  and a Beck-Chevalley compatibility witness (placeholder Prop form,
  analogous to F3c.BeckChevalleyCompatibility).
* `OuterBalance`: structure class for the second operation — the outer
  balance via colimit over the omission modulations. Carries a
  functoriality witness.
* `Skeleton`: structure class for the third operation — the structural
  skeleton marking. Carries a uniqueness witness (EA2 placeholder).
* `EndoFunctor`: the composition of the three operations as a function
  from the base category to the schema.

The EA1-EA3 and NEA1 statements that used to stand here were removed in the
Phase-2 sharpening; see the memorial block at the end of this module. The
structural content they claimed is carried by the three structure classes
above, not by a theorem.

See F3a_Klaerung_1.md §I, F3a_Klaerung_2.md §I, F3a_Klaerung_3.md §II,
F3a_Spec.md §III.
-/

namespace Reformulation.F3a

open CategoryTheory

/-- The first operation: restriction to the designative part.

The form takes a base category `𝒯` (the reflection space) and returns
a functor to a designative subcategory. The Beck-Chevalley compatibility
is enforced as a Prop field; the full form with concrete pull-back data
is local-layer material (F1 or domain study).

The stage index `n` is carried as a structure parameter; the concrete
restriction form is stage-modulated (Klärung 3 §II.2). -/
structure DesignativeRestriction
    (n : Stage) (𝒯 : Type*) [Category 𝒯]
    (designativePart : Type*) [Category designativePart] where
  /-- The restriction functor itself. -/
  resDes : 𝒯 ⥤ designativePart
  /-- Beck-Chevalley compatibility witness (EA3 placeholder). -/
  beckChevalley : True

/-- The second operation: outer balance via colimit over the omission
modulations.

The form takes the designative part and an indexing category `J` for the
omission modulations and returns a functor from the designative part to
a traces family. The functoriality witness is enforced as a Prop field;
concrete colimit construction is local-layer material.

The indexing category `J` is a structure parameter; its concrete form
is stage-modulated (Klärung 3 §II.2). In the architectural reading
(T8 II), `J` indexes the omission modulations over which the colimit
is taken; here we encode the result of that colimit as a direct
functor `designativePart ⥤ tracesFamily`, deferring the explicit
colimit construction to F1 or a domain study (Klärung 2 §I.3:
schlankere Form gegenüber HasColimit-Maschinerie). -/
structure OuterBalance
    (n : Stage) (J : Type*) [Category J]
    (designativePart : Type*) [Category designativePart]
    (tracesFamily : Type*) [Category tracesFamily] where
  /-- The balance-forming functor (encoding the colimit's output). -/
  outerBalance : designativePart ⥤ tracesFamily
  /-- Functoriality witness. -/
  isFunctorial : True

/-- The third operation: structural skeleton marking.

The form takes the traces family and returns a function to a schema
(V, E, S) for stage `n`. The uniqueness witness (EA2) is enforced as
a Prop field; concrete skeleton construction is stage-modulated.

Note: the schema is carried as a structure parameter (not as an
internal field) so that its universe level is explicit at the binding
site; otherwise Lean cannot infer universe levels for `Schema n`
across the structure boundary. -/
structure Skeleton
    (n : Stage)
    (tracesFamily : Type*) [Category tracesFamily]
    (schema : Schema n) where
  /-- The skeleton-forming function from the traces family to the
  positions of the schema. -/
  skeletonFun : tracesFamily → schema.positions
  /-- Uniqueness witness from the sub-stage structure (EA2). -/
  isUnique : True

/-- The full endofunctor F as composition of the three components.

Given:
* a `DesignativeRestriction` (first operation),
* an `OuterBalance` (second operation),
* a `Skeleton` (third operation),

the endofunctor produces, from a base-category object, a position in
the schema via the composition `Skeleton ∘ OuterBalance ∘ ResDes`.

Note: this is a `def`, not a `theorem`, because the endofunctor is
*data* in `Type` (a function/functor construction), not a `Prop`
(see F3a_Implementations_Vor_Klaerung.md §I.3). -/
def EndoFunctor
    {n : Stage} {J : Type*} [Category J]
    {𝒯 : Type*} [Category 𝒯]
    {designativePart : Type*} [Category designativePart]
    {tracesFamily : Type*} [Category tracesFamily]
    {schema : Schema n}
    (resDes : DesignativeRestriction n 𝒯 designativePart)
    (outerBalance : OuterBalance n J designativePart tracesFamily)
    (skeleton : Skeleton n tracesFamily schema) :
    𝒯 → schema.positions :=
  fun t =>
    skeleton.skeletonFun
      (outerBalance.outerBalance.obj
        (resDes.resDes.obj t))

/-! ## Memorial block: declarations removed because their statement was `True`

Removed in the Phase-2 sharpening (Setzungsregister, `docs/status-register.md`).
The reason is the same in every case: the name claimed content, the statement
was `True`. A theorem whose statement is `True` is not a false theorem, but its
name reads as a result; in a published tree that is a claim. No consumer in the
aggregate other than the ones removed alongside; the removal breaks nothing.

Signatures are quoted indented by two spaces so that the counting routes
`^theorem` and `^def` do not count the memorial quote as a declaration.

**Removed 1 — `resDes_functorial` (EA1).** Register row `S34`.

```
  theorem resDes_functorial
      {n : Stage} {𝒯 designativePart : Type*}
      [Category 𝒯] [Category designativePart]
      (_R : DesignativeRestriction n 𝒯 designativePart) :
      True :=
    trivial
```

*What was claimed:* that the restriction component is functorial.
*What a load-bearing statement would need:* nothing is left to prove here — the
`resDes` field already *is* a Mathlib functor, so functoriality holds by typing.
A statement with content would have to say something the structure does not
already give, for instance that the restriction is natural in the stage index:
that requires `DesignativeRestriction` to be indexed functorially over `Stage`
rather than to carry `n` as an inert parameter.

**Removed 2 — `skeleton_unique` (EA2).** Register row `S35`.

```
  theorem skeleton_unique
      {n : Stage} {tracesFamily : Type*} [Category tracesFamily]
      {schema : Schema n}
      (S : Skeleton n tracesFamily schema) :
      True :=
    S.isUnique
```

*What was claimed:* that the structural skeleton is unique.
*What a load-bearing statement would need:* uniqueness cannot be formulated
against an empty field — the same diagnosis `F3e/Theorems.lean` writes out for
`beckChevalley_unique`. `Skeleton` needs at least one contentful field against
which uniqueness can discriminate; then the statement would read
`∀ S S' : Skeleton n tracesFamily schema, S.skeletonFun = S'.skeletonFun`
under a determination condition on `skeletonFun`, and would have to be proved.

**Removed 3 — `resDes_beckChevalley` (EA3).** Register row `S36`.

```
  theorem resDes_beckChevalley
      {n : Stage} {𝒯 designativePart : Type*}
      [Category 𝒯] [Category designativePart]
      (R : DesignativeRestriction n 𝒯 designativePart) :
      True :=
    R.beckChevalley
```

*What was claimed:* Beck-Chevalley compatibility of the restriction.
*What a load-bearing statement would need:* the `beckChevalley` field must carry
an actual 2-isomorphism instead of `True`. That is exactly the step that closed
the corresponding gap in F3.e, where the datum became
`ModalTwoCategoryWithPullbacks.pullBackCommute` and the theorem could read it
off. The field `DesignativeRestriction.beckChevalley` remains a placeholder and
is registered as row `S14`.

**Removed 4 — `resDes_not_invertible` (NEA1).** Register row `S37`.

```
  theorem resDes_not_invertible
      {n : Stage} {𝒯 designativePart : Type*}
      [Category 𝒯] [Category designativePart]
      (_R : DesignativeRestriction n 𝒯 designativePart) :
      True :=
    trivial
```

*What was claimed:* that the restriction admits no inverse — a non-existence
statement, and the strongest-sounding of the four.
*What a load-bearing statement would need:* a witness, not an absence. The
structure carrying no inverse field says nothing about whether one exists; the
proof obligation is a concrete pair of categories together with a proof that no
functor back composes to the identity. Note the house rule in `CLAUDE.md` §5.2:
`¬ ∃ f` between carriers is the wrong shape for a discontexturality claim in
this corpus; the load-bearing shape is non-generability inside a term clone.
-/

end Reformulation.F3a
