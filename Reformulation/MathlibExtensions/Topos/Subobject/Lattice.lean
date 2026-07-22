/-
Copyright Reformulierung-Projekt 2026.
Released under PKL-internal license.
-/
import Mathlib.CategoryTheory.Subobject.Lattice
import Reformulation.MathlibExtensions.Topos.Subobject.WellPowered
import Reformulation.MathlibExtensions.Topos.Subobject.Bot

/-!
# CompleteLattice (Subobject B) for ElementaryTopos with three consumer hypotheses

## Main result

- `ElementaryTopos.completeLatticeSubobject`: under three additional consumer hypotheses
  (`LocallySmall.{w}`, `HasWidePullbacks.{w}`, `HasCoproducts.{w}`),
  `CompleteLattice (Subobject B)` is available for `[ElementaryTopos E]` via `inferInstance`.

## Consumer-hypothesis analysis

Mathlib's `CompleteLattice (Subobject B)` (Lattice.lean:690) requires six hypotheses:

| Hypothesis | Source |
|---|---|
| `[LocallySmall.{w} C]` | **consumer hypothesis** (not in `ElementaryTopos`) |
| `[WellPowered.{w} C]` | **derived** from `ElementaryTopos` (WellPowered.lean) |
| `[HasWidePullbacks.{w} C]` | **consumer hypothesis** (only finite pullbacks in topos) |
| `[HasImages C]` | **derived** from `ElementaryTopos` (from `HasFiniteLimits`) |
| `[HasCoproducts.{w} C]` | **consumer hypothesis** (only finite coproducts in topos) |
| `[InitialMonoClass C]` | **derived** from `ElementaryTopos` (InitialMonoClass.lean) |

Conclusion: 2 of 6 are derived, 3 remain as consumer hypotheses
(`LocallySmall`, `HasWidePullbacks`, `HasCoproducts`). The `WellPowered` hypothesis
is resolved by `ElementaryTopos.wellPowered` (WellPowered.lean).

## Methodological note

This file provides no independently provable theorems. Its substance is the documentation
of the consumer-hypothesis landscape: the three hypotheses that consuming files
(`TermSemantics.lean`, `Soundness.lean`, `ClassifyingEquivalence.lean`) must add to their
`variable` blocks in C22.

## Anschluss (C21-B6, C21-D-5)

Closes C21-B6 (the six-hypothesis bundle is now understood and partially resolved).
The three consumer hypotheses become the methodological scope for C22.
-/

namespace Reformulation.MathlibExtensions.Topos

open CategoryTheory Limits Reformulation.PathC

universe w u v

-- HasImages is NOT automatic from our ElementaryTopos definition;
-- it requires an additional consumer hypothesis (Klasse-ζ finding B-5).
variable {E : Type u} [Category.{v} E] [ElementaryTopos E] [HasInitial E] [HasImages E]
variable [LocallySmall.{w} E] [HasWidePullbacks.{w} E] [HasCoproducts.{w} E]

-- The local instance `has_smallest_coproducts_of_hasCoproducts` is needed by Mathlib's
-- CompleteLattice (Subobject B) instance (cf. Subobject/Lattice.lean:688).
attribute [local instance] has_smallest_coproducts_of_hasCoproducts

/-- In an elementary topos with consumer hypotheses `[HasImages E]`,
`[LocallySmall.{w} E]`, `[HasWidePullbacks.{w} E]`, `[HasCoproducts.{w} E]`,
and `[WellPowered.{w} E]`, `CompleteLattice (Subobject B)` holds for all `B : E`.

Note: `HasImages E` is an additional consumer hypothesis (Klasse-ζ finding B-5);
NOT automatic from `ElementaryTopos`.

These consumer hypotheses must be provided by consuming modules in C22. -/
noncomputable example [WellPowered.{w} E] (B : E) : CompleteLattice (Subobject B) :=
  inferInstance

end Reformulation.MathlibExtensions.Topos
