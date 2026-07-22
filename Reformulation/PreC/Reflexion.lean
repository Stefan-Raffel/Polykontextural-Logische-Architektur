/-!
# Reformulation.PreC.Reflexion — Gap documentation

This module carries NO Lean code beyond this doc-string. It documents the
six gaps between the Pre-C reduced tractability demonstration and a full
Pre-C implementation (Pfad C: PKL architecture as geometric theory with
classifying topos). Empirical basis: Pre_C_Mathlib_Befund.md.

## Gap 1 — Classifying topos

What is missing: the syntactic construction of a classifying topos `B[T]`
from a geometric theory `T`, together with the universal property as a
formal theorem (models of `T` in a topos `E` ↔ geometric morphisms `E → B[T]`).

Own-machinery estimate: 600–1200 Lean lines.

Mathlib status: completely absent (Pre_C_Mathlib_Befund §5.3: "nicht vorhanden").
No `ClassifyingTopos`, no universal property, no 2-category of topoi.

Methodological consequence: the central classificatory reading of F1-occupancies
— F1 as models in arbitrary toposes — is not formally accessible in Pre-C.
The tractability demonstration carries the form-choice, not the universality.

## Gap 2 — ElementaryTopos as typeclass

What is missing: a unified typeclass that bundles `HasFiniteLimits` +
`HasSubobjectClassifier` + `CartesianClosed` into a single `ElementaryTopos`
or `IsElementaryTopos` declaration.

Own-machinery estimate: 80–150 Lean lines.

Mathlib status: the three components are present individually (Mathlib's
2026 `Topos.Sheaf` shows sheaf categories are elementary topoi, but no
unified typeclass exists). Gap is mechanical.

Methodological consequence: Mathlib's individual typeclasses are used
locally ad-hoc in Pre-C, without a globally-typed topos structure.

## Gap 3 — GeometricMorphism as full structure class

What is missing: the full 2-category of toposes with composition,
2-morphisms (natural transformations between geometric morphisms),
adjunction-compatibility theorems, and the Beck-Chevalley condition.

Own-machinery estimate: 200–400 Lean lines (the minimal form in
`GeometricMorphismMin` carries 30–60 lines).

Mathlib status: no `GeometricMorphism` in the entire Mathlib tree
(Pre_C_Mathlib_Befund §4.3: exhaustive search, no hits).

Methodological consequence: composition of geometric morphisms is not
formally available; only the minimal structure-class form is demonstrated.

## Gap 4 — Geometric theory as general structure class

What is missing: sorts, operation symbols, and geometric-sequent families
as an abstract structure class for arbitrary geometric theories. The
geometric connectives (∃, ∧, ⊤, ⊥; not ∀, →) would need a dedicated
inductive type for geometric formulas.

Own-machinery estimate: 300–600 Lean lines.

Mathlib status: completely absent. No `GeometricTheory`, `GeometricFormula`,
or `GeometricSequent` in Mathlib (Pre_C_Mathlib_Befund §6.1: no hits).
ModelTheory is present but carries full first-order logic, not the
geometric-logic restriction, and is isolated from topos machinery.

Methodological consequence: Pre-C carries the PKL geometric substance
concretely (in the form-choice demonstrations), not abstractly (as an
instance of a general geometric-theory structure class).

## Gap 5 — Model functor

What is missing: a formal functor from geometric theories to toposes
(models of a theory `T` in a topos `E`), which is the prerequisite for
the universal property in Gap 1.

Own-machinery estimate: 200–400 Lean lines (requires Gap 3 and Gap 4 first).

Methodological consequence: the classificatory reading of F1-occupancies
as geometric morphisms `E → B[T_PKL]` is not formally accessible.

## Gap 6 — Cyclic interlocking with delta-bound

What is missing: a family of 2-morphism existence/non-existence sequents
for the modal triad's cyclic interlocking (τ→δ→ω→τ), with delta-bound
smoothness and the τ→ω ≠ ω→τ asymmetry, formally expressed as properties
of morphisms in the 2-category of geometric morphisms.

Own-machinery estimate: 100–200 Lean lines for the PKL-specific sequents,
plus the 2-category machinery from Gap 3 (200–400 lines) as prerequisite.

Methodological consequence: the fifth central form-choice of the ontological
position (cyclic entanglement with directional asymmetry) is reserved for
the full Pre-C implementation.

## Strategy for gap-closure in a full Pre-C implementation

Recommended order:

1. Gap 2 (ElementaryTopos typeclass) — mechanical, builds directly on
   existing Mathlib parts. Entry point for a full implementation.
2. Gap 3 (GeometricMorphism full structure) — substantial, prerequisite
   for Gaps 1 and 6.
3. Gap 4 (Geometric theory structure class) — substantial own-machinery,
   prerequisite for Gaps 1 and 5.
4. Gaps 1 and 5 (Classifying topos + model functor) — central, as
   connected machinery. Largest single item.
5. Gap 6 (Cyclic interlocking) — PKL-specific application, last because
   it requires Gaps 3, 4, 5.

Total estimate of full implementation: ca. 1380–2750 Lean lines on top
of the Pre-C tractability demonstration.
-/
