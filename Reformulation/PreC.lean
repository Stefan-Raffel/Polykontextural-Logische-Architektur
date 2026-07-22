import Reformulation.PreC.ClassifierAnschluss
import Reformulation.PreC.GeometricMorphismMin
import Reformulation.PreC.PKLFormWahlen
import Reformulation.PreC.Reflexion
import Reformulation.PreC.SiteAnschluss

/-!
# Reformulation.PreC — Pre-C reduced tractability demonstration

Aggregates the Pre-C reduced pre-formulation: a tractability demonstration
for Pfad C (PKL architecture as geometric theory with classifying topos).

## What this module carries

* **SiteAnschluss**: PKL contexture index categories as discrete categories
  over `Fin n`, trivial Grothendieck topology, contexture components as
  categories of type-valued sheaves. Phase-A Mathlib connection.

* **ClassifierAnschluss**: subobject classifier instance for PKL contexture
  components, inherited from Mathlib's 2026 sheaf-topos instances
  (`Topos.Sheaf`, `HasSubobjectClassifier (Sheaf J (Type w))`).
  Phase-B Mathlib connection.

* **GeometricMorphismMin**: minimal geometric morphism structure class
  (inverse image functor, direct image functor, adjunction, left-exactness),
  with identity example. Eigen-Maschinerie; no 2-categorical structure.

* **PKLFormWahlen**: four form-choice demonstrations —
  (1) topos-component pluralism (sheaf categories indexed by `Fin n`),
  (2) double fibration (contexture-axis × schema-axis + Belegungs-function),
  (3) `translate` as a function between types (not a functor),
  (4) B5 as initial singularity (`initialConfig 1 = k1`, proved by `rfl`).

* **Reflexion**: doc-only documentation of the six gaps to a full Pre-C
  implementation, with own-machinery estimates per gap and recommended
  gap-closure order.

## What this module does NOT carry

This module is NOT imported into the main `Reformulation` library aggregator.
Pre-C lives in parallel to the F3.x modules as a separate language-formulation
demonstration. To use it, import `Reformulation.PreC` explicitly.

Pre-C does not import from F3.x modules; it is autonomous.

## Methodological note

Pre-C is a *language formulation* — a third classification class alongside
form modules (F3.x) and content modules (F1.x). It demonstrates formal
tractability, not substantive content. The mathematical substance is
minimal (trivial examples throughout); the methodological substance lies
in the form-choices and their Mathlib-connection demonstration.

Pfad C itself (full PKL formulation as geometric theory with classifying
topos and universal property) is an open subsequent undertaking, with
empirically grounded effort estimate from Pre_C_Mathlib_Befund.
-/
