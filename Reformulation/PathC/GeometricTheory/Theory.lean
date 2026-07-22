import Mathlib.Data.Set.Basic
import Reformulation.PathC.GeometricTheory.Signature
import Reformulation.PathC.GeometricTheory.Formula

/-!
# Reformulation.PathC.GeometricTheory.Theory

Geometric sequences and the `GeometricTheory` structure class.

## What this module carries

- `GeometricSequence sig` — a sequent over signature `sig`: a context `Γ`
  (list of sorts for free variables), a hypothesis formula, and a conclusion
  formula, both in context `Γ`.

- `GeometricTheory` — a many-sorted signature together with a set of axiom
  sequents. The set form allows infinitely many axioms, consistent with the
  infinitary disjunction in `GeometricFormula`.

- `GeometricTheory.empty` — the empty geometric theory (empty signature, no axioms).

## Methodological note

This module carries the abstract substance of geometric theories without
provability machinery (reserved for Lücken 1+5). The substance suffices for
classifying topoi and the model functor construction.

Parallel-additive to PathC modules (ElementaryTopos, GeometricMorphism);
the connection comes in Lücken 1+5.
-/

namespace Reformulation.PathC.GeometricTheory

open ManySortedSignature

universe u v w

/-- A geometric sequent over signature `sig`: a context `Γ`, a hypothesis formula,
    and a conclusion formula, both in context `Γ`.

    Methodological pointer: a sequent `φ ⊢_Γ ψ` in standard notation corresponds
    to `⟨Γ, φ, ψ⟩` here. -/
structure GeometricSequence (sig : ManySortedSignature.{u, v, w}) :
    Type (max u (max v w) + 1) where
  /-- The context: a list of free-variable sorts. -/
  context    : List sig.sort
  /-- The hypothesis formula (left side of the sequent). -/
  hypothesis : GeometricFormula sig context
  /-- The conclusion formula (right side of the sequent). -/
  conclusion : GeometricFormula sig context

/-- A geometric theory: a many-sorted signature and a set of axiom sequents.
    The `Set` form allows infinitely many axioms.

    Named `Theory` (not `GeometricTheory`) to avoid namespace duplication with
    the enclosing `Reformulation.PathC.GeometricTheory` namespace (Klasse-A). -/
structure Theory : Type (max (u + 1) (v + 1) (w + 1)) where
  /-- The underlying many-sorted signature. -/
  signature : ManySortedSignature.{u, v, w}
  /-- The set of axiom sequents. -/
  axioms : Set (GeometricSequence signature)

namespace Theory

/-- The empty geometric theory: empty signature, no axioms.
    Demonstrates that `Theory` is instantiable. -/
def empty : Theory.{u, v, w} where
  signature := ManySortedSignature.empty
  axioms    := ∅

end Theory

end Reformulation.PathC.GeometricTheory
