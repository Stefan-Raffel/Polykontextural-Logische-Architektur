import Reformulation.F3b.Configurations

/-
Reformulation Günthers — F3.b Classes

The four classes i, ii, iii, iv of transitions, the type of non-canonical
status (degeneration / combination), and the class assignment function.

Per Way A of the spec, the reduction/refinement relation between
non-canonical and canonical configurations is part of the *definition*
of the assignment function `klasse`, not derived from a separate
reduction relation. If a future module (such as F3.a, the Endenfunktor
construction) requires a formal reduction relation, that is to be
added there as Way B, without invalidating the present definitions.
-/

namespace Reformulation.F3b

/--
The four classes of transitions, derived from B1–B5 in T8 III.

Each class corresponds to a unique canonical-bearer configuration in `K`,
formalised by `Klasse.canonicalBearer` below.
-/
inductive Klasse where
  /-- Class i: beginning, τ from the initial singularity (B5).
      Canonical bearer: K1. -/
  | i
  /-- Class ii: intra-familial δ without family change.
      Canonical bearer: K3. -/
  | ii
  /-- Class iii: inter-familial δ with family change.
      Canonical bearer: K4. -/
  | iii
  /-- Class iv: trans-stage ω, in initialising or continuing sub-form.
      Canonical bearer: K8. -/
  | iv
  deriving DecidableEq, Repr, Fintype

/--
The status of a non-canonical configuration.

A non-canonical configuration is either a *degeneration* (it reduces to
a poorer configuration that already occupies its structural role) or a
*combination* (it refines a canonical-bearer configuration without
changing the class).

The argument names the configuration on which the reduction or
refinement relation rests; this is part of the definition of `klasse`
(Way A), not the conclusion of a separately-proven reduction theorem.
-/
inductive NonCanonical where
  /-- Degeneration: this configuration reduces to the named poorer one. -/
  | degeneration (reductionTo : K)
  /-- Combination: this configuration refines the named canonical bearer. -/
  | combination (refinementOf : K)
  deriving Repr

/--
Class assignment function.

* For canonical bearers (K1, K3, K4, K8): returns the corresponding
  class via `Sum.inl`.
* For non-canonical configurations (K2, K5, K6, K7): returns the
  appropriate `NonCanonical` status via `Sum.inr`.

The reduction/combination targets are fixed by the clarification
session §IV. They are *part of this definition*, not consequences of
a separate reduction relation. See module-level remark above on
Way A vs. Way B.
-/
def klasse : K → Klasse ⊕ NonCanonical
  | .k1 => .inl .i
  | .k2 => .inr (.degeneration .k1)
  | .k3 => .inl .ii
  | .k4 => .inl .iii
  | .k5 => .inr (.degeneration .k1)
  | .k6 => .inr (.degeneration .k2)
  | .k7 => .inr (.combination .k3)
  | .k8 => .inl .iv

/--
Inverse on the canonical side: each class is mapped to its unique
canonical-bearer configuration.

Injectivity and the `klasse ∘ canonicalBearer = .inl` property are
proved in `Reformulation.F3b.Exhaustion` as Statement 2.
-/
def Klasse.canonicalBearer : Klasse → K
  | .i   => .k1
  | .ii  => .k3
  | .iii => .k4
  | .iv  => .k8

end Reformulation.F3b
