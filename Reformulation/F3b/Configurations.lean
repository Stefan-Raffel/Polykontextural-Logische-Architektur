import Reformulation.F3b.Variables
import Mathlib.Logic.Equiv.Defs

/-
Reformulation Günthers — F3.b Configurations

The eight configurations K1–K8 as both a triple structure (σ, β, υ) and
an enumeration type, with the equivalence between the two representations.

The equivalence captures Statement 1 of the exhaustion theorem in the
spec: the eight enumerated configurations exhaust the full product
{trivial, nonTrivial} × {constant, nonConstant} × {absent, present}.

Note on `Fintype Configuration`. The derived `Fintype` instance via
deriving handler requires a `Fintype` instance for the internal Sigma
representation of a three-component structure, which is not always
transitively available depending on the Mathlib version. Instead, we
derive `Fintype Configuration` after the equivalence `K ≃ Configuration`
is defined, via `Fintype.ofEquiv K K.equivConfiguration`. This documents
explicitly that the finiteness of Configuration follows from the
bijection to K.
-/

namespace Reformulation.F3b

/--
A configuration is a triple (σ, β, υ) of `SchemaShape`, `Valuation`,
and `Subtopos`. The full product has 2³ = 8 elements.

Architecture reference: clarification session §IV, paragraph on
"the triple form".
-/
structure Configuration where
  shape : SchemaShape
  valuation : Valuation
  subtopos : Subtopos
  deriving DecidableEq, Repr

/--
The eight configurations as an enumeration type.

Naming and ordering follow the clarification session §IV:

- K1 = (trivial,    constant,    absent)   — Class i (canonical bearer)
- K2 = (trivial,    nonConstant, absent)   — Degeneration → K1
- K3 = (nonTrivial, constant,    absent)   — Class ii (canonical bearer)
- K4 = (nonTrivial, nonConstant, absent)   — Class iii (canonical bearer)
- K5 = (trivial,    constant,    present)  — Degeneration → K1
- K6 = (trivial,    nonConstant, present)  — Degeneration → K2
- K7 = (nonTrivial, constant,    present)  — Combination refining K3
- K8 = (nonTrivial, nonConstant, present)  — Class iv (canonical bearer)

Class assignments are formalised in `Reformulation.F3b.Classes`.
-/
inductive K where
  /-- K1 = (trivial, constant, absent). Canonical bearer of Class i. -/
  | k1
  /-- K2 = (trivial, nonConstant, absent). Degeneration reducing to K1. -/
  | k2
  /-- K3 = (nonTrivial, constant, absent). Canonical bearer of Class ii. -/
  | k3
  /-- K4 = (nonTrivial, nonConstant, absent). Canonical bearer of Class iii. -/
  | k4
  /-- K5 = (trivial, constant, present). Degeneration reducing to K1. -/
  | k5
  /-- K6 = (trivial, nonConstant, present). Degeneration reducing to K2. -/
  | k6
  /-- K7 = (nonTrivial, constant, present). Combination refining K3. -/
  | k7
  /-- K8 = (nonTrivial, nonConstant, present). Canonical bearer of Class iv. -/
  | k8
  deriving DecidableEq, Repr, Fintype

namespace K

/-- Map from the enumeration type `K` to the triple `Configuration`. -/
def toConfiguration : K → Configuration
  | .k1 => ⟨.trivial,    .constant,    .absent⟩
  | .k2 => ⟨.trivial,    .nonConstant, .absent⟩
  | .k3 => ⟨.nonTrivial, .constant,    .absent⟩
  | .k4 => ⟨.nonTrivial, .nonConstant, .absent⟩
  | .k5 => ⟨.trivial,    .constant,    .present⟩
  | .k6 => ⟨.trivial,    .nonConstant, .present⟩
  | .k7 => ⟨.nonTrivial, .constant,    .present⟩
  | .k8 => ⟨.nonTrivial, .nonConstant, .present⟩

end K

namespace Configuration

/-- Map from the triple `Configuration` to the enumeration type `K`. -/
def toK : Configuration → K
  | ⟨.trivial,    .constant,    .absent⟩  => .k1
  | ⟨.trivial,    .nonConstant, .absent⟩  => .k2
  | ⟨.nonTrivial, .constant,    .absent⟩  => .k3
  | ⟨.nonTrivial, .nonConstant, .absent⟩  => .k4
  | ⟨.trivial,    .constant,    .present⟩ => .k5
  | ⟨.trivial,    .nonConstant, .present⟩ => .k6
  | ⟨.nonTrivial, .constant,    .present⟩ => .k7
  | ⟨.nonTrivial, .nonConstant, .present⟩ => .k8

end Configuration

/--
Equivalence between the enumeration type `K` and the triple
`Configuration`.

This is **Statement 1** of the exhaustion theorem: the eight enumerated
configurations exhaust the full product
{trivial, nonTrivial} × {constant, nonConstant} × {absent, present}.

The proof of `right_inv` proceeds by case analysis on the three
components σ, β, υ, yielding 2³ = 8 cases each closed by reflexivity.
-/
def K.equivConfiguration : K ≃ Configuration where
  toFun := K.toConfiguration
  invFun := Configuration.toK
  left_inv := by
    intro k
    cases k <;> rfl
  right_inv := by
    intro c
    obtain ⟨σ, β, υ⟩ := c
    cases σ <;> cases β <;> cases υ <;> rfl

/--
Finiteness of `Configuration`, derived from the equivalence to the
enumeration type `K`. This is the architectural reading: Configuration
is finite because it is in bijection with the eight-element enumeration K.
-/
instance : Fintype Configuration := Fintype.ofEquiv K K.equivConfiguration

end Reformulation.F3b
