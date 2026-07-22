import Reformulation.F3b.Classes
import Mathlib.Logic.Function.Basic

/-
Reformulation Günthers — F3.b Exhaustion

The three exhaustion theorems (Statements 1, 2, 3 of the spec) and the
combined `exhaustion` theorem.

Statement 1 — Completeness of enumeration — is captured by
`Reformulation.F3b.K.equivConfiguration` in `F3b.Configurations`.

Statements 2 and 3 are proved here.
-/

namespace Reformulation.F3b

/-! ## Statement 2 — Uniqueness of class assignment -/

/--
**Statement 2a.** The canonical-bearer function is injective: distinct
classes are assigned distinct canonical bearers.

The proof case-analyses both classes (16 cases) and closes diagonal
cases by reflexivity, off-diagonal cases by simplifying the bearer
definition and detecting the constructor mismatch.
-/
theorem Klasse.canonicalBearer_injective :
    Function.Injective Klasse.canonicalBearer := by
  intro k₁ k₂ h
  cases k₁ <;> cases k₂ <;> simp_all [Klasse.canonicalBearer]

/--
**Statement 2b.** Inverse property on the canonical side: applying
`klasse` to the canonical bearer of a class yields that class wrapped
in `Sum.inl`.

This is the round-trip property `klasse ∘ canonicalBearer = Sum.inl`.
-/
@[simp]
theorem klasse_canonicalBearer (k : Klasse) :
    klasse k.canonicalBearer = Sum.inl k := by
  cases k <;> rfl

/--
**Statement 2c.** Characterisation of the `Sum.inl` cases: a
configuration receives a canonical class assignment if and only if
it is one of the four canonical bearers K1, K3, K4, K8.
-/
theorem klasse_inl_iff (k : K) :
    (∃ c : Klasse, klasse k = Sum.inl c) ↔
    k = K.k1 ∨ k = K.k3 ∨ k = K.k4 ∨ k = K.k8 := by
  cases k <;> simp [klasse]

/-! ## Statement 3 — Non-canonical configurations are degenerations or combinations -/

/--
**Statement 3a.** Characterisation of the `Sum.inr` cases: a
configuration receives a non-canonical status if and only if it is
one of the four non-canonical configurations K2, K5, K6, K7.

Per Way A of the spec, the reduction/refinement structure is
definitional (in `klasse`), so Statement 3 reduces to this
characterisation; no separate reduction-relation theorem is required.
-/
theorem klasse_inr_iff (k : K) :
    (∃ n : NonCanonical, klasse k = Sum.inr n) ↔
    k = K.k2 ∨ k = K.k5 ∨ k = K.k6 ∨ k = K.k7 := by
  cases k <;> simp [klasse]

/--
The eight configurations partition into four canonical bearers and
four non-canonical configurations.
-/
theorem K.canonical_or_nonCanonical (k : K) :
    (k = K.k1 ∨ k = K.k3 ∨ k = K.k4 ∨ k = K.k8) ∨
    (k = K.k2 ∨ k = K.k5 ∨ k = K.k6 ∨ k = K.k7) := by
  cases k <;> simp

/-! ## Combined exhaustion theorem -/

/--
**Combined exhaustion theorem.**

Three propositions, one per statement of the spec:

* `Nonempty (K ≃ Configuration)` — Statement 1: the enumeration is
  complete (witnessed by `K.equivConfiguration`).
* `Function.Injective Klasse.canonicalBearer` — Statement 2:
  each class has a unique canonical bearer.
* the partition statement — Statement 3: every configuration is
  either canonical or non-canonical.

The combined theorem has no proof work of its own; it aggregates the
three statements proved above. Its value is the niederlegung that the
three together carry the exhaustion claim.
-/
theorem exhaustion :
    Nonempty (K ≃ Configuration) ∧
    Function.Injective Klasse.canonicalBearer ∧
    (∀ k : K,
      (k = K.k1 ∨ k = K.k3 ∨ k = K.k4 ∨ k = K.k8) ∨
      (k = K.k2 ∨ k = K.k5 ∨ k = K.k6 ∨ k = K.k7)) :=
  ⟨⟨K.equivConfiguration⟩,
   Klasse.canonicalBearer_injective,
   K.canonical_or_nonCanonical⟩

/-! ## Examples — illustrative sanity checks -/

/-- K1 is the canonical bearer of class i. -/
example : Klasse.i.canonicalBearer = K.k1 := rfl

/-- K3 is the canonical bearer of class ii. -/
example : Klasse.ii.canonicalBearer = K.k3 := rfl

/-- K4 is the canonical bearer of class iii. -/
example : Klasse.iii.canonicalBearer = K.k4 := rfl

/-- K8 is the canonical bearer of class iv. -/
example : Klasse.iv.canonicalBearer = K.k8 := rfl

/-- K2 is a degeneration reducing to K1. -/
example : klasse K.k2 = Sum.inr (NonCanonical.degeneration K.k1) := rfl

/-- K7 is a combination refining K3. -/
example : klasse K.k7 = Sum.inr (NonCanonical.combination K.k3) := rfl

/-- The triple (nonTrivial, nonConstant, present) is K8. -/
example : Configuration.toK ⟨.nonTrivial, .nonConstant, .present⟩ = K.k8 := rfl

/-- The round trip: K → Configuration → K is the identity. -/
example (k : K) : k.toConfiguration.toK = k := K.equivConfiguration.left_inv k

end Reformulation.F3b
