-- EINGEFROREN (29. Juli 2026): dieser Zweig wird nicht fortgeschrieben.
-- Status, Zahlen und die Bedingungen fuer ein Auftauen: docs/build-targets.md, Abschnitt PathC.
/-
Copyright Reformulierung-Projekt 2026.
Released under PKL-internal license.
-/
import Reformulation.PathC.GeometricTheory.Signature
import Reformulation.PathC.GeometricTheory.Formula
import Reformulation.PathC.GeometricTheory.Theory

/-!
# Reformulation.PathC.Classifying.SequentCalculus

Sequent calculus for geometric logic (Gentzen-style, one-sided sequents).

## What this module carries

- `Derivable T` — inductive provability of geometric sequents in theory T.
  Inference rules: identity, cut, conjunction introduction/elimination,
  infinitary disjunction introduction/elimination, top, bottom, theory axioms.

- `Derivable.refl`, `Derivable.trans` — reflexivity and transitivity.

- `Derivable.conj_mono`, `Derivable.disj_mono` — monotonicity under connectives.

## Klasse-C note (C18)

This module provides the sequent-calculus foundation for `GeometricTopology.lean`
(the Grothendieck topology J_T on the syntactic site C_T). It is the core
eigen-machinery for the first Klasse-C-Vervollständigung of the Pfad-C sequence.

## What this module does not carry

- Substitution stability (`substStable`). Requires `GeometricFormula.subst`,
  which in turn requires recursion over the `disj` constructor (indexed by an
  arbitrary type ι). This is a Klasse-D follow-up: defining `GeometricFormula.subst`
  needs either a fuel-based encoding or an explicit recursor (B-3/β universe level
  for the index type prevents standard structural recursion). The C21 Soundness
  module is the natural host.

- Existential introduction/elimination. These depend on `substStable` and are
  likewise deferred to C21.

- Cut elimination as a meta-theorem. Cut is a primitive inference rule; cut
  elimination is follow-on work.

## Methodological note

Constructors of `Derivable` mirror the standard inference rules of geometric
logic in Gentzen one-sided form. See Mac Lane–Moerdijk §IX and Caramello §2.

## Klasse-B findings (C18)

- **B-1/β** — `open CategoryTheory` would fail silently here because this module
  does not import Mathlib.CategoryTheory. When `open X Y` encounters an unknown
  namespace `X`, the entire open command fails, leaving `Y` (= GeometricTheory)
  also unopened. Removed `CategoryTheory` from the open list.
-/

namespace Reformulation.PathC.Classifying

-- Note: `open CategoryTheory` omitted — Mathlib.CategoryTheory is not imported here.
-- GeometricTheory is opened for Theory, GeometricFormula, GeometricSequence.
open GeometricTheory

universe u v w

/-!
### Derivable sequents
-/

/-- Provability of geometric sequents in theory `T`.

    `Derivable T φ ψ` (in implicit context `Γ : List T.signature.sort`) means
    the sequent `φ ⊢_Γ ψ` is derivable in T.

    Constructors mirror the standard rules of geometric-logic sequent calculus:
    identity, cut (= transitivity), conjunction intro/elim, infinitary disjunction
    intro/elim, top, bottom, and theory-axiom closure.

    **Universe note.** The `disj` constructor of `GeometricFormula` uses an index
    type `ι : Type (max u (max v w))`, one universe level below the formula universe.
    The `disjI`/`disjE` constructors here match that universe level. Since `Derivable`
    lands in `Prop` (which is impredicative), no universe inconsistency arises. -/
inductive Derivable (T : Theory.{u, v, w}) :
    {Γ : List T.signature.sort} →
    GeometricFormula T.signature Γ →
    GeometricFormula T.signature Γ → Prop where
  /-- Identity: every formula entails itself. -/
  | axm {Γ : List T.signature.sort} {φ : GeometricFormula T.signature Γ} :
      Derivable T φ φ
  /-- Cut (transitivity): if φ ⊢ ψ and ψ ⊢ χ, then φ ⊢ χ. -/
  | cut {Γ : List T.signature.sort} {φ ψ χ : GeometricFormula T.signature Γ} :
      Derivable T φ ψ → Derivable T ψ χ → Derivable T φ χ
  /-- Top-right: every formula entails ⊤. -/
  | topR {Γ : List T.signature.sort} {φ : GeometricFormula T.signature Γ} :
      Derivable T φ .top
  /-- Bottom-left: ⊥ entails every formula. -/
  | botL {Γ : List T.signature.sort} {ψ : GeometricFormula T.signature Γ} :
      Derivable T .bot ψ
  /-- Conjunction introduction: from φ ⊢ ψ₁ and φ ⊢ ψ₂, derive φ ⊢ ψ₁ ∧ ψ₂. -/
  | conjI {Γ : List T.signature.sort} {φ ψ₁ ψ₂ : GeometricFormula T.signature Γ} :
      Derivable T φ ψ₁ → Derivable T φ ψ₂ →
      Derivable T φ (.conj ψ₁ ψ₂)
  /-- Conjunction elimination (left): ψ₁ ∧ ψ₂ ⊢ ψ₁. -/
  | conjE_l {Γ : List T.signature.sort} {ψ₁ ψ₂ : GeometricFormula T.signature Γ} :
      Derivable T (.conj ψ₁ ψ₂) ψ₁
  /-- Conjunction elimination (right): ψ₁ ∧ ψ₂ ⊢ ψ₂. -/
  | conjE_r {Γ : List T.signature.sort} {ψ₁ ψ₂ : GeometricFormula T.signature Γ} :
      Derivable T (.conj ψ₁ ψ₂) ψ₂
  /-- Disjunction introduction: from φ ⊢ fs i, derive φ ⊢ ⋁ fs. -/
  | disjI {Γ : List T.signature.sort} {ι : Type (max u (max v w))}
          {fs : ι → GeometricFormula T.signature Γ}
          {φ : GeometricFormula T.signature Γ}
          (i : ι) :
      Derivable T φ (fs i) → Derivable T φ (.disj fs)
  /-- Disjunction elimination: from (∀ i, fs i ⊢ ψ), derive ⋁ fs ⊢ ψ. -/
  | disjE {Γ : List T.signature.sort} {ι : Type (max u (max v w))}
          {fs : ι → GeometricFormula T.signature Γ}
          {ψ : GeometricFormula T.signature Γ} :
      (∀ i : ι, Derivable T (fs i) ψ) → Derivable T (.disj fs) ψ
  /-- Theory axiom closure: every axiom of T is derivable. -/
  | axiomT (seq : GeometricSequence T.signature) (h : seq ∈ T.axioms) :
      Derivable T seq.hypothesis seq.conclusion
  -- -------------------------------------------------------
  -- C21 additions: substitution stability + existential rules
  -- -------------------------------------------------------
  /-- Substitution stability: derivable sequents are stable under substitution.

      If `φ ⊢ ψ` in context `Γ`, then `φ[σ] ⊢ ψ[σ]` in context `Δ`, for any
      de Bruijn substitution `σ : TermSubst T.signature`. -/
  | substStable {Γ Δ : List T.signature.sort}
                (σ : GeometricTheory.TermSubst T.signature)
                {φ ψ : GeometricFormula T.signature Γ} :
      Derivable T φ ψ →
      Derivable T (φ.subst (Δ := Δ) σ) (ψ.subst (Δ := Δ) σ)
  /-- Existential introduction with witness term.

      Sprach-Klassen-Substanz (F29): replaces the unsound general-σ form.
      `t : Term sig s` is the witness. The substitution `TermSubst.idCons t` maps
      position 0 to `t` and position `k+1` to `var k` (Γ-preserving).
      Standard form from Johnstone Elephant D1.3 / Pitts Categorical Logic. -/
  | exI {Γ : List T.signature.sort} {s : T.signature.sort}
        (t : Term T.signature s)
        {φ : GeometricFormula T.signature (s :: Γ)}
        {ψ : GeometricFormula T.signature Γ} :
      Derivable T ψ (φ.subst (Δ := Γ) (GeometricTheory.TermSubst.idCons t)) →
      Derivable T ψ (GeometricFormula.exists_ s φ)
  /-- Existential elimination with correct weakening substitution.

      Sprach-Klassen-Substanz (F29): replaces the incorrect `lift (id sig) s` form.
      `TermSubst.shift` maps variable `n` to `var (n+1)`, genuinely shifting χ
      into the extended context `s :: Γ` (leaving position 0 free for the binder).
      The original `lift (id sig) s = id sig` (by `id_lift`) did not shift at all. -/
  | exE {Γ : List T.signature.sort} {s : T.signature.sort}
        {φ : GeometricFormula T.signature (s :: Γ)}
        {ψ χ : GeometricFormula T.signature Γ} :
      Derivable T ψ (GeometricFormula.exists_ s φ) →
      Derivable T φ (χ.subst (Δ := s :: Γ) GeometricTheory.TermSubst.shift) →
      Derivable T ψ χ

/-!
### Helper lemmas for `Derivable`
-/

namespace Derivable

open GeometricTheory

variable {T : Theory.{u, v, w}}

/-- Reflexivity: every formula is derivable from itself. -/
@[simp]
theorem refl {Γ : List T.signature.sort} {φ : GeometricFormula T.signature Γ} :
    Derivable T φ φ := .axm

/-- Transitivity of derivability. -/
theorem trans {Γ : List T.signature.sort} {φ ψ χ : GeometricFormula T.signature Γ}
    (h₁ : Derivable T φ ψ) (h₂ : Derivable T ψ χ) : Derivable T φ χ := .cut h₁ h₂

/-- Conjunction is monotone in both arguments. -/
theorem conj_mono {Γ : List T.signature.sort}
    {φ₁ φ₂ ψ₁ ψ₂ : GeometricFormula T.signature Γ}
    (h₁ : Derivable T φ₁ ψ₁) (h₂ : Derivable T φ₂ ψ₂) :
    Derivable T (.conj φ₁ φ₂) (.conj ψ₁ ψ₂) :=
  .conjI (.cut .conjE_l h₁) (.cut .conjE_r h₂)

/-- Disjunction is monotone componentwise. -/
theorem disj_mono {Γ : List T.signature.sort} {ι : Type (max u (max v w))}
    {fs gs : ι → GeometricFormula T.signature Γ}
    (h : ∀ i : ι, Derivable T (fs i) (gs i)) :
    Derivable T (.disj fs) (.disj gs) :=
  .disjE (fun i => .disjI i (h i))

/-- Substitution is monotone for derivability (bundled form of `substStable`). -/
theorem subst_mono {Γ Δ : List T.signature.sort}
    (σ : GeometricTheory.TermSubst T.signature)
    {φ ψ : GeometricFormula T.signature Γ}
    (h : Derivable T φ ψ) :
    Derivable T (φ.subst (Δ := Δ) σ) (ψ.subst (Δ := Δ) σ) :=
  .substStable σ h

end Derivable

end Reformulation.PathC.Classifying
