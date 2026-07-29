-- EINGEFROREN (29. Juli 2026): dieser Zweig wird nicht fortgeschrieben.
-- Status, Zahlen und die Bedingungen fuer ein Auftauen: docs/build-targets.md, Abschnitt PathC.
import Mathlib.CategoryTheory.Category.Basic
import Reformulation.PathC.GeometricTheory.Theory

/-!
# Reformulation.PathC.Classifying.SyntacticSite

The syntactic category C_T of a geometric theory T.

## What this module carries

- `ContextTerm sig Γ s` — a well-typed term of sort `s` in context `Γ`,
  with `Fin`-indexed de Bruijn variables matching the context exactly.

- `ContextTerm.subst` — well-typed simultaneous substitution.

- `SyntacticContext T` — objects of C_T: lists of sorts.

- `SyntacticMorphism T Γ Δ` — morphisms: substitutions from Γ to Δ.

- `Category (SyntacticContext T)` — full category structure with proofs.

## Methodological note

`ContextTerm` extends the context-free `Term` (from Lücke 4) with proper
de Bruijn indexing into a fixed context, enabling well-typed substitution.
The category laws (id_comp, comp_id, assoc) follow by structural induction.
-/

namespace Reformulation.PathC.Classifying

open CategoryTheory GeometricTheory

universe u v w

/-- A well-typed term of sort `s` in context `Γ`.
    Variables are indexed by `Fin Γ.length` pointing into the context. -/
inductive ContextTerm (sig : ManySortedSignature.{u, v, w}) :
    List sig.sort → sig.sort → Type (max u v) where
  | var  {Γ : List sig.sort} (i : Fin Γ.length) : ContextTerm sig Γ (Γ.get i)
  | app  {Γ : List sig.sort} {args : List sig.sort} {result : sig.sort} :
      sig.func args result →
      (∀ j : Fin args.length, ContextTerm sig Γ (args.get j)) →
      ContextTerm sig Γ result

/-- Apply substitution `σ` (maps Δ-variables to Γ-terms) to a term in context Δ. -/
def ContextTerm.subst {sig : ManySortedSignature.{u, v, w}}
    {Γ Δ : List sig.sort}
    (σ : ∀ i : Fin Δ.length, ContextTerm sig Γ (Δ.get i)) :
    ∀ {s : sig.sort}, ContextTerm sig Δ s → ContextTerm sig Γ s
  | _, ContextTerm.var i   => σ i
  | _, ContextTerm.app f a => ContextTerm.app f (fun j => ContextTerm.subst σ (a j))

/-- Substituting identity variables leaves a term unchanged. -/
theorem ContextTerm.subst_id {sig : ManySortedSignature.{u, v, w}}
    {Γ : List sig.sort} {s : sig.sort} (t : ContextTerm sig Γ s) :
    ContextTerm.subst (fun i => ContextTerm.var i) t = t := by
  induction t with
  | var i  => simp [ContextTerm.subst]
  | app f a ih => simp [ContextTerm.subst]; funext j; exact ih j

/-- Composition of substitutions equals iterated substitution. -/
theorem ContextTerm.subst_comp {sig : ManySortedSignature.{u, v, w}}
    {Γ Δ Θ : List sig.sort}
    (σ : ∀ i : Fin Δ.length, ContextTerm sig Γ (Δ.get i))
    (τ : ∀ i : Fin Θ.length, ContextTerm sig Δ (Θ.get i))
    {s : sig.sort} (t : ContextTerm sig Θ s) :
    ContextTerm.subst σ (ContextTerm.subst τ t) =
    ContextTerm.subst (fun i => ContextTerm.subst σ (τ i)) t := by
  induction t with
  | var i  => simp [ContextTerm.subst]
  | app f a ih => simp [ContextTerm.subst]; funext j; exact ih j

-- ============================================================
-- Syntactic category
-- ============================================================

/-- Objects of C_T: contexts (lists of sorts). -/
def SyntacticContext (T : Theory.{u, v, w}) := List T.signature.sort

/-- Morphisms in C_T: substitutions from context Γ to context Δ. -/
def SyntacticMorphism (T : Theory.{u, v, w}) (Γ Δ : SyntacticContext T) :=
  ∀ i : Fin Δ.length, ContextTerm T.signature Γ (Δ.get i)

private def synId (T : Theory.{u, v, w}) (Γ : SyntacticContext T) :
    SyntacticMorphism T Γ Γ :=
  fun i => ContextTerm.var i

private def synComp (T : Theory.{u, v, w}) {Γ Δ Θ : SyntacticContext T}
    (f : SyntacticMorphism T Γ Δ) (g : SyntacticMorphism T Δ Θ) :
    SyntacticMorphism T Γ Θ :=
  fun i => ContextTerm.subst f (g i)

/-- The syntactic category of T: contexts as objects, substitutions as morphisms. -/
instance syntacticCategory (T : Theory.{u, v, w}) : Category (SyntacticContext T) where
  Hom    := SyntacticMorphism T
  id     := synId T
  comp   := @synComp T
  id_comp {Γ Δ} f := by
    funext i
    simp only [synComp, synId]
    exact ContextTerm.subst_id (f i)
  comp_id {Γ Δ} f := by
    funext i
    simp only [synComp, synId, ContextTerm.subst]
  assoc {Γ Δ Θ Ξ} f g h := by
    funext i
    simp only [synComp]
    exact (ContextTerm.subst_comp f g (h i)).symm

end Reformulation.PathC.Classifying
