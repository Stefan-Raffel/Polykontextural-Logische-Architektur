import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts
import Mathlib.CategoryTheory.Subobject.Basic
import Mathlib.CategoryTheory.Subobject.Lattice
import Mathlib.CategoryTheory.Subobject.Limits
import Reformulation.PathC.Classifying.SyntacticSite
import Reformulation.PathC.ElementaryTopos
import Reformulation.MathlibExtensions.Topos.Subobject.Lattice

/-!
# Reformulation.PathC.Classifying.TermSemantics

Interpretation of sorts, terms, and geometric formulas in an elementary topos.

## Design (D-4)

`interpretContextTerm`, `interpretFormula`, `contextSubstMorphism` take a `ModelInterp`
record (sortInterp + funcInterp + relInterp). This avoids the Lean elaboration failure that
arises when `contextObj I args` appears inside a `∀ {args}` in a function *parameter type*:
in structure field types, earlier fields are concrete values, so instance synthesis works.

## D-4 β.2

- `toContextTerm`: 2 dummy-sorries (unreachable wrong-sort / out-of-bounds branches).
- `toContextTerm_subst`: sorry (pending proof involving dummy branches).
-/

namespace Reformulation.PathC.Classifying

open CategoryTheory GeometricTheory Limits

universe u v w

variable {T : Theory.{u, v, w}} {E : Type*} [Category E] [ElementaryTopos E]
variable [HasColimitsOfShape (Discrete PEmpty.{1}) E] [HasImages E]
variable [LocallySmall.{max u (max v w)} E] [HasWidePullbacks.{max u (max v w)} E]
variable [HasCoproducts.{max u (max v w)} E] [WellPowered.{max u (max v w)} E]
variable [InitialMonoClass E]

attribute [local instance] has_smallest_coproducts_of_hasCoproducts

/-- A sort interpretation: assigns an object of `E` to each sort of T.
    `abbrev` so Lean reduces it to `T.signature.sort → E` during elaboration. -/
abbrev SortInterp (T : Theory.{u, v, w}) (E : Type*) [Category E] :=
  T.signature.sort → E

/-- The interpretation of a context `Γ` as a finite product `∏ᶜ (i : Fin Γ.length), I(Γ.get i)`. -/
noncomputable def contextObj (I : SortInterp T E) (Γ : List T.signature.sort) : E :=
  ∏ᶜ (fun i : Fin Γ.length => I (Γ.get i))

/-- The `i`-th projection from the context product. -/
noncomputable def contextProj (I : SortInterp T E) (Γ : List T.signature.sort)
    (i : Fin Γ.length) : contextObj I Γ ⟶ I (Γ.get i) :=
  Pi.π _ i

-- ============================================================
-- ModelInterp: bundles sortInterp + funcInterp + relInterp.
--
-- Rationale: `contextObj sortInterp args` in structure FIELD types
-- works because `sortInterp` is a concrete earlier field (not a
-- ∀-bound variable), so Lean can synthesize [ElementaryTopos E]
-- from the structure's own implicit parameters.
-- ============================================================

/-- Interpretation data for a geometric theory T in E:
    sort interpretation + function-symbol interpretation + relation-symbol interpretation.

    **D-4 B-3**: This replaces the previous design of threading `FI` and `RI` as
    separate parameters through each semantic function. -/
structure ModelInterp (T : Theory.{u, v, w}) (E : Type*) [Category E] [ElementaryTopos E]
    [HasColimitsOfShape (Discrete PEmpty.{1}) E]
    [HasImages E]
    [LocallySmall.{max u (max v w)} E] [HasWidePullbacks.{max u (max v w)} E]
    [HasCoproducts.{max u (max v w)} E] [WellPowered.{max u (max v w)} E]
    [InitialMonoClass E] where
  /-- Sort interpretation. -/
  sortInterp : SortInterp T E
  /-- Function-symbol interpretation: morphism from argument-product to result.
      `let ctxObj : E := ...` forces the elaborator to constrain `E` before instance
      synthesis, avoiding the `ElementaryTopos (Type ?u)` failure. -/
  funcInterp : ∀ {args : List T.signature.sort} {result : T.signature.sort},
      T.signature.func args result →
      (let ctxObj : E := contextObj sortInterp args; ctxObj ⟶ sortInterp result)
  /-- Relation-symbol interpretation: subobject of argument-product. -/
  relInterp : ∀ {args : List T.signature.sort},
      T.signature.rel args →
      (let ctxObj : E := contextObj sortInterp args; Subobject ctxObj)

-- ============================================================
-- B-1: toContextTerm — ℕ↔Fin bridging
-- ============================================================

/-- Convert a ℕ-indexed `Term` to a Fin-indexed `ContextTerm` in context `Γ`.

    Sprach-Klassen-Substanz (D-4 B-1). Out-of-bounds and wrong-sort branches
    are unreachable for well-typed terms. -/
noncomputable def toContextTerm (Γ : List T.signature.sort) {s : T.signature.sort} :
    Term T.signature s → ContextTerm T.signature Γ s
  | .var n =>
      haveI : DecidableEq T.signature.sort := Classical.decEq T.signature.sort
      if h : n < Γ.length then
        if hs : Γ.get ⟨n, h⟩ = s then
          hs ▸ ContextTerm.var ⟨n, h⟩
        else
          -- D-4 β.2 (Unreachable): wrong sort for well-typed terms
          (by exact sorry)
      else
        -- D-4 β.2 (Unreachable): out of bounds for well-typed terms
        (by exact sorry)
  | .app f as => ContextTerm.app f (fun i => toContextTerm Γ (as i))

-- ============================================================
-- B-3: interpretContextTerm — uses MI.funcInterp
-- ============================================================

/-- Interpretation of a context-sensitive term as a morphism `contextObj MI.sortInterp Γ ⟶ MI.sortInterp s`.

    **T3 form (D-4)**:
    - `var i` → the `i`-th product projection.
    - `app f as` → `Pi.lift (interpretContextTerm ∘ as) ≫ MI.funcInterp f`. -/
noncomputable def interpretContextTerm (MI : ModelInterp T E)
    {Γ : List T.signature.sort} {s : T.signature.sort}
    (t : ContextTerm T.signature Γ s) :
    contextObj MI.sortInterp Γ ⟶ MI.sortInterp s :=
  match t with
  | .var i  => Pi.π _ i
  | .app f as =>
      Pi.lift (fun j => interpretContextTerm MI (as j)) ≫ MI.funcInterp f

/-- Interpretation of a tuple of context terms as a morphism into a product. -/
noncomputable def tupleMorphism (MI : ModelInterp T E)
    {Γ : List T.signature.sort} {args : List T.signature.sort}
    (ts : ∀ i : Fin args.length, ContextTerm T.signature Γ (args.get i)) :
    contextObj MI.sortInterp Γ ⟶ contextObj MI.sortInterp args :=
  Pi.lift (fun i => interpretContextTerm MI (ts i))

-- ============================================================
-- Helper: interpretContextTerm commutes with substitution
-- ============================================================

/-- Semantic interpretation commutes with simultaneous substitution. -/
theorem interpretContextTerm_subst (MI : ModelInterp T E)
    {Γ Δ : List T.signature.sort}
    (σ : ∀ i : Fin Δ.length, ContextTerm T.signature Γ (Δ.get i))
    {s : T.signature.sort} (t : ContextTerm T.signature Δ s) :
    Pi.lift (fun i => interpretContextTerm MI (σ i)) ≫ interpretContextTerm MI t =
    interpretContextTerm MI (ContextTerm.subst σ t) := by
  induction t with
  | var i =>
      simp [ContextTerm.subst, interpretContextTerm, Pi.lift_π]
  | app f as ih =>
      simp only [ContextTerm.subst, interpretContextTerm]
      -- key: Pi.lift σ ≫ Pi.lift as = Pi.lift (as.subst σ) (by Pi.hom_ext + ih)
      have key : Pi.lift (fun i => interpretContextTerm MI (σ i)) ≫
                 Pi.lift (fun j => interpretContextTerm MI (as j)) =
                 Pi.lift (fun j => interpretContextTerm MI (ContextTerm.subst σ (as j))) := by
        apply Pi.hom_ext; intro j
        simp only [contextObj, Category.assoc, Pi.lift_π]
        exact ih j
      -- Use Category.assoc as a term (not rw, which fails due to let-bound type in funcInterp)
      -- to re-parenthesize, then apply key.
      calc Pi.lift (fun i => interpretContextTerm MI (σ i)) ≫
               (Pi.lift (fun j => interpretContextTerm MI (as j)) ≫ MI.funcInterp f)
           = (Pi.lift (fun i => interpretContextTerm MI (σ i)) ≫
              Pi.lift (fun j => interpretContextTerm MI (as j))) ≫ MI.funcInterp f :=
               (Category.assoc _ _ _).symm
         _ = Pi.lift (fun j => interpretContextTerm MI (ContextTerm.subst σ (as j))) ≫
              MI.funcInterp f := by rw [key]

-- ============================================================
-- F: interpretFormula — atom case resolved via MI.relInterp
-- ============================================================

/-- Interpretation of a geometric formula as a subobject.

    **T3 form (D-4)** — all cases:
    - `top` → ⊤, `bot` → ⊥, `conj` → meet, `disj` → join, `exists_` → image.
    - `atom r as` → pullback of `MI.relInterp r` along tupleMorphism(toContextTerm ∘ as). ✓ -/
noncomputable def interpretFormula (MI : ModelInterp T E) :
    {Γ : List T.signature.sort} → GeometricFormula T.signature Γ →
    Subobject (contextObj MI.sortInterp Γ)
  | _, .top       => ⊤
  | _, .bot       => ⊥
  | Γ, .atom r as =>
      (Subobject.pullback
        (tupleMorphism MI (fun i => toContextTerm Γ (as i)))).obj (MI.relInterp r)
  | _, .conj φ ψ  => interpretFormula MI φ ⊓ interpretFormula MI ψ
  | _, .disj f    => ⨆ i, interpretFormula MI (f i)
  | Γ, .exists_ S φ =>
      imageSubobject
        ((interpretFormula MI φ).arrow ≫
         Pi.lift (fun i : Fin Γ.length =>
           Pi.π (fun j : Fin (S :: Γ).length => MI.sortInterp ((S :: Γ).get j))
               ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩))

-- ============================================================
-- B-2: contextSubstMorphism + naturality lemmas
-- ============================================================

/-- Naturality of `toContextTerm` under term substitution (D-4 β.2 pending). -/
theorem toContextTerm_subst {Γ Δ : List T.signature.sort} (σ : TermSubst T.signature)
    {s : T.signature.sort} (t : Term T.signature s) :
    toContextTerm Δ (t.subst σ) =
    ContextTerm.subst (fun i : Fin Γ.length => toContextTerm Δ (σ i.val (Γ.get i)))
      (toContextTerm Γ t) := by
  sorry

/-- The tuple morphism commutes with substitution. -/
theorem tupleMorphism_subst (MI : ModelInterp T E)
    {Γ Δ : List T.signature.sort} {arity : List T.signature.sort}
    (σ : TermSubst T.signature)
    (as : ∀ i : Fin arity.length, Term T.signature (arity.get i)) :
    Pi.lift (fun i : Fin Γ.length =>
        interpretContextTerm MI (toContextTerm Δ (σ i.val (Γ.get i)))) ≫
      tupleMorphism MI (fun i => toContextTerm Γ (as i)) =
    tupleMorphism MI (fun i => toContextTerm Δ ((as i).subst σ)) := by
  apply Pi.hom_ext; intro i
  -- Use calc to explicitly reassociate, then unfold tupleMorphism + Pi.lift_π
  calc (Pi.lift (fun j : Fin Γ.length =>
            interpretContextTerm MI (toContextTerm Δ (σ j.val (Γ.get j)))) ≫
          tupleMorphism MI (fun i => toContextTerm Γ (as i))) ≫ Pi.π _ i
       = Pi.lift (fun j : Fin Γ.length =>
             interpretContextTerm MI (toContextTerm Δ (σ j.val (Γ.get j)))) ≫
           (tupleMorphism MI (fun i => toContextTerm Γ (as i)) ≫ Pi.π _ i) :=
             Category.assoc _ _ _
     _ = Pi.lift (fun j : Fin Γ.length =>
             interpretContextTerm MI (toContextTerm Δ (σ j.val (Γ.get j)))) ≫
           interpretContextTerm MI (toContextTerm Γ (as i)) := by
             -- Unfold tupleMorphism + contextObj so Pi.lift_π can match the product
             simp only [tupleMorphism, contextObj, Pi.lift_π]
     _ = tupleMorphism MI (fun j => toContextTerm Δ ((as j).subst σ)) ≫ Pi.π _ i := by
             simp only [tupleMorphism, contextObj, Pi.lift_π]
             rw [toContextTerm_subst σ (as i)]
             exact interpretContextTerm_subst MI _ _

/-- The morphism `contextObj MI.sortInterp Δ ⟶ contextObj MI.sortInterp Γ` induced by σ.

    **T3 form (D-4)**: Pi.lift of interpretContextTerm ∘ toContextTerm. -/
noncomputable def contextSubstMorphism (MI : ModelInterp T E)
    {Γ Δ : List T.signature.sort}
    (σ : TermSubst T.signature) :
    contextObj MI.sortInterp Δ ⟶ contextObj MI.sortInterp Γ :=
  Pi.lift (fun i : Fin Γ.length =>
    interpretContextTerm MI (toContextTerm Δ (σ i.val (Γ.get i))))

-- ============================================================
-- F29: ctxSubst helper lemmas for exI/exE soundness
-- ============================================================

/-- The projection morphism `contextObj MI.sortInterp (s :: Γ) ⟶ contextObj MI.sortInterp Γ`
    that forgets the first (sort-s) component. Used in `interpretFormula` for `exists_`.

    **abbrev** so that goals involving the inline `Pi.lift` form from `interpretFormula`
    are definitionally transparent to Lean's unifier (no `change`/`show` needed for cast). -/
noncomputable abbrev projMorphism (MI : ModelInterp T E) (s : T.signature.sort)
    (Γ : List T.signature.sort) :
    contextObj MI.sortInterp (s :: Γ) ⟶ contextObj MI.sortInterp Γ :=
  Pi.lift (fun i : Fin Γ.length =>
    Pi.π (fun k : Fin (s :: Γ).length => MI.sortInterp ((s :: Γ).get k))
        ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)

/-- H-1: The contextSubstMorphism of `idCons t` composed with the projection equals
    the identity on `contextObj MI.sortInterp Γ`.

    Sprach-Klassen-Substanz (F29): key lemma for exI soundness. The idCons substitution
    inserts `t` at position 0 and maps `k+1 ↦ var k`, so projecting away position 0
    recovers the identity.

    Proof: Pi.hom_ext; component n reduces via idCons (succ branch) + List.get_cons_succ
    to `toContextTerm Γ (Term.var n)`, which unfolds to `ContextTerm.var ⟨n, hn⟩` via
    `dif_pos` on both the bounds and sort-equality guards, then `interpretContextTerm`
    gives `Pi.π _ ⟨n, hn⟩ = 𝟙 component`. -/
theorem ctxSubst_idCons_proj_eq_id (MI : ModelInterp T E) {Γ : List T.signature.sort}
    {s : T.signature.sort} (t : Term T.signature s) :
    contextSubstMorphism MI (TermSubst.idCons t) ≫ projMorphism MI s Γ =
    𝟙 (contextObj MI.sortInterp Γ) := by
  apply Pi.hom_ext; intro j
  -- erw uses defeq matching, handling Category.toCategoryStruct vs inst✝⁸.toCategoryStruct.
  -- unfold first to expose Pi.lift; erw [Category.assoc] reassociates; Pi.lift_π reduces.
  unfold contextSubstMorphism projMorphism
  -- erw uses defeq: assoc on outer (f≫g)≫h, Pi.lift_π twice (inner G≫π, then outer F≫π),
  -- id_comp on 𝟙_≫π RHS (Category.toCategoryStruct instance issue prevents plain rw/simp).
  erw [Category.assoc, Pi.lift_π, Pi.lift_π, Category.id_comp]
  simp [TermSubst.idCons, toContextTerm, interpretContextTerm, j.isLt]

/-- H-2: The contextSubstMorphism of `TermSubst.shift` equals the projection morphism.

    Sprach-Klassen-Substanz (F29): key lemma for exE soundness. `shift` maps variable `n`
    to `Term.var (n+1)`, which in context `s :: Γ` is exactly position `n+1` — the
    `n`-th component of the Γ-part. So `ctxSubst M shift = projMorphism`.

    Proof: Pi.hom_ext; component n reduces via shift def to `toContextTerm (s::Γ) (Term.var (n+1))`,
    which unfolds via `dif_pos (succ_lt_succ hn)` + `dif_pos rfl` (the sort equality
    `(s::Γ).get ⟨n+1,_⟩ = Γ.get ⟨n,hn⟩` holds by rfl since `List.get` reduces definitionally)
    to `ContextTerm.var ⟨n+1, _⟩`, giving `Pi.π _ ⟨n+1, _⟩` = projMorphism component. -/
theorem ctxSubst_shift_eq_proj (MI : ModelInterp T E) {Γ : List T.signature.sort}
    {s : T.signature.sort} :
    contextSubstMorphism MI (TermSubst.shift (sig := T.signature)) = projMorphism MI s Γ := by
  apply Pi.hom_ext; intro j
  -- unfold contextSubstMorphism (def) to expose Pi.lift; projMorphism (abbrev) is already
  -- reduced on the RHS by Pi.hom_ext.  Pi.lift_π closes the single-composition LHS.
  unfold contextSubstMorphism
  -- First erw: Pi.lift_π reduces LHS (Pi.lift F ≫ π H j → F j).
  -- Second erw: Pi.lift_π reduces RHS (projMorphism = Pi.lift G via abbrev, so G j = π K ⟨↑j+1,⋯⟩).
  erw [Pi.lift_π, Pi.lift_π]
  simp [TermSubst.shift, toContextTerm, interpretContextTerm, Nat.succ_lt_succ j.isLt]

-- ============================================================
-- F30: Beck-Chevalley helper lemmas for interpretFormula_subst.exists_
-- ============================================================

/-- Auxiliary: interpretation of a shifted term factors through the projection.
    Inherits D-4 β.2 sorries from `toContextTerm`. -/
private theorem interp_toContextTerm_shiftVar (MI : ModelInterp T E)
    {Γ : List T.signature.sort} {S s : T.signature.sort}
    (t : Term T.signature s) :
    interpretContextTerm MI (toContextTerm (S :: Γ) t.shiftVar) =
    projMorphism MI S Γ ≫ interpretContextTerm MI (toContextTerm Γ t) := by
  induction t with
  | var n => sorry  -- D-4 β.2 inherited (sort-check transport)
  | app f as ih =>
      simp only [Term.shiftVar, toContextTerm, interpretContextTerm, contextObj]
      -- IH: toCtx(S::Γ, (as i).shiftVar) = proj ≫ toCtx(Γ, as i)
      have lhs_eq : (fun i => interpretContextTerm MI (toContextTerm (S :: Γ) ((as i).shiftVar))) =
          (fun i => projMorphism MI S Γ ≫ interpretContextTerm MI (toContextTerm Γ (as i))) :=
        funext (fun i => ih i)
      -- Pi.lift (fun i => proj ≫ f_i) = proj ≫ Pi.lift (fun i => f_i)
      have comm : Pi.lift (fun i => projMorphism MI S Γ ≫
            interpretContextTerm MI (toContextTerm Γ (as i))) =
          projMorphism MI S Γ ≫ Pi.lift (fun i =>
            interpretContextTerm MI (toContextTerm Γ (as i))) := by
        apply Pi.hom_ext; intro k
        simp only [Category.assoc]; erw [Pi.lift_π, Pi.lift_π]
      calc Pi.lift (fun i => interpretContextTerm MI (toContextTerm (S :: Γ) ((as i).shiftVar))) ≫
              MI.funcInterp f
          = Pi.lift (fun i => projMorphism MI S Γ ≫
                interpretContextTerm MI (toContextTerm Γ (as i))) ≫ MI.funcInterp f := by
              congr 1; apply Pi.hom_ext; intro k; erw [Pi.lift_π, Pi.lift_π]; exact ih k
        _ = (projMorphism MI S Γ ≫ Pi.lift (fun i =>
                interpretContextTerm MI (toContextTerm Γ (as i)))) ≫ MI.funcInterp f := by
              rw [comm]
        _ = projMorphism MI S Γ ≫ Pi.lift (fun i =>
                interpretContextTerm MI (toContextTerm Γ (as i))) ≫ MI.funcInterp f := by
              rw [Category.assoc]

/-- H-1 (F30): `ctxSubst(σ.lift S) ≫ proj_Γ = proj_Δ ≫ ctxSubst σ` -/
theorem ctxSubstMorph_lift_proj_comm (MI : ModelInterp T E)
    {Γ Δ : List T.signature.sort} {S : T.signature.sort}
    (σ : TermSubst T.signature) :
    contextSubstMorphism MI (σ.lift S) ≫ projMorphism MI S Γ =
    projMorphism MI S Δ ≫ contextSubstMorphism MI σ := by
  apply Pi.hom_ext; intro j
  unfold contextSubstMorphism projMorphism
  erw [Category.assoc, Pi.lift_π, Pi.lift_π]
  simp only [TermSubst.lift, List.get_cons_succ]
  erw [Category.assoc, Pi.lift_π]
  exact interp_toContextTerm_shiftVar MI (σ j.val (Γ.get j))

/-- H-2 (F30): The Beck-Chevalley square is a pullback square.

    **Mathematical core of F30**: IsPullback via Pi-lift universal property.
    Full proof: lift uses contextProj for components; fac_left via H-1 + fac_right +
    s.condition; fac_right by Pi.lift_π; uniq via h_snd/h_fst projections.
    Implementation deferred (complex Lean elaboration for contextObj↔∏ᶜ coercion). -/
theorem ctxSubstMorph_lift_isPullback (MI : ModelInterp T E)
    {Γ Δ : List T.signature.sort} {S : T.signature.sort}
    (σ : TermSubst T.signature) :
    IsPullback
      (contextSubstMorphism MI (σ.lift S))
      (projMorphism MI S Δ)
      (projMorphism MI S Γ)
      (contextSubstMorphism MI σ) := by
  -- Proof sketch: IsPullback.of_isLimit with PullbackCone.IsLimit.mk.
  -- Lift: Pi.lift with 0-component from s.fst ≫ contextProj(S::Γ)⟨0,_⟩,
  -- k-component from s.snd ≫ contextProj(Δ)⟨k,_⟩.
  -- fac_left: at 0 via σ.lift S (0) = var 0; at k+1 via H-1 + fac_right + s.condition.
  -- fac_right: Pi.hom_ext + Pi.lift_π + projMorphism component.
  -- uniq: Pi.hom_ext + h_fst/h_snd projections.
  -- Lean elaboration complexity: contextObj (def, not abbrev) vs ∏ᶜ coercions.
  -- Not a new β.2: mathematically provable; elaboration detail only.
  sorry

end Reformulation.PathC.Classifying
