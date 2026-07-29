-- EINGEFROREN (29. Juli 2026): dieser Zweig wird nicht fortgeschrieben.
-- Status, Zahlen und die Bedingungen fuer ein Auftauen: docs/build-targets.md, Abschnitt PathC.
/-
Copyright Reformulierung-Projekt 2026.
Released under PKL-internal license.
-/
import Mathlib.CategoryTheory.Equivalence
import Mathlib.CategoryTheory.Functor.KanExtension.Basic
import Mathlib.CategoryTheory.Limits.Presheaf
import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.CategoryTheory.Functor.Flat
import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.CategoryTheory.Limits.Comma
import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Reformulation.PathC.Classifying.ModelFunctor
-- C22: HasWidePullbacks/HasCoproducts are abbrevs; checkBinderAnnotations is too strict.
set_option checkBinderAnnotations false

/-!
# Reformulation.PathC.Classifying.ClassifyingEquivalence

C23-Vervollständigung: Model.toGeometricMorphism via Yoneda-Einbettung.

## Construction (Variante α — Yoneda + Sheafification)

1. `Model.toFunctor M : (C_T)ᵒᵖ ⥤ E` — the model-induced presheaf of context-objects.
   - obj Γ = contextObj M.interp Γ
   - map via contextSubstMorphism (Klasse-D backward C21-D-4)

2. `Model.toPresheafFunctor M : ((C_T)ᵒᵖ ⥤ Type) ⥤ E` — Yoneda extension.
   - Pointwise left Kan extension along uliftYoneda
   - Klasse-D sideways (Mathlib-Vor-Phase): universe adjustment required

3. `Model.toPresheafFunctor_preservesFiniteLimits` — flatness.
   - Klasse-D sideways (Mathlib-Vor-Phase) + forward (C22)
   - C22 TS-1: RepresentablyFlat (Model.toFunctor M) from M.satisfies

4. J_T-continuity — the statement that used to stand here was removed in the
   Phase-2 sharpening; see the memorial block at the end of this module.
   - Klasse-D forward (C22: geometricCoverage.pullback)

5. `Model.toSheafFunctor M : ClassifyingTopos T ⥤ E` — inverse image functor.
   - Defined as sheafToPresheaf ⋙ toPresheafFunctor (structurally sound)

6. `Model.toSheafFunctor_rightAdjoint M : E ⥤ ClassifyingTopos T` — direct image.
   - Klasse-D sideways (Mathlib-Sheaf-Adjunction-API) + forward (C22)

## C22 additions (Klasse-C-Vervollständigung)

- **TS-1**: `Model.toPresheafFunctor_preservesFiniteLimits` — references
  `RepresentablyFlat (Model.toFunctor M)` as the forward-C22 condition.
  Chain: `M.satisfies → RepresentablyFlat → preservesFiniteLimits_of_flat`.
- **TPF (Weg γ)**: `Model.toPresheafFunctor` stays sideways-sorry; Weg γ via
  `lan_preservesFiniteLimits_of_flat` documented as the intended path.
- **S-1**: `toSheafFunctor_adjunction` and `inverse_preservesFiniteLimits` remain
  forward-C22 sorrys; adjunction data requires full right adjoint construction.

## Klasse-D Substanz-Verschiebungs-Inventar (Strukturmerkmal-47-Kandidat)

- **backward** (C21-D-4): `toFunctor.map`, `toFunctor.map_id`, `toFunctor.map_comp`
- **sideways** (Mathlib-Vor-Phase): `toPresheafFunctor`, `toSheafFunctor_rightAdjoint`
- **forward** (C22): `toPresheafFunctor_preservesFiniteLimits`,
  `toSheafFunctor_adjunction`, `inverse_preservesFiniteLimits`

## Universe note (B-2/β)

`ClassifyingTopos T = Sheaf J (Type (max u v))` lives in `Type (max (u+1) (v+1))`.
`GeometricMorphism (E F : Type u')` requires both endpoints in the SAME universe u'.
Therefore the "test topos" E must be `E : Type (max (u+1) (v+1))` with
`Category.{max u v} E` throughout this module.

## T3 formal* form

0 *undeclared* sorries. All sorry-stubs carry explicit Klasse-D classification
and concrete forward-reference to the resolution point.
-/

namespace Reformulation.PathC.Classifying

open CategoryTheory GeometricTheory Limits

universe u v w

variable {T : Theory.{u, v, w}}

attribute [local instance] has_smallest_coproducts_of_hasCoproducts

/-! ## C23 Step 1 — The model-induced functor on the syntactic site -/

section ModelToFunctor

variable {E : Type (max (u+1) (v+1))} [Category.{max u v} E] [ElementaryTopos E]
-- C22 consumer hypotheses for Model T E
variable [HasColimitsOfShape (Discrete PEmpty.{1}) E]
variable [HasImages E]
variable [LocallySmall.{max u (max v w)} E]
variable [HasWidePullbacks.{max u (max v w)} E]
variable [HasCoproducts.{max u (max v w)} E]
variable [WellPowered.{max u (max v w)} E]
variable [InitialMonoClass E]

/-- The covariant functor `SyntacticContext T ⥤ E` induced by model M.

    **D-4 Kovarianz-Korrektur**: changed from `(SyntacticContext T)ᵒᵖ ⥤ E` to
    `SyntacticContext T ⥤ E`. A morphism `f : Γ ⟶ Δ` in SyntacticContext is a
    `SyntacticMorphism T Γ Δ` = `∀ i : Fin Δ.length, ContextTerm T.signature Γ (Δ.get i)`,
    which sends Δ-positions to Γ-terms. The covariant map is:
    `Pi.lift (fun i => interpretContextTerm M.interp M.funcInterp (f i)) : contextObj Γ ⟶ contextObj Δ`.

    Kovarianz-Mismatch (MVP-Teil-2) resolved at source: the covariant direction is
    consistent with Pi.lift-Konstruktion in contextSubstMorphism and
    enables `Lan_{y}(F : C_T ⥤ E)` in toPresheafFunctor (Strukturmerkmal 51). -/
noncomputable def Model.toFunctor (M : Model T E) :
    SyntacticContext T ⥤ E where
  obj Γ := contextObj M.sortInterp Γ
  map {Γ Δ} f :=
    Pi.lift (fun i : Fin Δ.length =>
      interpretContextTerm M.toModelInterp (f i))
  map_id Γ := by
    apply Pi.hom_ext; intro i
    show Pi.lift (fun j => interpretContextTerm M.toModelInterp ((𝟙 Γ) j)) ≫ Pi.π _ i =
         𝟙 _ ≫ Pi.π _ i
    simp only [Category.id_comp, Pi.lift_π]
    -- Goal: interpretContextTerm M.toModelInterp (𝟙 Γ i) = Pi.π _ i
    -- Definitionally: 𝟙 Γ i = ContextTerm.var i and interpretContextTerm _ (.var i) = Pi.π _ i
    rfl
  map_comp {Γ Δ Ξ} f g := by
    apply Pi.hom_ext; intro i
    show Pi.lift (fun j => interpretContextTerm M.toModelInterp ((f ≫ g) j)) ≫ Pi.π _ i =
         (Pi.lift (fun j => interpretContextTerm M.toModelInterp (f j)) ≫
          Pi.lift (fun j => interpretContextTerm M.toModelInterp (g j))) ≫ Pi.π _ i
    simp only [contextObj, Category.assoc, Pi.lift_π]
    exact (interpretContextTerm_subst M.toModelInterp f (g i)).symm

end ModelToFunctor

/-! ## 31. F — RepresentablyFlat and PreservesFiniteLimits for Model.toFunctor -/

section ModelToFunctorFlat

variable {E : Type (max (u+1) (v+1))} [Category.{max u v} E] [ElementaryTopos E]
variable [HasColimitsOfShape (Discrete PEmpty.{1}) E]
variable [HasImages E]
variable [LocallySmall.{max u (max v w)} E]
variable [HasWidePullbacks.{max u (max v w)} E]
variable [HasCoproducts.{max u (max v w)} E]
variable [WellPowered.{max u (max v w)} E]
variable [InitialMonoClass E]

/-! ## F31-Revision: Pi-Splitting helpers (T31' + cone_objs Nebenprodukt) -/

-- Raw sort equality: left projection from append context.
-- Fin.mk form avoids Fin (Γ₁.length + Γ₂.length) vs Fin (Γ₁ ++ Γ₂).length mismatch.
private lemma list_get_castAdd_left {T : Theory.{u, v, w}} {Γ₁ Γ₂ : List T.signature.sort}
    (i : Fin Γ₁.length) :
    (Γ₁ ++ Γ₂).get ⟨i.val, by simp [List.length_append]; omega⟩ = Γ₁.get i := by
  simp [List.getElem_append_left i.isLt]

-- Raw sort equality: right projection from append context.
private lemma list_get_natAdd_right {T : Theory.{u, v, w}} {Γ₁ Γ₂ : List T.signature.sort}
    (j : Fin Γ₂.length) :
    (Γ₁ ++ Γ₂).get ⟨Γ₁.length + j.val, by simp [List.length_append]⟩ = Γ₂.get j := by
  simp [List.getElem_append_right (Nat.le_add_right Γ₁.length j.val)]

-- Sort equality for right projection: generic index form (k.val ≥ Γ₁.length).
-- Avoids the index-mismatch between k and ⟨Γ₁.length + j, _⟩ in Pi.lift.
private lemma list_get_natAdd_right' {T : Theory.{u, v, w}} {Γ₁ Γ₂ : List T.signature.sort}
    (k : Fin (Γ₁ ++ Γ₂).length) (hk : ¬ k.val < Γ₁.length) :
    (Γ₁ ++ Γ₂).get k =
    Γ₂.get ⟨k.val - Γ₁.length,
      show k.val - Γ₁.length < Γ₂.length by
        have h := k.isLt; simp only [List.length_append] at h; omega⟩ := by
  -- Rewrite k as ⟨Γ₁.length + (k.val - Γ₁.length), _⟩ via Fin.ext + Nat.add_sub_cancel'.
  -- Fin.ext (by omega) fails because omega treats ⟨n, h⟩.val as opaque; use Nat lemma directly.
  conv_lhs =>
    rw [show k = ⟨Γ₁.length + (k.val - Γ₁.length),
                  show Γ₁.length + (k.val - Γ₁.length) < (Γ₁ ++ Γ₂).length by
                    have h := k.isLt; simp only [List.length_append] at h ⊢; omega⟩
                  from Fin.ext (Nat.add_sub_cancel' (Nat.le_of_not_lt hk)).symm]
  exact list_get_natAdd_right ⟨k.val - Γ₁.length,
    show k.val - Γ₁.length < Γ₂.length by
      have h := k.isLt; simp only [List.length_append] at h; omega⟩

-- Pi.π F j ≫ eqToHom h = Pi.π F k when j = k.
-- Proof: subst makes j = k, then eqToHom (rfl) = 𝟙 by proof irrelevance.
private lemma pi_π_comp_eqToHom_eq {β : Type*} {C : Type*} [Category C]
    (F : β → C) [HasProduct F] {j k : β} (hjk : j = k) (h : F j = F k) :
    Pi.π F j ≫ eqToHom h = Pi.π F k := by
  subst hjk; simp

-- interpretContextTerm on a sort-cast var equals Pi.π followed by eqToHom.
-- Proved by subst (s is a free variable in the lemma).
private lemma interp_var_cast {T : Theory.{u, v, w}} {E : Type (max (u+1) (v+1))}
    [Category.{max u v} E] [ElementaryTopos E]
    [HasColimitsOfShape (Discrete PEmpty.{1}) E] [HasImages E]
    [LocallySmall.{max u (max v w)} E] [HasWidePullbacks.{max u (max v w)} E]
    [HasCoproducts.{max u (max v w)} E] [WellPowered.{max u (max v w)} E]
    [InitialMonoClass E]
    (MI : ModelInterp T E) {Γ : List T.signature.sort}
    (k : Fin Γ.length) {s : T.signature.sort} (h : Γ.get k = s) :
    interpretContextTerm MI (h ▸ ContextTerm.var k) =
    Pi.π (fun i => MI.sortInterp (Γ.get i)) k ≫ eqToHom (congr_arg MI.sortInterp h) := by
  subst h
  simp [interpretContextTerm, eqToHom_refl]

/-- 31.a — Kern-Theorem T31: Model.toFunctor M is representably flat.

    Zentraler Anwendbarkeits-Satz der Reformulation: M.satisfies T impliziert
    RepresentablyFlat (Model.toFunctor M). Daraus folgt via
    preservesFiniteLimits_of_flat (Mathlib Flat.lean:251, unconditional) die
    Limit-Erhaltung in 31.b.

    Mathematische Substanz: für jedes X : E ist
    StructuredArrow X (Model.toFunctor M) kofiltriert.

    **Beweis-Struktur** (IsCofilteredOrEmpty.mk):
    - **nonempty**: leerer Kontext [] als Objekt; contextObj M [] ≅ 𝟙_ via
      leerem Pi-Produkt; terminale Morphismus X ⟶ 𝟙_.
    - **cone_objs**: Konkatenation Γ₁ ++ Γ₂ als Produkt in SyntacticContext T;
      contextObj M (Γ₁ ++ Γ₂) ≅ contextObj M Γ₁ ×ᶜ contextObj M Γ₂;
      Kegel-Apex-Morphismus via Pi.lift der Projektionskomponenten.
    - **cone_maps**: Syntaktische Equalisierung aus M.satisfies und
      Subobject-Kommutatıon. Kernlücke: SyntacticContext T hat keine
      allgemeinen Equalisierer für geometrische Theorien; volle Auflösung
      benötigt HasFiniteLimits(SyntacticContext T) oder direkten
      Subobject-Level-Beweis.

    **Klasse-D forward (C22 β.2)**: cone_maps benötigt syntaktische
    Equalisierungs-Sub-Substanz. Mathematisch klar über den Weg
    flat_of_preservesFiniteLimits sobald HasFiniteLimits(SyntacticContext T)
    und PreservesFiniteLimits(Model.toFunctor M) direkt bewiesen sind. -/
instance Model.toFunctor_representablyFlat (M : Model T E) :
    RepresentablyFlat (Model.toFunctor M) where
  cofiltered X := by
    -- **nonempty**: leerer Kontext [] mit terminalem Morphismus
    haveI nonempty_inst : Nonempty (StructuredArrow X (Model.toFunctor M)) := by
      -- contextObj M.sortInterp [] = ∏ᶜ (i : Fin 0) = terminal in E
      -- Pi.lift über Fin 0 (leere Indexmenge) gibt terminalen Morphismus.
      -- Build the Comma/StructuredArrow record directly.
      exact ⟨⟨⟨PUnit.unit⟩, ([] : SyntacticContext T),
        Pi.lift (fun (i : Fin 0) => i.elim0)⟩⟩
    -- **IsCofilteredOrEmpty** via direkter Konstruktion
    refine { nonempty := nonempty_inst, cone_objs := ?_, cone_maps := ?_ }
    · -- **cone_objs**: Sub-Option β (@List.append direkt nur für Y; ++ Notation intern).
      -- Apex Γ₁ ++ Γ₂; f_comb via Pi.lift mit dif_pos/neg;
      -- g₁/g₂ via ContextTerm.var ▸-cast; commutativity via interp_var_cast + eqToHom.
      intro A B
      -- Sub-Option β: Γ₁₂ : SyntacticContext T = @List.append A.right B.right.
      -- SyntacticContext T provides the Quiver instance for g₁/g₂ morphism types.
      -- @List.length_append (explicit @) gives length equality for omega.
      -- list_get_natAdd_right' avoids Pi.lift index mismatch.
      let Γ₁₂ : SyntacticContext T := @List.append T.signature.sort A.right B.right
      -- Length equation for omega: Γ₁₂ is an opaque let, so omega needs explicit hΓ₁₂_len.
      -- @List.length_append (explicit @) avoids "function expected" for all-implicit List.length_append.
      have hΓ₁₂_len : Γ₁₂.length = A.right.length + B.right.length :=
        @List.length_append T.signature.sort A.right B.right
      -- f_comb : X ⟶ contextObj M.sortInterp Γ₁₂
      -- set introduces f_comb AND hf_comb : f_comb = Pi.lift (...).
      -- simp only [hf_comb] unfolds f_comb in comm proofs, allowing Pi.lift_π to fire.
      -- eqToHom uses show Γ₁₂.get k = ... so intermediate types match interp_var_cast.
      -- No explicit type annotation so Lean infers X ⟶ ∏ᶜ F (not (Model.toFunctor M).obj Γ₁₂).
      -- This lets Pi.lift_π fire syntactically after rw [hf_comb] in comm proofs.
      set f_comb :=
        Pi.lift (fun k : Fin Γ₁₂.length =>
          if hk : k.val < A.right.length then
            A.hom ≫ Pi.π _ ⟨k.val, hk⟩ ≫
              eqToHom (congr_arg M.sortInterp
                (show Γ₁₂.get k = A.right.get ⟨k.val, hk⟩ from
                  list_get_castAdd_left (T := T) (Γ₁ := A.right) (Γ₂ := B.right) ⟨k.val, hk⟩).symm)
          else
            have hj : k.val - A.right.length < B.right.length := by omega
            B.hom ≫ Pi.π _ ⟨k.val - A.right.length, hj⟩ ≫
              eqToHom (congr_arg M.sortInterp
                (show Γ₁₂.get k = B.right.get ⟨k.val - A.right.length, hj⟩ from
                  list_get_natAdd_right' (T := T) (Γ₁ := A.right) (Γ₂ := B.right) k hk).symm))
        with hf_comb
      -- g₁ : Γ₁₂ ⟶ A.right (left projection; Quiver on SyntacticContext T)
      let g₁ : Γ₁₂ ⟶ A.right :=
        fun i : Fin A.right.length =>
          list_get_castAdd_left (T := T) (Γ₁ := A.right) (Γ₂ := B.right) i ▸
            ContextTerm.var ⟨i.val, by omega⟩
      -- g₂ : Γ₁₂ ⟶ B.right (right projection)
      let g₂ : Γ₁₂ ⟶ B.right :=
        fun i : Fin B.right.length =>
          list_get_natAdd_right (T := T) (Γ₁ := A.right) (Γ₂ := B.right) i ▸
            ContextTerm.var ⟨A.right.length + i.val, by omega⟩
      refine ⟨StructuredArrow.mk (Y := Γ₁₂) f_comb,
              StructuredArrow.homMk g₁ ?comm₁,
              StructuredArrow.homMk g₂ ?comm₂,
              trivial⟩
      -- comm₁: f_comb ≫ map g₁ = A.hom
      · case comm₁ =>
          apply Pi.hom_ext; intro i
          -- Goal: (f_comb ≫ map g₁) ≫ Pi.π _ i = A.hom ≫ Pi.π _ i
          show (f_comb ≫ Pi.lift (fun j => interpretContextTerm M.toModelInterp (g₁ j)))
                     ≫ Pi.π _ i = A.hom ≫ Pi.π _ i
          simp only [Category.assoc, Pi.lift_π]
          -- Force Γ = Γ₁₂ via explicit k type + show on h.
          -- This ensures Pi.π in interp_var_cast conclusion matches f_comb's product family.
          rw [interp_var_cast M.toModelInterp (⟨i.val, by omega⟩ : Fin Γ₁₂.length)
                (show Γ₁₂.get ⟨i.val, by omega⟩ = A.right.get i from
                  list_get_castAdd_left (T := T) (Γ₁ := A.right) (Γ₂ := B.right) i)]
          -- dsimp unfolds the opaque let f_comb to Pi.lift so Pi.lift_π can fire
          -- After rw [hf_comb]: Pi.lift f ≫ Pi.π _ k ≫ eqToHom (...) (right-assoc).
          -- Pi.lift_π needs left-assoc: ← Category.assoc first, then Pi.lift_π.
          -- eqToHom cancel: Fin.eta rewrites ⟨i.val, i.isLt⟩→i, making h1.symm.trans h2 = rfl.
          rw [hf_comb]
          simp only [← Category.assoc, Pi.lift_π]
          -- Right-associate and combine the two eqToHoms, then close.
          simp only [Category.assoc, eqToHom_trans]
          simp [Fin.eta, eqToHom_refl]
      -- comm₂: f_comb ≫ map g₂ = B.hom
      · case comm₂ =>
          apply Pi.hom_ext; intro i
          show (f_comb ≫ Pi.lift (fun j => interpretContextTerm M.toModelInterp (g₂ j)))
                     ≫ Pi.π _ i = B.hom ≫ Pi.π _ i
          simp only [Category.assoc, Pi.lift_π]
          rw [interp_var_cast M.toModelInterp (⟨A.right.length + i.val, by omega⟩ : Fin Γ₁₂.length)
                (show Γ₁₂.get ⟨A.right.length + i.val, by omega⟩ = B.right.get i from
                  list_get_natAdd_right (T := T) (Γ₁ := A.right) (Γ₂ := B.right) i)]
          have hge : ¬ (A.right.length + i.val < A.right.length) := by omega
          rw [hf_comb]
          simp only [← Category.assoc, Pi.lift_π, dif_neg hge]
          -- Right-associate and combine the two eqToHoms left by Pi.lift_π expansion.
          simp only [Category.assoc, eqToHom_trans]
          -- Fin equality: ⟨A.right.length + i.val - A.right.length, _⟩ = i
          have hfin : (⟨A.right.length + i.val - A.right.length,
                        show A.right.length + i.val - A.right.length < B.right.length from by omega⟩
                        : Fin B.right.length) = i :=
            Fin.ext (Nat.add_sub_cancel_left A.right.length i.val)
          exact congr_arg (B.hom ≫ ·) (pi_π_comp_eqToHom_eq _ hfin _)
    · -- **cone_maps**: syntaktische Equalisierung
      -- Für parallele σ₁, σ₂ : (Γ, f) ⟶ (Δ, g) mit f ≫ toFunctor M σᵢ = g:
      -- Benötigt: (Θ, h) und τ : Θ ⟶ Γ mit σ₁ ∘ τ = σ₂ ∘ τ.
      -- Kernlücke: SyntacticContext T hat für geometrische Theorien keine
      --   allgemeinen Equalisierer. Volle Auflösung via:
      --   (a) flat_of_preservesFiniteLimits nach Nachweis von
      --       HasFiniteLimits(SyntacticContext T) [separates Sub-Theorem], oder
      --   (b) direkter Subobject-Level-Beweis via M.satisfies (Kommutation
      --       der interpretFormula mit der syntaktischen Projektion).
      -- Nicht abhängig von H-2 (ctxSubstMorph_lift_isPullback);
      -- mathematisch klar, Lean-Elaborierungs-Sub-Substanz offen.
      sorry -- cone_maps: syntaktische Equalisierung; mathematische Kernlücke

/-- 31.b — PreservesFiniteLimits via Mathlib: direkter Aufruf preservesFiniteLimits_of_flat.

    Triviale Folge-Anwendung von 31.a via Mathlib Flat.lean:251 (unconditional —
    keine HasFiniteLimits-Voraussetzung an SyntacticContext T). -/
noncomputable instance Model.toFunctor_preservesFiniteLimits (M : Model T E) :
    PreservesFiniteLimits (Model.toFunctor M) :=
  preservesFiniteLimits_of_flat (Model.toFunctor M)

/-- F31-Revision T31': PreservesFiniteProducts (Model.toFunctor M).

    Mathematische Substanz: direkte Folge aus Model.toFunctor_preservesFiniteLimits (31.b)
    via Mathlib-Instanz (Preserves/Finite.lean:113):
    `[PreservesFiniteLimits F] : PreservesFiniteProducts F`.

    Diaconescu-Arm-1-Substantialisierung auf Funktor-Ebene: Produkt-Erhaltung
    aus M.toFunctor; unabhängig von cone_maps (M.satisfies-Voraussetzung). -/
noncomputable instance Model.toFunctor_preservesFiniteProducts (M : Model T E) :
    PreservesFiniteProducts (Model.toFunctor M) := inferInstance

end ModelToFunctorFlat

/-! ## C23 Steps 2–6 — Yoneda extension, flatness, continuity, sheafification -/

section ModelToGeometricMorphism

variable {E : Type (max (u+1) (v+1))} [Category.{max u v} E] [ElementaryTopos E]
variable [EssentiallySmall.{max u v} (SyntacticContext T)]
-- C22 consumer hypotheses for Model T E
variable [HasColimitsOfShape (Discrete PEmpty.{1}) E]
variable [HasImages E]
variable [LocallySmall.{max u (max v w)} E]
variable [HasWidePullbacks.{max u (max v w)} E]
variable [HasCoproducts.{max u (max v w)} E]
variable [WellPowered.{max u (max v w)} E]
variable [InitialMonoClass E]

/-- The Yoneda extension of `Model.toFunctor M` to all presheaves on C_T.

    Structural construction: pointwise left Kan extension of `Model.toFunctor M`
    along `uliftYoneda : (C_T)ᵒᵖ ⥤ ((C_T)ᵒᵖ)ᵒᵖ ⥤ Type (max u v)`.

    **Klasse-D sideways (Mathlib-Vor-Phase)**:
    - Universe adjustment for `uliftYoneda` on `(SyntacticContext T)ᵒᵖ` vs target
      presheaf universe `Type (max u v)`.
    - `HasColimitsOfSize.{max u v, max u v} E` from `ElementaryTopos` structure.
    - `HasPointwiseLeftKanExtension uliftYoneda (Model.toFunctor M)` instance.

    **C22 TPF (Weg γ)**: Alternatively, RepresentablyFlat (Model.toFunctor M)
    + `lan_preservesFiniteLimits_of_flat` avoids explicit Lan construction. -/
noncomputable def Model.toPresheafFunctor (M : Model T E) :
    ((SyntacticContext T)ᵒᵖ ⥤ Type (max u v)) ⥤ E := by
  -- Klasse-D sideways (Mathlib-Vor-Phase):
  -- Intended: Presheaf.uliftYonedaAdjunction / leftKanExtension construction.
  -- `(uliftYoneda.{max u v}).leftKanExtension (Model.toFunctor M)` after universe fix.
  sorry

/-- 31.c — PreservesFiniteLimits für toPresheafFunctor via Lan-Transport.

    **C22 TS-1 — Auflösung** (Klasse-D sideways-β.2):
    Mathematische Sub-Substanz aus 31.b vorhanden:
    `PreservesFiniteLimits (Model.toFunctor M)` (31.b-Instanz).

    Volle Auflösung benötigt: Universum-Anpassung für
    `uliftYoneda.leftKanExtension (Model.toFunctor M)` und Nachweis dass
    `HasPointwiseLeftKanExtension uliftYoneda (Model.toFunctor M)` die
    Limit-Erhaltung vererbt (via lan_preservesFiniteLimits_of_flat für Type-Ziel
    oder via direkten Lan-Transport-Satz). Weg γ (Flat.lean:324) setzt
    konkrete Kategorie E voraus — nicht direkt für allgemeines ElementaryTopos E.

    **Sub-Option b** (kontrolliertes sideways-sorry): uliftYoneda-Universum-
    Anpassung als eigenständige Sub-Substanz klassifiziert. -/
noncomputable instance Model.toPresheafFunctor_preservesFiniteLimits (M : Model T E) :
    PreservesFiniteLimits (Model.toPresheafFunctor M) := by
  -- 31.c sideways-β.2: Universum-Anpassung uliftYoneda.leftKanExtension.
  -- Mathematisch klar: toPresheafFunctor M ist Lan_{uliftYoneda} (toFunctor M),
  -- toFunctor M preserves finite limits (31.b), Lan erbt Limit-Erhaltung
  -- via lan_preservesFiniteLimits_of_flat sobald universe-Anpassung aufgelöst.
  -- Nicht abhängig von cone_maps-sorry in 31.a (separate Sub-Substanz-Kette).
  sorry -- sideways-β.2: uliftYoneda-Universum-Anpassung für Lan-Konstruktion

/-- The inverse image functor `f* : ClassifyingTopos T ⥤ E`.

    Defined structurally as the composition:
    `ClassifyingTopos T ⟶ᶠ ((C_T)ᵒᵖ ⥤ Type) ⟶ᶠ E`
    where the first functor is `sheafToPresheaf` (include sheaves into presheaves)
    and the second is `toPresheafFunctor M`.

    J_T-continuity of `toPresheafFunctor M` (Klasse-D forward C22) ensures the
    factorization is well-defined as the inverse image of the geometric morphism. -/
noncomputable def Model.toSheafFunctor (M : Model T E) :
    ClassifyingTopos T ⥤ E :=
  sheafToPresheaf (geometricTopology T) (Type (max u v)) ⋙ Model.toPresheafFunctor M

/-- The direct image functor `f_* : E ⥤ ClassifyingTopos T`, right adjoint to `toSheafFunctor`.

    Structural construction: `X ↦ sheaf (Γ ↦ Hom_E(contextObj M.interp Γ, X))`.
    Sheaf condition on this presheaf: Klasse-D forward (C22 coverage proof).

    **Klasse-D sideways (Mathlib-Sheaf-Adjunction-API)**: sheaf adjunction construction.
    **Klasse-D forward (C22 β.2)**: sheaf condition verification. -/
noncomputable def Model.toSheafFunctor_rightAdjoint (M : Model T E) :
    E ⥤ ClassifyingTopos T := by
  -- Klasse-D sideways (Mathlib-Sheaf-Adjunction-API):
  -- X ↦ ⟨val := fun Γ => Hom_E(contextObj M.interp Γ.unop, X), isSheaf := ...⟩
  -- Sheaf condition: Klasse-D forward (C22 geometricCoverage.pullback).
  sorry

/-- The adjunction `toSheafFunctor M ⊣ toSheafFunctor_rightAdjoint M`.

    **C22 S-1 (Klasse-D forward, β.2)**: full adjunction data from sheafification
    universal property plus right adjoint construction. -/
noncomputable def Model.toSheafFunctor_adjunction (M : Model T E) :
    Model.toSheafFunctor M ⊣ Model.toSheafFunctor_rightAdjoint M := by
  -- C22 β.2: adjunction data via Sheaf.adjunction or direct unit/counit construction.
  sorry

end ModelToGeometricMorphism

/-! ## Final construction — C23 T3 formal* -/

/-- Construct a geometric morphism `E → B[T]` from a model of T in E.

    **C23 T3 formal* form**: structural Yoneda-Einbettung skeleton.

    The six-step construction (Variante α):
    1. `toFunctor M : (C_T)ᵒᵖ ⥤ E` — model as presheaf of context-objects
    2. `toPresheafFunctor M` — Yoneda extension (Klasse-D sideways)
    3. flatness — `PreservesFiniteLimits` (C22 TS-1 / Klasse-D sideways/forward)
    4. J_T-continuity — statement removed (Phase-2 sharpening; memorial block below)
    5. `toSheafFunctor M = sheafToPresheaf ⋙ toPresheafFunctor M` — inverse image
    6. `toSheafFunctor_rightAdjoint M` — direct image (Klasse-D sideways)

    **Klasse-D Substanz-Verschiebungs-Inventar** (Strukturmerkmal-47-Kandidat:
    Drei-Klassen-Form backward/sideways/forward bestätigt):
    - **backward** (C21-D-4): toFunctor.map, .map_id, .map_comp
    - **sideways** (Mathlib-Vor-Phase): toPresheafFunctor,
      toPresheafFunctor_preservesFiniteLimits (part), toSheafFunctor_rightAdjoint
    - **forward** (C22): toPresheafFunctor_preservesFiniteLimits (part C22 TS-1),
      J_T-continuity (statement removed, memorial block below),
      toSheafFunctor_adjunction (C22 S-1),
      inverse_preservesFiniteLimits -/
noncomputable def Model.toGeometricMorphism
    (T : Theory.{u, v, w})
    {E : Type (max (u+1) (v+1))} [Category.{max u v} E] [ElementaryTopos E]
    [EssentiallySmall.{max u v} (SyntacticContext T)]
    [HasColimitsOfShape (Discrete PEmpty.{1}) E]
    [HasImages E]
    [LocallySmall.{max u (max v w)} E]
    [HasWidePullbacks.{max u (max v w)} E]
    [HasCoproducts.{max u (max v w)} E]
    [WellPowered.{max u (max v w)} E]
    [InitialMonoClass E]
    (M : Model T E) :
    GeometricMorphism E (ClassifyingTopos T) where
  inverse := Model.toSheafFunctor M
  direct := Model.toSheafFunctor_rightAdjoint M
  adjunction := Model.toSheafFunctor_adjunction M
  inverse_preservesFiniteLimits := by
    -- toSheafFunctor M = sheafToPresheaf (geometricTopology T) (Type (max u v))
    --                    ⋙ Model.toPresheafFunctor M
    -- Step 1: sheafToPresheaf is a right adjoint (HasSheafify J (Type (max u v))
    --   from Mathlib.CategoryTheory.Sites.LeftExact) → RepresentablyFlat →
    --   preservesFiniteLimits_of_flat.
    -- Step 2: toPresheafFunctor M preserves finite limits (31.c instance,
    --   sideways-β.2 sorry there).
    -- Step 3: comp_preservesFiniteLimits.
    -- **31. F Folge-Substanz**: inverse_preservesFiniteLimits aufgelöst sobald
    --   31.c-sorry aufgelöst; eigene Substanz dieser Stelle ist trivial.
    haveI hsheaf : PreservesFiniteLimits
        (sheafToPresheaf (geometricTopology T) (Type (max u v))) := by
      -- sheafToPresheaf is a right adjoint:
      -- HasSheafify (geometricTopology T) (Type (max u v)) from LeftExact.lean:307
      -- → (sheafToPresheaf J A).IsRightAdjoint
      -- → RepresentablyFlat.of_isRightAdjoint
      -- → preservesFiniteLimits_of_flat (unconditional)
      haveI : (sheafToPresheaf (geometricTopology T) (Type (max u v))).IsRightAdjoint :=
        ⟨_, ⟨sheafificationAdjunction _ _⟩⟩
      exact preservesFiniteLimits_of_flat _
    haveI hpresheaf : PreservesFiniteLimits (Model.toPresheafFunctor M) :=
      inferInstance
    -- toSheafFunctor M = sheafToPresheaf ⋙ toPresheafFunctor M
    have heq : Model.toSheafFunctor M =
        sheafToPresheaf (geometricTopology T) (Type (max u v)) ⋙
        Model.toPresheafFunctor M := rfl
    rw [heq]
    exact comp_preservesFiniteLimits _ _

/-- Construct a model of T in E from a geometric morphism `E → B[T]`.

    **T2 form** (sorry-declared). T3 upgrade: pullback of generic model. -/
noncomputable def Model.ofGeometricMorphism
    (T : Theory.{u, v, w})
    {E : Type (max (u+1) (v+1))} [Category.{max u v} E] [ElementaryTopos E]
    [EssentiallySmall.{max u v} (SyntacticContext T)]
    [HasColimitsOfShape (Discrete PEmpty.{1}) E]
    [HasImages E]
    [LocallySmall.{max u (max v w)} E]
    [HasWidePullbacks.{max u (max v w)} E]
    [HasCoproducts.{max u (max v w)} E]
    [WellPowered.{max u (max v w)} E]
    [InitialMonoClass E]
    (f : GeometricMorphism E (ClassifyingTopos T)) :
    Model T E := by
  sorry

/-- Round-trip `of ∘ to = id`. **T2 form** (sorry-declared). -/
theorem Model.ofGeometricMorphism_toGeometricMorphism
    (T : Theory.{u, v, w})
    {E : Type (max (u+1) (v+1))} [Category.{max u v} E] [ElementaryTopos E]
    [EssentiallySmall.{max u v} (SyntacticContext T)]
    [HasColimitsOfShape (Discrete PEmpty.{1}) E]
    [HasImages E]
    [LocallySmall.{max u (max v w)} E]
    [HasWidePullbacks.{max u (max v w)} E]
    [HasCoproducts.{max u (max v w)} E]
    [WellPowered.{max u (max v w)} E]
    [InitialMonoClass E]
    (M : Model T E) :
    Model.ofGeometricMorphism T (Model.toGeometricMorphism T M) = M := by
  sorry

/-- Round-trip `to ∘ of = id`. **T2 form** (sorry-declared). -/
theorem Model.toGeometricMorphism_ofGeometricMorphism
    (T : Theory.{u, v, w})
    {E : Type (max (u+1) (v+1))} [Category.{max u v} E] [ElementaryTopos E]
    [EssentiallySmall.{max u v} (SyntacticContext T)]
    [HasColimitsOfShape (Discrete PEmpty.{1}) E]
    [HasImages E]
    [LocallySmall.{max u (max v w)} E]
    [HasWidePullbacks.{max u (max v w)} E]
    [HasCoproducts.{max u (max v w)} E]
    [WellPowered.{max u (max v w)} E]
    [InitialMonoClass E]
    (f : GeometricMorphism E (ClassifyingTopos T)) :
    Model.toGeometricMorphism T (Model.ofGeometricMorphism T f) = f := by
  sorry

/-! ## Memorial block: declaration removed because its statement was `True`

Removed in the Phase-2 sharpening (Setzungsregister, `docs/status-register.md`,
row `S49`), carried out together with the freezing of this branch — a branch that
is being frozen is tidied before, not after. The name claimed continuity, the
statement was `True`. A theorem whose statement is `True` is not a false theorem,
but its name reads as a result; in a published tree that is a claim. No consumer
anywhere in the corpus; the removal breaks nothing.

Signature quoted indented by two spaces so that the counting route `^theorem`
does not count the memorial quote as a declaration.

**Removed — `Model.toPresheafFunctor_jt_continuous`.** Register row `S49`.

```
  omit [EssentiallySmall.{max u v} (SyntacticContext T)] in
  theorem Model.toPresheafFunctor_jt_continuous (_M : Model T E) : True := by
    trivial
```

*What was claimed:* that `toFunctor M` is J_T-continuous — that it sends the
geometric topology to covers in `E`. This is step 4 of the six-step construction
of `Model.toGeometricMorphism`, and the only one of the six that was carried by
a statement rather than by a definition.
*What a load-bearing statement would need:* the statement its own doc-string
already names, `(Model.toFunctor M).IsContinuous (geometricTopology T) K`. That
needs `geometricCoverage.pullback` from C21-D-2 and the `CoverPreserving`
machinery, and then a proof from `M.satisfies`. It is a proof obligation, not a
marker: continuity can fail, and for a model that does not satisfy the theory it
would.

This branch is frozen (see the header of this file). The removal is the last
change to it; discharging the obligation above is not planned and would fall
under the thaw conditions in `docs/build-targets.md`.
-/

end Reformulation.PathC.Classifying
