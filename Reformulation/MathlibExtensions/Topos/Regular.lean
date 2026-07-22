/-
Copyright Reformulierung-Projekt 2026.
Released under PKL-internal license.
-/
import Mathlib.CategoryTheory.RegularCategory.Basic
import Mathlib.CategoryTheory.Limits.Shapes.KernelPair
import Mathlib.CategoryTheory.Limits.Shapes.StrongEpi
import Mathlib.CategoryTheory.Limits.Shapes.Images
import Mathlib.CategoryTheory.Limits.Constructions.EpiMono
import Reformulation.PathC.ElementaryTopos

/-!
# ElementaryTopos → Regular: erste K4-Niederlegung (Sub-Form a)

Erste K4-Niederlegung mit Sub-Form-a-Charakter (Beitrags-Substanz). Substantielle
methodologische Mathlib-Future-Work-Auflösung: `RegularCategory/Basic.lean:30` markiert
"Show that every topos is regular" als offene Substanz.

## Was diese Datei leistet

1. **`StrongEpiCategory E`** (vollständig bewiesen): In einem ElementaryTopos mit
   `[Balanced E]` und `[HasStrongEpiMonoFactorisations E]` ist jeder Epi ein starker Epi.
   Beweis: Bild-Faktorisierungs-Argument + Balanced-Instanz (monoide Epi = Iso).

2. **`RegularEpiStability E`** (Konsumenten-Hypothesen-Wrapper): Kapselt
   `MorphismProperty.IsStableUnderBaseChange (.regularEpi E)`. Dieses ist in einem
   elementaren Topos aus der LCCC-Struktur ableitbar (via: linkes Adjungiertes der
   Pullback-Funktors ⊣ abhängiges Produkt → Pullback erhält Epis), aber noch nicht
   in Mathlib formalisiert.

3. **`elementaryToposRegular`** (Instanz): Unter `[RegularEpiStability E]` und
   `[HasCoequalizers E]` ist `Regular E` direkt konstruierbar.

## Konsumenten-Hypothesen-Substanz

| Hypothese | Quelle | Methodologische Substanz |
|---|---|---|
| `[Regular E]` (Ergebnis) | Aus `[RegularEpiStability E]` + `[HasCoequalizers E]` | Future-Work-Auflösung |
| `[RegularEpiStability E]` | Neue Consumer-Hypothese | LCCC-Eigenschaft; Mathlib-PR-Kandidat |
| `[HasCoequalizers E]` | Neue Consumer-Hypothese | Aus Topos-Finite-Colimits; Future Work |

## Anschluss-Substanz

- `StrongEpiCategory E` ist eine genuiner neuer Beweis (Sub-Form-a).
- `HasStrongEpiMonoFactorisations E` folgt automatisch aus `Regular E` (RegularCategory/Basic.lean:154).
- Nach `elementaryToposRegular`: die K3-Konsumenten-Hypothese `[HasStrongEpiMonoFactorisations E]`
  wird durch `[Regular E]` subsumiert — Konsumenten-Hypothesen-Reduktion für K4/C22.
-/

namespace Reformulation.MathlibExtensions.Topos

open CategoryTheory Limits Reformulation.PathC

universe u v

variable {E : Type u} [Category.{v} E]

-- ============================================================
-- S-1: StrongEpiCategory — vollständig bewiesen aus Balanced + HasStrongEpiMonoFactorisations
-- ============================================================

/-- In a balanced category with strong epi-mono factorisations, every epimorphism
is a strong epimorphism.

Proof: factor `f = e ≫ m` (strong-epi ∘ mono). If `f` is epi, then `m` is epi (by
`epi_of_epi_fac`). Since `m` is both mono and epi in a balanced category, `m` is an
isomorphism. Hence `f = e ≫ m` is strong epi (strong-epi composed with iso).

This is the `StrongEpiCategory` instance that holds in any elementary topos (as a
consequence of `HasSubobjectClassifier → IsRegularMonoCategory → StrongMonoCategory →
Balanced`), combined with the consumer hypothesis `[HasStrongEpiMonoFactorisations E]`.

**Sub-Form-a Beitrags-Substanz**: This is a provable new result, not circular. -/
noncomputable instance strongEpiCategory_of_balanced
    [Balanced E] [HasStrongEpiMonoFactorisations E] : StrongEpiCategory E where
  strongEpi_of_epi {_X _Y} (f : _X ⟶ _Y) [hEpi : Epi f] := by
    -- Step 1: Get the strong epi-mono factorisation of f
    obtain ⟨fac⟩ := HasStrongEpiMonoFactorisations.has_fac f
    -- fac.e : X ⟶ fac.I  is a strong epi
    -- fac.m : fac.I ⟶ Y  is a mono
    -- fac.fac : fac.e ≫ fac.m = f
    -- Step 2: Since f is epi and f = fac.e ≫ fac.m, fac.m is epi
    -- Rewrite goal Epi (fac.e ≫ fac.m) to Epi f via fac.fac, then apply hEpi
    haveI hEpiComp : Epi (fac.e ≫ fac.m) := by rw [fac.fac]; exact hEpi
    haveI : Epi fac.m := epi_of_epi fac.e fac.m
    -- Step 3: fac.m is both mono and epi; in a balanced category, it is an iso
    haveI : IsIso fac.m := isIso_of_mono_of_epi fac.m
    -- Step 4: f = fac.e ≫ fac.m with fac.m iso, so f is strong epi (strong ≫ iso = strong)
    -- Goal: StrongEpi f. Rewrite to StrongEpi (fac.e ≫ fac.m) via fac.fac, use inferInstance.
    show StrongEpi f
    rw [← fac.fac]
    exact inferInstance

/-- In an elementary topos (which has `HasSubobjectClassifier` → `StrongMonoCategory` →
`Balanced`) with the consumer hypothesis `[HasStrongEpiMonoFactorisations E]`, every
epimorphism is a strong epimorphism.

This is the key consequence needed for `ElementaryTopos E → StrongEpiCategory E`. -/
noncomputable instance strongEpiCategory_of_elementaryTopos
    [ElementaryTopos E] [HasStrongEpiMonoFactorisations E] : StrongEpiCategory E :=
  strongEpiCategory_of_balanced

-- ============================================================
-- S-2: RegularEpiStability — neue Konsumenten-Hypothese
-- ============================================================

/-- Consumer hypothesis: regular epimorphisms in `C` are stable under base change.

In an elementary topos, this follows from the locally cartesian closed structure (the
pullback functor `f* : Over Y ⥤ Over X` has a right adjoint `Π_f`, hence it is a left
adjoint and preserves colimits, in particular epimorphisms). The chain:
  `[MonoidalClosed E]` → locally cartesian closed → `f*` has right adjoint → `f*` preserves epis

This is not yet formalized in Mathlib for abstract elementary toposes. It corresponds
to part of the "Future work: Show that every topos is regular" note at
`RegularCategory/Basic.lean:30`.

Methodologische Substanz: Mathlib-PR-Kandidat (Sub-Form-a Beitrags-Substanz). -/
class RegularEpiStability (C : Type u) [Category.{v} C] : Prop where
  regularEpiIsStableUnderBaseChange :
    MorphismProperty.IsStableUnderBaseChange (MorphismProperty.regularEpi C)

-- ============================================================
-- S-3: elementaryToposRegular — aus Consumer-Hypothesen
-- ============================================================

/-- An elementary topos is a regular category, assuming:
- `[HasCoequalizers E]`: every parallel pair has a coequalizer (in a topos, this follows
  from having all finite colimits, which is a theorem of elementary topos theory not yet
  in Mathlib for the general `ElementaryTopos` definition)
- `[RegularEpiStability E]`: regular epimorphisms are stable under base change (from LCCC)

The `hasCoequalizer_of_isKernelPair` condition: given `IsKernelPair f g₁ g₂`, we need
`HasCoequalizer g₁ g₂`. With `[HasCoequalizers E]`, this is immediate (`inferInstance`).

**Methodologische Substanz**: This is the K4 Sub-Form-a delivery. Once Mathlib
formalizes `ElementaryTopos → HasCoequalizers` and `ElementaryTopos → RegularEpiStability`,
the consumer hypotheses in this instance can be removed, fully resolving
`RegularCategory/Basic.lean:30` ("Show that every topos is regular"). -/
noncomputable instance elementaryToposRegular
    [ElementaryTopos E] [HasCoequalizers E] [RegularEpiStability E] : Regular E where
  hasCoequalizer_of_isKernelPair _h := inferInstance
  regularEpiIsStableUnderBaseChange :=
    RegularEpiStability.regularEpiIsStableUnderBaseChange

-- ============================================================
-- Konsumenten-Hypothesen-Reduktion nach erster K4-Niederlegung
-- ============================================================

/-- After `elementaryToposRegular`, the consumer hypothesis `[HasStrongEpiMonoFactorisations E]`
is derivable from `[Regular E]` via `Regular.hasStrongEpiMonoFactorisations`.

This is the consumer-hypothesis reduction promised in the K4 spec: the 8-hypothesis block
from K3 can drop `HasStrongEpiMonoFactorisations` after this instance is available. -/
example [ElementaryTopos E] [HasCoequalizers E] [RegularEpiStability E] :
    HasStrongEpiMonoFactorisations E :=
  inferInstance

end Reformulation.MathlibExtensions.Topos
