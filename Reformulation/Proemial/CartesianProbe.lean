import Mathlib.CategoryTheory.FiberedCategory.Cartesian
import Mathlib.CategoryTheory.FiberedCategory.Fibered
import Mathlib.CategoryTheory.Grothendieck
import Reformulation.Proemial.AlphaGammaSubstantial

/-!
# CartesianProbe — Entscheidungs-Sonde für Position B (cartesian lift)

STANDALONE, NICHT im Aggregat (wie AxiomProbe). Zweck: die §I-offene Frage der
Position-B-Sondierung entscheiden — trägt ein cartesian lift Substanz ÜBER α+γ
hinaus, oder kollabiert er auf γ (das ein Iso ist)?

- P1: Andock-Test — Mathlibs cartesian-API resolviert mit universeller Eigenschaft
      (hebt §III-Befund von *niedergelegt* auf *bewiesen*).
- P2: Kollaps-Hebel allgemein — jeder Iso-Lift ist (strongly) cartesian,
      UNKONDITIONAL (keine Diskretheit der Basis nötig).
- P3: Kollaps auf den proemialen Daten — γ ist ein Iso, also ist jeder
      γ-abgeleitete Lift zwangsläufig cartesian; kein Datum über "γ ist Iso" hinaus.
-/

namespace Reformulation.Proemial.CartesianProbe

open CategoryTheory
open Reformulation.Proemial.Substantial

-- ============================================================
-- P1 — Andock-Test: API resolviert mit universeller Eigenschaft
-- ============================================================

-- Mathlibs cartesian-Morphismus-Klasse mit ∃!-Faktorisierung existiert:
#check @CategoryTheory.Functor.IsCartesian
#check @CategoryTheory.Functor.IsCartesian.universal_property
#check @CategoryTheory.Functor.IsStronglyCartesian
#check @CategoryTheory.Functor.IsFibered
#check @CategoryTheory.Grothendieck

-- Der Andock-Vorbehalt am Term: IsCartesian ist relativ zu einer Basis-Projektion
-- `p : 𝒳 ⥤ 𝒮`. Ohne ein solches p gibt es die universelle Eigenschaft nicht.
example {𝒮 𝒳 : Type} [Category 𝒮] [Category 𝒳] (p : 𝒳 ⥤ 𝒮)
    {R S : 𝒮} {a b : 𝒳} (f : R ⟶ S) (φ : a ⟶ b) [p.IsHomLift f φ] [p.IsCartesian f φ]
    {a' : 𝒳} (φ' : a' ⟶ b) [p.IsHomLift f φ'] :
    ∃! χ : a' ⟶ a, p.IsHomLift (𝟙 R) χ ∧ χ ≫ φ = φ' :=
  Functor.IsCartesian.universal_property (p := p) (f := f) (φ := φ) φ'

-- ============================================================
-- P2 — Kollaps-Hebel: Iso ⟹ cartesian, UNKONDITIONAL
-- ============================================================

-- Jeder Iso, der eine Basis-Abbildung liftet, ist (strongly) cartesian — ohne
-- jede Voraussetzung an die Basis (insbesondere KEINE Diskretheit nötig).
-- `inferInstance` chaint `of_isIso` ⟹ `isCartesian_of_isStronglyCartesian`.
example {𝒮 𝒳 : Type} [Category 𝒮] [Category 𝒳] (p : 𝒳 ⥤ 𝒮)
    {R S : 𝒮} {a b : 𝒳} (f : R ⟶ S) (φ : a ⟶ b) [IsIso φ] [p.IsHomLift f φ] :
    p.IsCartesian f φ := inferInstance

-- Variante über ein Iso-Objekt `a ≅ b` (Mathlib `of_iso`, Cartesian.lean:342).
example {𝒮 𝒳 : Type} [Category 𝒮] [Category 𝒳] (p : 𝒳 ⥤ 𝒮)
    {R S : 𝒮} {a b : 𝒳} (f : R ⟶ S) (e : a ≅ b) [p.IsHomLift f e.hom] :
    p.IsStronglyCartesian f e.hom := inferInstance

-- ============================================================
-- P3 — Kollaps auf den proemialen α+γ-Daten
-- ============================================================

variable {S K : Type} [Category S] [Category K]
  (PAS : ProemialAdjunctionSubstantial S K)
  (BC : SubstantialBeckChevalleyData S K PAS)
  (PGM : ProemialGammaMorphismSubstantial PAS BC)

-- γ ist ein natürlicher Iso; seine Komponenten sind Isos:
example (s : S) : IsIso (PGM.γ.hom.app s) := inferInstance

-- Die Adjunktions-Einheit fällt komponentenweise mit γ.inv zusammen (Feld
-- `naturality_S`) — also ist auch sie ein Iso-Component. Kein eigenes Lift-Datum.
example (s : S) : PAS.adj.unit.app s = PGM.γ.inv.app s := PGM.naturality_S s

-- PUNCHLINE. Für JEDE Basis-Projektion `p : S ⥤ 𝒮` und JEDE Basis-Abbildung `f`,
-- die einen γ-Komponenten-Iso liftet, ist der Lift ZWANGSLÄUFIG (strongly) cartesian.
-- Die universelle Eigenschaft trägt auf den α+γ-Daten KEIN Datum über
-- "γ ist ein Iso" hinaus — sie ist erzwungen, nicht gewählt.
example {𝒮 : Type} [Category 𝒮] (p : S ⥤ 𝒮) {R T : 𝒮} (f : R ⟶ T) (s : S)
    [p.IsHomLift f (PGM.γ.hom.app s)] :
    p.IsStronglyCartesian f (PGM.γ.hom.app s) := inferInstance

end Reformulation.Proemial.CartesianProbe
