import Reformulation.Proemial.AlphaGammaRelPullback
import Mathlib.CategoryTheory.Limits.Types.Limits
import Mathlib.CategoryTheory.Monoidal.Closed.Types

/-!
# Reformulation.Proemial.AlphaGammaWitnesses — F-3.6.a.1 + F-3.6.b Zeugen-Einheit

Sechste Niederlegungs-Schicht (über F-1, F-3, F-3.4/5, F-3.6, F-3.6.a). Additiv zu
`AlphaGammaRelPullback.lean`; keine Modifikation der bestehenden Dateien.

Vier Substanz-Blöcke:

1. **Äquivalenz (F-3.6.b, ehrliche Form):** `tritoStellungsVielfalt_implies_substantial`
   via Koeinheits-Stellung; daraus `tritoStellungsVielfalt_iff_substantial`.
   ERSETZT die mathematisch falsche Nicht-Implikations-Aussage der F-3.6-Niederlegung
   (Spec-Stopp-Befund, Sub-Substanz I in erster operativer Anwendung).
2. **Bewohntheits-Zeuge (F-3.6.a.1):** konkrete Stellung mit
   `IsSplitEpi σ.rel ∧ ¬ IsIso σ.rel` über der Identitäts-Adjunktion in Type;
   Anwendungs-Korollar durch das F-3.6.a-Diagonal-Theorem (Vakuitäts-Flanke geschlossen).
3. **𝟙-Kontrast-Zeuge:** `IsIso (pullback.diagonal (𝟙 k))` — versiegelt das
   semantische Argument der binären Bewährung in Lean statt in Prosa.
4. **Punktweiser Unabhängigkeits-Zeuge:** Stellung mit iso rel bei nicht-iso
   Koeinheit (Produkt-Hom-Adjunktion `· × Bool ⊣ Bool → ·` in Type).
5. **Bewohnungs-Korollare (Nachtrag, Bewertungs-Stelle 1):** das Trito-Prädikat
   und seine substantielle Form GELTEN für das konkrete prodHomWitnessPAS —
   die Äquivalenz aus Block 1 ist damit an einem bewohnten Fall exerziert
   (Schließung der Rest-Vakuitäts-Flanke aus F3_6a1_b_Bewertung.md II.2).

Spec: F3_6a1_b_Sub_Spec.md. Prompt: F3_6a1_b_Sub_Prompt.md. Frühjahr 2026.

## Klasse-B-Befunde

(in der Implementation gefüllt; siehe F3_6a1_b_Implementation_Final.md)
-/

/-! ## Zeugen-Markierung

Dieses Modul trägt ZEUGEN (Bewohntheits-, Kontrast- und Unabhängigkeits-Belege),
keine Architektur. Die Instanziierungen mit S = K = Type sind zulässig, weil
Zeugen nur Existenz belegen — sie sind kein Rückfall in die B-2-Spezialisierung.
Die α₂-Architektur (S ≠ K, zwei primitive Funktoren) bleibt die Form der
Niederlegungs-Schichten F-1 bis F-3.6.a; dieses Modul bewohnt sie.
-/

/-! ## Quer-Markierung zur F-3.6-Niederlegung (Deprecation-Vorgriff)

Beide Sorry-Stellen in AlphaGammaBeckChevalley.lean betreffen mathematisch
falsche Aussagen (Befunde: F-3.6.a-Korrektur-Notiz Sektion V;
diese Spec Sektion II):

1. `rel_not_through_counit`: die Faktorisierung u existiert IMMER
   (u := L.map (adj.homEquiv σ.s σ.k σ.rel); Koeinheits-Zerlegung).
2. `TritoStellungsVielfaltExists_does_not_imply_substantial`: das
   bezeugende PAS existiert NIE (Koeinheits-Stellung als universeller
   Gegen-Zeuge; siehe tritoStellungsVielfalt_implies_substantial).

Beide Falschheits-Gründe haben dieselbe Wurzel: die Koeinheit als
universelle Zerlegung bzw. universeller Zeuge. Die Deprecation der
F-3.6-Stellen erfolgt in F-3.6.a.3 (gebündelt mit dem positiven
Faktorisierungs-Lemma rel_factors_through_counit); dieses Modul trägt
die ersetzenden positiven Theoreme.
-/

namespace Reformulation.Proemial.Substantial.Witnesses

open CategoryTheory CategoryTheory.Limits
open Reformulation.Proemial.Substantial
open Reformulation.Proemial.Substantial.Refined

-- ============================================================
-- Theorem-Block 1 — die Äquivalenz (F-3.6.b, ehrliche Form)
-- ============================================================

/-- F-3.6.b (positive Form): die F-3-Form impliziert die substantielle Form.

    Beweis via Koeinheits-Stellung: gegeben σ₀ mit counit.app σ₀.k non-iso
    ist σ* := ⟨R(σ₀.k), σ₀.k, counit.app σ₀.k⟩ eine Stellung, deren rel
    DIE KOEINHEIT SELBST ist — beide Konjunktions-Glieder fallen zusammen.

    Methodologische Markierung (Spec Sektion II): dieses Theorem ERSETZT
    die in F-3.6 mit Sorry niedergelegte Nicht-Implikations-Aussage
    `TritoStellungsVielfaltExists_does_not_imply_substantial`, die
    mathematisch falsch ist (Sub-Substanz-I-Vor-Prüfungs-Befund;
    Quantoren-Fehler der F-3.4/5-Bewertung Sektion II.5).
-/
theorem tritoStellungsVielfalt_implies_substantial
    {S K : Type*} [Category S] [Category K]
    {PAS : ProemialAdjunctionSubstantial S K}
    (h : TritoStellungsVielfaltExists PAS) :
    TritoStellungsVielfaltExists_substantial PAS := by
  obtain ⟨σ₀, h₀⟩ := h
  exact ⟨⟨PAS.R.obj σ₀.k, σ₀.k, PAS.adj.counit.app σ₀.k⟩, h₀, h₀⟩

/-- Die F-3-Form und die F-3.5-substantielle Form sind existenziell ÄQUIVALENT.

    Strukturelle Klärung (Spec Sektion III.1): die rel-Substanz lebt in der
    Hypothesen-Schicht (Diagonal-Theorem F-3.6.a), nicht in der
    Existenz-Quantifizierung. Die F-3.5-Definitions-Verstärkung war auf
    Existenz-Ebene leer; ihre Substanz ist die punktweise Unabhängigkeit
    (siehe Theorem-Block 3), nicht die existenzielle Trennung.

    Ehrliche Substanz-Markierung (Sub-Substanzen F + G): der Beweis ist
    konzeptuell scharf, technisch flach (Koeinheits-Stellung als
    Drei-Zeilen-Konstruktion). Die Substanz liegt im BEFUND (Falschheit
    der Gegen-Aussage), nicht in der Beweis-Tiefe.
-/
theorem tritoStellungsVielfalt_iff_substantial
    {S K : Type*} [Category S] [Category K]
    (PAS : ProemialAdjunctionSubstantial S K) :
    TritoStellungsVielfaltExists PAS ↔ TritoStellungsVielfaltExists_substantial PAS :=
  ⟨tritoStellungsVielfalt_implies_substantial,
   TritoStellungsVielfaltExists_substantial_implies_F3⟩

-- ============================================================
-- Theorem-Block 2 — Bewohntheits- und Kontrast-Zeugen (F-3.6.a.1)
-- ============================================================

/-- Zeugen-Instanziierung: die Identitäts-Adjunktion über Type.

    ZEUGEN-MARKIERUNG (siehe Modul-Kopf): S = K = Type ist hier zulässig,
    weil ein Bewohntheits-Zeuge nur EXISTENZ belegt — er ist
    Instanziierung, nicht Architektur. Kein B-2-Rückfall.
-/
def identityWitnessPAS : ProemialAdjunctionSubstantial Type Type where
  L := 𝟭 Type
  R := 𝟭 Type
  adj := Adjunction.id

/-- F-3.6.a.1: die Hypothesen-Kombination des Diagonal-Theorems ist bewohnt.

    Konkrete Stellung: σ.s = Bool, σ.k = PUnit, rel = konstante Abbildung.
    Split-epi: Schnitt fun _ => true (Komposition nach PUnit ist 𝟙, da
    PUnit definitionale Eta trägt). Nicht iso: nicht injektiv (true und
    false ↦ unit); via isIso_iff_bijective in Type.

    Schließt die Vakuitäts-Flanke der F-3.6.a-Bewertung (II.3 Flanke 1):
    das Diagonal-Theorem hat einen echten Anwendungsfall.
-/
theorem exists_stellung_splitEpi_not_iso :
    ∃ (σ : Stellung identityWitnessPAS),
      IsSplitEpi σ.rel ∧ ¬ IsIso σ.rel := by
  refine ⟨⟨Bool, PUnit, ↾fun _ => PUnit.unit⟩, ?_, ?_⟩
  · exact ⟨⟨⟨↾fun _ => true, rfl⟩⟩⟩
  · intro h
    rw [isIso_iff_bijective] at h
    exact Bool.noConfusion (h.1 (a₁ := true) (a₂ := false) rfl)

/-- Kontrast-Zeuge: die Diagonale der Identität IST iso (Mono 𝟙).
    Versiegelt das semantische Argument der binären Bewährung
    (F-3.6.a-Bewertung I.1/II.5) in Lean statt in Prosa. -/
theorem diagonal_id_isIso (k : Type) : IsIso (pullback.diagonal (𝟙 k)) := by
  rw [pullback.isIso_diagonal_iff]
  infer_instance

/-- BC-Daten für die Identitäts-Adjunktion über Type: Pullbacks via
    Mathlib-Limits-Instanzen; bcIso als Links-Unitor 𝟭 ⋙ 𝟭 ≅ 𝟭;
    compat via Adjunction.id-Einheit = 𝟙 (komponentenweise rfl). -/
def identityWitnessBC :
    BeckChevalley.SubstantialBeckChevalleyData Type Type identityWitnessPAS where
  pullback_S := inferInstance
  pullback_K := inferInstance
  bcIso := Functor.leftUnitor (𝟭 Type)
  compat := fun _ => rfl

/-- Der Bewohntheits-Zeuge, durch das F-3.6.a-Diagonal-Theorem gezogen:
    eine konkrete nicht-iso Diagonale. Vakuitäts-Flanke vollständig
    geschlossen — das bewährte Theorem trägt einen konkreten Fall. -/
theorem concrete_diagonal_not_iso :
    ∃ (σ : Stellung identityWitnessPAS),
      ¬ IsIso (pullback.diagonal σ.rel) := by
  obtain ⟨σ, h_split, h_not_iso⟩ := exists_stellung_splitEpi_not_iso
  exact ⟨σ, RelPullback.rel_pullback_diagonal_not_iso
    identityWitnessBC σ h_split h_not_iso⟩

-- ============================================================
-- Theorem-Block 3 — der punktweise Unabhängigkeits-Zeuge
-- ============================================================

/-- Zeugen-PAS des punktweisen Unabhängigkeits-Zeugen:
    die Produkt-Hom-Adjunktion Bool ⊗ · ⊣ Bool → · über Type.

    Klasse-B-3-Befund (positiv): die Adjunktion liegt in Mathlib als
    `Types.tensorProductAdjunction : tensorLeft X ⊣ coyoneda.obj (op X)`
    (Mathlib.CategoryTheory.Monoidal.Closed.Types); keine Hand-Konstruktion
    via mkOfHomEquiv nötig. Der Spec-Kandidat `Types.binaryProductAdjunction`
    existiert nicht; die tensorLeft-Form ist die lebende API
    (X ⊗ Y = X × Y ist rfl in Type, `types_tensorObj_def`).
-/
def prodHomWitnessPAS : ProemialAdjunctionSubstantial Type Type where
  L := MonoidalCategory.tensorLeft Bool
  R := coyoneda.obj (Opposite.op Bool)
  adj := Types.tensorProductAdjunction Bool

/-- Die Koeinheit des Produkt-Hom-Zeugen ist an Bool ⊗ PUnit NICHT iso.

    counit.app (Bool ⊗ PUnit) ist die Auswertung
    Bool ⊗ (Bool ⟶ Bool ⊗ PUnit) → Bool ⊗ PUnit — nicht injektiv
    (Kardinalität 8 ≫ 2): die Funktionen fun _ => (true, unit) und
    fun b => (b, unit) werten bei true beide zu (true, unit).

    Als eigenes Lemma extrahiert (Bewertungs-Stelle 1), damit der Befund
    für das KONKRETE prodHomWitnessPAS zitierbar ist — nicht nur hinter
    dem Existenz-Quantor des punktweisen Zeugen verborgen.
-/
theorem prodHomWitness_counit_not_iso :
    ¬ IsIso (prodHomWitnessPAS.adj.counit.app
      ((MonoidalCategory.tensorLeft Bool).obj PUnit)) := by
  intro h
  rw [isIso_iff_bijective] at h
  -- Injektivität der Auswertung widerlegen: zwei verschiedene Funktionen
  -- mit demselben Auswertungs-Wert an true.
  have key :
      prodHomWitnessPAS.adj.counit.app ((MonoidalCategory.tensorLeft Bool).obj PUnit)
        (true, ↾fun _ => (true, PUnit.unit)) =
      prodHomWitnessPAS.adj.counit.app ((MonoidalCategory.tensorLeft Bool).obj PUnit)
        (true, ↾fun b => (b, PUnit.unit)) := rfl
  have h12 := h.1 key
  have hfun := congrArg Prod.snd h12
  have happ := congrArg (fun g => (ConcreteCategory.hom g) false) hfun
  exact Bool.noConfusion (congrArg Prod.fst happ)

/-- Punktweise Unabhängigkeit: es gibt eine Adjunktion und eine Stellung
    mit ISO rel bei NICHT-ISO Koeinheit. Die zwei Bedingungen der
    substantiellen Form sind auf Stellungs-Ebene unabhängig — obwohl die
    Existenz-Aussagen äquivalent sind (Theorem-Block 1).

    Konstruktion: Produkt-Hom-Adjunktion in Type, L := Bool ⊗ · ⊣ R := Bool → ·.
    σ := ⟨PUnit, Bool ⊗ PUnit, 𝟙 (Bool ⊗ PUnit)⟩ — rel ist 𝟙, also iso;
    Koeinheits-Nicht-Iso via `prodHomWitness_counit_not_iso`.

    Das ist exakt die Bewertungs-Skizzen-Konfiguration (σ.rel := 𝟙 σ.k mit
    σ.k im Bild von L), korrekt formalisiert auf der Stellungs-Ebene.
-/
theorem exists_stellung_rel_iso_counit_not_iso :
    ∃ (PAS : ProemialAdjunctionSubstantial Type Type) (σ : Stellung PAS),
      IsIso σ.rel ∧ ¬ IsIso (PAS.adj.counit.app σ.k) := by
  refine ⟨prodHomWitnessPAS,
    ⟨PUnit, (MonoidalCategory.tensorLeft Bool).obj PUnit,
      𝟙 ((MonoidalCategory.tensorLeft Bool).obj PUnit)⟩, ?_,
    prodHomWitness_counit_not_iso⟩
  -- rel der Stellung ist wörtlich 𝟙; Literal-Projektion via show reduziert.
  show IsIso (𝟙 ((MonoidalCategory.tensorLeft Bool).obj PUnit))
  infer_instance

-- ============================================================
-- Bewohnungs-Korollare — die Äquivalenz an einem bewohnten Fall
-- (Bewertungs-Stelle 1: Rest-Vakuitäts-Flanke der Existenz-Schicht)
-- ============================================================

/-- Bewohnungs-Zeuge der Existenz-Schicht: für das KONKRETE prodHomWitnessPAS
    gilt die F-3-Form der Trito-Stellungs-Vielfalt.

    Erstes PAS im Framework, für das das Trito-Prädikat NIEDERGELEGT GILT
    (nicht nur als Hypothese geführt wird). Schließt die in der Bewertung
    (F3_6a1_b_Bewertung.md II.2) markierte Rest-Vakuitäts-Flanke:
    die Äquivalenz der Existenz-Formen ist damit nicht nur universell
    bewiesen, sondern an einem bewohnten Fall belegt.
-/
theorem prodHomWitness_tritoVielfalt :
    TritoStellungsVielfaltExists prodHomWitnessPAS :=
  ⟨⟨PUnit, (MonoidalCategory.tensorLeft Bool).obj PUnit,
    𝟙 ((MonoidalCategory.tensorLeft Bool).obj PUnit)⟩,
   prodHomWitness_counit_not_iso⟩

/-- Bewohnungs-Korollar: die SUBSTANTIELLE Form gilt für prodHomWitnessPAS —
    via der Äquivalenz (Theorem-Block 1) aus der F-3-Form gewonnen.

    Damit ist die Hinrichtung der Äquivalenz (Koeinheits-Stellung) erstmals
    an einem Fall durchlaufen, an dem ihre Prämisse tatsächlich gilt: der
    erzeugte substantielle Zeuge ist die Koeinheits-Stellung
    ⟨R(Bool ⊗ PUnit), Bool ⊗ PUnit, counit.app (Bool ⊗ PUnit)⟩,
    deren rel die Koeinheit selbst ist. Existenz-Schicht-Klärung
    vollständig: äquivalent (Block 1) UND bewohnt (dieses Korollar).
-/
theorem prodHomWitness_tritoVielfalt_substantial :
    TritoStellungsVielfaltExists_substantial prodHomWitnessPAS :=
  (tritoStellungsVielfalt_iff_substantial prodHomWitnessPAS).mp
    prodHomWitness_tritoVielfalt

/-! **Wachen (Wachenspitze Stufe 2).** Ist-Ausgabe des gruenen Builds (v4.30.0-rc2).
Gewacht ist die Aequivalenz, die **aus dem Doc-Index von `Proemial.lean` beim Namen gefuehrt**
wird. Das Profil traegt `Classical.choice` aus der Kategorien-Maschinerie; der Weg des
Axioms in den Term ist **nicht** gemessen (`CLAUDE.md` §8 Fallstrick 10). -/

/--
info: 'Reformulation.Proemial.Substantial.Witnesses.tritoStellungsVielfalt_iff_substantial' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms tritoStellungsVielfalt_iff_substantial


end Reformulation.Proemial.Substantial.Witnesses
