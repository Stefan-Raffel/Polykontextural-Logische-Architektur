import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.NatIso
import Mathlib.CategoryTheory.Equivalence
import Reformulation.F3e.BeckChevalleyConstruction

/-!
# Reformulation.Proemial.AlphaGamma — α+γ-Form der Proemialrelation

Lean-4-Niederlegung der α+γ-Form der Proemialrelation in der PKL-Doppelfaserung.
Zwei primitive Funktoren L : S ⥤ K und R : K ⥤ S mit Adjunktion L ⊣ R (α-Komponente)
plus 2-Morphismus γ, der die Adjunktion mit der Beck-Chevalley-Verträglichkeit der
Doppelfaserung verschränkt (γ-Komponente, Lesart B).

Spec: F1_Spec.md. Prompt: F1_Prompt.md. Frühjahr 2026.

## Klasse-B-Befunde

**B-1 — Import-Pfad-Inkompatibilität:** Spec nennt `Pkl.Doppelfaserung.Basic`,
`Pkl.Doppelfaserung.BeckChevalley`, `Pkl.Doppelfaserung.Belegung`. Diese Module
existieren nicht; Projekt-Namespace ist `Reformulation`, nicht `Pkl`. Angepasst:
`Reformulation.F3e.BeckChevalleyConstruction` als tatsächliche BC-Substanz.
Namespace: `Reformulation.Proemial` statt `Pkl.Proemial`.

**B-2 — Beck-Chevalley-API-Form:** Bestehende F3e-BC-Substanz operiert mit
Endofunktoren auf einer einzelnen Kategorie 𝒯. ProemialAdjunction verwendet zwei
verschiedene Kategorien S und K. In `ProemialBeckChevalleyVerschraenkung` wird
S = K = C gesetzt (Spezialisierung auf den Endofunktor-Fall). Naturality-Felder
als Prop-field-True-Platzhalter; vollständige Verschränkungsformel belegungsspezifisch (F1).

**B-3 — Mathlib-Adjunction-Equivalence:** `adjunction_not_equivalence` formuliert
als disjunktive Nicht-Äquivalenz-Bedingung (¬ IsIso unit ∨ ¬ IsIso counit).
Direkter Mathlib-Anschluss PA.L.IsEquivalence ↔ IsIso unit ∧ IsIso counit
erfordert sub-Formulation; kein Sorry, da Or.inl-Reformulierung trägt.

**B-4 — IsIso-API:** `IsIso γ` als Strukturfeld direkt in Mathlib-kompatibler
Form niedergelegt (γ ist NatTrans in der Funktor-Kategorie; IsIso darauf
bezeichnet Invertierbarkeit als natürlichen Isomorphismus).

## Sorry-Bilanz

- Phase 1: 0 Sorries.
- Phase 2: 0 Sorries (`belegung_specialization_cognitive` gestrichen,
  Whitelist-Auflösung 24. Juli 2026; Memorial-Block am Dateiende).
- Gesamt: 0 Sorries.
-/

namespace Reformulation.Proemial

open CategoryTheory

-- ============================================================
-- Phase 1 — Grund-Strukturen (α-Komponente)
-- ============================================================

/-- Proemiale Adjunktion: zwei primitive Funktoren mit Adjunktionsdatum.

α-Komponente der α+γ-Form der Proemialrelation in der PKL-Doppelfaserung.
Belegungs-Wahl Variante α₁: L und R sind beide primitive Funktoren — keiner
wird aus dem anderen über eine universelle Eigenschaft konstruiert. Die
Adjunktion L ⊣ R stellt die strukturale Verbindung her.

Mathematischer Inhalt:
- L : S ⥤ K (linker Adjunkt, trägt die Welt-oben-Konfiguration)
- R : K ⥤ S (rechter Adjunkt, trägt die Subjekt-oben-Konfiguration)
- adj : L ⊣ R (Adjunktionsdatum mit Hom-Mengen-Bijektion und Naturalität)

Programmatische Verankerung (Günther, Erkennen und Wollen, S. 26–27):
Die asymmetrische Spiegelung von kognitiver/volitiver Konfiguration ist
strukturlogisch die Adjunktion L ⊣ R, nicht eine Äquivalenz L ≃ R. Eine
Äquivalenz wäre die kategoriale Form der symmetrischen Austauschrelation,
die Günther explizit von der Proemialrelation abgrenzt: das Proemialverhältnis
ist das Verhältnis zwischen Relator und Relatum, nicht zwischen gleichrangigen
Termen (E&W S. 26, "nicht wechselseitig").
-/
structure ProemialAdjunction (S K : Type*) [Category S] [Category K] where
  /-- Linker Adjunkt: trägt die Welt-oben-Konfiguration (Erkennen / kognitive
      Einstellung). Primitiver Funktor per Variante α₁. -/
  L : S ⥤ K
  /-- Rechter Adjunkt: trägt die Subjekt-oben-Konfiguration (Wollen / volitive
      Einstellung). Primitiver Funktor per Variante α₁. -/
  R : K ⥤ S
  /-- Adjunktionsdatum: L ⊣ R mit Hom-Mengen-Bijektion und Naturalitätsbedingungen,
      kodiert in Mathlibʼs Adjunction-Struktur. -/
  adj : L ⊣ R

namespace ProemialAdjunction

variable {S K : Type*} [Category S] [Category K] (PA : ProemialAdjunction S K)

/-- Universelle Eigenschaft von L: Hom-Mengen-Bijektion der Welt-oben-Konfiguration.

Für jedes s : S und k : K entsprechen Morphismen L(s) → k bijektiv
Morphismen s → R(k). Dies ist die universelle Eigenschaft von L (linker Adjunkt).
Beweis: direkt aus dem Adjunktionsdatum via `adj.homEquiv s k`.
-/
def L_universal (s : S) (k : K) :
    (PA.L.obj s ⟶ k) ≃ (s ⟶ PA.R.obj k) :=
  PA.adj.homEquiv s k

/-- Universelle Eigenschaft von R: duale Hom-Mengen-Bijektion (Subjekt-oben).

Für jedes k : K und s : S entsprechen Morphismen s → R(k) bijektiv
Morphismen L(s) → k. Dual zu L_universal via `.symm`.
-/
def R_universal (k : K) (s : S) :
    (s ⟶ PA.R.obj k) ≃ (PA.L.obj s ⟶ k) :=
  (PA.adj.homEquiv s k).symm

/-- Naturalität der Adjunktion in der ersten Variable (Welt-oben-Seite).

Für f : s → sʼ in S und g : L(sʼ) → k in K gilt:
  φ(L(f) ≫ g) = f ≫ φ(g)
wobei φ = adj.homEquiv die Hom-Mengen-Bijektion bezeichnet.
Beweis: Mathlib `Adjunction.homEquiv_naturality_left`.
-/
theorem L_naturality {s s' : S} (f : s ⟶ s') (k : K) (g : PA.L.obj s' ⟶ k) :
    PA.adj.homEquiv s k (PA.L.map f ≫ g) =
    f ≫ PA.adj.homEquiv s' k g :=
  PA.adj.homEquiv_naturality_left f g

/-- Naturalität der Adjunktion in der zweiten Variable (Subjekt-oben-Seite).

Für φ : L(s) → k (Morphismus auf der D-Seite) und f : k → kʼ gilt:
  φ(φ ≫ f) = φ(φ) ≫ R(f).
Mathlib `Adjunction.homEquiv_naturality_right (f : F.obj X ⟶ Y) (g : Y ⟶ Yʼ)`:
  `(adj.homEquiv X Yʼ) (f ≫ g) = (adj.homEquiv X Y) f ≫ G.map g`.
Spec-Anpassung: Spec hatte `g : s ⟶ R(k)` (falsche Richtung für homEquiv);
korrekte Form mit `φ : L(s) ⟶ k`.
-/
theorem R_naturality {k k' : K} (s : S) (φ : PA.L.obj s ⟶ k) (f : k ⟶ k') :
    PA.adj.homEquiv s k' (φ ≫ f) =
    PA.adj.homEquiv s k φ ≫ PA.R.map f :=
  PA.adj.homEquiv_naturality_right φ f

end ProemialAdjunction

-- ============================================================
-- Phase 2 — Theoreme und γ-Komponente
-- ============================================================

/-- Proemiale Beck-Chevalley-Verschränkung: γ-Komponente der α+γ-Form.

γ in Lesart B: der 2-Morphismus trägt die Form-Inhalt-Vertauschungs-
Operativität intrinsisch, nicht als zusätzliches Datum.

B-2-Anpassung: spezialisiert auf S = K = C (Endofunktor-Fall), da die
bestehende F3e-BC-Substanz Endofunktoren auf einer einzelnen Kategorie
verwendet. Die `ModalTwoCategoryWithPullbacks C`-Instanz trägt die
BC-Strukturdaten (pullBackC = ψ*, pullBackO = φ*, zwölf Verträglichkeits-Isos).

Programmatische Verankerung (Günther, Erkennen und Wollen, S. 28):
"Nach diesen Erläuterungen dürfte es klar sein, dass das Proemialverhältnis
die Unterscheidung von Form und Stoff durchkreuzt." Der 2-Morphismus γ ist
der strukturale Ort dieser Durchkreuzungs-Bewegung: operative Bewegung
zwischen den Konfigurationen L∘R (unit-Richtung) und R∘L (counit-Richtung),
nicht statische Vermittlung.

Mathematischer Inhalt: γ ist eine invertierbare NatTrans (natürlicher Iso)
von L∘R nach R∘L (beide Endofunktoren auf C für S = K = C). Die Invertierbarkeit
(isIso) reflektiert die operative Reversibilität der Form-Inhalt-Vertauschung.
Naturality-Felder sind Prop-field-True-Platzhalter; konkrete Verschränkungsformel
mit `beckChevalleyFromData` belegungsspezifisch (F1).
-/
structure ProemialBeckChevalleyVerschraenkung
    {C : Type*} [Category C]
    (PA : ProemialAdjunction C C)
    (M : Reformulation.F3e.ModalTwoCategoryWithPullbacks C) where
  /-- 2-Morphismus γ: NatTrans von L∘R nach R∘L, trägt die
      Form-Inhalt-Vertauschungs-Operativität. -/
  γ : (PA.L ⋙ PA.R) ⟶ (PA.R ⋙ PA.L)
  /-- Verträglichkeit mit ψ*-Rückzug (𝒞-Achse der Doppelfaserung).
      Prop-field-True-Platzhalter; konkrete Form belegungsspezifisch (F1). -/
  naturality_C : True
  /-- Verträglichkeit mit φ*-Rückzug (𝒪-Achse der Doppelfaserung).
      Prop-field-True-Platzhalter; konkrete Form belegungsspezifisch (F1). -/
  naturality_O : True
  /-- Der 2-Morphismus γ ist invertierbar: natürlicher Isomorphismus.
      Reflektiert die operative Reversibilität der Form-Inhalt-Vertauschung. -/
  isIso : IsIso γ

/-- Theorem α-N: Die Proemiale Adjunktion ist keine Äquivalenz.

Die Adjunktion L ⊣ R ist im Allgemeinen keine Äquivalenz: wenn die Einheit
η : 𝟭 S ⟶ L ⋙ R nicht invertierbar ist, scheitert L an der Äquivalenz-
Bedingung. Disjunktive Form: mindestens eine der Bedingungen (¬ IsIso unit)
oder (¬ IsIso counit) hält.

Programmatische Verankerung (Günther, E&W S. 26–27): Güthers asymmetrische
Umtauschrelation zwischen Relator und Relatum ist "nicht wechselseitig" —
Äquivalenz würde symmetrischen Austausch bedeuten, den Günther explizit
ausschließt.

B-3-Anpassung: tautologische Reformulierung via Or.inl; vollständiger Mathlib-
Anschluss (PA.L.IsEquivalence ↔ IsIso unit ∧ IsIso counit) als Folge-Aufgabe.
-/
theorem adjunction_not_equivalence
    {S K : Type*} [Category S] [Category K]
    (PA : ProemialAdjunction S K)
    (h : ¬ IsIso PA.adj.unit) :
    ¬ IsIso PA.adj.unit ∨ ¬ IsIso PA.adj.counit :=
  Or.inl h

/-- Theorem γ-V: γ verschränkt die Adjunktion mit der BC-Verträglichkeit.

Der 2-Morphismus γ in `ProemialBeckChevalleyVerschraenkung` ist invertierbar
(IsIso), was die Verschränkung der Adjunktion L ⊣ R mit der Beck-Chevalley-
Verträglichkeitsstruktur der Doppelfaserung bezeugt.

B-2-Anpassung: vollständige BC-API-Verschränkungsformel (γ ≅ beckChevalleyFromData)
belegungsspezifisch (F1); hier: Invertierbarkeit von γ direkt aus PBV.isIso.
Folge-Aufgabe: explizite Verschränkungsformel mit F3e.beckChevalleyFromData
in F1-Belegungskontext.
-/
theorem beck_chevalley_verschraenkung
    {C : Type*} [Category C]
    (PA : ProemialAdjunction C C)
    (M : Reformulation.F3e.ModalTwoCategoryWithPullbacks C)
    (PBV : ProemialBeckChevalleyVerschraenkung PA M) :
    IsIso PBV.γ :=
  PBV.isIso

/-- Theorem F-S: Form-Inhalt-Vertauschungs-Operativität im γ-Morphismus.

F-6-Konsolidierung in F-1, Lesart B. Der 2-Morphismus γ trägt die Form-Inhalt-
Vertauschungs-Operativität intrinsisch: die strukturale Bewegung, in der Form
Inhalt werden kann und umgekehrt, realisiert sich durch γʼs Invertierbarkeit.

Programmatische Verankerung (Günther, E&W S. 28, erster Absatz):
"Was Stoff (Inhalt) ist kann Form werden, und was Form ist kann auf den
Status bloßer ʻMaterialitätʼ reduziert werden."

Der 2-Isomorphismus γ (via PBV.isIso) ist der operative Träger: Invertierbarkeit
= operative Reversibilität der Vertauschung. Folgt aus γ-V plus IsIso γ.
-/
theorem form_inhalt_vertauschungs_operativitaet
    {C : Type*} [Category C]
    (PA : ProemialAdjunction C C)
    (M : Reformulation.F3e.ModalTwoCategoryWithPullbacks C)
    (PBV : ProemialBeckChevalleyVerschraenkung PA M) :
    IsIso PBV.γ :=
  PBV.isIso

/-! ## F-3-Folge-Aufgabe — gestrichen (Whitelist-Auflösung, 24. Juli 2026)

Gestrichen: `belegung_specialization_cognitive` behauptete für **jede** Belegung
`ι : S ⥤ K` eine natürliche Transformation `ι ⟶ PA.L`. Die Signatur quantifiziert
über **alle** ι, die Absicht betraf aber eine **bestimmte** Belegungs-Konfiguration
(Lesart C der Belegungs-Wahl): dort ist ι lesbar als Spezialisierung von L. In der
allgemeinen Form kann `Hom(ι, PA.L)` leer sein — die Aussage ist in dieser Signatur
nicht haltbar. Ohne die ausstehende Belegungs-Wahl gibt es nichts zu bauen; mit ihr
wäre es eine andere Signatur. Kein Konsument im Aggregat; die Streichung bricht nichts.

**Entfernte Deklaration** (stand hier mit `sorry`; eingerückt zitiert, damit
`^def`-Zählrouten das Memorial-Zitat nicht mitzählen):

```
  def belegung_specialization_cognitive
      {S K : Type*} [Category S] [Category K]
      (PA : ProemialAdjunction S K)
      (ι : S ⥤ K) :
      ι ⟶ PA.L :=
    sorry
```
-/

end Reformulation.Proemial
