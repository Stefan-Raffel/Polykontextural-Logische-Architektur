import Reformulation.Proemial.AlphaGammaSubstantial
-- Mathlib-Imports werden transitiv aus F-3 geerbt (Adjunction.Basic,
-- Adjunction.FullyFaithful, Equivalence, NatIso, AlphaGamma)

/-!
# Reformulation.Proemial.AlphaGammaSubstantialRefined — F-3.4/5-Folge-Iterationen

Additive Erweiterung der F-3-Niederlegung (`AlphaGammaSubstantial.lean`).
Niederlegung der zwei Folge-Iterationen aus der F-3-Implementations-Final-Korrektur-Notiz.
F-3 bleibt unverändert; F-3.4/5 sind additiv als dritte Schicht über F-1 und F-3.

**F-3.4** löst Schwäche 2 auf: `naturality_K` als Feld-verkleidetes-Theorem →
`naturality_K_from_S` als abgeleitetes Theorem mit eigener Beweis-Tiefe
(aus `naturality_S` + rechter Dreieck-Identität der Adjunktion + Iso-Inversion).

**F-3.5** löst Schwäche 3 auf: `Stellung.rel` ungenutzt →
`TritoStellungsVielfaltExists_substantial` mit konjunktiver Form:
`¬ IsIso σ.rel ∧ ¬ IsIso (counit.app σ.k)`.

Spec: F3_45_Sub_Spec.md. Prompt: F3_45_Sub_Prompt.md. Frühjahr 2026.

## Klasse-B-Befunde

**B-1 — right_triangle_components API-Form:** Bestätigt. Mathlib-Signatur:
`adj.right_triangle_components Y : adj.unit.app (R.obj Y) ≫ R.map (adj.counit.app Y) = 𝟙 _`.
(Aus `Mathlib.CategoryTheory.Adjunction.Basic` Zeile 118-119.)

**B-2 — Iso.inv_hom_id_app Namespace:** In `Iso`-Namespace (NatIso.lean Zeile 65),
erreichbar als `Iso.inv_hom_id_app α X` nach `open CategoryTheory`. Typ:
`α.inv.app X ≫ α.hom.app X = 𝟙 (G.obj X)`.

## Sorry-Bilanz

- `naturality_K_from_S`: 0 Sorries (Beweis via Iso.inv_hom_id_app + cancel_epi).
- `TritoStellungsVielfaltExists_substantial_implies_F3`: 0 Sorries.
- `adjunction_not_equivalence_substantial_refined`: 0 Sorries.
- Gesamt: 0 Sorries (konditional auf Build-Bestätigung).

## Theorem-Differenzierungs-Prüfung (Sub-Substanz G)

**F-3.4 (naturality_K_from_S):**
- *Syntaktisch:* eigenstängiges Theorem mit Hypothesen `(PGMm, k)`, Aussage über
  `R.map (counit.app k)`. Nicht-Feld.
- *Mathematisch:* Beweis-Tiefe aus `right_triangle_components` + `inv_hom_id_app` +
  `cancel_epi`. Kein Definitions-Korollar von `naturality_S`.

**F-3.5 (TritoStellungsVielfaltExists_substantial):**
- *Syntaktisch:* stärkere Aussage als F-3-Form (konjunktiv mit `¬ IsIso σ.rel`).
- *Mathematisch:* konditional auf Sub-Frage 1 (Horistês).
-/

namespace Reformulation.Proemial.Substantial.Refined

open CategoryTheory
open Reformulation.Proemial.Substantial

-- ============================================================
-- Phase 1 — F-3.4: naturality_K als Theorem
-- (ProemialGammaMorphismMinimal + Bridge + naturality_K_from_S)
-- ============================================================

/-- Proemialer γ-Morphismus in der minimalen Form.

    Refactoring von `ProemialGammaMorphismSubstantial` (F-3): nur `γ` und
    `naturality_S` als unabhängige Daten. `naturality_K` ist ABGELEITETES THEOREM
    (`naturality_K_from_S` unten), nicht Feld der Struktur.

    Sub-Substanz G operativ (F-3.4-Kern): die Differenzierung zwischen
    `naturality_S` (Datum) und `naturality_K` (Theorem) ist mathematisch
    substantiell — `naturality_K_from_S` trägt Beweis-Tiefe aus der
    rechten Dreieck-Identität der Adjunktion plus Iso-Inversion.

    Methodologische Verankerung (F-3-Korrektur-Notiz II.2):
    Felder einer Struktur sollten unabhängige Daten tragen, nicht erzwungene
    Konsequenzen. Die minimale Form macht diese Strukturierung sichtbar.

    `BC` als Parameter für Kompatibilität mit `ProemialGammaMorphismSubstantial.toMinimal`
    (Brücken-Definition unten); `BC` trägt kein Feld in `ProemialGammaMorphismMinimal`.
-/
structure ProemialGammaMorphismMinimal
    {S K : Type*} [Category S] [Category K]
    (PAS : ProemialAdjunctionSubstantial S K)
    (BC : SubstantialBeckChevalleyData S K PAS) where
  /-- Der natürliche Isomorphismus γ: L⋙R ≅ 𝟭 S. -/
  γ : PAS.L ⋙ PAS.R ≅ 𝟭 S
  /-- Naturalität in der S-Achse: adj.unit = γ.inv komponentenweise.
      Substantielles Datum (nicht True-Platzhalter wie in F-1). -/
  naturality_S : ∀ (s : S), PAS.adj.unit.app s = γ.inv.app s

/-- Brücke: jedes `ProemialGammaMorphismSubstantial` (F-3) ergibt ein
    `ProemialGammaMorphismMinimal` (F-3.4).

    Triviale Field-Projection: `γ` und `naturality_S` sind gemeinsame Felder.
    `naturality_K` (F-3-Feld) geht in die Brücke nicht ein — es ist im
    Minimal-Modell abgeleitet (via `naturality_K_from_S`).

    Brücken-Richtung: F-3 → F-3.4 (Minimal). Die Umkehrung erfordert den
    Beweis von `naturality_K_from_S` — nicht trivial (Dreieck-Identität).
-/
def ProemialGammaMorphismSubstantial.toMinimal
    {S K : Type*} [Category S] [Category K]
    {PAS : ProemialAdjunctionSubstantial S K}
    {BC : SubstantialBeckChevalleyData S K PAS}
    (PGM : ProemialGammaMorphismSubstantial PAS BC) :
    ProemialGammaMorphismMinimal PAS BC where
  γ := PGM.γ
  naturality_S := PGM.naturality_S

/-- Theorem `naturality_K_from_S`: `naturality_K` folgt aus `naturality_S`
    plus der rechten Dreieck-Identität der Adjunktion.

    Beweis-Strategie (drei Schritte):
    (1) `adj.right_triangle_components k`:
        `η_{R(k)} ≫ R(ε_k) = 𝟙 (R(k))`
        (Signatur: `unit.app (R.obj k) ≫ R.map (counit.app k) = 𝟙 _`)
    (2) `naturality_S`-Substitution:
        `γ.inv.app (R.obj k) ≫ R.map (counit.app k) = 𝟙 (R.obj k)`
    (3) `Iso.inv_hom_id_app γ (R.obj k)`:
        `γ.inv.app (R.obj k) ≫ γ.hom.app (R.obj k) = 𝟙 (R.obj k)`
    (4) `cancel_epi (γ.inv.app (R.obj k))`:
        aus (2) und (3): `R.map (counit.app k) = γ.hom.app (R.obj k)`.

    Programmatische Verankerung (F3_Bewertung.md Sektion IV.1):
    Beweis-Tiefe aus der rechten Dreieck-Identität der Adjunktion (Mac Lane
    Kapitel IV, Dreieck-Identitäten) plus Iso-Inversion. Kein Definitions-Korollar.

    Theorem-Differenzierungs-Prüfung (Sub-Substanz G, zwei Schichten):
    — Syntaktisch: eigenständiges Theorem, Hypothesen `(PGMm, k)`, Aussage
      über `R.map (counit.app k)`. Nicht-Feld der Struktur.
    — Mathematisch: Beweis-Tiefe aus `right_triangle_components` + Iso-Inversion.
      Strukturell verschieden von `naturality_S` (S-Achse vs. K-Achse;
      Dreieck-Identität ist eigene Kategorialstruktur).
-/
theorem naturality_K_from_S
    {S K : Type*} [Category S] [Category K]
    {PAS : ProemialAdjunctionSubstantial S K}
    {BC : SubstantialBeckChevalleyData S K PAS}
    (PGMm : ProemialGammaMorphismMinimal PAS BC)
    (k : K) :
    PAS.R.map (PAS.adj.counit.app k) = PGMm.γ.hom.app (PAS.R.obj k) := by
  have rt := PAS.adj.right_triangle_components k
  -- rt : PAS.adj.unit.app (PAS.R.obj k) ≫ PAS.R.map (PAS.adj.counit.app k) = 𝟙 (PAS.R.obj k)
  rw [PGMm.naturality_S (PAS.R.obj k)] at rt
  -- rt : PGMm.γ.inv.app (PAS.R.obj k) ≫ PAS.R.map (PAS.adj.counit.app k) = 𝟙 (PAS.R.obj k)
  -- Iso-Inversion via Epi-Kancellation:
  -- inv_hom : γ.inv.app (R.obj k) ≫ γ.hom.app (R.obj k) = 𝟙 (R.obj k)
  -- rt.trans inv_hom.symm : γ.inv ≫ R.map ε = γ.inv ≫ γ.hom
  -- cancel_epi (γ.inv.app): R.map ε = γ.hom
  haveI : IsIso (PGMm.γ.inv.app (PAS.R.obj k)) := inferInstance
  exact (cancel_epi (PGMm.γ.inv.app (PAS.R.obj k))).mp
    (rt.trans (Iso.inv_hom_id_app PGMm.γ (PAS.R.obj k)).symm)

-- ============================================================
-- Phase 2 — F-3.5: TritoStellungsVielfaltExists mit rel-Substanz
-- ============================================================

/-- Trito-Stellungs-Vielfalt in der substantiellen Form mit rel-Substanz.

    Adressiert F-3-Bewertung Schwäche 3 (Stellung-rel ungenutzt):
    Das `rel`-Feld von `Stellung` trägt jetzt strukturellen Inhalt als
    konjunktive Bedingung:
    `¬ IsIso σ.rel ∧ ¬ IsIso (PAS.adj.counit.app σ.k)`.

    Die F-3-Form (`TritoStellungsVielfaltExists`) erlaubt `σ.rel` iso —
    die substantielle Form schließt das aus (stärkere Hypothese).

    Konjunktive Form (Mathematiker-Antizipation aus der Lage-Klärung):
    `¬ IsIso σ.rel` ist Positions-Relevanz-Substanz auf Relator-Niveau;
    `¬ IsIso (counit.app σ.k)` ist Adjunktions-Niveau-Bedingung (wie in F-3).
    Beide als unabhängige Bedingungen (konjunktiv, nicht strukturell-verbunden).

    Programmatische Verankerung: `σ.rel : L(σ.s) ⟶ σ.k` als Positions-Relevanz
    in der Trito-Schicht (LZEE Tafel VIII via Horistês F-3 Anker 1).
    Stellung-rel-Nicht-Iso-ität: Position ist nicht-reversibel konfiguriert.

    KonditionalitätsMarkierung (Sub-Frage 1, offen für Horistês-Klärung):
    Ist `¬ IsIso σ.rel` mathematisch unabhängig von `¬ IsIso (counit.app σ.k)`?
    Wenn nicht (eine folgt aus der anderen via Adjunktions-Eigenschaft): ist die
    konjunktive Form mathematisch leer; Re-Iteration mit strukturell-verbundener
    Form angemessen. Sub-Frage in der Final-Notiz als Befund dokumentiert.

    Schicht-Trennung F-3 / F-2: Definition operiert auf der Belegungs-Schicht (F-3);
    kenogrammatische Substanz (was macht eine Stellung "Trito"?) bleibt F-2-Aufgabe.
-/
def TritoStellungsVielfaltExists_substantial
    {S K : Type*} [Category S] [Category K]
    (PAS : ProemialAdjunctionSubstantial S K) : Prop :=
  ∃ (σ : Stellung PAS), ¬ IsIso σ.rel ∧ ¬ IsIso (PAS.adj.counit.app σ.k)

/-! ## Sub-Frage 1 (offen): Stellung-rel-Substanz und Trito-Unabhängigkeit

Die konjunktive Form `¬ IsIso σ.rel ∧ ¬ IsIso (counit.app σ.k)` ist
Mathematiker-Antizipation. Sub-Frage 1 an Horistês ist methodologisch offen:

**Frage:** Folgt `¬ IsIso σ.rel` automatisch aus `¬ IsIso (counit.app σ.k)`
(oder umgekehrt) via Adjunktions-Eigenschaft? Speziell: besteht eine
strukturelle Verbindung zwischen dem Relator `σ.rel : L(σ.s) ⟶ σ.k` und
der Koeinheit `PAS.adj.counit.app σ.k : L(R(σ.k)) ⟶ σ.k`?

**Wenn ja (abhängig):** `¬ IsIso σ.rel` ist keine eigene Substanz;
die konjunktive Form ist mathematisch leer (verstärkt nicht die F-3-Form).
Re-Iteration mit strukturell-verbundener Form (σ.rel als Stelle, an der
Reversibilität bricht; counit-Non-Iso als Konsequenz) angemessen.

**Wenn nein (unabhängig):** `¬ IsIso σ.rel` trägt eigene Substanz —
Stellung-rel-Nicht-Iso als Positions-Relevanz ist genuine Verstärkung.
Substantielle Differenzierung von F-3 (Schwäche 3) eingelöst.

Status: Mathematiker-Wahl konjunktive Form; konditionale Markierung offen.
Implementierungs-Final-Notiz trÃ¤gt Befund.
-/

/-- `TritoStellungsVielfaltExists_substantial` impliziert `TritoStellungsVielfaltExists` (F-3-Form).

    Implication-only-Beziehung: die substantielle Form ist STÄRKER als die F-3-Form.
    Die F-3-Form erlaubt `σ.rel` iso; die substantielle Form schließt es aus.

    Umkehrung gilt NICHT trivialerweise (und vermutlich nicht):
    die F-3-Form gibt keine Information über `σ.rel`.

    Beweis: triviale `obtain`-Extraktion (And.right).
-/
theorem TritoStellungsVielfaltExists_substantial_implies_F3
    {S K : Type*} [Category S] [Category K]
    {PAS : ProemialAdjunctionSubstantial S K}
    (h : TritoStellungsVielfaltExists_substantial PAS) :
    TritoStellungsVielfaltExists PAS := by
  obtain ⟨σ, _h_rel, h_counit⟩ := h
  exact ⟨σ, h_counit⟩

/-- Theorem α-N (substantielle Form, refined): Adjunktion ist keine Äquivalenz,
    weil substantielle Trito-Stellungs-Vielfalt existiert.

    Beweis-Struktur strukturell identisch mit F-3 (`adjunction_not_equivalence_substantial`),
    mit zusätzlicher `obtain`-Komponente für `h_rel`. Die Bedingung `¬ IsIso σ.rel`
    geht NICHT in den Widerspruch ein — der Widerspruch entsteht aus
    `h_counit` (counit-Non-Iso) wie in F-3.

    Methodologische Markierung: `h_rel` ist Bedingung der substantiellen Form.
    Sie macht die Hypothese stärker (mehr verlangt), ändert den Beweis-Pfad nicht.
    Anti-Tautologie-Disziplin: der Beweis ist kein Definitions-Korollar von F-3;
    er trägt die stärkere Hypothese explizit (via `obtain`), auch wenn `h_rel`
    im Beweis-Rumpf nicht erscheint.

    Widerspruchs-Pfad (wie in F-3):
    (1) `haveI : L.IsEquivalence := hL` — registriert Äquivalenz-Hypothese.
    (2) `haveI : IsIso PAS.adj.counit := inferInstance` — Mathlib-Instanz
        aus `Adjunction.FullyFaithful` (L.IsEquivalence → IsIso counit).
    (3) `exact inferInstance` — `isIso_app_of_isIso` ergibt IsIso (counit.app σ.k).
    (4) Widerspruch mit `h_counit : ¬ IsIso (counit.app σ.k)`.
-/
theorem adjunction_not_equivalence_substantial_refined
    {S K : Type*} [Category S] [Category K]
    (PAS : ProemialAdjunctionSubstantial S K)
    (h_trito : TritoStellungsVielfaltExists_substantial PAS) :
    ¬ PAS.L.IsEquivalence := by
  intro hL
  obtain ⟨σ, _h_rel, h_counit⟩ := h_trito
  -- _h_rel : ¬ IsIso σ.rel  (nicht im Widerspruch verwendet)
  -- h_counit : ¬ IsIso (PAS.adj.counit.app σ.k)  (Widerspruch wie in F-3)
  apply h_counit
  haveI : PAS.L.IsEquivalence := hL
  haveI : IsIso PAS.adj.counit := inferInstance
  exact inferInstance

/-! **Wachen (Wachenspitze Stufe 2).** Ist-Ausgabe des gruenen Builds (v4.30.0-rc2). Zwei
Wachen mit verschiedener Grundlage. `naturality_K_from_S` ist **aus dem Doc-Index von
`Proemial.lean` beim Namen gefuehrt** (F-3.4). `adjunction_not_equivalence_substantial_refined`
steht auf **Ermessensauswahl:** keine Quelle des Strangs benennt diesen Satz; er traegt den
Begriff, fuer den seine Datei steht. Die Marke steht hier und nicht nur im
Spezifikationskorpus, damit ein spaeterer Zug mit besserer Grundlage erkennen kann, was er
umstuft. Beide Profile tragen `Classical.choice` aus der Kategorien-Maschinerie; der Weg des
Axioms in den Term ist **nicht** gemessen (`CLAUDE.md` §8 Fallstrick 10). -/

/--
info: 'Reformulation.Proemial.Substantial.Refined.naturality_K_from_S' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms naturality_K_from_S

/--
info: 'Reformulation.Proemial.Substantial.Refined.adjunction_not_equivalence_substantial_refined' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms adjunction_not_equivalence_substantial_refined


end Reformulation.Proemial.Substantial.Refined
