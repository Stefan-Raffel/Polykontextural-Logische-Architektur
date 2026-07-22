import Reformulation.Proemial.AlphaGammaWitnesses
import Mathlib.CategoryTheory.Adjunction.FullyFaithful
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks

/-!
# Reformulation.Proemial.AlphaGammaTransport — F-3.6.a.2 + F-3.6.a.3 Transport- und Deprecation-Einheit

Siebte Niederlegungs-Schicht (über F-1, F-3, F-3.4/5, F-3.6, F-3.6.a, F-3.6.a.1+b).
Additiv zu `AlphaGammaWitnesses.lean`; einzige dokumentierte Bestands-Modifikation:
die Option-B-Bereinigung in `AlphaGammaBeckChevalley.lean` (Memorial-Block, siehe dort)
plus Aggregat-Nachführung.

Zwei Blöcke:

**Block A (F-3.6.a.2 — Transport):**
1. Treue-Brücke `r_faithful_of_counit_epi` (Mathlib-Lemma gefunden, eigene Rechnung
   als Kommentar geführt).
2. Haupt-Theorem `rel_diagonal_transport`: die Stellungs-Hypothesen erzwingen den
   Diagonal-Bruch AUCH auf der S-Seite, am R-Transport von σ.rel —
   `BC.pullback_S` erstmals Statement-tragend.
3. Verschränkungs-Gleichung `diagonal_transport_eq` (Anker-5-Einlösung: die zwei
   Diagonalen, durch R und den Pullback-Vergleichs-Morphismus verbunden) plus
   konditionale Verschärfung `pullbackComparison_rel_isIso` (iso-dichte Verschränkung).
4. Bewohnungs-Korollar `prodHomWitness_counit_epi` (konditional, getragen).
5. Stufe-5-Kandidat `bcIso_diagonal_transport`: bcIso/compat-Anbindung an die
   Stufe-3-Gleichung (eingelöst, da Stufen 1-3 sorry-frei tragen).

**Block B (F-3.6.a.3 — Deprecation-Anker):**
- positives Faktorisierungs-Lemma `rel_factors_through_counit`;
- formale Negationen `rel_not_through_counit_is_false` und `does_not_imply_is_false`;
- 2×2-Quadranten-Bilanz als Doc-string-Block;
- rfl-Härtung: lokales Auswertungs-Lemma `tensorProductAdjunction_counit_apply`
  (die Umstellung der key-Gleichung in `AlphaGammaWitnesses.lean` selbst ist durch
  die additive Disziplin gesperrt; Wartungs-Markierung dort bleibt bestehen).

Spec: F3_6a2_a3_Sub_Spec.md. Prompt: F3_6a2_a3_Sub_Prompt.md. Frühjahr 2026.

## Klasse-B-Befunde

**B-1 (positiv) — Treue-Brücke in Mathlib:** `Adjunction.faithful_R_of_epi_counit_app`
(Mathlib.CategoryTheory.Adjunction.FullyFaithful, Instanz-Hypothese
`[∀ X, Epi (h.counit.app X)]`). Die eigene Rechnung der Spec (counit-Naturalität +
Epi-Kancellation) ist als Kommentar an der Brücke geführt.

**B-2 — Mono-Reflexion zweistufig:** `Functor.mono_of_mono_map` verlangt
`[ReflectsMonomorphisms F]`, nicht `[Faithful F]`; die Brücke ist die
priority-100-Instanz `reflectsMonomorphisms_of_faithful`
(Mathlib.CategoryTheory.Functor.EpiMono). Mit `haveI : PAS.R.Faithful` im Kontext
löst die Instanz-Suche die Kette selbständig auf.

**B-3 — pullbackComparison liegt bei HasPullback, nicht bei Preserves:**
`pullbackComparison` samt `pullbackComparison_comp_fst/snd` (beide `@[reassoc (attr := simp)]`)
liegt in `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback` — transitiv
schon importiert. Der Preserves-Import wird nur für die Iso-Verschärfung gebraucht
(`PreservesPullback.iso_hom`-Umfeld, Instanz `IsIso (pullbackComparison ...)`).

**B-4 — PreservesLimits-Gewinnung:** `Adjunction.rightAdjoint_preservesLimits`
(Lemma, keine Instanz) liefert `PreservesLimitsOfSize`; via `haveI` registriert
zieht die Instanz-Kette `PreservesLimitsOfShape WalkingCospan` →
`PreservesLimit (cospan σ.rel σ.rel)` → `IsIso (pullbackComparison ...)` durch.

**B-5 — homEquiv_counit als Alias:** `Adjunction.homEquiv_counit` ist Alias von
`homEquiv_symm_apply` (`(adj.homEquiv X Y).symm g = F.map g ≫ counit.app Y`);
zusammen mit `Equiv.symm_apply_apply` ist die Koeinheits-Zerlegung eine
Zwei-Schritt-Rechnung.

**B-6 — Epi-Surjektivität durch den TypeCat-Wrapper:** `epi_iff_surjective`
(Mathlib.CategoryTheory.Types.Basic) operiert auf dem Hom-Wrapper; das
Urbild-Paar `(true, ↾fun _ => y)` braucht die `↾`-Promotion (B-2*-Bestand),
die Auswertung ist danach rfl-defeq — kein Mehraufwand.

## Sorry-Bilanz

- Block A Stufen 1-3 + Verschärfung: 0 Sorries.
- Stufe 4 (`prodHomWitness_counit_epi`): 0 Sorries.
- Stufe 5 (`bcIso_diagonal_transport`): 0 Sorries (Kandidat eingelöst).
- Block B: 0 Sorries.
- Gesamt: 0 Sorries.
-/

/-! ## Transport-Substanz — Begründungs-Block

Die Adjunktions-Verschränkung der Diagonal-Substanz löst die drei in der
F-3.6.a-Bewertung monierten Abwesenheiten auf (Generizitäts-Befund II.2):

- **PAS.adj** erscheint in Hypothese (counit-Epi) und Beweis (Treue-Brücke,
  Limes-Erhaltung);
- **PAS.R** trägt das Goal (R.map σ.rel) und die Beweis-Substanz (R.Faithful,
  Mono-Reflexion);
- **BC.pullback_S** ist erstmals Statement-tragend: die S-Diagonale
  `pullback.diagonal (R.map σ.rel)` existiert nur durch die letI-Bindung.

**Programmatische Verankerung:** Anker 5 („zwei Pullback-Strukturen für zwei
Pfeil-Richtungen") ist mit `diagonal_transport_eq` wörtlich eingelöst:
pullback_K trägt die K-Diagonale, pullback_S die S-Diagonale, der
R-Transport verbindet sie durch den Pullback-Vergleichs-Morphismus —
und die Adjunktions-Limes-Erhaltung macht die Verbindung iso-dicht
(`pullbackComparison_rel_isIso`).

**Methodologischer Einsatz:** zweiter Sub-Substanz-I-Testlauf an der härtesten
Aussagen-Klasse der Serie (Iso/Mono/Epi unter Adjunktions-Transport). Alle
Spec-Aussagen waren vor-geprüft (Spec Sektion II); Abweichungen der
Implementation von den Spec-Skizzen sind als Befunde dokumentiert
(F3_6a2_a3_Implementation_Final.md), nicht still repariert.
-/

namespace Reformulation.Proemial.Substantial.Transport

open CategoryTheory CategoryTheory.Limits
open Reformulation.Proemial.Substantial
open Reformulation.Proemial.Substantial.Refined
open Reformulation.Proemial.Substantial.Witnesses

-- Die F-3.6-BC-Struktur (nicht der F-3-Stub gleichen Namens), qualifiziert
-- referenziert wie in AlphaGammaRelPullback.lean.
private abbrev BCData := Reformulation.Proemial.Substantial.BeckChevalley.SubstantialBeckChevalleyData

-- ============================================================
-- Block A, Stufe 1 — Treue-Brücke
-- ============================================================

/-- Punktweise epi Koeinheit macht R treu.

    Klasse-B-1-Befund (positiv): Mathlib trägt das Lemma als
    `Adjunction.faithful_R_of_epi_counit_app`. Die eigene Adjunktions-Rechnung
    der Spec (Sektion II.1, geprüft) zur Dokumentation:
    aus `R.map f = R.map g` folgt via counit-Naturalität
    `counit.app X ≫ f = L.map (R.map f) ≫ counit.app Y
                      = L.map (R.map g) ≫ counit.app Y = counit.app X ≫ g`;
    Epi-Kancellation an `counit.app X` liefert `f = g`. -/
theorem r_faithful_of_counit_epi
    {S K : Type*} [Category S] [Category K]
    (PAS : ProemialAdjunctionSubstantial S K)
    (h_counit_epi : ∀ k : K, Epi (PAS.adj.counit.app k)) :
    PAS.R.Faithful :=
  haveI : ∀ k : K, Epi (PAS.adj.counit.app k) := h_counit_epi
  PAS.adj.faithful_R_of_epi_counit_app

-- ============================================================
-- Block A, Stufe 2 — Haupt-Theorem: Diagonal-Transport nach S
-- ============================================================

/-- F-3.6.a.2 Haupt-Theorem: die Stellungs-Hypothesen erzwingen den
    Diagonal-Bruch AUCH AUF DER S-SEITE, am R-Transport von σ.rel.

    Statement-tragend: `BC.pullback_S` (die S-Diagonale existiert nur dadurch);
    `PAS.adj.counit` (Hypothese), `PAS.R` (Goal). Die drei in der
    F-3.6.a-Bewertung monierten Abwesenheiten (adj, R, Statement-Bezug)
    sind damit Statement-seitig adressiert.

    Beweis-Kette: h_split + h_rel_not_iso ⟹ ¬ Mono σ.rel (F-3.6.a-Mechanik);
    Treue-Brücke (Stufe 1) + Mono-Reflexion ⟹ ¬ Mono (R.map σ.rel);
    isIso_diagonal_iff in S ⟹ ¬ IsIso der S-Diagonale.

    Ternäre Bewährungs-Matrix (Spec VI, durchgeführt): alle drei Hypothesen
    einzeln entfernt, alle drei Läufe brechen den Build — h_rel_not_iso
    (𝟙-Fall), h_split (Mono-Gegenbeispiel), h_counit_epi
    (Kollaps-Gegenbeispiel Spec II.3). Befunde in der Final-Notiz. -/
theorem rel_diagonal_transport
    {S K : Type*} [Category S] [Category K]
    {PAS : ProemialAdjunctionSubstantial S K}
    (BC : BCData S K PAS)
    (σ : Stellung PAS)
    (h_split : IsSplitEpi σ.rel)
    (h_rel_not_iso : ¬ IsIso σ.rel)
    (h_counit_epi : ∀ k : K, Epi (PAS.adj.counit.app k)) :
    letI : HasPullbacks S := BC.pullback_S
    ¬ IsIso (pullback.diagonal (PAS.R.map σ.rel)) := by
  -- BC.pullback_S operativ: trägt die HasPullback-Instanz der Aussage
  -- (B-3-Mechanik aus F-3.6.a: letI erneut registrieren + show-Reduktion).
  letI : HasPullbacks S := BC.pullback_S
  show ¬ IsIso (pullback.diagonal (PAS.R.map σ.rel))
  intro h_iso_diag
  apply h_rel_not_iso
  -- Treue-Brücke: Epi-Koeinheit ⟹ R treu ⟹ R reflektiert Monos
  -- (priority-100-Instanz reflectsMonomorphisms_of_faithful, B-2-Befund).
  haveI : PAS.R.Faithful := r_faithful_of_counit_epi PAS h_counit_epi
  -- Diagonale iso ⟹ R.map σ.rel mono (isIso_diagonal_iff, S-seitig).
  haveI : Mono (PAS.R.map σ.rel) :=
    (pullback.isIso_diagonal_iff (PAS.R.map σ.rel)).mp h_iso_diag
  -- Mono-Reflexion entlang des treuen R.
  haveI : Mono σ.rel := PAS.R.mono_of_mono_map ‹Mono (PAS.R.map σ.rel)›
  haveI : IsSplitEpi σ.rel := h_split
  -- Mono + split-epi ⟹ iso — Widerspruch mit h_rel_not_iso (F-3.6.a-Mechanik).
  exact isIso_of_mono_of_isSplitEpi σ.rel

-- ============================================================
-- Block A, Stufe 3 — Verschränkungs-Gleichung (Anker-5-Einlösung)
-- ============================================================

/-- Die zwei Diagonalen sind durch R verbunden: der R-Transport der
    K-Diagonale ist — bis auf den Pullback-Vergleichs-Morphismus —
    die S-Diagonale des R-Bilds. „Zwei Pullback-Strukturen für zwei
    Pfeil-Richtungen" (Anker 5) wörtlich: pullback_K und pullback_S,
    durch die Funktor-Schicht verschränkt.

    Die Gleichung selbst braucht die Limes-Erhaltung NICHT (der
    Vergleichs-Morphismus existiert immer); die Iso-Dichte der
    Verschränkung trägt `pullbackComparison_rel_isIso`. -/
theorem diagonal_transport_eq
    {S K : Type*} [Category S] [Category K]
    {PAS : ProemialAdjunctionSubstantial S K}
    (BC : BCData S K PAS)
    (σ : Stellung PAS) :
    letI : HasPullbacks S := BC.pullback_S
    letI : HasPullbacks K := BC.pullback_K
    PAS.R.map (pullback.diagonal σ.rel) ≫ pullbackComparison PAS.R σ.rel σ.rel
      = pullback.diagonal (PAS.R.map σ.rel) := by
  letI : HasPullbacks S := BC.pullback_S
  letI : HasPullbacks K := BC.pullback_K
  -- Beide Seiten gegen fst/snd: R.map (diagonal ≫ fst) = R.map 𝟙 = 𝟙 = diagonal_S ≫ fst.
  apply pullback.hom_ext <;>
    simp [← Functor.map_comp]

/-- Konditionale Verschärfung (Spec Stufe 3): der Pullback-Vergleichs-Morphismus
    ist iso — Rechtsadjungierte erhalten Limiten. Die Verschränkung der zwei
    Diagonalen ist damit iso-dicht: die S-Diagonale ist der R-Transport der
    K-Diagonale bis auf Iso.

    B-4-Mechanik: `Adjunction.rightAdjoint_preservesLimits` ist Lemma (keine
    Instanz); via haveI registriert zieht die Instanz-Kette bis
    `IsIso (pullbackComparison ...)` durch. -/
theorem pullbackComparison_rel_isIso
    {S K : Type*} [Category S] [Category K]
    {PAS : ProemialAdjunctionSubstantial S K}
    (BC : BCData S K PAS)
    (σ : Stellung PAS) :
    letI : HasPullbacks S := BC.pullback_S
    letI : HasPullbacks K := BC.pullback_K
    IsIso (pullbackComparison PAS.R σ.rel σ.rel) := by
  letI : HasPullbacks S := BC.pullback_S
  letI : HasPullbacks K := BC.pullback_K
  haveI := PAS.adj.rightAdjoint_preservesLimits
  show IsIso (pullbackComparison PAS.R σ.rel σ.rel)
  infer_instance

-- ============================================================
-- Block A, Stufe 5 — bcIso/compat-Anbindung (Kandidat, eingelöst)
-- ============================================================

/-- Stufe-5-Kandidat (Spec IV, eingelöst, da Stufen 1-3 sorry-frei tragen):
    Verhalten der Diagonal-Verschränkung unter bcIso-Transport.

    Die compat-Substanz von γ-V (bcIso.inv = adj.unit komponentenweise)
    bindet den bcIso-Rückweg an die Stufe-3-Gleichung: von σ.s aus gesehen
    sind bcIso-Rückweg-plus-K-Diagonal-Transport und Einheits-Weg-plus-
    S-Diagonale derselbe Morphismus. Erste Stelle der Folge, an der
    bcIso/compat und die Pullback-Substanz in EINEM Theorem stehen.

    Ehrliche Reichweiten-Markierung: die Beweis-Substanz ist compat plus
    Stufe 3 (Korollar-Tiefe, keine eigene Rechnung). Die volle Drei-fach-
    Verschränkung mit eigener Beweis-Substanz bleibt offen; die
    Halb-Operativitäts-Markierung der Zeugen-Korrektur-Notiz III.3 ist
    damit angebunden, nicht aufgelöst. -/
theorem bcIso_diagonal_transport
    {S K : Type*} [Category S] [Category K]
    {PAS : ProemialAdjunctionSubstantial S K}
    (BC : BCData S K PAS)
    (σ : Stellung PAS) :
    letI : HasPullbacks S := BC.pullback_S
    letI : HasPullbacks K := BC.pullback_K
    BC.bcIso.inv.app σ.s ≫
        PAS.R.map (pullback.diagonal σ.rel) ≫ pullbackComparison PAS.R σ.rel σ.rel
      = PAS.adj.unit.app σ.s ≫ pullback.diagonal (PAS.R.map σ.rel) := by
  letI : HasPullbacks S := BC.pullback_S
  letI : HasPullbacks K := BC.pullback_K
  rw [BC.compat σ.s]
  exact congrArg (PAS.adj.unit.app σ.s ≫ ·) (diagonal_transport_eq BC σ)

-- ============================================================
-- Block B (F-3.6.a.3) — positives Faktorisierungs-Lemma
-- ============================================================

/-- Jedes σ.rel faktorisiert durch die Koeinheit — die Standard-Zerlegung
    der Adjunktion (Zeuge: L-Bild des adjungierten Morphismus). Dieses Lemma
    ist das positive Gegenstück zur deprecierten Nicht-Faktorisierbarkeits-
    Aussage `rel_not_through_counit` (F-3.6) und dokumentiert formal,
    WARUM sie falsch war: die Faktorisierung existiert IMMER, unabhängig
    von jeder Iso-Hypothese an σ.rel.

    B-5-Mechanik: `Adjunction.homEquiv_counit` plus `Equiv.symm_apply_apply`. -/
theorem rel_factors_through_counit
    {S K : Type*} [Category S] [Category K]
    {PAS : ProemialAdjunctionSubstantial S K}
    (σ : Stellung PAS) :
    ∃ u : PAS.L.obj σ.s ⟶ PAS.L.obj (PAS.R.obj σ.k),
      σ.rel = u ≫ PAS.adj.counit.app σ.k :=
  ⟨PAS.L.map (PAS.adj.homEquiv σ.s σ.k σ.rel),
    ((PAS.adj.homEquiv σ.s σ.k).symm_apply_apply σ.rel).symm.trans
      (PAS.adj.homEquiv_counit σ.s σ.k _)⟩

-- ============================================================
-- Block B — formale Negationen (Deprecation-Anker)
-- ============================================================

/-- Formale Negation der F-3.6-Aussage `rel_not_through_counit`
    (Option-B-deprecier, Memorial-Block in AlphaGammaBeckChevalley.lean):
    ihre Behauptung ist widerlegt.

    Implementations-Wahl (Spec V.2): Doppelnegations-Form, weil sie die
    deprecierte Aussage `¬ ∃ u, …` wörtlich spiegelt; die direkt-positive
    Form ist `rel_factors_through_counit`. Die Hypothesen der deprecierten
    Aussage (BC, h_rel_not_iso) sind hier NICHT geführt — die Widerlegung
    gilt hypothesenfrei, was die Falschheit der alten Aussage in ihrer
    stärksten Form versiegelt. -/
theorem rel_not_through_counit_is_false
    {S K : Type*} [Category S] [Category K]
    {PAS : ProemialAdjunctionSubstantial S K}
    (σ : Stellung PAS) :
    ¬ ¬ ∃ u : PAS.L.obj σ.s ⟶ PAS.L.obj (PAS.R.obj σ.k),
        σ.rel = u ≫ PAS.adj.counit.app σ.k :=
  fun h => h (rel_factors_through_counit σ)

/-- Formale Negation der F-3.6-Aussage
    `TritoStellungsVielfaltExists_does_not_imply_substantial`
    (Option-B-deprecier, Memorial-Block in AlphaGammaBeckChevalley.lean):
    maschinelle Versiegelung des Quantoren-Fehlers als eigenständiger Anker.

    Die positive Substanz trägt `tritoStellungsVielfalt_implies_substantial`
    (Koeinheits-Stellung als universeller Gegen-Zeuge, F-3.6.a.1+b). -/
theorem does_not_imply_is_false
    {S K : Type*} [Category S] [Category K] :
    ¬ ∃ (PAS : ProemialAdjunctionSubstantial S K),
        TritoStellungsVielfaltExists PAS ∧
        ¬ TritoStellungsVielfaltExists_substantial PAS := by
  rintro ⟨PAS, h, hn⟩
  exact hn (tritoStellungsVielfalt_implies_substantial h)

-- ============================================================
-- Block B — rfl-Härtung + Bewohnungs-Korollar (Stufe 4)
-- ============================================================

/-- rfl-Härtung (Spec V.4): lokales Auswertungs-Lemma für die Koeinheit
    von `Types.tensorProductAdjunction` — die Koeinheit ist die Auswertung
    `(x, f) ↦ f x`. Benannte Stelle statt anonymer rfl-Abhängigkeit von der
    Mathlib-Definition; nachgelagerte Beweise (Stufe 4) gehen durch dieses
    Lemma.

    Reichweiten-Markierung: die key-Gleichung des punktweisen Zeugen in
    `AlphaGammaWitnesses.lean` selbst kann NICHT umgestellt werden, ohne die
    additive Disziplin zu brechen (einzige zulässige Bestands-Modifikation
    dieser Einheit ist die Option-B-Bereinigung); die Wartungs-Markierung
    dort bleibt bestehen. -/
theorem tensorProductAdjunction_counit_apply
    {X Y : Type} (x : X) (f : X ⟶ Y) :
    (Types.tensorProductAdjunction X).counit.app Y (x, f) = f x :=
  rfl

/-- Stufe 4 (Bewohnungs-Korollar, Spec II.5 Fund a): der prodHomWitness
    bewohnt die Hypothesen-Kombination des Haupt-Theorems counit-seitig —
    seine Koeinheit ist PUNKTWEISE EPI (die Auswertung ist surjektiv in Type:
    konstante Funktion als Urbild) bei NICHT-ISO (Zeugen-Einheit,
    `prodHomWitness_counit_not_iso`). Die Hypothesen-Klasse Epi-bei-¬Iso ist
    bewohnt; das Haupt-Theorem ist über diesem PAS NICHT anwendbar — es
    verlangt BC-Daten, und über prodHomWitnessPAS existieren keine, siehe
    `Stratification.prodHomWitness_not_bcData` (F-3.6.a.5).

    ZWEITE BEREINIGUNGS-AUSNAHME (F-3.6.a.5, Spec VI; eng begrenzt auf
    diese eine Doc-string-Stelle). Memorial — die ursprüngliche Zeile
    lautete: „Epi-bei-¬Iso ist exakt die Konfiguration, die `h_counit_epi`
    mit der Trito-Substanz verträglich macht: das Haupt-Theorem ist über
    prodHomWitnessPAS nicht vakuum." Falschheits-Grund: das Haupt-Theorem
    `rel_diagonal_transport` ist BC-parametrisiert; das Negativ-Lemma
    `prodHomWitness_not_bcData` zeigt `IsEmpty (BCData Type Type
    prodHomWitnessPAS)` — über prodHomWitnessPAS ist das Haupt-Theorem
    vakuum (die Epi-Hypothese ist bewohnt, die BC-Hypothese nicht).

    B-6-Mechanik: `epi_iff_surjective` + `↾`-Promotion des konstanten
    Urbild-Zeugen (B-2*-Bestand). -/
theorem prodHomWitness_counit_epi :
    ∀ k : Type, Epi (prodHomWitnessPAS.adj.counit.app k) := by
  intro k
  rw [epi_iff_surjective]
  intro y
  exact ⟨(true, ↾fun _ => y), tensorProductAdjunction_counit_apply true _⟩

/-! ## 2×2-Quadranten-Bilanz (Spec V.3)

Die zwei Bedingungen der substantiellen Trito-Form — `¬ IsIso σ.rel` und
`¬ IsIso (counit.app σ.k)` — spannen vier Quadranten auf; alle vier sind
durch Niederlegungs-Substanz getragen:

| | counit iso | counit ¬iso |
|---|---|---|
| **rel iso** | trivial: σ.rel = 𝟙 über `Adjunction.id` (𝟙/𝟙-Fall, Kontrast-Zeuge `diagonal_id_isIso`) | punktweiser Unabhängigkeits-Zeuge `exists_stellung_rel_iso_counit_not_iso` (prodHomWitness, σ.rel = 𝟙) |
| **rel ¬iso** | Bewohntheits-Zeuge `exists_stellung_splitEpi_not_iso` (identityWitnessPAS: counit = 𝟙 iso, rel nicht-iso split-epi) | Koeinheits-Stellung über prodHomWitness: `prodHomWitness_tritoVielfalt_substantial` (rel IST die nicht-iso Koeinheit) |

Doc-string-Nachführung (Spec V.3, II.3-Diskrepanz): über `identityWitnessPAS`
ist das TRITO-Prädikat falsch (jede Koeinheits-Komponente ist 𝟙, also iso) —
der Bewohntheits-Zeuge belegt nur die rel-Flanke (links unten). Das
Trito-geltende PAS ist `prodHomWitnessPAS` (rechte Spalte); mit
`prodHomWitness_counit_epi` bewohnt es zusätzlich die Epi-Hypothese des
Haupt-Theorems — Epi-bei-¬Iso als die volle Stufe-2-Konfiguration.
-/

end Reformulation.Proemial.Substantial.Transport
