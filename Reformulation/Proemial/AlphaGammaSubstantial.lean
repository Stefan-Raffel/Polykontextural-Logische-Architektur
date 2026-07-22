import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Adjunction.FullyFaithful
import Mathlib.CategoryTheory.Equivalence
import Mathlib.CategoryTheory.NatIso
import Reformulation.Proemial.AlphaGamma
import Reformulation.F3e.BeckChevalleyConstruction

/-!
# Reformulation.Proemial.AlphaGammaSubstantial — substantielle Tiefe der α+γ-Form

F-3-Niederlegung der substantiellen Tiefe der α+γ-Form der Proemialrelation in der
PKL-Doppelfaserung. Additiv zu F-1 (`AlphaGamma.lean`), die invariante Schicht bleibt
unverändert. F-3 löst drei methodologische Schwächen der F-1-Niederlegung auf:

- **F-3.1 — γ-V/F-S-Differenzierung:** γ-V operiert auf Funktor-Niveau
  (`PGM.γ = BC.bcIso`); F-S operiert auf Objekt-Niveau mit Quantifizierung über
  Stellungen (Stellung-Strukturmerkmal-Substanz als Differenziator).
- **F-3.2 — Aufhebung der Endofunktor-Spezialisierung:** `ProemialAdjunctionSubstantial`
  verwendet zwei verschiedene Kategorien S und K (Anker 5: emanative/evolutive Richtung
  als strukturell verschiedene Kategorien). Keine B-2-Spezialisierung S = K = C mehr.
- **F-3.3 — Functor.IsEquivalence-AuflÃ¶sung:** `adjunction_not_equivalence_substantial`
  verwendet `Functor.IsEquivalence` und `TritoStellungsVielfaltExists` (echte
  Kategorial-Struktur); kein Or.inl-Tautologie-B-3-Befund mehr.

Spec: F3_Spec.md. Prompt: F3_Prompt.md. FrÃ¼hjahr 2026.

## Klasse-B-Befunde

**B-1 — Functor.IsEquivalence-Import:** `Mathlib.CategoryTheory.Functor.IsEquivalence`
existiert nicht als eigenständige Datei. `Functor.IsEquivalence` liegt in
`Mathlib.CategoryTheory.Equivalence` (Zeile 610). `instance [L.IsEquivalence] : IsIso h.counit`
liegt in `Mathlib.CategoryTheory.Adjunction.FullyFaithful`. Beide explizit importiert.

**B-2 — BC-API-Architektur-Mismatch:** `beckChevalleyFromData` operiert auf
`ModalTwoCategoryWithPullbacks 𝒯` (einzelne Kategorie); für S ≠ K ist direktes
Erbe architektonisch blockiert. Minimaler Stub: `SubstantialBeckChevalleyData S K PAS`
mit einem `bcIso`-Feld gleichen Typs wie `PGM.γ`. Theorem γ-V als `PGM.γ = BC.bcIso`
formuliert; Sorry mit Folge-Aufgaben-Markierung. Belegungsspezifische F1-Integration
ist die nächste Iterations-Aufgabe.

**B-3 — Naturality-Felder substantiell:** naturality_S und naturality_K sind echte
Prop-Felder (keine Prop-field-True-Platzhalter). naturality_S identifiziert `adj.unit`
mit `γ.inv` komponentenweise; naturality_K identifiziert `R.map(ε_k)` mit `γ.hom` an
`R(k)`. F-S ist aus naturality_S ohne Sorry beweisbar. Knotenpunkt-Prüfung bestätigt:
γ-V und F-S sind strukturell verschieden (Funktor-Niveau vs. Objekt-Niveau).

**B-4 — NatIso als Namespace:** In Mathlib ist `NatIso` ein Namespace, kein Typ.
Natürliche Isomorphismen werden als `F ≅ G` geschrieben. γ : `PAS.L ⋙ PAS.R ≅ 𝟭 S`.

## Sorry-Bilanz

- Phase 1: 0 Sorries.
- Phase 2: 1 Sorry (Theorem γ-V, BC-API-Mismatch-bedingt; transparente Markierung).
- F-S bewiesen (aus naturality_S via Adjunction.homEquiv_unit).
- α-N bewiesen (aus Mathlib-Instanzen: `[L.IsEquivalence] : IsIso h.counit` und
  `isIso_app_of_isIso`).
- Gesamt: 1 Sorry.
-/

namespace Reformulation.Proemial.Substantial

open CategoryTheory

-- ============================================================
-- Phase 1 — Erweiterung der α-Struktur
-- ============================================================

/-- Proemiale Adjunktion in der substantiellen Schicht: zwei primitive Funktoren
    zwischen ZWEI VERSCHIEDENEN Kategorien.

    Substantielle Tiefe der α-Komponente: hebt die F-1-B-2-Spezialisierung S = K = C auf.
    Die zwei Kategorien tragen strukturell verschiedene Schichten:
    S = emanative/kognitive Schicht (Reversibilitäts-Anlage),
    K = evolutive/volitive Schicht (Positions-Relevanz-Anlage).

    Programmatische Verankerung (Horistês F-3 Anker 5, Günther LZEE):
    Die emanative und evolutive Abbildung sind zwei strukturell verschiedene
    Pfeil-Richtungen, nicht endomorph auf einer einzelnen Struktur. L trägt
    die emanative Ausrichtung (kognitiv, Welt-zu-Subjekt), R die evolutive
    (volitiv, Positions-Relevanz).

    Methodologische Markierung (Schärfung 1, Hermeneutes F-3-VK-2):
    Die Identifikation L-emanativ-kognitiv / R-evolutiv-volitiv ist PKL-Konstruktion,
    nicht aufgenommene Günther-Pointe. Konstruktiver Charakter im Doc-string explizit.
    Quellen-Substanz: Günther, Erkennen und Wollen, S. 26-28; LZEE via Florenz-Fund.
-/
structure ProemialAdjunctionSubstantial (S K : Type*) [Category S] [Category K] where
  /-- Linker Adjunkt: emanative-kognitive Schicht.
      Trägt Reversibilitäts-Anlage (Proto/Deutero-Schicht).
      Hermeneutische Identifikation: Einstellung der kognitiven Form (E&W S. 26:
      Symmetrie von Position und Negation als Subjektivitäts-Form).
      Methodologische Markierung: PKL-Konstruktion, nicht explizite Günther-Pointe. -/
  L : S ⥤ K
  /-- Rechter Adjunkt: evolutive-volitive Schicht.
      Trägt Positions-Relevanz-Anlage (Trito-Schicht).
      Hermeneutische Identifikation: Einstellung der volitiven Form (E&W S. 26:
      physische Wahlmöglichkeit). -/
  R : K ⥤ S
  /-- Adjunktionsdatum: L ⊣ R mit Hom-Mengen-Bijektion und Naturalitätsbedingungen. -/
  adj : L ⊣ R

/-! ## Belegungs-Wahl-Begründung

Die Belegungs-Wahl in Lesart C (L emanativ-kognitiv, R evolutiv-volitiv) ist
PKL-Konstruktion mit hermeneutischer Substanz.

**Methodologische Markierung:** Günther verbindet die zwei Schichten (E&W kognitiv/volitiv
und LZEE emanativ/evolutiv) in seinen Schriften NICHT EXPLIZIT. Die Identifikation ist
konstruktiv-strukturlogisch substanziert, nicht aufgenommen.

**Drei strukturlogische Parallelen** (Hermeneutes F-3 Sektion III):

1. *Symmetrie-Parallele:* emanative Reversibilität ↔ kognitive Symmetrie von Position
   und Negation (E&W S. 26).
2. *Positions-Relevanz-Parallele:* evolutive Irreversibilität ↔ volitive physische
   Wahlmöglichkeit (E&W S. 26).
3. *Bewegungs-Richtungs-Parallele:* emanative Außen-zum-Innen ↔ kognitive
   Welt-zum-Subjekt.

**Alternative Lesart** (Plotin/neuplatonisch): L emanativ-volitiv, R evolutiv-kognitiv.
Substantielle Alternative mit eigener historischer Substanz. Vorzug der gewählten
Identifikation: strukturlogische Substanz (drei Parallelen) versus historische Resonanz,
plus Konvergenz mit Florenz-Fund. Folge-Folge-Aufgabe: eigene Konsolidierungs-Sitzung.
-/

/-- Belegungs-Lesart für die kontextuelle Spezialisierung.

    Lesart-C-Markierung aus der Belegungs-Wahl-Schluss-Notiz: ι ist kontextabhängig
    als Spezialisierung von L (kognitive Konfiguration) oder R-dual (volitive
    Konfiguration) lesbar. Das Reading-Feld trägt den hermeneutischen Kontext.
-/
inductive BelegungReading
  /-- Kognitive Konfiguration: ι spezialisiert als NatTrans ι ⟶ L. -/
  | cognitive : BelegungReading
  /-- Volitive Konfiguration: ι spezialisiert in dualer Richtung (R-Seite). -/
  | volitive : BelegungReading

/-- Kontextuelle Belegung in Lesart C: Reading-abhängige Spezialisierung.

    Für eine gegebene Belegungs-Konfiguration ist ι lesbar als Spezialisierung
    von L (kognitive Konfiguration) oder dual (volitive Konfiguration). Die α+γ-Form
    ist belegungs-neutral auf der Ebene von L und R; die kontextuelle Spezialisierung
    bestimmt, welche Lesart gilt.

    Methodologische Markierung: operative Form von Lesart C aus der Belegungs-Wahl-
    Schluss-Notiz III.3. Die `specialization`-NatTrans trägt die kognitive Spezialisierung
    (Variante α₁: ι ⟶ L als primitive NatTrans).
-/
structure BelegungContextual {S K : Type*} [Category S] [Category K]
    (PAS : ProemialAdjunctionSubstantial S K) (ι : S ⥤ K) where
  /-- Das Reading: kognitive oder volitive Konfiguration. -/
  reading : BelegungReading
  /-- Spezialisierungs-NatTrans: ι ⟶ PAS.L (kognitive Konfiguration, Variante α₁).
      Für die volitive Konfiguration wäre eine duale Konstruktion auf K-Seite
      nötig; diese ist belegungsspezifisch und hier als kognitive Form niedergelegt. -/
  specialization : ι ⟶ PAS.L

/-- Stellung in der Trito-Schicht: positions-relevante Konfiguration.

    Stellung ist SUBSTANTIELLE STRUKTUR, nicht nur quantifizierter Parameter.
    Sie trägt den operativen Ort, an dem Form-Stoff-Durchkreuzung wirksam wird.

    Programmatische Verankerung: Trito-Stellungs-Vielfalt aus Günther LZEE Tafel VIII
    (via Horistês F-3 Anker 1). Die Stellung trägt operativ die Positions-Relevanz,
    an der Form-Stoff-Durchkreuzung wirksam wird.

    Schärfungs-Stelle 1 (Speculum F-3-VK-2 Sektion II): Stellung als eigenständige
    Struktur (nicht Quantifizierung) ist die operative Form der γ-V/F-S-Differenzierung:
    γ-V operiert auf Funktor-Niveau ohne Stellungs-Quantifizierung; F-S operiert
    auf Objekt-Niveau mit Stellung als Strukturmerkmal-Substanz.
-/
structure Stellung {S K : Type*} [Category S] [Category K]
    (PAS : ProemialAdjunctionSubstantial S K) where
  /-- Das Objekt in S an dieser Stellung. -/
  s : S
  /-- Das Objekt in K an dieser Stellung. -/
  k : K
  /-- Der Relator: Morphismus L(s) → k, der die Stellung-Konfiguration definiert. -/
  rel : PAS.L.obj s ⟶ k

/-- Substantielle Beck-Chevalley-Daten für die zwei-Kategorien-Form.

    Klasse-B-2-Befund: Minimaler Stub für BC-Daten im zwei-Kategorien-Fall.
    Das bestehende `beckChevalleyFromData` (F3e) operiert auf `ModalTwoCategoryWithPullbacks 𝒯`
    (einzelne Kategorie 𝒯); für S ≠ K ist direktes Erbe architektonisch blockiert
    (Endofunktor-Form nicht direkt anschlussfähig).

    Folge-Aufgabe: belegungsspezifische F1-BC-Integration als nächste Iterations-Aufgabe.
    Die `bcIso`-Struktur hat denselben Typ wie `ProemialGammaMorphismSubstantial.γ`,
    um die γ-V-Theorem-Formulierung `PGM.γ = BC.bcIso` zu ermöglichen.
-/
structure SubstantialBeckChevalleyData (S K : Type*) [Category S] [Category K]
    (PAS : ProemialAdjunctionSubstantial S K) where
  /-- BC-Iso in zwei-Kategorien-Form: Platzhalter für belegungsspezifische
      BC-Konstruktion. Typ identisch mit ProemialGammaMorphismSubstantial.γ.
      In F1-Belegung: aus konkretem Pullback-Quadrat via NatIso.ofComponents. -/
  bcIso : PAS.L ⋙ PAS.R ≅ 𝟭 S

-- ============================================================
-- Phase 2 — Theoreme und γ-Komponente
-- ============================================================

/-- Proemialer γ-Morphismus in der substantiellen Schicht.

    γ ist ein natürlicher Isomorphismus `L ⋙ R ≅ 𝟭 S`, der die Form-Inhalt-
    Vertauschungs-Operativität in der substantiellen Schicht trägt. Im Unterschied
    zu F-1 (γ : L⋙R ⟶ R⋙L als NatTrans auf S=K=C) operiert F-3's γ zwischen
    L⋙R : S⥤S und 𝟭 S.

    Die Struktur trägt ZWEI substantielle Aussagen (Form A + Form C aus F-3-VK-2):
    (i) Auf Funktor-Niveau: γ = BC.bcIso (γ-V-Substanz; Theorem γ-V).
    (ii) Auf Objekt-Niveau: Stellungs-Vielfalt-vermittelte Form-Inhalt-Verlagerung
    (F-S-Substanz; Theorem F-S, beweisbar aus naturality_S).

    Substantielle Naturality-Felder (nicht Prop-field-True wie in F-1):
    naturality_S identifiziert adj.unit mit γ.inv (S-Achse);
    naturality_K identifiziert R.map(ε_k) mit γ.hom|_{R(k)} (K-Achse).

    Programmatische Verankerung (Hermeneutes F-3 Sektion I.3; γ-Strategie-Sitzung
    Lesart B): γ trägt Durchkreuzungs-Operativität intrinsisch.
    Quellen-Substanz: Günther, E&W S. 28 erster Absatz.
-/
structure ProemialGammaMorphismSubstantial {S K : Type*} [Category S] [Category K]
    (PAS : ProemialAdjunctionSubstantial S K)
    (BC : SubstantialBeckChevalleyData S K PAS) where
  /-- Der natürliche Isomorphismus γ: L⋙R ≅ 𝟭 S.
      γ.hom.app s : R(L(s)) ⟶ s; γ.inv.app s : s ⟶ R(L(s)).
      Trägt die Form-Inhalt-Vertauschungs-Operativität als 2-Iso. -/
  γ : PAS.L ⋙ PAS.R ≅ 𝟭 S
  /-- Naturality in der S-Achse: adj.unit = γ.inv komponentenweise.
      Substantielle Bedingung (nicht True-Platzhalter): die Adjunktions-Einheit
      η_s : s ⟶ R(L(s)) ist komponentenweise gleich γ.inv.app s.
      Ermöglicht direkten Beweis von F-S (via Adjunction.homEquiv_unit). -/
  naturality_S : ∀ (s : S), PAS.adj.unit.app s = γ.inv.app s
  /-- Naturality in der K-Achse: R.map(ε_k) = γ.hom|_{R(k)} komponentenweise.
      Substantielle Bedingung: der R-Bildmorphismus der Koeinheit an k entspricht
      γ.hom an R(k). Beide haben Typ R(L(R(k))) ⟶ R(k).
      Folgt aus naturality_S und dem rechten Dreieck-Identität der Adjunktion. -/
  naturality_K : ∀ (k : K), PAS.R.map (PAS.adj.counit.app k) = γ.hom.app (PAS.R.obj k)
  /-- Beck-Chevalley-Verträglichkeit: Platzhalter.
      B-2-Befund: Architektur-Mismatch zwischen F3e-BC (Endofunktor) und F-3 (S ≠ K).
      Vollständige BC-Integration belegungsspezifisch (F1). -/
  bc_compat : True

/-!
## Theorem-Differenzierungs-Prüfung (Sub-Substanz F)

Die beiden Theoreme γ-V und F-S sind STRUKTURELL VERSCHIEDEN:

- **γ-V** (`beck_chevalley_verschraenkung_substantial`): operiert auf Funktor-Niveau.
  Aussage: `PGM.γ = BC.bcIso` — Gleichheit zweier natürlicher Isomorphismen
  (als `Iso`-Objekte in der Funktor-Kategorie). Keine Stellungs-Quantifizierung.

- **F-S** (`form_inhalt_vertauschungs_operativitaet_substantial`): operiert auf
  Objekt-Niveau. Aussage: `PAS.adj.homEquiv σ.s σ.k σ.rel = γ.inv.app σ.s ≫ R.map σ.rel`
  — Gleichheit von Morphismen in S, mit Quantifizierung über `σ : Stellung PAS`.
  Strukturmerkmal-Substanz `Stellung` ist essenziell.

Die Differenzierung ist am Theorem-Text prüfbar (Sub-Substanz F, Schärfungs-Stelle 3):
verschiedene Quantifizierungen, verschiedene Strukturniveaus, verschiedene Kategorien
der Aussage. Kein Tautologie-Duplikations-Befund wie in F-1.
-/

/-! ## Memorial-Block: das veraltete γ-V (`beck_chevalley_verschraenkung_substantial`)

**Dokumentierte einmalige Bereinigungs-Ausnahme von der additiven Disziplin**
(Sorry-Konsolidierung γ-V): die additive Disziplin schützt *bewährte* Substanz
vor Überschreibung — sie ist kein Bestandsschutz für eine veraltete, durch eine
sorry-freie Form bereits ersetzte Behauptung. Eng begrenzt: nur das eine folgende
Theorem-Statement samt Doc-string und `sorry`-Körper wurde entfernt; alle übrigen
Bestände dieser Datei (insbesondere die Struktur `ProemialGammaMorphismSubstantial`,
der Stub `SubstantialBeckChevalleyData` und das sorry-freie F-S
`form_inhalt_vertauschungs_operativitaet_substantial`) sind byte-identisch erhalten.

**Entfernte Aussage** (stand hier mit Sorry):

```
theorem beck_chevalley_verschraenkung_substantial
    {S K : Type*} [Category S] [Category K]
    (PAS : ProemialAdjunctionSubstantial S K)
    (BC : SubstantialBeckChevalleyData S K PAS)
    (PGM : ProemialGammaMorphismSubstantial PAS BC) :
    PGM.γ = BC.bcIso :=
  sorry
```

*Veraltetheits-Grund:* Diese Form operiert auf dem **F-3-Stub**
`SubstantialBeckChevalleyData` (nur `bcIso`-Feld, **kein** `compat`). Mit diesem
Stub ist `PGM.γ = BC.bcIso` *wirklich unbeweisbar* — `bcIso` ist ein freies Feld
ohne Bindung an die Adjunktions-Einheit; daher das `sorry`. Es trägt also keine
bewährte Substanz, sondern war eine unbewiesene Parallelform.
*Sorry-freie Einlösung:* `Substantial.BeckChevalley.beck_chevalley_verschraenkung_truly_substantial`
(AlphaGammaBeckChevalley.lean) verwendet die stärkere F-3.6-BC-Struktur **mit**
`compat : ∀ s, bcIso.inv.app s = adj.unit.app s` und beweist `γ = bcIso`
**sorry-frei** (über `naturality_S` + `compat`, Epi-Kanzelierung und Iso-Inversions-Eindeutigkeit).
Die γ-V-Substanz lebt dort weiter.

Sorry-Bestand des Aggregats durch diese Bereinigung: 4 → 3
(verbleibend: F3e ×2 `beckChevalleyFromData`/abgeleitet, F-1 ×1
`belegung_specialization_cognitive`). Gate-Whitelist entsprechend 5 → 4
(`Reformulation/AxiomGate.lean`).
-/

/-- Theorem F-S (substantielle Form): Form-Inhalt-Vertauschungs-Operativität auf Objekt-Niveau.

    Substantielle Aussage: die Adjunktions-Hom-Bijektion von σ.rel (Morphismus
    L(σ.s) ⟶ σ.k in K) nach σ.s ⟶ R(σ.k) in S ist gleich der γ-vermittelten
    Form: `γ.inv.app σ.s ≫ R.map σ.rel`.

    Dies operiert auf OBJEKT-NIVEAU mit Quantifizierung über `σ : Stellung PAS`.

    Differenzierung von γ-V (Sub-Substanz F, Schärfungs-Stelle 1):
    F-S verwendet die Stellung-Strukturmerkmal-Substanz essentiell (σ.s, σ.k, σ.rel);
    γ-V hat keine Stellung-Quantifizierung. Beide Theoreme sind strukturell verschieden.

    Beweis: vollständig (kein Sorry). Aus `Adjunction.homEquiv_unit` und `naturality_S`.

    Programmatische Verankerung: Form-Stoff-Durchkreuzung (E&W S. 28), operativer
    Ort in der Stellungs-Vielfalt der Trito-Schicht (LZEE Tafel VIII).
-/
theorem form_inhalt_vertauschungs_operativitaet_substantial
    {S K : Type*} [Category S] [Category K]
    (PAS : ProemialAdjunctionSubstantial S K)
    (BC : SubstantialBeckChevalleyData S K PAS)
    (PGM : ProemialGammaMorphismSubstantial PAS BC)
    (σ : Stellung PAS) :
    PAS.adj.homEquiv σ.s σ.k σ.rel =
    PGM.γ.inv.app σ.s ≫ PAS.R.map σ.rel := by
  -- F-S Beweis: Adjunction.homEquiv_unit gibt homEquiv f = unit.app s ≫ R.map f;
  -- naturality_S gibt unit.app s = γ.inv.app s; Kombination ergibt rfl.
  simp only [Adjunction.homEquiv_unit, PGM.naturality_S]
  rfl

/-- Trito-Stellungs-Vielfalt: strukturelle Hypothese für Positions-Relevanz.

    Schicht-Markierung (Schicht-Trennung F-3 / F-2):
    Diese Hypothese operiert auf der Belegungs-Schicht (F-3), nicht auf der
    kenogrammatischen Möglichkeits-Schicht (F-2). Die volle kenogrammatische
    Substanz (Proto/Deutero/Trito als eigenständige Strukturen) bleibt F-2 vorbehalten.

    Schärfungs-Stelle 2 (Speculum F-3-VK-2 Sektion III): präzise Sprach-Form,
    die abstrakt-Funktor-Niveau (Functor.IsEquivalence) und konkret-Belegungs-Niveau
    (TritoStellungsVielfaltExists) verbindet ohne sie zu vermengen.

    Operative Semantik: es gibt eine Stellung σ, an der die Koeinheit der Adjunktion
    NICHT iso ist. Dies ist das strukturelle Hindernis für L.IsEquivalence. Die
    Trito-Schicht (LZEE Tafel VIII via Horistês F-3 Anker 8) trÃ¤gt den
    Trito-Reversibilitäts-Bruch als Quellen-Substanz dieser Hypothese.
-/
def TritoStellungsVielfaltExists
    {S K : Type*} [Category S] [Category K]
    (PAS : ProemialAdjunctionSubstantial S K) : Prop :=
  ∃ (σ : Stellung PAS), ¬ IsIso (PAS.adj.counit.app σ.k)

/-- Theorem α-N (substantielle Form): Adjunktion ist keine Äquivalenz wegen
    Trito-Stellungs-Vielfalt.

    Substantielle Aussage: wenn TritoStellungsVielfaltExists gilt (d.h. es gibt
    eine Stellung σ mit nicht-iso Koeinheit an σ.k), dann ist L keine Äquivalenz
    (`¬ PAS.L.IsEquivalence`).

    Beweis-Strategie: vollständig bewiesen via Mathlib-Instanzen.
    (1) `instance [L.IsEquivalence] : IsIso h.counit` aus `Adjunction.FullyFaithful`
    gibt: L.IsEquivalence → IsIso PAS.adj.counit.
    (2) `instance isIso_app_of_isIso` aus `Mathlib.CategoryTheory.NatIso`
    gibt: IsIso PAS.adj.counit → IsIso (PAS.adj.counit.app σ.k) für alle k.
    (3) Widerspruch mit TritoStellungsVielfaltExists.

    Differenzierung von F-1's adjunction_not_equivalence (B-3-AuflÃ¶sung):
    - F-1: `¬ IsIso PA.adj.unit ∨ ¬ IsIso PA.adj.counit` aus `Or.inl h` (tautologisch).
    - F-3: `¬ PAS.L.IsEquivalence` aus struktureller Hypothese `TritoStellungsVielfaltExists`
      via echtem Mathlib-Instanz-Pfad. Keine Tautologie.

    Programmatische Verankerung (Horistês F-3 Anker 8): Trito-Reversibilitäts-Bruch
    als struktureller Ort, an dem Adjunktion-zur-Äquivalenz nicht aufsteigen kann.
    Quellen-Substanz: Günther E&W S. 26-27 asymmetrische Umtauschrelation.
    Externe Beglaubigung: Gould vs. Conway Morris als Prüfstein für Trito-Bruchstellen.
-/
theorem adjunction_not_equivalence_substantial
    {S K : Type*} [Category S] [Category K]
    (PAS : ProemialAdjunctionSubstantial S K)
    (h_trito : TritoStellungsVielfaltExists PAS) :
    ¬ PAS.L.IsEquivalence := by
  intro hL
  obtain ⟨σ, hσ⟩ := h_trito
  apply hσ
  -- haveI registriert PAS.L.IsEquivalence als lokale Typeclass-Instanz.
  haveI : PAS.L.IsEquivalence := hL
  -- Mathlib instance [L.IsEquivalence] : IsIso h.counit (Adjunction.FullyFaithful Z. 255)
  -- ergibt IsIso PAS.adj.counit.
  haveI : IsIso PAS.adj.counit := inferInstance
  -- Mathlib instance isIso_app_of_isIso (NatIso Z. 165)
  -- ergibt IsIso (PAS.adj.counit.app σ.k).
  exact inferInstance

end Reformulation.Proemial.Substantial
