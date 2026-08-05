import Reformulation.Proemial.AlphaGammaSubstantialRefined
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-!
# Reformulation.Proemial.AlphaGammaBeckChevalley — F-3.6 BC-Architektur-Niederlegung

Vierte Niederlegungs-Schicht (über F-1, F-3, F-3.4/5). Additiv zu den bestehenden
Dateien; keine Modifikation von `AlphaGammaSubstantial.lean` oder
`AlphaGammaSubstantialRefined.lean`.

Vier Sub-Aufgaben:
- **F-3.6 zentral:** `SubstantialBeckChevalleyData` mit eigenstängiger BC-Konstruktion
  (Pullback-Daten in S und K, bcIso, compat-Feld).
- **F-3.4.b:** `ProemialGammaMorphismTrulyMinimal` ohne BC-Parameter (Bereinigung).
- **F-3.4.a:** `ProemialGammaMorphismTrulyMinimal.toSubstantial`-Rückweg.
- **F-3.5.a:** zwei Aussagen, in F-3.6.a.3 als falsch erwiesen und per
  Option-B-Bereinigung entfernt — siehe Memorial-Block unten.

Spec: F3_6_Sub_Spec.md. Prompt: F3_6_Sub_Prompt.md. Frühjahr 2026.

## Klasse-B-Befunde

**B-1 — HasPullbacks-Modul:** `HasPullbacks` liegt in
`Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback` (kein
`Shapes/Pullbacks.lean` in dieser Mathlib-Version; Pullbacks sind in
`Shapes/Pullback/`-Unterverzeichnis aufgeteilt). Import entsprechend angepasst.

## Sorry-Bilanz

- `SubstantialBeckChevalleyData`: 0 Sorries (Struktur).
- `ProemialGammaMorphismTrulyMinimal`: 0 Sorries (Struktur).
- `ProemialGammaMorphismMinimal.toTrulyMinimal`: 0 Sorries (triviale Projektion).
- `ProemialGammaMorphismTrulyMinimal.toSubstantial`: 0 Sorries.
- `TritoStellungsVielfaltExists_does_not_imply_substantial`: ENTFERNT
  (F-3.6.a.3 Option-B-Bereinigung; Memorial-Block unten).
- `rel_not_through_counit`: ENTFERNT (F-3.6.a.3 Option-B-Bereinigung;
  Memorial-Block unten).
- `beck_chevalley_verschraenkung_truly_substantial`: 0 Sorries.
-/

/-! ## Beck-Chevalley-Konstruktion — Begründungs-Block

Die eigenstängige BC-Konstruktion mit Pullback-Daten in S und K
ist PKL-Konstruktion mit hermeneutischer Substantierung.

**Methodologische Markierung:** Günther trägt Beck-Chevalley-Verträglichkeit
nicht explizit. Die SubstantialBeckChevalleyData-Substanz ist konstruktiv-
strukturlogisch substantiiert, nicht aus Günther aufgenommen.

**Hermeneutische Verankerung** (Hermeneutes F-3.6 Sektion IV-V):
- E&W S. 28 erster Absatz: Form-Stoff-Durchkreuzung als zentrale Pointe;
- E&W S. 28 Schluss-Absatz: folglich-Verbindung der drei Heterarchien
  (Form-Stoff — Subjekt-Objekt — Wollen-Erkennen);
- LZEE-Substanz (Stellungs-Vielfalt) vermittelt durch Florenz-Fund
  und Horistês F-3-VK-1-Anker 4, 5, 8.

**Programmatische Verankerung** (Horistês F-3.6 Sektion III-V):
- Anker 5 substantialisiert in zwei Pullback-Strukturen (statt
  endofunktorial-kollabiert in Option a);
- Schicht-Trennung F-3/F-2 sauber gehalten;
- Falsifikations-Stelle 1 (F-3-VK-2) empirisch bewährbar in dieser
  Niederlegung.

**Methodische Konsequenz** (Speculum F-3.6 Sektion VII):
ZWEITE PKL-Konstruktion nach der Belegungs-Wahl. Sie hält die zwei
Kategorien S ≠ K als zwei und trägt das compat-Feld als operative
Verbindung zwischen BC-Verträglichkeit und Adjunktions-Substanz.

**Externe Beglaubigungs-Stellen:**
- Mathlib: CategoryTheory.Limits.Shapes.Pullback.HasPullback (HasPullbacks);
  CategoryTheory.NatIso; CategoryTheory.Adjunction.Basic;
- Günther E&W S. 26-28; LZEE Tafel VIII;
- McCullochs Heterarchische Regel; Gould-Conway-Morris (Florenz-Fund);
- F-3.6-VK-Schluss-Notiz mit vierschichtiger Substantierung.

**Alternative Architektur** (F-3.6-VK Option a, methodisch geprüft
und nicht gewählt): Spezialfall-Ableitung aus ModalTwoCategoryWithPullbacks
für S = K = 𝒯. Kollabiert die Spiegelbild-Pointe Günthers zur
Endo-Konfiguration. Strukturell-hermeneutisch günther-fern.
-/

namespace Reformulation.Proemial.Substantial.BeckChevalley

open CategoryTheory CategoryTheory.Limits
open Reformulation.Proemial.Substantial
open Reformulation.Proemial.Substantial.Refined

-- Kürzel für den alten (F-3) BC-Stub, um Namens-Kollisionen eindeutig aufzulösen.
private abbrev OldBC := Reformulation.Proemial.Substantial.SubstantialBeckChevalleyData

-- ============================================================
-- Phase 1 — F-3.6 zentral: SubstantialBeckChevalleyData (neu)
-- ============================================================

/-- Substantial Beck-Chevalley data für die α+γ-Form in der
    zwei-Kategorien-Konfiguration. Vierte Niederlegungs-Schicht.

    F-3.6-Kernstruktur: löst F-3-Korrektur-Notiz Schwäche 4
    (BC.bcIso als konzeptionelle Leerstelle) auf. Die Struktur trägt:
    - Pullback-Strukturen auf S und K (operative Pullback-Daten).
    - Den BC-Iso bcIso : L⋙R ≅ 𝟭 S als konstruierte Substanz.
    - Das compat-Feld: bcIso.inv = adj.unit komponentenweise
      (operative Verbindung zwischen BC-Verträglichkeit und
      Adjunktions-Substanz).

    Programmatische Verankerung (Horistês F-3-VK-1 Anker 5;
    F-3.6-VK Schärfung 1): die zwei Pullback-Strukturen tragen
    die zwei Pfeil-Richtungen (emanativ auf S, evolutiv auf K)
    als strukturell verschieden, nicht endofunktorial kollabiert.
    Das compat-Feld substantialisiert die folglich-Verbindung der
    drei Heterarchien (E&W S. 28 Schluss-Absatz).

    Methodologische Markierung (F-3.6-VK Sektion IV):
    ZWEITE PKL-Konstruktion nach der Belegungs-Wahl
    (L-emanativ-kognitiv, R-evolutiv-volitiv). Konsistenz mit
    Begründungs-Block (Sektion oben).
-/
structure SubstantialBeckChevalleyData (S K : Type*) [Category S] [Category K]
    (PAS : ProemialAdjunctionSubstantial S K) where
  /-- Pullback-Struktur auf S (emanative Seite). -/
  pullback_S : HasPullbacks S
  /-- Pullback-Struktur auf K (evolutive Seite). -/
  pullback_K : HasPullbacks K
  /-- Der BC-Iso: L⋙R ≅ 𝟭 S als konstruierte Substanz
      (nicht Platzhalter wie in F-3-Stub). -/
  bcIso : PAS.L ⋙ PAS.R ≅ 𝟭 S
  /-- Verträglichkeit: bcIso.inv = adj.unit komponentenweise.
      Operative Verbindung zwischen BC-Verträglichkeit und
      Adjunktions-Substanz (parallel zu naturality_S in PGMm). -/
  compat : ∀ s, bcIso.inv.app s = PAS.adj.unit.app s

-- ============================================================
-- Phase 2 — F-3.4.b: ProemialGammaMorphismTrulyMinimal
-- ============================================================

/-- Proemialer γ-Morphismus in der wirklich minimalen Form.

    Refactoring von ProemialGammaMorphismMinimal (F-3.4/5):
    der BC-Parameter wird gestrichen, weil er als Phantom-Parameter
    erschien (kein Feld der Struktur trägt BC-Daten).

    F-3.4.b architektonische Bereinigung: nur γ und naturality_S
    als unabhängige Daten, ohne BC-Parameter-Mitführung.

    Methodologische Markierung (F-3.4/5-Korrektur-Notiz II.1):
    Felder einer Struktur sollten unabhängige Daten tragen.
    `ProemialGammaMorphismMinimal` (F-3.4) wird damit als transitionale
    Form markiert; `TrulyMinimal` ist die finale saubere Form.

    Theorem-Differenzierungs-Prüfung (Sub-Substanzen F + G):
    — Syntaktisch: verschieden von Minimal (kein BC-Parameter).
    — Mathematisch: eigenstängige konzeptuelle Substanz;
      BC-Parameter-Bereinigung trägt strukturelle Substanz
      (nicht nur Namens-Differenz).
-/
structure ProemialGammaMorphismTrulyMinimal {S K : Type*} [Category S] [Category K]
    (PAS : ProemialAdjunctionSubstantial S K) where
  /-- Der natürliche Isomorphismus γ: L⋙R ≅ 𝟭 S. -/
  γ : PAS.L ⋙ PAS.R ≅ 𝟭 S
  /-- Naturalität in der S-Achse: adj.unit = γ.inv komponentenweise. -/
  naturality_S : ∀ (s : S), PAS.adj.unit.app s = γ.inv.app s

/-- Brücke: ProemialGammaMorphismMinimal (F-3.4, mit Phantom-BC) →
    ProemialGammaMorphismTrulyMinimal (F-3.6, ohne BC).

    Trivialer Def via Field-Projektion: γ und naturality_S sind
    gemeinsame Felder. BC-Parameter geht nicht ein — Phantom-Charakter
    bestätigt durch diese Brücke.
-/
def ProemialGammaMorphismMinimal.toTrulyMinimal
    {S K : Type*} [Category S] [Category K]
    {PAS : ProemialAdjunctionSubstantial S K}
    {BC_old : OldBC S K PAS}
    (PGMm : ProemialGammaMorphismMinimal PAS BC_old) :
    ProemialGammaMorphismTrulyMinimal PAS where
  γ := PGMm.γ
  naturality_S := PGMm.naturality_S

-- ============================================================
-- F-3.4.a: TrulyMinimal.toSubstantial — Rückweg
-- ============================================================

/-- Brücke: ProemialGammaMorphismTrulyMinimal → ProemialGammaMorphismSubstantial (F-3).

    Mit `naturality_K` ableitbar aus `naturality_S` plus rechter
    Dreieck-Identität (via `naturality_K_from_S` aus F-3.4), sind
    TrulyMinimal und Substantial äquivalente Datenpakete.

    Programmatische Verankerung (F-3.4/5-Korrektur II.2):
    "Der natürliche Rückweg schließt die strukturelle Lücke."

    Methodologische Substanz: TrulyMinimal und Substantial sind Iso
    im Kategorie-Sinn (zwei Datenpakete mit gleicher Information).

    Technische Anmerkung: `naturality_K_from_S` (aus F-3.4) erwartet
    eine `ProemialGammaMorphismMinimal PAS BC_old` mit dem alten F-3-Stub.
    Wir konstruieren ihn inline via `⟨BC.bcIso⟩` als OldBC-Zeuge.
-/
def ProemialGammaMorphismTrulyMinimal.toSubstantial
    {S K : Type*} [Category S] [Category K]
    {PAS : ProemialAdjunctionSubstantial S K}
    (BC : SubstantialBeckChevalleyData S K PAS)
    (PGMt : ProemialGammaMorphismTrulyMinimal PAS) :
    Reformulation.Proemial.Substantial.ProemialGammaMorphismSubstantial PAS ⟨BC.bcIso⟩ where
  γ := PGMt.γ
  naturality_S := PGMt.naturality_S
  naturality_K := fun k =>
    @Reformulation.Proemial.Substantial.Refined.naturality_K_from_S
      S K _ _ PAS ⟨BC.bcIso⟩
      { γ := PGMt.γ, naturality_S := PGMt.naturality_S } k
  bc_compat := trivial

-- ============================================================
-- Phase 3/4 (F-3.5.a) — MEMORIAL-BLOCK (F-3.6.a.3 Option-B-Bereinigung)
-- ============================================================

/-! ## Memorial-Block: zwei entfernte, als falsch erwiesene Aussagen

**Dokumentierte einmalige Bereinigungs-Ausnahme von der additiven Disziplin**
(F-3.6.a.3, Option B gemäß F3_6a2_a3_Sub_Spec Sektion VIII): die additive
Disziplin schützt bewährte Substanz vor Überschreibung — sie ist kein
Bestandsschutz für als falsch erwiesene Aussagen. Eng begrenzt: nur die zwei
folgenden Theorem-Statements samt Doc-strings wurden entfernt; alle übrigen
Bestände dieser Datei sind byte-identisch erhalten.

**Entfernte Aussage 1** (F-3.5.a Teil 1, stand hier mit Sorry):

```
  theorem TritoStellungsVielfaltExists_does_not_imply_substantial
      {S K : Type*} [Category S] [Category K] :
      ∃ (PAS : ProemialAdjunctionSubstantial S K),
        TritoStellungsVielfaltExists PAS ∧
        ¬ TritoStellungsVielfaltExists_substantial PAS
```

*Falschheits-Grund:* das bezeugende PAS existiert NIE. Zu jeder Stellung σ₀
mit nicht-iso Koeinheit ist die Koeinheits-Stellung
⟨R(σ₀.k), σ₀.k, counit.app σ₀.k⟩ ein substantieller Zeuge — beide
Konjunktions-Glieder fallen an ihr zusammen (Quantoren-Fehler der
F-3.4/5-Bewertung Sektion II.5; Spec-Stopp-Befund der Zeugen-Einheit).
*Positive Ersetzung:* `tritoStellungsVielfalt_implies_substantial` und
`tritoStellungsVielfalt_iff_substantial` (AlphaGammaWitnesses.lean).
*Formaler Negations-Anker:* `does_not_imply_is_false`
(AlphaGammaTransport.lean).

**Entfernte Aussage 2** (F-3.5.a Teil 2, stand hier mit Sorry):

```
  theorem rel_not_through_counit
      {S K : Type*} [Category S] [Category K]
      {PAS : ProemialAdjunctionSubstantial S K}
      (BC : SubstantialBeckChevalleyData S K PAS)
      (σ : Stellung PAS)
      (h_rel_not_iso : ¬ IsIso σ.rel) :
      ¬ ∃ (u : PAS.L.obj σ.s ⟶ PAS.L.obj (PAS.R.obj σ.k)),
          σ.rel = u ≫ PAS.adj.counit.app σ.k
```

*Falschheits-Grund:* die Faktorisierung existiert IMMER — mit dem Zeugen
u := L.map (adj.homEquiv σ.s σ.k σ.rel) ist die Gleichung die
Standard-Koeinheits-Zerlegung der Adjunktion (homEquiv_counit), unabhängig
von jeder Iso-Hypothese an σ.rel. Die ursprüngliche Sub-Substanz H
(counit-Faktorisierungs-Bruch) war damit mathematisch falsch; ihre
modifizierte Form trägt AlphaGammaRelPullback.lean (Pfad D).
*Positive Ersetzung:* `rel_factors_through_counit` (AlphaGammaTransport.lean).
*Formaler Negations-Anker:* `rel_not_through_counit_is_false`
(AlphaGammaTransport.lean).

Sorry-Bestand des Projekts durch diese Bereinigung: 6 → 4
(verbleibend: F3e ×2, F-1 ×1, F-3 γ-V ×1).
-/

-- ============================================================
-- Phase 4 — γ-V-Substantialisierung
-- ============================================================

/-- Theorem γ-V in der wirklich substantiellen Form (BC explizit konstruiert).

    F-3-Korrektur-Notiz Schwäche 4 aufgelöst: BC.bcIso ist nicht mehr
    Stub-Platzhalter, sondern explizit mit compat-Feld konstruiert.
    γ-V wird durch compat-Substanz plus naturality_S beweisbar —
    kein Sorry mehr (anders als `beck_chevalley_verschraenkung_substantial`
    in F-3, welches Sorry trägt).

    Beweis-Substanz (Iso-Inversions-Eindeutigkeit):
    Aus naturality_S: γ.inv.app s = adj.unit.app s.
    Aus compat: bcIso.inv.app s = adj.unit.app s.
    Also: γ.inv.app s = bcIso.inv.app s (call it `hinv`).
    Via Epi-Kanzelierung: γ.inv.app s ist Epi (da Iso);
    aus γ.inv ≫ γ.hom = 𝟙 = bcIso.inv ≫ bcIso.hom und `hinv`:
    γ.inv ≫ γ.hom = γ.inv ≫ bcIso.hom → γ.hom = bcIso.hom.
    Via Iso.ext: γ = bcIso.

    Theorem-Differenzierungs-Prüfung (Sub-Substanzen F + G):
    — Syntaktisch: NatIso-Gleichheit auf Funktor-Niveau (verschieden
      von naturality_S und compat, die komponentenweise Prop-Gleichheit
      tragen).
    — Mathematisch: eigenstängige Substanz durch Iso-Inversions-
      Eindeutigkeit (Epi-Kanzelierung). Kein Definitions-Korollar.
-/
theorem beck_chevalley_verschraenkung_truly_substantial
    {S K : Type*} [Category S] [Category K]
    {PAS : ProemialAdjunctionSubstantial S K}
    (BC : SubstantialBeckChevalleyData S K PAS)
    (PGMt : ProemialGammaMorphismTrulyMinimal PAS) :
    PGMt.γ = BC.bcIso := by
  apply Iso.ext
  ext s
  -- Ziel: PGMt.γ.hom.app s = BC.bcIso.hom.app s
  -- Schritt 1: γ.inv.app s = bcIso.inv.app s
  -- Schritt 1: γ.inv.app s = bcIso.inv.app s (aus naturality_S + compat)
  -- naturality_S s : adj.unit = γ.inv; compat s : bcIso.inv = adj.unit
  -- γ.inv = adj.unit (symm) = bcIso.inv (symm of compat)
  have hinv : PGMt.γ.inv.app s = BC.bcIso.inv.app s :=
    (PGMt.naturality_S s).symm.trans (BC.compat s).symm
  -- Schritt 2: γ.inv.app s ist Epi (weil Iso)
  haveI : IsIso (PGMt.γ.inv.app s) := inferInstance
  -- Schritt 3: Epi-Kanzelierung
  apply (cancel_epi (PGMt.γ.inv.app s)).mp
  have lhs : PGMt.γ.inv.app s ≫ PGMt.γ.hom.app s = 𝟙 s :=
    Iso.inv_hom_id_app PGMt.γ s
  have rhs : PGMt.γ.inv.app s ≫ BC.bcIso.hom.app s = 𝟙 s := by
    rw [hinv]; exact Iso.inv_hom_id_app BC.bcIso s
  exact lhs.trans rhs.symm

/-! **Wachen (Wachenspitze Stufe 2).** Ist-Ausgabe des gruenen Builds (v4.30.0-rc2).
Gewacht ist der Satz, der den Begriff dieser Datei benennt. **Ermessensauswahl:** keine
Quelle des Strangs benennt diesen Satz; er traegt den Begriff, fuer den seine Datei steht.
Die Marke steht hier und nicht nur im Spezifikationskorpus, damit ein spaeterer Zug mit
besserer Grundlage erkennen kann, was er umstuft. Das Profil traegt `Classical.choice` aus
der Kategorien-Maschinerie; der Weg des Axioms in den Term ist **nicht** gemessen
(`CLAUDE.md` §8 Fallstrick 10). -/

/--
info: 'Reformulation.Proemial.Substantial.BeckChevalley.beck_chevalley_verschraenkung_truly_substantial' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms beck_chevalley_verschraenkung_truly_substantial


end Reformulation.Proemial.Substantial.BeckChevalley
