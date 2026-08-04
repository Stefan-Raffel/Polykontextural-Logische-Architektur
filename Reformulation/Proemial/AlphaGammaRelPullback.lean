import Reformulation.Proemial.AlphaGammaBeckChevalley
import Mathlib.CategoryTheory.Limits.Shapes.Diagonal

/-!
# Reformulation.Proemial.AlphaGammaRelPullback — F-3.6.a Pullback-getragene rel-Substanz

Fünfte Niederlegungs-Schicht (über F-1, F-3, F-3.4/5, F-3.6). Additiv zu
`AlphaGammaBeckChevalley.lean`; keine Modifikation der bestehenden Dateien.

**Zentrale Substanz:** ein Haupt-Theorem (`rel_pullback_diagonal_not_iso`) plus
Konjunktions-Korollar (`rel_pullback_diagonal_not_both`), die vier substantielle
Anforderungen erfüllen:

- (i)   `h_rel_not_iso : ¬ IsIso σ.rel` wesentlich verwendet
        (binäre Sub-Substanz-H-Bewährung, Sektion VII der Sub-Spec);
- (ii)  `BC.pullback_K` operativ verwendet — die Pullback-Konstruktion
        `pullback σ.rel σ.rel` in K ist nur durch `BC.pullback_K` möglich
        (F-3.6-Schwäche-1-Auflösung: Pullback-Phantom aufgelöst);
- (iii) strukturlogische Konsistenz mit α₂: S ≠ K als zwei Kategorien gehalten;
- (iv)  Substanz auf Objekt-Niveau (Pullback-Substanz in K), parallel zur
        γ-V-Substanz auf Funktor-Niveau.

Spec: F3_6a_Sub_Spec.md. Prompt: F3_6a_Sub_Prompt.md. Frühjahr 2026.

## Klasse-B-Befunde

**B-1 — Pullback-Diagonal-API:** Die Diagonal-Konstruktion liegt in
`Mathlib.CategoryTheory.Limits.Shapes.Diagonal` (nicht im
`Shapes/Pullback/`-Unterverzeichnis): `pullback.diagonal f : X ⟶ pullback f f`
mit `[HasPullback f f]`-Instanz-Anforderung, `pullback.diagonal_fst/snd`,
Instanz `IsSplitMono (diagonal f)`.

**B-2 — Mono/Iso-Verbindung direkt vorhanden:** `pullback.isIso_diagonal_iff :
IsIso (diagonal f) ↔ Mono f` (Diagonal.lean Zeile 66). Kein eigener Hilfssatz
nötig; der antizipierte Befund „Mathlib-Hilfssatz erforderlich" löst sich
positiv auf.

**B-3 — BC.pullback_K-Operativität via letI:** `BC.pullback_K : HasPullbacks K`
ist Struktur-Feld, keine Typeclass-Instanz im Kontext. Die Theorem-Aussage
selbst verlangt die `HasPullback σ.rel σ.rel`-Instanz (für `pullback.diagonal`).
Operative Form: `letI : HasPullbacks K := BC.pullback_K` im Theorem-Statement —
die Pullback-Substanz der Aussage ist damit wörtlich von BC.pullback_K getragen
(stärkste Form der Operativität: nicht nur der Beweis, schon die *Aussage*
existiert nur durch BC.pullback_K).

**B-4 — Theorem-Form-Korrektur (Mathematiker-Selbst-Korrektur, Sub-Substanz F
Schicht 4):** Die Vorschlag-Form der Sub-Spec Sektion VI.1 („wenn σ.rel nicht
iso, ist die Diagonal-Abbildung nicht iso") ist mathematisch NICHT haltbar:
`¬ IsIso σ.rel` impliziert nicht `¬ Mono σ.rel` (Gegenbeispiel: jedes
nicht-iso Monomorphismus hat iso Diagonale, etwa ℕ ↪ ℤ in Type). Die
korrigierte Form trägt `IsSplitEpi σ.rel` als Zusatzhypothese:
`¬ IsIso σ.rel` + `IsSplitEpi σ.rel` ⟹ `¬ Mono σ.rel`
(via `isIso_of_mono_of_isSplitEpi`) ⟹ `¬ IsIso (diagonal σ.rel)`
(via `isIso_diagonal_iff`). Die binäre Bewährungs-Prüfung bleibt intakt:
ohne `h_rel_not_iso` ist die Aussage falsch (𝟙 ist split-epi mit iso
Diagonale), der Beweis kann ohne die Hypothese nicht kompilieren.

## Sorry-Bilanz

- `rel_pullback_diagonal_not_iso`: 0 Sorries (vollständiger Beweis).
- `rel_pullback_diagonal_not_both`: 0 Sorries (vollständiger Beweis).
- Gesamt: 0 Sorries.

## Binäre Sub-Substanz-H-Bewährungs-Prüfung (Sektion IV des Sub-Prompts)

Durchgeführt nach Theorem-Niederlegung: Hypothese `h_rel_not_iso`
auskommentiert, Build laufen lassen. Befund in F3_6a_Implementation_Final.md
dokumentiert.
-/

/-! ## Pullback-getragene rel-Substanz — Begründungs-Block (dritte PKL-Konstruktion)

Die rel-Substantialisierung über Pullback-Universalität ist PKL-Konstruktion
mit hermeneutischer Substantierung. Es ist die DRITTE PKL-Konstruktion nach
der Belegungs-Wahl (L-emanativ-kognitiv) und der BC-Architektur (Option b
mit eigenständiger Pullback-Substanz).

**Methodologische Markierung:** Günther trägt Pullback-Universalität als
operative Substanz für die Stellungs-rel-Substanz nicht explizit. Die
rel-Pullback-Substantialisierung ist konstruktiv-strukturlogisch substantiiert
aus der Mathematiker-Vor-Prüfung der F-3.6-Bewertungs-Substanz (siehe
F-3.6.a-VK-Schluss-Notiz Sektion III) und der drei Standort-Substantierungen
in der F-3.6.a-Vor-Klärungs-Sub-Sub-Sitzung.

DRITTE PKL-Konstruktion (nach Belegungs-Wahl und BC-Architektur).
Methodologisch konstruktiv-strukturlogisch substantiiert.
Vierte Lesart: MODIFIZIERTE Sub-Substanz H, nicht ursprüngliche.

**Hermeneutische Verankerung** (Hermeneutes F-3.6.a Sektion V und VII):
- Verschränkungs-Substanz auf Objekt-Niveau, parallel zur γ-V-Substanz
  auf Funktor-Niveau;
- Pullback als universelle Form der Verschränkung zweier Pfeile mit
  gemeinsamem Ziel;
- rel als positions-relevante Verbindung in der Trito-Schicht (LZEE Tafel VIII).

**Programmatische Verankerung** (Horistês F-3.6.a Sektion VIII):
- Volle Anker-5-Substantialisierung (zwei Pullback-Strukturen für zwei
  Pfeil-Richtungen) versus partielle Substantialisierung in Pfad B;
- Direkte BC-Konvergenz (BC.pullback_K wird operativ);
- Substantielle Schicht-Trennung F-3/F-2 durch saubere Anwesenheit;
- Konsistente Stellungs-Architektur in F-3.6 — keine Asymmetrie zwischen
  BC-Architektur (Pullback) und Sub-Substanz H (non-Pullback).

**Methodologische Konsequenz** (Speculum F-3.6.a Sektion III):
- Sub-Substanz F Schicht 4 operiert in EINER Stufe — die Spec trägt
  die Substanz, die Implementation verifiziert sie ohne erneute
  Substanz-Verschiebung;
- Asymmetrie-Auflösung der dritten Iterations-Schicht der F-3-Folge-
  Iterations-Sequenz (nicht Vertiefung);
- Binäre Bewährungs-Disziplin substantiell-direkt (Pullback-Substanz
  erzwingt strukturlogische rel-Bedingungen).

**Externe Beglaubigungs-Stellen:**
- Mathlib: HasPullbacks, CategoryTheory.Limits.Shapes.Diagonal
  (pullback.diagonal, isIso_diagonal_iff);
- Günther: E&W S. 25-28 (Stellungs-Substanz), LZEE Tafel VIII (positions-
  relevante Verteilungs-Substanz);
- McCullochs Heterarchische Regel; Gould-Conway-Morris (Florenz-Fund);
- F-3.6.a-VK-Schluss-Notiz mit 15 substantiellen Schichten;
- F-3.6-Bewertung Sektion II.1 (Pullback-Phantom-Befund, in dieser
  Niederlegung operativ aufgelöst).

**Vierte Lesart als operative Reichweiten-Markierung:**
Die ursprüngliche Sub-Substanz H (Faktorisierungs-Bruch durch counit
in F-3.6-Sub-Spec Sektion VII) war mathematisch falsch — die Faktorisierung
existiert immer durch Adjunktions-Bijektion. Die MODIFIZIERTE Sub-Substanz H
ist Pullback-getragene rel-Substanz mit positions-relevanter Substanz.
Diese Niederlegung trägt die modifizierte Form; die ursprüngliche Form
ist transparent als gescheitert markiert (siehe F-3.6.a-VK-Schluss-Notiz
Sektion IV).

**Konditionale Eskalations-Pfade** (Sub-Spec Sektion V):
- Pfad B (Iso-Korrespondenz) wenn Pfad D in der Implementation nicht trägt;
- Pfad C (Stellungs-Erweiterung) als letzte Eskalation;
- Falsifikations-Stelle 4 wenn keiner der drei Pfade trägt.
-/

namespace Reformulation.Proemial.Substantial.RelPullback

open CategoryTheory CategoryTheory.Limits
open Reformulation.Proemial.Substantial

-- Die F-3.6-BC-Struktur (nicht der F-3-Stub gleichen Namens) wird qualifiziert
-- referenziert, um die Namens-Kollision eindeutig aufzulösen.
private abbrev BCData := Reformulation.Proemial.Substantial.BeckChevalley.SubstantialBeckChevalleyData

-- ============================================================
-- Phase 2/3 — F-3.6.a Haupt-Theorem: rel als Pullback-Operationsstelle
-- ============================================================

/-- F-3.6.a Pfad D: σ.rel als Pullback-Operationsstelle (Diagonal-Form,
    korrigiert um den B-4-Befund).

    Wenn σ.rel split-epi und NICHT iso ist, ist die Diagonal-Abbildung
    `pullback.diagonal σ.rel : L(σ.s) ⟶ pullback σ.rel σ.rel` nicht iso.

    Substantielle Substanz: die Diagonale in den Pullback von σ.rel mit
    sich selbst ist iso genau dann wenn σ.rel mono ist
    (`pullback.isIso_diagonal_iff`). Ein split-epi Mono ist iso
    (`isIso_of_mono_of_isSplitEpi`) — also erzwingt `h_rel_not_iso`,
    dass die Diagonale nicht iso sein kann. σ.rel trägt damit eine
    Pullback-Universalitäts-Substanz, die `h_rel_not_iso` wesentlich
    verwendet.

    Vier-Anforderungs-Prüfung (Sub-Spec Sektion III.1):
    (i)   `h_rel_not_iso` wesentlich: der Widerspruchs-Kern des Beweises;
          ohne die Hypothese ist die Aussage FALSCH (σ.rel = 𝟙 ist
          split-epi mit iso Diagonale). Binär bewährt.
    (ii)  `BC.pullback_K` operativ: die `letI`-Bindung trägt die
          `HasPullbacks K`-Substanz, ohne die weder Aussage noch Beweis
          existieren (die Pullback-Konstruktion `pullback σ.rel σ.rel`
          in K ist wörtlich BC-getragen).
    (iii) S ≠ K: beide Kategorien generisch gehalten; der Pullback
          operiert in K, die Stellung trägt σ.s in S.
    (iv)  Objekt-Niveau: Aussage über Morphismen/Objekte in K
          (Diagonale in den Pullback), nicht über NatIso auf Funktor-Niveau.

    Theorem-Differenzierungs-Prüfung (Sub-Substanzen F + G + H):
    — Syntaktisch: Nicht-Iso-Aussage über eine Pullback-Diagonale
      (verschieden von allen bisherigen Theoremen; erste Aussage der
      Folge, deren STATEMENT eine Limes-Konstruktion trägt).
    — Mathematisch: Beweis-Tiefe aus isIso_diagonal_iff (Kern-Paar-
      Substanz der Diagonale) plus split-epi/mono-Iso-Schluss.
      Kein Definitions-Korollar.
    — Sub-Substanz-H-Operativität: h_rel_not_iso ist der Widerspruchs-
      Kern, nicht verworfene Hypothese.

    /- Theorem trägt MODIFIZIERTE Sub-Substanz H (Pfad D der F-3.6.a-VK).
       Ursprüngliche Sub-Substanz H (counit-Faktorisierungs-Bruch) ist
       mathematisch falsch und wird hier NICHT formalisiert. -/
-/
theorem rel_pullback_diagonal_not_iso
    {S K : Type*} [Category S] [Category K]
    {PAS : ProemialAdjunctionSubstantial S K}
    (BC : BCData S K PAS)
    (σ : Stellung PAS)
    (h_split : IsSplitEpi σ.rel)
    (h_rel_not_iso : ¬ IsIso σ.rel) :
    letI : HasPullbacks K := BC.pullback_K
    ¬ IsIso (pullback.diagonal σ.rel) := by
  -- BC.pullback_K operativ: trägt die HasPullback-Instanz der Aussage.
  letI : HasPullbacks K := BC.pullback_K
  show ¬ IsIso (pullback.diagonal σ.rel)
  intro h_diag
  apply h_rel_not_iso
  -- Diagonale iso ⟹ σ.rel mono (Mathlib isIso_diagonal_iff, Kern-Paar-Substanz).
  haveI : Mono σ.rel := (pullback.isIso_diagonal_iff σ.rel).mp h_diag
  haveI : IsSplitEpi σ.rel := h_split
  -- Mono + split-epi ⟹ iso — Widerspruch mit h_rel_not_iso.
  exact isIso_of_mono_of_isSplitEpi σ.rel

-- ============================================================
-- Konjunktions-Korollar: Unverträglichkeits-Form
-- ============================================================

/-- F-3.6.a Konjunktions-Korollar: keine Stellung mit nicht-iso Relator
    kann zugleich iso Diagonale und split-epi Relator tragen.

    Äquivalente Umformulierung des Haupt-Theorems als Unverträglichkeits-
    Aussage: `h_rel_not_iso` schließt die Konjunktion
    (Diagonale iso ∧ σ.rel split-epi) aus. Die Stellungs-Konfiguration
    mit nicht-reversiblem Relator (¬ IsIso σ.rel als Positions-Relevanz,
    F-3.5-Substanz) ist strukturell unverträglich mit der vollen
    Pullback-Reversibilität (iso Diagonale + Spaltung).

    /- Theorem trägt MODIFIZIERTE Sub-Substanz H (Pfad D der F-3.6.a-VK).
       Ursprüngliche Sub-Substanz H (counit-Faktorisierungs-Bruch) ist
       mathematisch falsch und wird hier NICHT formalisiert. -/
-/
theorem rel_pullback_diagonal_not_both
    {S K : Type*} [Category S] [Category K]
    {PAS : ProemialAdjunctionSubstantial S K}
    (BC : BCData S K PAS)
    (σ : Stellung PAS)
    (h_rel_not_iso : ¬ IsIso σ.rel) :
    letI : HasPullbacks K := BC.pullback_K
    ¬ (IsIso (pullback.diagonal σ.rel) ∧ IsSplitEpi σ.rel) := by
  letI : HasPullbacks K := BC.pullback_K
  show ¬ (IsIso (pullback.diagonal σ.rel) ∧ IsSplitEpi σ.rel)
  rintro ⟨h_diag, h_split⟩
  exact rel_pullback_diagonal_not_iso BC σ h_split h_rel_not_iso h_diag

/-! **Wachen.** Ist-Ausgabe des gruenen Builds (v4.30.0-rc2). Gewacht ist der im Kopf
als **Zentrale Substanz** benannte Kern dieser Datei; die Wachenspitze des Strangs ist in
`Wachenspitze_AlphaGamma_Vorgabe.md` begruendet. Das Profil traegt `Classical.choice` aus
der Kategorien- und Pullback-Maschinerie; der Weg des Axioms in den Term ist **nicht**
gemessen (`CLAUDE.md` §8 Fallstrick 10). -/

/--
info: 'Reformulation.Proemial.Substantial.RelPullback.rel_pullback_diagonal_not_iso' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms rel_pullback_diagonal_not_iso


end Reformulation.Proemial.Substantial.RelPullback
