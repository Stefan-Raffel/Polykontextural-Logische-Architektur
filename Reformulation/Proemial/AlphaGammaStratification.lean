import Reformulation.Proemial.AlphaGammaTransport

/-!
# Reformulation.Proemial.AlphaGammaStratification — F-3.6.a.5 Schicht-Formalisierungs-Einheit

Achte Niederlegungs-Schicht (über F-1, F-3, F-3.4/5, F-3.6, F-3.6.a, F-3.6.a.1+b,
F-3.6.a.2+3) — die Schichtung selbst als Gegenstand: Lean-Niederlegung der
Weichen-Entscheidung Lesart A′ (VK Stelle 1 + a.4).

Vier Stufen:

1. **Zentrum-Lemma** `unit_isIso_of_natIso` (Konditionalitäts-Auflösung): die
   Existenz IRGENDEINES NatIso L ⋙ R ≅ 𝟭 S erzwingt die punktweise iso Einheit.
2. **Vorbehalts-Korollar** `unit_isIso_of_bcData`: jede BC-Instanz erzwingt die
   punktweise iso Einheit — der Vorbehalt liegt am TYP des bcIso-Felds.
3. **Schicht-Selektions-Theorem**: Konstruktion `bcDataOfUnitIso` (Rückrichtung)
   plus Charakterisierung `bcData_nonempty_iff_unit_isIso`.
4. **Negativ-Lemma** `prodHomWitness_not_bcData`: über prodHomWitnessPAS
   existieren KEINE BC-Daten — prodHomWitness formal als Kontrast-Zeuge.

Bestands-Berührung dieses Zuges, hier abschließend aufgezählt und genau eine: die
zweite dokumentierte Bereinigungs-Ausnahme (eine falsche Doc-string-Zeile an
`prodHomWitness_counit_epi` in AlphaGammaTransport.lean, ersetzt mit
Memorial-Kommentar — siehe dort). Der Zug liegt vor der Versionsgeschichte; ein
Commit, der ihn eingrenzte, gibt es nicht — die Datei betritt das Repositorium
mit dem Wurzel-Commit 0085d09. Nachprüfbar ist die Aussage darum an der Spec
unten und am Gegenstück in AlphaGammaTransport.lean, nicht an einem Diff.

Spec: F3_6a5_Sub_Spec.md. Prompt: F3_6a5_Sub_Prompt.md. Frühjahr 2026.

## Klasse-B-Befunde

**B-1 (positiv) — Mathlib trägt das Zentrum-Lemma:** `Adjunction.isIso_unit_of_iso`
(Mathlib.CategoryTheory.Monad.Adjunction) beweist `IsIso adj.unit` aus
`i : L ⋙ R ≅ 𝟭 C` — über Monaden-Transport (`adj.toMonad.transport i`), nicht
über die Zentrum-Rechnung. Da die Weichen-Entscheidung konditional auf der
Lean-Niederlegung der ZENTRUM-Rechnung ruht (VK-Schluss-Notiz Sektion V), ist
das Zentrum-Lemma hier mit der eigenen Rechnung aus Spec II.1 bewiesen; der
Mathlib-Parallelweg ist als unabhängige Bestätigung dokumentiert, nicht als
Beweis-Substanz verwendet.

**B-2 — Naturalitäts-Richtung und 𝟭-Normalformen in Schritt 2:** die
unit-Naturalität wird in der ←-Richtung an der vor-assoziierten Form gebraucht
(`← Category.assoc`, dann `← NatTrans.naturality`); `Functor.id_obj`/
`Functor.id_map`/`Functor.comp_obj` sind als simp-only-Normalisierungen
VOR dem Dreieck nötig, damit `right_triangle_components` syntaktisch greift
(die Spec-Antizipation Functor.comp_map-Normalformen traf die Stelle, die
Richtung war die obj-Seite).

**B-3 — NatTrafo-zu-Iso-API wie sondiert:** `NatIso.isIso_of_isIso_app`
(explizit KEINE Instanz — Loop-Gefahr mit `isIso_app_of_isIso`, Mathlib-
Kommentar) plus `asIso`; compat der Rückrichtung ist `rfl`-nah
(`Iso.symm_inv` + `asIso_hom`, per simp).

**B-4 — unit-Form der Tensor-Adjunktion (B-2*-Folge):**
`(Types.tensorProductAdjunction X).unit = { app Z := ↾fun z ↦ ↾fun x => ⟨x, z⟩ }`
— doppelte ↾-Promotion (äußerer Hom UND Bild-Element sind Hom-Wrapper).
Auswertung durch beide Wrapper ist rfl-defeq; das Gegen-Element braucht die
↾-Promotion und die Anwendung `ConcreteCategory.hom g false` (B-2*-Bestand).

**B-5 — IsEmpty-Konvention für Struktur-Typen:** `IsEmpty` via
`⟨fun BC => absurd …⟩`-Form (refine ⟨fun BC => ?_⟩); kein Sonder-API nötig.

## Sorry-Bilanz

- Stufe 1 (Zentrum-Lemma): 0 Sorries.
- Stufe 2 (Vorbehalts-Korollar): 0 Sorries.
- Stufe 3 (Konstruktion + Charakterisierung): 0 Sorries.
- Stufe 4 (Negativ-Lemma): 0 Sorries.
- Gesamt: 0 Sorries.
-/

/-! ## Schicht-Markierung (Lesart A′ — VK Stelle 1 + a.4)

Die BC-Struktur selektiert die EMANATIV-REVERSIBLE SCHICHT (Schicht-
Selektions-Theorem unten): bewohnt genau bei iso Einheit. Hermeneutische
Verankerung — LZEE S. 23, einschließlich der Schicht-Klausel:

  "Die Relationen selbst sind durch Doppelpfeile dargestellt, womit
  angezeigt werden soll, dass es möglich ist, die Beziehungen in beiden
  Richtungen zu lesen, was im Falle des evolutiven Zusammenhangs nicht
  möglich ist. [...] Prozesse, die nur evolutiven Gesetzen folgen, sind
  irreversibel. Im emanativen Bereich ist das Gegenteil der Fall."
  — und ausdrücklich: "Aber [...] nur für Proto- und Deutero-Struktur."

Die BC-Schicht ist das formale Proto/Deutero-Analogon; die Trito-Substanz
ist F-2-eigenständig (das F-3-Prädikat TritoStellungsVielfaltExists ist
Vor-Substanz der Trito-Schicht). Alle BC-parametrisierten Theoreme
(γ-V, Diagonal-Theorem, Transport-Theorem, Stufen 3/5) gelten auf dieser
Schicht — Schicht-Zugehörigkeit, nicht Defekt-Vorbehalt.

Konditionalitäts-Protokoll: die Weichen-Entscheidung A′ war konditional
auf die Lean-Niederlegung des Zentrum-Lemmas (VK-Schluss-Notiz Sektion V);
mit unit_isIso_of_natIso ist die Konditionalität aufgelöst.
-/

namespace Reformulation.Proemial.Substantial.Stratification

open CategoryTheory CategoryTheory.Limits
open Reformulation.Proemial.Substantial
open Reformulation.Proemial.Substantial.Witnesses

-- Die F-3.6-BC-Struktur (nicht der F-3-Stub gleichen Namens), qualifiziert
-- referenziert wie in AlphaGammaRelPullback.lean / AlphaGammaTransport.lean.
private abbrev BCData := Reformulation.Proemial.Substantial.BeckChevalley.SubstantialBeckChevalleyData

-- ============================================================
-- Stufe 1 — Zentrum-Lemma (Konditionalitäts-Auflösung)
-- ============================================================

/-- ZENTRUM-LEMMA (Konditionalitäts-Auflösung der Architektur-Weiche).

    Die bloße Existenz IRGENDEINES natürlichen Isomorphismus L ⋙ R ≅ 𝟭
    erzwingt bei vorliegender Adjunktion die punktweise iso Einheit —
    der Geltungs-Vorbehalt liegt im bcIso-Feld-TYP, nicht erst in compat
    (VK-Eingang Sektion II; Lesart-B-Eliminierung).

    Beweis: e := unit ≫ θ.hom und seine natürliche Retraktion r leben im
    Zentrum End(𝟭 S) — einem KOMMUTATIVEN Monoid (Naturalitäts-Quadrat an
    der Identität). Links-Inverses ist dort beidseitig: e iso, also unit
    = e ≫ θ.inv iso.

    B-1-Befund: Mathlib trägt die Aussage unabhängig als
    `Adjunction.isIso_unit_of_iso` (Monaden-Transport-Weg); hier ist die
    Zentrum-Rechnung der Spec (II.1) selbst niedergelegt, weil die
    Konditionalität der Weiche AN DIESER RECHNUNG hängt. -/
theorem unit_isIso_of_natIso
    {S K : Type*} [Category S] [Category K]
    (PAS : ProemialAdjunctionSubstantial S K)
    (θ : PAS.L ⋙ PAS.R ≅ 𝟭 S) (s : S) :
    IsIso (PAS.adj.unit.app s) := by
  -- (1) e als ECHTE NatTrans im Zentrum End(𝟭 S); r nur punktweise
  --     (Spec-Hinweis: nur e braucht die Natürlichkeit).
  let e : 𝟭 S ⟶ 𝟭 S := PAS.adj.unit ≫ θ.hom
  let r : s ⟶ s :=
    θ.inv.app s ≫ (PAS.L ⋙ PAS.R).map (θ.inv.app s) ≫
      PAS.R.map (PAS.adj.counit.app (PAS.L.obj s)) ≫ θ.hom.app s
  -- (2) r ist Retraktion von e.app s: vier Umformungen
  --     (hom_inv_id, unit-Naturalität, Dreieck 2, inv_hom_id).
  have key : e.app s ≫ r = 𝟙 s := by
    show (PAS.adj.unit.app s ≫ θ.hom.app s) ≫
        θ.inv.app s ≫ (PAS.L ⋙ PAS.R).map (θ.inv.app s) ≫
          PAS.R.map (PAS.adj.counit.app (PAS.L.obj s)) ≫ θ.hom.app s = 𝟙 s
    rw [Category.assoc, Iso.hom_inv_id_app_assoc]
    -- B-2: die 𝟭-Wrapper sitzen in den IMPLIZITEN Objekt-Argumenten der
    -- Komposition — rw scheitert syntaktisch, erw matcht bis auf defeq
    -- (F29-Bestand: erw für Kompositions-Normalform-Mismatches).
    erw [← Category.assoc, ← PAS.adj.unit.naturality (θ.inv.app s)]
    simp only [Functor.id_obj, Functor.id_map, Functor.comp_obj, Category.assoc,
      Adjunction.right_triangle_components_assoc]
    exact θ.inv_hom_id_app s
  -- (3) Zentrum-Kommutativität: Naturalität von e entlang r : s ⟶ s
  --     gibt wörtlich die Vertauschung — r muss dafür NICHT natürlich sein.
  have comm : r ≫ e.app s = e.app s ≫ r := by
    simpa using e.naturality r
  -- (4) e.app s iso (Links-Inverses ist im Zentrum beidseitig);
  --     Rücktransport: unit.app s = e.app s ≫ θ.inv.app s.
  haveI : IsIso (e.app s) := ⟨r, key, comm.trans key⟩
  have hu : PAS.adj.unit.app s = e.app s ≫ θ.inv.app s := by
    show PAS.adj.unit.app s = (PAS.adj.unit.app s ≫ θ.hom.app s) ≫ θ.inv.app s
    rw [Category.assoc, Iso.hom_inv_id_app, Category.comp_id]
  rw [hu]
  infer_instance

-- ============================================================
-- Stufe 2 — Vorbehalts-Korollar
-- ============================================================

/-- Jede BC-Instanz erzwingt die punktweise iso Einheit (voll-treues L) —
    der II.2-Befund der Transport-Bewertung, via Zentrum-Lemma am TYP des
    bcIso-Felds (nicht am compat-Feld) geführt: schon die bloße Existenz
    des NatIso im Feld-Typ trägt die Erzwingung; compat wird nicht
    verwendet (Lesart-B-Eliminierung). -/
theorem unit_isIso_of_bcData
    {S K : Type*} [Category S] [Category K]
    {PAS : ProemialAdjunctionSubstantial S K}
    (BC : BCData S K PAS) (s : S) :
    IsIso (PAS.adj.unit.app s) :=
  unit_isIso_of_natIso PAS BC.bcIso s

-- ============================================================
-- Stufe 3 — Schicht-Selektions-Theorem (Charakterisierung)
-- ============================================================

/-- Konstruktion (Rückrichtung der Charakterisierung): bei punktweise iso
    Einheit existieren BC-Daten — bcIso als inverse Einheit
    ((asIso adj.unit).symm), compat per Konstruktion (Iso.symm_inv +
    asIso_hom), Pullback-Felder aus den Kontext-Instanzen.

    B-3-Mechanik: `NatIso.isIso_of_isIso_app` ist bewusst KEINE Instanz
    (Loop mit `isIso_app_of_isIso`); via haveI registriert. -/
noncomputable def bcDataOfUnitIso
    {S K : Type*} [Category S] [Category K]
    {PAS : ProemialAdjunctionSubstantial S K}
    [HasPullbacks S] [HasPullbacks K]
    (h : ∀ s, IsIso (PAS.adj.unit.app s)) :
    BCData S K PAS :=
  haveI : ∀ s, IsIso (PAS.adj.unit.app s) := h
  haveI : IsIso PAS.adj.unit := NatIso.isIso_of_isIso_app _
  { pullback_S := inferInstance
    pullback_K := inferInstance
    bcIso := (asIso PAS.adj.unit).symm
    compat := fun s => by simp }

/-- SCHICHT-SELEKTIONS-THEOREM (Lesart A′): SubstantialBeckChevalleyData
    ist bewohnt genau auf der emanativ-reversiblen Schicht — den
    Adjunktionen mit iso Einheit (voll-treuem L). Das Vorbehalts-Lemma in
    seiner positiven Gestalt: die Struktur SELEKTIERT die Schicht, sie
    definiert formal das Proto/Deutero-Analogon (Schicht-Markierungs-Block
    am Modul-Kopf; LZEE S. 23 einschließlich Schicht-Klausel).

    η-Begründungs-Block (vierter Block der Folge): bcIso markiert die
    Zugehörigkeit zur emanativ-reversiblen Schicht; sie ist strukturlogisch
    die inverse Einheit, mit positiver Substanz als Schicht-Selektion
    (Lesart A′). -/
theorem bcData_nonempty_iff_unit_isIso
    {S K : Type*} [Category S] [Category K]
    {PAS : ProemialAdjunctionSubstantial S K}
    [HasPullbacks S] [HasPullbacks K] :
    Nonempty (BCData S K PAS) ↔ ∀ s, IsIso (PAS.adj.unit.app s) :=
  ⟨fun ⟨BC⟩ s => unit_isIso_of_bcData BC s, fun h => ⟨bcDataOfUnitIso h⟩⟩

-- ============================================================
-- Stufe 4 — Negativ-Lemma (Kontrast-Zeuge)
-- ============================================================

/-- rfl-Härtung (parallel zu `tensorProductAdjunction_counit_apply` der
    Transport-Einheit): die Einheit von `Types.tensorProductAdjunction` ist
    das Einsetzen `z ↦ (fun x => (x, z))` — benannte Stelle statt anonymer
    rfl-Abhängigkeit von der Mathlib-Definition (B-4-Befund: doppelte
    ↾-Promotion in der Mathlib-Quelle; Auswertung durch beide Wrapper
    rfl-defeq). -/
theorem tensorProductAdjunction_unit_apply
    {X Y : Type} (z : Y) (x : X) :
    ConcreteCategory.hom ((Types.tensorProductAdjunction X).unit.app Y z) x
      = (x, z) :=
  rfl

/-- Über prodHomWitnessPAS existieren KEINE BC-Daten: die Einheit an
    PUnit (z ↦ fun b => (b, z)) ist nicht surjektiv (Kardinalität 1
    gegen 4), also nicht iso. Zusammen mit `prodHomWitness_tritoVielfalt`
    (Zeugen-Einheit) ist prodHomWitness damit formal der KONTRAST-ZEUGE
    der Schichtung: Trito-geltend, nicht emanativ-reversibel — nicht jede
    Trito-Situation trägt Proto/Deutero-Reversibilität (Lesart A′;
    Bestätigungs-Signal der Hermeneutes-Antwort). Korrigiert formal den
    Stufe-4-Doc-string der Transport-Einheit (zweite Bereinigungs-Ausnahme,
    siehe `prodHomWitness_counit_epi`).

    Gegen-Element: `↾fun _ => (true, PUnit.unit)` hat kein Urbild — jedes
    Bild-Element der Einheit trägt an `false` den Wert `(false, ·)`
    (Auswertungs-rfl, B-4-Mechanik). -/
theorem prodHomWitness_not_bcData :
    IsEmpty (BCData Type Type prodHomWitnessPAS) := by
  refine ⟨fun BC => ?_⟩
  have h := unit_isIso_of_bcData BC PUnit
  rw [isIso_iff_bijective] at h
  -- Nicht-Surjektivität: Urbild des konstanten Gegen-Elements extrahieren …
  obtain ⟨z, hz⟩ := h.2 (↾fun _ => (true, PUnit.unit))
  -- … und an false auswerten: (false, z) = (true, unit) — Widerspruch.
  have happ := congrArg (fun g => (ConcreteCategory.hom g) false) hz
  exact Bool.noConfusion (congrArg Prod.fst happ)

end Reformulation.Proemial.Substantial.Stratification
