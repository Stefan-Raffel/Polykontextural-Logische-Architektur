import Reformulation.Proemial.AlphaGammaStratification

/-!
# Reformulation.Proemial.AlphaGammaRounding — F-3.6.a.6 Abrundungs-Paket

Neunte Niederlegungs-Schicht (über F-1, F-3, F-3.4/5, F-3.6, F-3.6.a,
F-3.6.a.1+b, F-3.6.a.2+3, F-3.6.a.5) — der erste reine Abrundungs-Zyklus
der Folge. Fünf Inhalte:

0. **Taktik-Konventions-Block** (unten; erstmaliger Einsatz des
   Serien-Gegenmittels).
1. **End-Lemma** `end_id_comm`: das Zentrum End(𝟭 S) ist kommutativ —
   macht die Zentrum-Erzählung von a.5 formal wahr.
2. **Unkonditionale Iff** `bcData_nonempty_iff_unconditional`: alle drei
   Bewohnbarkeits-Flanken ohne Kontext-Instanzen.
3. **Rück-Richtungs-Korollar** `identityWitnessBC'` (via `bcDataOfUnitIso`
   über der Identitäts-Adjunktion) plus compat-Vergleich
   `identityWitnessBC'_bcIso_app_eq` und volle Struktur-Gleichheit
   `identityWitnessBC'_eq_identityWitnessBC` (Prop-Felder + Iso-ext).
4. **Konsistenz-Korollar** `prodHomWitness_not_unconditional`: die
   unkonditionale Iff am prodHomWitness negativ exerziert.

FORM-ENTSCHEIDUNG (Anfügung von Wahrheit statt Änderung): dieses Paket
lebt vollständig in diesem neuen Modul; null Bestands-Berührung (außer
der regulären Aggregat-Nachführung). Die drei Erzähl-Unschärfen von a.5
werden nicht durch Editieren geheilt, sondern durch nebenstehende formale
Einlösung — die Bereinigungs-Ausnahme bleibt Falschheiten vorbehalten,
die Ausnahme-Frequenz bleibt bei zwei.

Spec: F3_6a6_Sub_Spec.md. Prompt: F3_6a6_Sub_Prompt.md. Frühjahr 2026.

## Klasse-B-Befunde

**B-1 (positiv) — Prop-Status der HasPullbacks-Klasse:** `HasPullbacks` ist
in Mathlib4 Prop-wertig (`HasLimitsOfShape` ist eine Prop-Klasse); die
Konjunktion `HasPullbacks S ∧ HasPullbacks K ∧ …` ist zulässig, die
Projektionen aus den Strukturfeldern tragen die Hinrichtung wörtlich.

**B-2 — Instanz-Übergabe via haveI:** die Rückrichtung registriert die
zwei Pullback-Belege per `haveI := hS; haveI := hK`; die @-Form war nicht
nötig (die Instanzen werden nach Registrierung synthetisiert).

**B-3 — Adjunction.id-unit-Defeq trägt:** `Adjunction.id` hat
`unit := 𝟙 (𝟭 Type)`; die Komponente an s ist defeq `𝟙 s` — die
`show IsIso (𝟙 s)`-Reduktion (Konventions-Block-Muster 3) greift durch
die 𝟭⋙𝟭-Wrapper ohne Justierung.

**B-4 — ext-Form des Vergleichs:** Komponenten-Gleichheit per simp
(beide Seiten 𝟙 s; `Adjunction.id` und `Functor.leftUnitor` sind @[simps]);
volle Struktur-Gleichheit via `bcData_ext` (cases + Komponenten-Eq +
Prop-Proof-Irrelevanz für pullback_S/pullback_K/compat) — die volle
Daten-Gleichheit ist billig, das Korollar ist angefügt.

**B-5 — Kommentar-Terminator im Spec-Wortlaut:** die Spec-Formulierung
des Konventions-Block-Musters 1 („𝟭-Wrapper Schrägstrich ⋙-Wrapper")
enthält nach dem Bindestrich des ersten Wrappers die Zeichenfolge, die
Lean-Block-Kommentare schließt, und kann nicht wörtlich in einem
Doc-Block stehen; justiert zu „𝟭- bzw. ⋙-Wrapper" (einzige
Wortlaut-Abweichung, syntaktisch erzwungen).

## Sorry-Bilanz

- Inhalt 1 (End-Lemma): 0 Sorries.
- Inhalt 2 (unkonditionale Iff): 0 Sorries.
- Inhalt 3 (Rück-Richtung + compat-Vergleich + Struktur-Gleichheit): 0 Sorries.
- Inhalt 4 (Konsistenz-Korollar): 0 Sorries.
- Gesamt: 0 Sorries.
-/

/-! ## Taktik-Konventions-Block (Serien-Referenz, eingeführt F-3.6.a.6)

Drei bekannte Muster der Implicit-Arg-Steuer (Belege: F29, cone_objs,
Transport-B-2*, Stratification-B-2):
1. `erw` statt `rw` bei Implicit-Objekt-Mismatch (𝟭- bzw. ⋙-Wrapper in den
   impliziten Argumenten der Komposition).
2. `exact`/term-mode statt simp-Lemma, wo der Schluss defeq ist, aber
   syntaktisch nicht feuert (z. B. Iso.inv_hom_id_app).
3. `show`-Reduktion vor Instanz-Synthese bei Literal-Projektionen
   (z. B. IsIso ⟨…⟩.rel, Adjunction.id-Einheits-Komponenten).
-/

/-! ## Erzähl-Präzisierungen (Anfügung statt Änderung — Form-Entscheidung a.6)

Drei Unschärfen der a.5-Erzählung, hier durch nebenstehende Wahrheit geheilt,
ohne Bestands-Änderung (die Bereinigungs-Ausnahme bleibt Falschheiten
vorbehalten; Ausnahme-Frequenz unverändert zwei):

1. ZENTRUM: Der Beweis von `unit_isIso_of_natIso` (a.5) nutzt die
   End(s)-Zentralität von e.app s (via e.naturality am Morphismus r) — einen
   STÄRKEREN Pfad als die Doc-string-Erzählung vom kommutativen Zentrum
   End(𝟭 S). Das Lemma `end_id_comm` löst die Erzählung formal ein.
2. PULLBACK-RELATIVITÄT: `bcData_nonempty_iff_unit_isIso` (a.5)
   charakterisiert unter [HasPullbacks S] [HasPullbacks K] — die
   unkonditionale Form trägt `bcData_nonempty_iff_unconditional` (hier).
3. FORM-DOKUMENTATION: `tensorProductAdjunction_unit_apply` (a.5) wird von
   keinem Beweis konsumiert; es ist Form-Dokumentation der unit-Gestalt,
   keine Härtung (kein Routing; die rfl-Stellen des Negativ-Lemmas laufen
   defeq). Die treffende Vokabel gilt ab dieser Schicht.
-/

namespace Reformulation.Proemial.Substantial.Rounding

open CategoryTheory CategoryTheory.Limits
open Reformulation.Proemial.Substantial
open Reformulation.Proemial.Substantial.Witnesses
open Reformulation.Proemial.Substantial.Stratification

-- Die F-3.6-BC-Struktur, qualifiziert referenziert wie in
-- AlphaGammaStratification.lean (das dortige BCData ist private).
private abbrev BCData := Reformulation.Proemial.Substantial.BeckChevalley.SubstantialBeckChevalleyData

-- ============================================================
-- Inhalt 1 — End-Lemma (löst Bewertungs-Stelle 3)
-- ============================================================

/-- Das Zentrum End(𝟭 S) ist kommutativ — das Naturalitäts-Quadrat an der
    Identität. Löst die Zentrum-Erzählung des Zentrum-Lemmas (a.5) formal
    ein; der dortige Haupt-Beweis nutzt den STÄRKEREN punktweisen Pfad
    (End(s)-Zentralität von e.app s via e.naturality, ohne Natürlichkeit
    der Retraktion) — siehe Erzähl-Präzisierungs-Block. -/
theorem end_id_comm {S : Type*} [Category S] (α β : 𝟭 S ⟶ 𝟭 S) :
    α ≫ β = β ≫ α := by
  ext s
  -- Muster 2 des Konventions-Blocks: exact statt simp — die 𝟭-map-Form
  -- der Naturalität ist defeq zur Komponenten-Komposition.
  exact β.naturality (α.app s)

-- ============================================================
-- Inhalt 2 — Unkonditionale Iff (löst Bewertungs-Stelle 2)
-- ============================================================

/-- Unkonditionale Charakterisierung: BC-Daten sind bewohnt genau bei
    Pullbacks BEIDERSEITS und punktweise iso Einheit — alle drei Flanken,
    ohne Kontext-Instanzen. Vervollständigt bcData_nonempty_iff_unit_isIso
    (dort pullback-relativ; siehe Erzähl-Präzisierungs-Block). -/
theorem bcData_nonempty_iff_unconditional
    {S K : Type*} [Category S] [Category K]
    (PAS : ProemialAdjunctionSubstantial S K) :
    Nonempty (BCData S K PAS) ↔
      HasPullbacks S ∧ HasPullbacks K ∧ ∀ s, IsIso (PAS.adj.unit.app s) := by
  constructor
  · rintro ⟨BC⟩
    exact ⟨BC.pullback_S, BC.pullback_K, fun s => unit_isIso_of_bcData BC s⟩
  · rintro ⟨hS, hK, h⟩
    haveI := hS; haveI := hK
    exact ⟨bcDataOfUnitIso h⟩

-- ============================================================
-- Inhalt 3 — Rück-Richtungs-Korollar plus compat-Vergleich
-- (löst Bewertungs-Stelle 1 und die alte „Stelle 2-billig")
-- ============================================================

/-- Die Rück-Richtung exerziert: konstruierte BC-Daten über der
    Identitäts-Adjunktion. Schließt die letzte unexerzierte Flanke der
    a.5-Einheit. -/
noncomputable def identityWitnessBC' :
    BCData Type Type identityWitnessPAS :=
  bcDataOfUnitIso (fun s => by
    -- Adjunction.id-Einheit = 𝟙; show-Reduktion: Muster 3.
    show IsIso (𝟙 s)
    infer_instance)

/-- compat-Vergleich: konstruierte und handgebaute BC-Daten stimmen im
    bcIso-Feld komponentenweise überein (beide punktweise 𝟙) — die
    Konstruktion reproduziert den handgebauten Zeugen. -/
theorem identityWitnessBC'_bcIso_app_eq (s : Type) :
    identityWitnessBC'.bcIso.hom.app s = identityWitnessBC.bcIso.hom.app s := by
  simp [identityWitnessBC', identityWitnessBC, bcDataOfUnitIso,
    identityWitnessPAS]

/-- ext-Prinzip der BC-Struktur: zwei BC-Daten mit gleichem bcIso-Feld
    sind gleich — die übrigen Felder (pullback_S, pullback_K, compat)
    sind Prop-wertig (B-1/B-4-Befund: Proof-Irrelevanz). -/
theorem bcData_ext
    {S K : Type*} [Category S] [Category K]
    {PAS : ProemialAdjunctionSubstantial S K}
    {BC₁ BC₂ : BCData S K PAS} (h : BC₁.bcIso = BC₂.bcIso) :
    BC₁ = BC₂ := by
  cases BC₁; cases BC₂; cases h; rfl

/-- Volle Struktur-Gleichheit (billiges Korollar, da die übrigen Felder
    Prop-wertig sind): die Konstruktion `bcDataOfUnitIso` reproduziert
    über der Identitäts-Adjunktion EXAKT den handgebauten Zeugen der
    Zeugen-Einheit — volle Daten-Gleichheit, nicht nur komponentenweise. -/
theorem identityWitnessBC'_eq_identityWitnessBC :
    identityWitnessBC' = identityWitnessBC :=
  bcData_ext (Iso.ext (NatTrans.ext (funext identityWitnessBC'_bcIso_app_eq)))

-- ============================================================
-- Inhalt 4 — Konsistenz-Korollar (negative Exerzierung der neuen Iff)
-- ============================================================

/-- Die unkonditionale Iff am prodHomWitness negativ exerziert: über
    prodHomWitnessPAS kann die rechte Seite nicht gelten (sonst gäbe es
    BC-Daten gegen `prodHomWitness_not_bcData`). Zusammen mit
    `identityWitnessBC'` (positiv) ist die neue Iff damit beidseitig
    exerziert — erstmals VOR der Bewertung. -/
theorem prodHomWitness_not_unconditional :
    ¬ (HasPullbacks Type ∧ HasPullbacks Type ∧
        ∀ s, IsIso (prodHomWitnessPAS.adj.unit.app s)) :=
  fun h => ((bcData_nonempty_iff_unconditional prodHomWitnessPAS).mpr h).elim
    prodHomWitness_not_bcData.false

end Reformulation.Proemial.Substantial.Rounding
