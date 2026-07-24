import Reformulation.Proemial.ContexturalTransjunction
import Reformulation.Proemial.RealizedTransjunction
import Reformulation.Proemial.TransjunctionCloneBound
import Reformulation.Proemial.StageAggregation
import Reformulation.Proemial.IrreversibleAdvance
import Reformulation.Proemial.DiscontexturalStratification

/-!
# Proemial.AsymmetricDiscontexturality — das Zeugenregister der asymmetrischen Brüche

**Benennung.** Diese Datei liefert **keinen neuen Satz**. Sie klassifiziert
vorhandene asymmetrische Bruchzeugen des Korpus durch dünne, propositionale
Wrapper-Typen — je ein Typ pro **Beweisart**, nicht pro Deutungsanspruch. Die
Statements der Zeugen werden wörtlich re-zitiert und die Beweise unverändert
konsumiert; neu ist allein die Sortierung.

Diese Datei klassifiziert vorhandene asymmetrische Bruchzeugen. Sie beweist
nicht, dass diese Zeugen Günthers asymmetrische Diskontexturalität erschöpfen.

## Gerichtet und ungerichtet — was der Titel nicht einlöst

Von den sechs Beweisarten tragen nur zwei einen **Richtungssinn**: die
Faser-Asymmetrie (4) und die Irreversibilität (5). Die Arten 1 bis 3 belegen
Nicht-Internalität beziehungsweise Nicht-Erzeugbarkeit im Termklon. Das ist nach
Günthers eigener Unterscheidung die **symmetrische** Seite: ein
Umtauschverhältnis zwischen Kontexturen, ein ungeordnetes Paar. Die
asymmetrische Diskontexturalität verlangt ein **geordnetes** Paar mit
Richtungssinn — Stufengang, Rangverlust, das Neue.

Die Arten 1 bis 3 stehen hier darum als **Kontrast**, nicht als Einlösung des
Titels. Damit zeigt das Register zugleich, wie dünn die asymmetrische Seite
besetzt ist: zwei von sechs Beweisarten, und die Instanzen der Art 4 liegen
sämtlich im standalone Sonden-Register. Wer aus der Zahl der Einträge auf den
Stand der asymmetrischen Seite schlösse, läse das Register falsch.

**Nachtrag (der gebundene Zeuge).** Die asymmetrische Seite ist inzwischen
nicht mehr nur durch die zwei ungebundenen Beweisarten 4 und 5 besetzt, sondern
durch **einen gebundenen** Zeugen: `TowerAsymmetryProbe.tower_asymmetric` bindet
Richtung (Irreversibilität, Art 5), Substruktur-Erhaltung und
Determinationsverlust (Faser-Asymmetrie, Art 4) an **einem** Träger — der erste
Zeuge im Korpus, der die drei Merkmale von Günthers asymmetrischer
Diskontexturalität zugleich trägt. `AsymmetricDiscontexturalTransition`
(Namespace `AsymmetricTransition`) bündelt ihn zur Struktur mit drei
Beweisfeldern und einem markierten Kontextur-Setzungsfeld. **Kein siebter
Wrapper-Typ**: die Bindung ist keine neue Beweisart, sondern die Verschaltung
zweier vorhandener. Beide Dateien sind standalone (sie konsumieren Sonden); der
Anschluss bleibt darum im standalone Sonden-Register, nicht hier. Die
verbleibende Grenze ist dort benannt: der gebundene Zeuge entscheidet KA nur
**modulo** der markierten Identifikation „Stufenwechsel = Kontexturwechsel".

## Die Leitentscheidung

Es gibt hier **kein** globales `AsymmetricDiscontexturality : Prop`. Eine solche
Definition wäre entweder zu schwach (`True`, Nichtgleichheit, Disjunktheit —
alles nach CLAUDE.md §5 verworfene Formen) oder würde verschiedene Beweisarten
verwischen. Stattdessen trägt jeder Wrapper-Typ genau eine Beweisart:

1. `ConcreteNotInternal` — Wert- oder Kontexturwechsel einer konkreten Operation,
   die keine interne Lift-Darstellung besitzt.
2. `TermCloneNotGenerated` — Nicht-Erzeugbarkeit im Termklon (die tragfähige
   Form der Diskontexturalität nach CLAUDE.md §5.2).
3. `NoGenericSwitchWitness` — keine generische, träger-uniforme Wechselfunktion.
4. `FiberAsymmetryWitness` — Split-Epi ohne Iso, Fasermehrdeutigkeit
   (Instanzen ausschließlich im standalone `…ProbeRegister`, siehe unten).
5. `IrreversibleWitness` — Rückkehrfreiheit, gerichtete Stufenbewegung.
6. `PositedWitness` — gesetzte Diskontexturalität, bewusst markierter Rand.

## Kern/Rand

Die Wrapper 1–5 tragen **bewiesene** Sätze. `PositedWitness` ist strikt davon
getrennt: er ist keine beweisbare Nicht-Internalität, sondern klassifiziert
konstitutive Setzungen, die der Korpus bewusst nicht als Nicht-Existenz-Theorem
ausgibt (das `True`-Feld der B5-Form in `DiscontexturalStratification`). Ein
`PositedWitness` sagt nur, dass die gesetzte Struktur **bewohnt** ist — nicht,
dass Diskontexturalität bewiesen wurde.

## Universum (gemessen, nicht vermutet)

`structure W (P : Prop) where proof : P` landet in **Prop** (per Wegwerf-Datei
gemessen: `W : Prop → Prop`); die Annotation `: Prop` unten macht das explizit.
Die Instanzen sind darum Beweise und werden als `theorem` geführt, nicht als
`def`. Proof-Irrelevanz ist hier erwünscht: das Register behauptet keine Daten.

## Sonden-Grenze

Die Zeugen der Standalone-Sonden (`ProemialInversionProbe.split_epi_not_iso`,
`K4DiscontexturalityProbe.descent_not_factoring`) werden **nicht** hier
angeschlossen, sondern in `AsymmetricDiscontexturalityProbeRegister.lean` —
standalone, außerhalb des Aggregats, damit diese Datei aggregatfähig bleibt.

## STATEMENT-PIN-Entscheid (CLAUDE.md §3)

Die Wrapper-Statements sind Re-Zitationen, aber **keine** STATEMENT-PINs im
Sinne der Zählroute: sie sind konsumierende Theoreme, keine `example`-Pins.
Der Marker wird darum absichtlich nicht gesetzt.

## Status

Benennung mit Zeugenregister, 0 Sorries. Ein Ertrag entstünde erst, wenn zwei
bisher getrennte Zeugenformen durch ein gemeinsames, nicht-triviales Lemma
verbunden würden — ein solches Lemma wird hier bewusst nicht behauptet.
-/

open FirstOrder Language

namespace Reformulation.Proemial.AsymmetricDiscontexturality

open Reformulation.Proemial.Transjunction
  (exTransjunction liftS exTransjunction_not_S_internal)
open Reformulation.Proemial.RealizedTransjunction (no_generic_switch)
open Reformulation.Proemial.TransjunctionCloneBound (L T T_not_in_clone)
open Reformulation.Proemial.GeneralCloneBound (Lc)
open Reformulation.Proemial.StageAggregation
  (Stufe agg agg_nicht_erzeugbar agg_nicht_erzeugbar_konstanten)
open Reformulation.Proemial.IrreversibleAdvance (NoReturn succ_noreturn)
open Reformulation.Proemial.Discontextural
  (DiscontexturalStratification discontexturalStratification_nonempty)

-- ============================================================
-- Teil 1 — Die Beweisart-Typen (dünne, propositionale Hüllen)
-- ============================================================

/-- **Beweisart 1: konkrete Nicht-Internalität.** Eine konkrete Operation
    besitzt keine Darstellung als interner Lift. Der Wrapper ist absichtlich
    dünn: er trägt das Statement und sonst nichts. -/
structure ConcreteNotInternal (P : Prop) : Prop where
  proof : P

/-- **Beweisart 2: Termklon-Nicht-Erzeugbarkeit.** Keine Verschaltung
    intra-kontextureller Operationen (kein Term über der Sprache) realisiert
    die Zieloperation. Die nach CLAUDE.md §5.2 tragfähige Form. -/
structure TermCloneNotGenerated (P : Prop) : Prop where
  proof : P

/-- **Beweisart 3: kein generischer Wechsel.** Es gibt keine träger-uniforme
    Wechselkonstruktion über alle Kontexturpaare. -/
structure NoGenericSwitchWitness (P : Prop) : Prop where
  proof : P

/-- **Beweisart 4: Faser-Asymmetrie.** Split-Epi ohne Iso, nicht-injektiver
    Abstieg, Nicht-Faktorisierung über Vergröberung. Instanzen liegen
    ausschließlich im standalone Sonden-Register (Sonden-Grenze, Dateikopf). -/
structure FiberAsymmetryWitness (P : Prop) : Prop where
  proof : P

/-- **Beweisart 5: Irreversibilität.** Rückkehrfreiheit einer gerichteten
    Bewegung — die Zeitform der Asymmetrie. -/
structure IrreversibleWitness (P : Prop) : Prop where
  proof : P

/-- **Beweisart 6: gesetzter Rand.** KEINE beweisbare Nicht-Internalität.
    Klassifiziert konstitutive Setzungen (B5-Muster, `True`-Feld), deren
    Bewohntheit bewiesen ist — nicht mehr. Strikt getrennt von den
    Beweisarten 1–5 zu halten (Kern/Rand, Dateikopf). -/
structure PositedWitness (P : Prop) : Prop where
  proof : P

-- ============================================================
-- Teil 2 — Die beweisbaren Zeugen (Beweisarten 1–3, 5)
-- ============================================================

/-- **Zeuge zu Beweisart 1.** Die exemplarische Transjunktion ist nicht
    S-intern: keine Träger-Operation `op` stellt sie als `liftS op` dar
    (`ContexturalTransjunction.exTransjunction_not_S_internal`, zehnte
    Schicht). -/
theorem exTransjunction_notInternal_witness :
    ConcreteNotInternal (¬ ∃ op, exTransjunction = liftS op) :=
  ⟨exTransjunction_not_S_internal⟩

/-- **Zeuge zu Beweisart 3.** Kein generischer Kontexturwechsel: `Nonempty
    (S → K)` ist nicht für alle Träger ableitbar (Zeuge `Bool → Empty`;
    `RealizedTransjunction.no_generic_switch`, elfte Schicht). Beachte den
    Allquantor: die Nicht-Existenz einer *uniformen* Konstruktion, nicht die
    falsche Behauptung, es gäbe gar kein Wechselpaar. -/
theorem realized_noGenericSwitch_witness :
    NoGenericSwitchWitness (¬ ∀ (S K : Type), Nonempty (S → K)) :=
  ⟨no_generic_switch⟩

/-- **Zeuge zu Beweisart 2 (Satz D).** Die Transjunktion `T` liegt nicht im
    Termklon über `L` (`TransjunctionCloneBound.T_not_in_clone`). Robustheit
    nach CLAUDE.md §9: die Invariante (Elementarkontextur `{0,2}`) ist
    **nicht** reflexiv — diese Schranke überlebt Signatur-Erweiterung um
    Konstanten nicht. Den konstanten-robusten Gegenpart liefert
    `stageAggregation_konstanten_witness`. -/
theorem T_notInClone_witness :
    TermCloneNotGenerated
      (¬ ∃ t : L.Term (Fin 2), ∀ v : Fin 2 → Fin 3,
        t.realize v = T (v 0) (v 1)) :=
  ⟨T_not_in_clone⟩

/-- **Zeuge zu Beweisart 2 (E4).** Die Stufenaggregations-Politik `agg` ist
    aus lokalen, kontextur-blinden Prüfern nicht komponierbar
    (`StageAggregation.agg_nicht_erzeugbar`, Instanz von E3 bei m = 4). -/
theorem stageAggregation_witness :
    TermCloneNotGenerated
      (¬ ∃ t : L.Term (Fin 2), ∀ v : Fin 2 → Stufe,
        t.realize v = agg (v 0) (v 1)) :=
  ⟨agg_nicht_erzeugbar⟩

/-- **Zeuge zu Beweisart 2, konstanten-robust (E4 + CLAUDE.md §9).** Auch mit
    beliebigen konstanten Prüfern als Bausteinen (`Lc 4`) bleibt `agg`
    unkomponierbar — Träger ist die Reflexivität von `R 4`
    (`StageAggregation.agg_nicht_erzeugbar_konstanten`). Das Register führt
    beide Fassungen, weil ihre Invarianten verschieden robust sind. -/
theorem stageAggregation_konstanten_witness :
    TermCloneNotGenerated
      (¬ ∃ t : (Lc 4).Term (Fin 2), ∀ v : Fin 2 → Stufe,
        t.realize v = agg (v 0) (v 1)) :=
  ⟨agg_nicht_erzeugbar_konstanten⟩

/-- **Zeuge zu Beweisart 5.** `Nat.succ` ist rückkehrfrei: keine positive
    Iterationszahl führt zurück (`IrreversibleAdvance.succ_noreturn`,
    dreiundzwanzigste Schicht — das zweite Zeit-Differential). -/
theorem succ_noreturn_witness :
    IrreversibleWitness (NoReturn Nat.succ) :=
  ⟨succ_noreturn⟩

-- ============================================================
-- Teil 3 — Der gesetzte Rand (Beweisart 6, strikt getrennt)
-- ============================================================

/-- **Zeuge zu Beweisart 6.** Die gesetzte Diskontexturalitäts-Struktur ist
    bewohnt (`Discontextural.discontexturalStratification_nonempty`). NICHT
    mehr: das `discontextural`-Feld ist ein `True`-Setzungs-Feld nach dem
    B5-Muster; seine Bewohntheit beweist keine Nicht-Internalität. Genau
    darum trägt dieser Zeuge `PositedWitness` und keinen der Beweisart-Typen
    1–5. -/
theorem discontexturalStratification_posited :
    PositedWitness (Nonempty (DiscontexturalStratification Type)) :=
  ⟨discontexturalStratification_nonempty⟩

-- ============================================================
-- Wachen — Axiom-Profile der Register-Sätze
-- ============================================================

/-! **Wachen.** Ist-Ausgabe des grünen Builds (v4.30.0-rc2), pro Satz als
Regressions-Wache eingefroren (Datei-Vollständigkeits-Regel: alle sieben Sätze
der Datei). Nach der Hüllen-Lehre erbt jeder Wrapper das Profil seiner Quelle
und unterbietet es nie; die Profile unten sind gemessen, nicht geschätzt.
**Kein Satz zieht `Classical.choice` oder `sorryAx`.** Zwei Zeugen sind
axiom-frei (`no_generic_switch` und die Bewohntheit der Setzung tragen selbst
kein Axiom); der 120-Spalten-Umbruch im `konstanten`-Profil ist Ist-Ausgabe. -/

/-- info: 'Reformulation.Proemial.AsymmetricDiscontexturality.exTransjunction_notInternal_witness' depends on axioms: [propext] -/
#guard_msgs in #print axioms exTransjunction_notInternal_witness

/-- info: 'Reformulation.Proemial.AsymmetricDiscontexturality.realized_noGenericSwitch_witness' does not depend on any axioms -/
#guard_msgs in #print axioms realized_noGenericSwitch_witness

/-- info: 'Reformulation.Proemial.AsymmetricDiscontexturality.T_notInClone_witness' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms T_notInClone_witness

/-- info: 'Reformulation.Proemial.AsymmetricDiscontexturality.stageAggregation_witness' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms stageAggregation_witness

/--
info: 'Reformulation.Proemial.AsymmetricDiscontexturality.stageAggregation_konstanten_witness' depends on axioms: [propext,
 Quot.sound]
-/
#guard_msgs in #print axioms stageAggregation_konstanten_witness

/-- info: 'Reformulation.Proemial.AsymmetricDiscontexturality.succ_noreturn_witness' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms succ_noreturn_witness

/-- info: 'Reformulation.Proemial.AsymmetricDiscontexturality.discontexturalStratification_posited' does not depend on any axioms -/
#guard_msgs in #print axioms discontexturalStratification_posited

end Reformulation.Proemial.AsymmetricDiscontexturality
