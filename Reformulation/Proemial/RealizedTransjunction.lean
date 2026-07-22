import Reformulation.Proemial.ContexturalTransjunction
import Mathlib.CategoryTheory.Discrete.Basic

/-!
# Reformulation.Proemial.RealizedTransjunction — die Realisierungs-Naht

Elfte Niederlegungs-Schicht. Sie **webt** die zwei Inseln der zehnten Schicht
(`ContexturalTransjunction.lean`) auf *einem* parametrischen Trägerpaar `S, K`
zusammen:

* die operationslose Hebung `ContexturalLift S K` (Funktor `S ⥤ K`, OHNE
  Operation) und
* den hebungslosen Kern `exTransjunction` (die Operation, OHNE getrennte
  parametrische Träger — ein getaggter Einzelträger `Bool ⊕ Bool`).

Die Naht-Struktur `LiftedTransjunctiveC` trägt **beide** Daten in *einem* Term;
die Sondierung (`NahtFormSondierung.lean`) hat die Form bereits am Code als
tragend nachgewiesen (Type-check grün, Kerne axiom-frei). Diese Datei überträgt
das Erprobte in die niedergelegte Form — sie erfindet nichts Neues.

## Die Einwebung (zentral)

Die zehnte Schicht ließ Hebung und Operation als zwei *Inseln*. Hier leben sie
als zwei Felder in *einem* Term `LiftedTransjunctiveC` (Insel-Test: ein
gemeinsamer Term, in dem `transition` UND `transject` vorkommen). Die
zehnte-Schicht-Schere ist aufgelöst; `toContexturalLift` zeigt zudem, dass die
erste Insel (`ContexturalLift`) aus der Naht rekonstruierbar ist.

## Der ehrliche Preis (nicht zu überdecken)

`transition` (Funktor, 1-stellig: Objekt + Morphismus) und `transject`
(Operation, 2-stellig) bleiben **zwei Felder**. Sie verschmelzen NICHT: eine
binäre Transjunktion `S → S → (S ⊕ K)` lässt sich nicht als der Funktor selbst
fassen (der C-Befund der Sondierung). Das ist eine *strukturelle Tatsache*, kein
Defekt und kein `sorry`-Anlass. Die Naht ist geschlossen (beide auf einem
`S, K`), die Naht-Stelle bleibt sichtbar (zwei Felder).

## Die strukturelle Nicht-Konstruierbarkeit (der gehaltvolle Rand)

`no_generic_switch` ist der **axiom-freie** Ersatz des `True`-Rand-Felds der
zehnten Schicht (`contexturePartitionGenuine : True`): die
Nicht-Konstruierbarkeit ist hier ein negatives Existenz-Resultat *über die
Träger selbst* (`¬ ∀ S K, Nonempty (S → K)`, Zeuge `S = Bool`, `K = Empty`),
nicht eine Setzung. Der Rand hat Gehalt bekommen — von der Setzung zur
strukturellen Tatsache.

## Entscheidungen (aus der Spec)

* **Entscheidung 1 — Funktor (C) statt schlanke `switch` (B).** `transition` ist
  der volle Funktor `S ⥤ K` (Anschluss an `ContexturalLift`); er subsumiert die
  schlanke `switch` via `.obj` (`switchOfTransition`). Anmerkung: in DIESER Datei
  wird nur `.obj` konsumiert (konstanter Funktor); die Morphismus-Funktorialität
  wird nicht verbraucht — wäre B (schlanke `switch`) die einzige Anforderung,
  wäre sie die schlankere Form. Der Funktor ist gewählt für den Anschluss an die
  gehobene Struktur.
* **Entscheidung 2 — K2 konkret, Abstraktions-Grenze benannt.** Die Vorzeigung
  `exTransject_not_internal` lebt auf der Zwei-Parameter-Instanz
  `Discrete Bool` / `Discrete Unit` (KEINE kanonische `S → K`, anders als die
  Insel-`Bool → Bool`). Die *abstrakte* `not_internal`-Form über parametrische
  `S, K` wird NICHT verlangt — sie wäre nur über eine zusätzliche
  Trennungs-Hypothese erreichbar, die der Befund als offen markierte.
* **Entscheidung 3 — Degenerations-Falle ausgeschlossen.** Der Zeuge `exLifted`
  führt zwei *verschiedene* Träger (`Discrete Bool ≠ Discrete Unit`) und einen
  *nicht-trivialen* Übergang (der konstante Funktor nach `Unit`, KEIN
  Identitäts-Funktor — `exLifted_transition_collapses` bezeugt den echten
  Kollaps zweier verschiedener Objekte). Das behebt II.5 der zehnten Schicht
  (deren Zeuge war `Type/Type/𝟙`, degeneriert).

## Die `internalS`-Definitions-Wahl (Behebung 2 gegen II.4)

`internalS` ist die **gesetzte** Operationalisierung von „S-intern" als die
punktweise von einer träger-internen Funktion `op : S → S → S` induzierte
Familie `fun a b => Sum.inl (op a b)`. Dass sie *alle* S-internen Operationen
erfasst, ist eine Definitions-Wahl, KEIN Theorem; das Vorzeige-Theorem
`exTransject_not_internal` ist relativ zu dieser Wahl scharf. Die Naht *benennt*
die Wahl (Ehrlichkeit), statt sie als selbstverständlich zu nehmen.

## „ruht auf"-Audit

Der Körper konsumiert: `ContexturalLift` (zehnte Schicht, für
`toContexturalLift`); `CategoryTheory.Discrete` + `Discrete.functor` (die
Kategorien-Hüllen für `Bool`/`Unit`, Entscheidung 3); die Sum-Konstruktor-
Maschinerie (`Sum.inl`/`Sum.inr`, No-Confusion via `simp`/`decide`). Für
`no_generic_switch` wird nichts außer `Empty.elim` konsumiert (axiom-frei).

## Sorry-Bilanz

* Teil 1 (`LiftedTransjunctiveC`): 0 — reine Struktur.
* Teil 2 (`no_generic_switch`): 0 — axiom-frei, Zeuge `Bool/Empty`.
* Teil 3 (Vorzeigung + Zeuge): 0 — `exTransject_not_internal` über das konkrete
  `inl`/`inr`-Bild-Argument; der Zeuge konkret und nicht-degeneriert.
* Gesamt: 0 Sorries. Ein Sorry an irgendeiner Stelle wäre ein Befund (die
  Sondierung hat Sorry-Freiheit gezeigt).

## Konditionalität (Baubarkeit jetzt, Beglaubigung nachgelagert)

Diese Datei trägt die BAUBARKEIT (Einwebung + gehaltvoller Rand + nicht-
degenerierter Zeuge). Die drei Stimmen-Beglaubigungen sind KEINE Anker der
Baubarkeit, nachgelagert offen:
- Janus (Binde-Kraft): bindet die eingewobene Form den Skeptiker?
- Hermeneutes (Günther-Treue): ist die Rejektions-Funktion günther-treu?
- Horistês (Komplementarität): trägt das Mediations-Gewebe?
-/

namespace Reformulation.Proemial.RealizedTransjunction

open CategoryTheory
open Reformulation.Proemial.Transjunction

-- ============================================================
-- Teil 1 — Die Naht-Struktur (die Einwebung)
-- ============================================================

/-- DIE REALISIERUNGS-NAHT: Hebung UND Operation auf *einem* `S, K` in *einem*
    Term.

    * `transition : S ⥤ K` — die Träger-Hebung (Funktor; subsumiert die schlanke
      `switch` via `.obj`, Entscheidung 1). Das ist die erste Insel
      (`ContexturalLift`), hier eingewoben.
    * `transject : S → S → (S ⊕ K)` — die Operation als SEPARATES Datum, KEIN
      Funktor (der ehrliche Preis: 2-stellig vs. 1-stellig). Das ist die zweite
      Insel (`exTransjunction`), hier eingewoben.
    * `rejects` — die Rejektion bezeugt (Lesart b): es gibt ein Paar, dessen
      Transjunktionswert ein Kontexturwechsel `Sum.inr k` ist.

    Die Naht ist geschlossen (beide auf einem `S, K`), die Naht-Stelle bleibt
    sichtbar (zwei Felder). Die strukturelle Nicht-Konstruierbarkeit der
    fehlenden kanonischen `S → K` trägt `no_generic_switch` (Teil 2). -/
structure LiftedTransjunctiveC (S K : Type*) [Category S] [Category K] where
  /-- die Hebung: der Funktor (Wechsel auf Trägern; subsumiert `switch` via `.obj`). -/
  transition : S ⥤ K
  /-- die Operation: ein SEPARATES Datum, KEIN Funktor (der C-Befund). -/
  transject  : S → S → (S ⊕ K)
  /-- die Rejektion bezeugt (Lesart b): ein Kontexturwechsel `inr`. -/
  rejects    : ∃ a b k, transject a b = Sum.inr k

/-- Die Hebung subsumiert die schlanke `switch : S → K` via `.obj` (Entscheidung
    1). NUR `.obj` wird hier konsumiert — die Morphismus-Funktorialität nicht. -/
def switchOfTransition {S K : Type*} [Category S] [Category K]
    (L : LiftedTransjunctiveC S K) : S → K :=
  L.transition.obj

/-- DIE EINWEBUNG, explizit: aus der Naht ist die erste Insel der zehnten Schicht
    (`ContexturalLift`) rekonstruierbar. Die Naht enthält die Hebung; sie fügt
    die Operation (`transject`) als zweites Feld hinzu. -/
def toContexturalLift {S K : Type*} [Category S] [Category K]
    (L : LiftedTransjunctiveC S K) : ContexturalLift S K :=
  { transition := L.transition }

-- ============================================================
-- Teil 2 — Die strukturelle Nicht-Konstruierbarkeit (axiom-frei, gehaltvoller Rand)
-- ============================================================

/-- DER GEHALTVOLLE RAND (axiom-frei, aus der Sondierung übernommen): der Wechsel
    `S → K` folgt NICHT aus den Träger-Daten allein — `Nonempty (S → K)` ist
    nicht für alle `S`, `K` ableitbar. Zeuge: `S = Bool`, `K = Empty` (`Bool →
    Empty` ist unbewohnt).

    Das ist der gehaltvolle Ersatz des `True`-Rand-Felds der zehnten Schicht
    (`contexturePartitionGenuine : True`): die Nicht-Konstruierbarkeit als
    negatives Existenz-Resultat über die Träger, nicht als Setzung. Der Rand ist
    von der Setzung zur strukturellen Tatsache gewandert. -/
theorem no_generic_switch : ¬ ∀ (S K : Type), Nonempty (S → K) := by
  intro h
  obtain ⟨f⟩ := h Bool Empty
  exact (f true).elim

-- ============================================================
-- Teil 3 — Die konkrete Vorzeigung und der nicht-degenerierte Zeuge
-- ============================================================

/-- Die `internalS`-Familie (Behebung 2, BENANNT als Definitions-Wahl): die
    gesetzte Operationalisierung von „S-intern" als die punktweise von einer
    träger-internen Funktion `op : S → S → S` induzierte Familie. Das Bild ist
    IMMER `inl` (die Operation bleibt im S-Träger). Dass sie *alle* S-internen
    Operationen erfasst, ist eine Wahl, kein Theorem. -/
def internalS {S K : Type*} (op : S → S → S) : S → S → (S ⊕ K) :=
  fun a b => Sum.inl (op a b)

/-- Die konkrete Transjunktion auf der Zwei-Parameter-Instanz
    `Discrete Bool` / `Discrete Unit`: bei gleichem Träger-Wert bleibt sie in
    `S` (`inl`), bei ungleichem wechselt sie nach `K` (`inr ⟨()⟩` — Lesart b,
    Kontexturwechsel, kein dritter Wert). -/
def exTransject : Discrete Bool → Discrete Bool → (Discrete Bool ⊕ Discrete Unit) :=
  fun a b => if a.as = b.as then Sum.inl a else Sum.inr ⟨()⟩

/-- DER NICHT-DEGENERIERTE ZEUGE (Behebung 1, gegen II.5): die Naht-Instanz auf
    ZWEI VERSCHIEDENEN Trägern `Discrete Bool ≠ Discrete Unit` mit einem
    NICHT-TRIVIALEN Übergang (dem konstanten Funktor nach `Unit`, KEIN
    Identitäts-Funktor). Anders als die zehnte Schicht (`Type/Type/𝟙`) bezeugt
    dieser Zeuge die Getrenntheit, die er nominell zeigt. -/
def exLifted : LiftedTransjunctiveC (Discrete Bool) (Discrete Unit) where
  transition := Discrete.functor (fun _ => ⟨()⟩)
  transject  := exTransject
  rejects    := ⟨⟨true⟩, ⟨false⟩, ⟨()⟩, by decide⟩

/-- NICHT-DEGENERATIONS-ZEUGE (Entscheidung 3, Behebung 1): der Übergang ist
    nicht-trivial — er kollabiert die zwei verschiedenen Objekte `⟨true⟩` und
    `⟨false⟩` auf dasselbe `Unit`-Objekt. Kein Identitäts-Funktor. -/
theorem exLifted_transition_collapses :
    exLifted.transition.obj ⟨true⟩ = exLifted.transition.obj ⟨false⟩ := rfl

/-- NICHT-DEGENERATIONS-ZEUGE (Entscheidung 3): die Domäne hat zwei
    verschiedene Objekte, die der Übergang kollabiert — der Kollaps ist also
    echt (nicht der eines Identitäts-Funktors auf gleichem Träger). -/
theorem exLifted_domain_distinct : (⟨true⟩ : Discrete Bool) ≠ ⟨false⟩ := by
  decide

/-- VORZEIGBARER KERN (beweisbar, Entscheidung 2, KEIN Form α): die konkrete
    Operation `exLifted.transject` ist nicht S-intern — es gibt kein
    `op : Discrete Bool → Discrete Bool → Discrete Bool`, das sie als
    `internalS op` darstellt.

    Beweis (positives Bild-Argument für DIE EINE konkrete Operation, kein
    globales Nicht-Existenz-Theorem): der Zeuge `(⟨true⟩, ⟨false⟩)` liefert unter
    `exTransject` den `inr`-Wert (Kontexturwechsel), unter `internalS op` aber
    stets einen `inl`-Wert. `inr ≠ inl` (Sum-No-Confusion).

    Abstraktions-Grenze (Entscheidung 2, benannt): dies ist die KONKRETE Form auf
    `Discrete Bool`/`Discrete Unit`. Die abstrakte Form über parametrische
    `S, K` wird NICHT behauptet — sie bräuchte eine Trennungs-Hypothese. -/
theorem exTransject_not_internal :
    ¬ ∃ op : Discrete Bool → Discrete Bool → Discrete Bool,
      exLifted.transject = internalS op := by
  rintro ⟨op, h⟩
  have hcontra := congrFun (congrFun h ⟨true⟩) ⟨false⟩
  simp [exLifted, exTransject, internalS] at hcontra

-- Axiom-Sauberkeit als Regressions-Wachen (Zug „Wachen-Vollzug", Datei-Vollständigkeit).
-- Ist-Ausgabe des grünen Builds (v4.30.0-rc2), pro Satz eingefroren; ab hier bricht
-- jede Axiom-Drift den Build.
/-- info: 'Reformulation.Proemial.RealizedTransjunction.no_generic_switch' does not depend on any axioms -/
#guard_msgs in #print axioms no_generic_switch

/-- info: 'Reformulation.Proemial.RealizedTransjunction.exTransject_not_internal' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms exTransject_not_internal

/-- info: 'Reformulation.Proemial.RealizedTransjunction.exLifted_transition_collapses' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms exLifted_transition_collapses

/-- info: 'Reformulation.Proemial.RealizedTransjunction.exLifted_domain_distinct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms exLifted_domain_distinct

end Reformulation.Proemial.RealizedTransjunction
