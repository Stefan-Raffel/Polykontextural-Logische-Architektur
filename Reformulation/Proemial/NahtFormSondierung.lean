import Reformulation.Proemial.ContexturalTransjunction

/-!
# Reformulation.Proemial.NahtFormSondierung — EXPLORATIVE SONDIERUNG (keine Schicht)

Dies ist KEINE Niederlegungs-Schicht und KEIN Aggregat-Eintrag. Es ist eine
explorative Datei, deren Zweck das ERPROBEN dreier Kandidaten-Formen für die
„zwei getrennten Träger mit Wechsel" ist. Sie darf gescheiterte/teiltragende
Kandidaten nebeneinander enthalten; das Ergebnis ist ein BEFUND
(`Naht_Form_Sondierung_Befund.md`), keine festgeschriebene Spec.

Hintergrund: Die Insel-Form (`ContexturalTransjunction.lean`) hält zwei Inseln:
* `ContexturalLift S K` (Funktor `S ⥤ K`) — getrennte Träger, OHNE Operation.
* `exTransjunction` auf `Contextural := Bool ⊕ Bool` — die Operation, OHNE
  getrennte parametrische Träger (ein getaggter Einzelträger, beide `Bool`).

Erprobt werden drei Formen, die beide auf EINEM `S`, `K` zusammenbringen, gemessen
an K1 (echte parametrische Trägertrennung), K2 (vorzeigbarer Kern: konkrete
Transjunktion mit Rejektion + beweisbares `not_internal`, kein Form α), K3
(strukturelle Nicht-Konstruierbarkeit durch fehlende kanonische `S → K`), K4
(Insel-Verbindung: Hebung und Transjunktion in EINEM Term).

Disziplin: kein `sorry` zum Retten, keine kanonische `S → K`, kein Form α, kein
Łukasiewicz-Kippen. Ein nicht-tragender Kandidat ist ein wertvoller Befund
(siebte Antizipations-Korrektur).
-/

namespace Reformulation.Proemial.NahtFormSondierung

open CategoryTheory
open Reformulation.Proemial.Transjunction

-- ============================================================
-- DIE SCHLÜSSEL-FRAGE zuerst: trägt K1 (Trägertrennung) das K3
-- (strukturelle Nicht-Konstruierbarkeit) wirklich?
-- ============================================================

/-- SCHLÜSSEL-FRAGE, konkrete Seite: für `S = Bool`, `K = Empty` ist `S → K`
    leer. Ohne ein zusätzliches Datum gibt es keinen Wechsel `S → K`. -/
theorem switch_isEmpty_bool_empty : IsEmpty (Bool → Empty) := by
  constructor
  intro f
  exact (f true).elim

/-- SCHLÜSSEL-FRAGE, parametrische Seite (der mathematische Kern der ganzen
    Sondierung): `Nonempty (S → K)` ist NICHT für alle `S`, `K` ableitbar. Die
    Parametrizität erzwingt also strukturell, dass der Wechsel ein zusätzliches
    Datum sein MUSS — er folgt nicht aus den Träger-Daten allein. Zeuge:
    `S = Bool`, `K = Empty`. -/
theorem no_generic_switch : ¬ ∀ (S K : Type), Nonempty (S → K) := by
  intro h
  obtain ⟨f⟩ := h Bool Empty
  exact (f true).elim

-- ============================================================
-- KANDIDAT A — parametrische Typen mit Summen-Wechsel
-- ============================================================

section CandidateA

/-- Kandidat A: zwei beliebige, unverbundene Träger `S`, `K`; die Transjunktion
    als partielle Rejektion `S → S → (S ⊕ K)` mit bezeugter Rejektion. KEINE
    kanonische `S → K`. -/
structure Transjunctive (S K : Type*) where
  transject : S → S → (S ⊕ K)
  rejects : ∃ a b, ∃ k, transject a b = Sum.inr k

/-- K2 (A): konkrete Instanz mit Rejektion. `S = Bool`, `K = Unit`; bei `a ≠ b`
    Wechsel nach `K` (`inr`), kein dritter Wert in `S` (Lesart b, kein
    Łukasiewicz). -/
def exA : Transjunctive Bool Unit where
  transject a b := if a = b then Sum.inl a else Sum.inr ()
  rejects := ⟨true, false, (), by decide⟩

/-- K2 (A): die Operation ist NICHT S-intern — sie ist nicht von der Form
    `fun a b => Sum.inl (op a b)`. Positives Bild-Argument über den konkreten
    Zeugen `(true, false) ↦ inr ()` (kein Form α: ein `¬∃` über die EINE
    konkrete Operation, nicht über alle Faktorisierungen). -/
theorem exA_not_internal :
    ¬ ∃ op : Bool → Bool → Bool, exA.transject = fun a b => Sum.inl (op a b) := by
  rintro ⟨op, h⟩
  have hcontra := congrFun (congrFun h true) false
  simp [exA] at hcontra

/-- K3 (A) — der strukturelle Kern: eine REJEKTIERENDE Transjunktion ist nicht
    generisch baubar. Für `K = Empty` ist keine Rejektion möglich (der
    `inr`-Zweig verlangt einen `K`-Wert). Parametrizität blockiert den
    generischen Wechsel — das trägt K3 strukturell, nicht als `True`-Feld. -/
theorem no_transjunctive_into_empty : IsEmpty (Transjunctive Unit Empty) := by
  constructor
  intro t
  obtain ⟨_, _, k, _⟩ := t.rejects
  exact k.elim

/-- K3 (A), Folgerung: es gibt keine generische Konstruktion `∀ S K,
    Transjunctive S K`. Die fehlende kanonische `S → K` trägt die
    Nicht-Konstruierbarkeit. -/
theorem no_generic_transjunctive : ¬ ∀ (S K : Type), Nonempty (Transjunctive S K) := by
  intro h
  obtain ⟨t⟩ := h Unit Empty
  exact no_transjunctive_into_empty.false t

/-- K4 (A): Hebung (`ContexturalLift`, der Funktor) UND Transjunktion
    (`Transjunctive`) auf DEMSELBEN `S`, `K` in EINEM Term. Per grep nachweisbar
    verbunden: beide Felder leben in dieser einen Struktur. -/
structure LiftedTransjunctiveA (S K : Type*) [Category S] [Category K] where
  lift : ContexturalLift S K
  trans : Transjunctive S K

/-- K4 (A): der gemeinsame Term ist bewohnt (über `Type`/`Type`). -/
def exLiftedA : LiftedTransjunctiveA Type Type where
  lift := { transition := Functor.id Type }
  trans := { transject := fun a _ => Sum.inr a, rejects := ⟨PUnit, PUnit, PUnit, rfl⟩ }

end CandidateA

-- ============================================================
-- KANDIDAT B — Struktur mit ausgezeichnetem Wechsel-Morphismus
-- ============================================================

section CandidateB

/-- Kandidat B: der Wechsel `switch : S → K` als GEGEBENES Struktur-Datum (nicht
    kanonisch). `no_generic_switch` zeigt, dass dieses Datum NICHT ableitbar ist
    — B macht die Nicht-Konstruierbarkeit zum first-class-Datum. -/
structure ContexturalSwitch (S K : Type*) where
  switch : S → K

/-- K2 (B): konkrete Instanz. `switch` ist hier das Datum, das den `K`-Wert der
    Rejektion liefert. -/
def exB : ContexturalSwitch Bool Unit := { switch := fun _ => () }

/-- K2 (B): die aus `switch` gebaute Transjunktion. Bei `a ≠ b` Wechsel nach `K`
    über `exB.switch a` (Lesart b). Der `switch`-Wert SPEIST den Rejektionswert. -/
def exBtransject : Bool → Bool → (Bool ⊕ Unit) :=
  fun a b => if a = b then Sum.inl a else Sum.inr (exB.switch a)

/-- K2 (B): die gebaute Transjunktion ist nicht S-intern. -/
theorem exBtransject_not_internal :
    ¬ ∃ op : Bool → Bool → Bool, exBtransject = fun a b => Sum.inl (op a b) := by
  rintro ⟨op, h⟩
  have hcontra := congrFun (congrFun h true) false
  simp [exBtransject, exB] at hcontra

/-- K3 (B): das `switch`-Datum ist genau das, was nicht generisch existiert —
    `no_generic_switch` ist der Beleg. B ist die EHRLICHE Form von K3: die
    Nicht-Konstruierbarkeit ist als fehlendes-und-darum-gefordertes Datum
    sichtbar gemacht, nicht als leeres `True`-Feld gesetzt. -/
theorem switch_not_generic : ¬ ∀ (S K : Type), Nonempty (ContexturalSwitch S K) := by
  intro h
  obtain ⟨c⟩ := h Bool Empty
  exact (c.switch true).elim

/-- K4 (B): Hebung und Wechsel-Datum auf DEMSELBEN `S`, `K` in EINEM Term. -/
structure LiftedSwitch (S K : Type*) [Category S] [Category K] where
  lift : ContexturalLift S K
  sw : ContexturalSwitch S K

end CandidateB

-- ============================================================
-- KANDIDAT C — zwei Kategorien mit Funktor (die stärkste Form)
-- ============================================================

section CandidateC

/-- C, positiver Teil: der Funktor `S ⥤ K` liefert auf OBJEKTEN bereits eine
    Wechsel-Abbildung `S → K` (`.obj`). C SUBSUMIERT also B's `switch` und fügt
    Funktorialität auf Morphismen hinzu — die stärkste Träger-Hebung. -/
def switchOfFunctor {S K : Type*} [Category S] [Category K] (F : S ⥤ K) : S → K :=
  F.obj

/-- C, der Vorbehalt (BEFUND): die binäre Transjunktion `S → S → (S ⊕ K)` lässt
    sich NICHT als der Funktor selbst fassen. Ein Funktor ist 1-stellig
    (Objekt + Morphismus); die Transjunktion ist 2-stellig. Sie bleibt ein
    SEPARATES Datum (`transject`) neben dem Funktor — der Mathematiker-Vorbehalt
    bestätigt sich. C = `ContexturalLift` PLUS die Operation als Extra-Feld. -/
structure LiftedTransjunctiveC (S K : Type*) [Category S] [Category K] where
  /-- die Hebung: der Funktor (Wechsel auf Trägern). -/
  transition : S ⥤ K
  /-- die Operation: ein SEPARATES Datum, KEIN Funktor (der Befund von C). -/
  transject : S → S → (S ⊕ K)
  rejects : ∃ a b, ∃ k, transject a b = Sum.inr k

/-- C: bewohnt — aber `transition` (Funktor) und `transject` (Operation) sind
    zwei getrennte Felder; die Operation konnte NICHT in den Funktor absorbiert
    werden. Genau das ist der Befund. -/
def exLiftedC : LiftedTransjunctiveC Type Type where
  transition := Functor.id Type
  transject := fun a _ => Sum.inr a
  rejects := ⟨PUnit, PUnit, PUnit, rfl⟩

end CandidateC

-- ============================================================
-- Wachen — Axiom-Profile
-- ============================================================

/-! **Wachen (Zug B).** Ist-Ausgabe des grünen Builds (v4.30.0-rc2), pro Satz
eingefroren; sie ersetzen die vier vormals nackten Aufrufe über den beweisbaren Kernen.

`no_generic_switch` und `no_generic_transjunctive` sind **axiomfrei** und tragen darum
den anderen der beiden Ausgabe-Wortlaute (`CLAUDE.md` §8 Fallstrick 15).

Drei Sätze dieser Datei bleiben nach der Vorgabe ungewacht
(`switch_isEmpty_bool_empty`, `no_transjunctive_into_empty`, `switch_not_generic`): kein
Aufruf, kein fremdes Zitat. -/

/-- info: 'Reformulation.Proemial.NahtFormSondierung.no_generic_switch' does not depend on any axioms -/
#guard_msgs in #print axioms no_generic_switch

/-- info: 'Reformulation.Proemial.NahtFormSondierung.exA_not_internal' depends on axioms: [propext] -/
#guard_msgs in #print axioms exA_not_internal

/-- info: 'Reformulation.Proemial.NahtFormSondierung.no_generic_transjunctive' does not depend on any axioms -/
#guard_msgs in #print axioms no_generic_transjunctive

/-- info: 'Reformulation.Proemial.NahtFormSondierung.exBtransject_not_internal' depends on axioms: [propext] -/
#guard_msgs in #print axioms exBtransject_not_internal

end Reformulation.Proemial.NahtFormSondierung
