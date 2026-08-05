import Reformulation.Proemial.RecurringGround
import Reformulation.Proemial.AlphaGammaSubstantial
import Mathlib.CategoryTheory.Comma.Arrow
import Mathlib.CategoryTheory.Types.Basic
import Mathlib.Logic.Function.Basic

/-!
# Reformulation.Proemial.ArrowAscent — die Schranke unten und der Aufstieg darüber

**Ertrag.** Ein Differential zu **einer** Richtung des Rollentauschs zwischen einer
Relation und ihren Gliedern:

* **die arme Hälfte** (`no_naming_of_fixpointfree`) — über **jedem** Träger, dessen
  Wertevorrat einen fixpunktfreien Umtausch trägt, gibt es keine Benennung der
  zweistelligen Relationen durch die Glieder: keine Surjektion `α → (α → β)`;
* **die reiche Hälfte** (`arrow_left_id`, `arrow_left_not_injective`) — eine Ordnung
  höher, in der Pfeilkategorie, ist ein Morphismus ein **Objekt**; die Rückprojektion
  auf die Quelle hat einen Schnitt und vergisst.

Der Dateiname sagt die konstruktive Seite; die arme Hälfte ist ihre Kehrseite — die
Schranke auf der Stufe, über die der Aufstieg hinausführt.

## Quellenanker

Günther, *Erkennen und Wollen* (E&W), Teil 3, zwei Sätze, die diesen Bau tragen und die
im Korpus bisher nicht abgelegt waren:

* **S. 26** — „Der Relator kann zum Relatum werden, **doch nicht in der Relation, für die
  er zuvor die Beziehung einrichtete, sondern nur relativ zu einem Verhältnis bzw.
  Relator höherer Ordnung.**" Der Rollentausch existiert dort **ausschliesslich** als
  Ordnungswechsel; den flachen, innerstufigen Tausch führt E&W ausdrücklich als
  Kontrastfigur („Er hat *nicht* die Form: wechselseitiger Umtausch").
* **S. 27** — „Die Proemialrelation gehört zur Ebene der **kenogrammatischen
  Strukturen**, weil sie eine reine Möglichkeit darstellt, die nur entweder als
  symmetrische Umtauschrelation oder nicht-symmetrische Ordnungsrelation eine aktuelle
  Relation wird."

## Die arme Klasse wurde umbenannt — beide Fassungen, mit Grund

**Angekündigt** war: *jeder Träger, dessen Rollen durch den **Typ** unterschieden sind*.
Diese Fassung ist gefallen, aus zwei unabhängigen Gründen:

1. **Sie ist nicht internalisierbar.** Sie quantifiziert über Typurteile der
   Umgebungssprache; der verbotene Gegenstand ist kein wohlgeformter Term, und ein nicht
   wohlgeformter Term hat keine Proposition, die man im System verneinen könnte.
2. **Sie wäre falsch.** Der Gegenzeuge steht im Bestand: über einem einelementigen
   Wertevorrat existiert das innerstufige Benennen sehr wohl — hier als
   `naming_when_fixpoint` mitgeführt. Die Typtrennung allein leistet nichts.

**Gebaut ist statt dessen:** *jeder Träger, dessen Wertevorrat einen **fixpunktfreien
Umtausch** trägt.* Die Klassenbedingung wandert aus der Metasprache in die **Hypothese
des Satzes** und ist damit allquantifiziert im System.

**Warum diese Ersetzung keine Verschiebung ist:** die neue Hypothese ist Günthers
symmetrische Umtauschrelation selbst — die Negationstafel, involutiv und fixpunktfrei
(E&W Bild 3/4). Der Satz sagt in Satzform: **der Umtausch erzwingt die Ordnung.**

## Deutungsgrenzen

* **Die arme Hälfte ist bekannte Mathematik** — Lawvere/Cantor, aus Mathlib konsumiert.
  Der Ertrag dieses Moduls ist ihre **Verortung** als arme Klasse und die Wanderung der
  Klassenbedingung in die Hypothese; **nichts wird als erstmalig behauptet.**
* Die Gleichsetzung *Relator = zweistellige Relation auf dem Träger* ist **Modellwahl**.
  Günthers Relator ist weiter (jeder Operator); die zweiwertige Fassung ist aber seine
  eigene Kontrastfolie.
* Dass die Pfeilkategorie Günthers **Relator-Abstieg ist**, ist **Deutung**. Bewiesen
  sind eine Schnitt-Gleichung, eine Nicht-Injektivität und eine Benennungs-Schranke.
* **Dies ist nicht die proemiale Relation** und kein Teil des vollen ρ.

## Offene Marken

* **Die Abstiegs-Richtung** — Relatoren injektiv in die Relata — ist ein eigener Satz
  mit eigenem Profil. **Nicht gemessen, nicht behauptet**, ausdrücklich kein Gegenstand
  dieses Moduls.
* **Die Vier-Relata-Simultaneität** (E&W S. 29: der proemiale Wechsel involviert vier
  Relata, und die Rangordnung von Subjekt und Objekt kehrt sich mit um) bleibt **offen**.
  Dieses Modul trägt eine Richtung, nicht die Simultaneität.

## Zuschnitt-Vermerk

`arrow_left_id` und `arrow_left_not_injective` sind **zwei Sätze und bleiben es**. Ihre
Zusammensetzung — *Retraktion ohne Iso* — ist eine **eigene Behauptung** und nicht die
bequemere Schreibweise dieser beiden; sie gehört einem späteren Zug, der sie für **beide**
Stränge aufstellen müsste.

**Die kenogrammatische Seite ist anders geschnitten:** dort liegt die Zusammensetzung als
**ein** Satz vor (`Proemial.ProemialInversionProbe.split_epi_not_iso`, Standalone-Sonde).
Ein späterer Zug, der beide Seiten wörtlich nimmt, wird diese Differenz benennen müssen.

## Bereich

Dieses Modul berührt die **kenogrammatische Schicht nicht** — kein Beweisterm hier zieht
ein `Kenogram.*`-Modul. Das ist gemessen und beabsichtigt: die Zahl der Konstanten, die
beide Stränge berühren, bleibt bei null, und zwar konstruktiv.

Kein `sorry`, kein `axiom`, kein `: True`-Feld.
-/

namespace Reformulation.Proemial.ArrowAscent

open Function CategoryTheory
open Reformulation.Proemial.RecurringGround (FixpointFree swap swap_fixpointfree)

-- ============================================================
-- §I — Die arme Hälfte: keine Benennung unter fixpunktfreiem Umtausch
-- ============================================================

/-- **Die arme Hälfte.** Trägt der Wertevorrat `β` einen fixpunktfreien Umtausch, so ist
über **jedem** Träger `α` keine Abbildung `α → (α → β)` surjektiv: die zweistelligen
Relationen über `α` mit Werten in `β` lassen sich nicht durch die Glieder von `α`
benennen.

Allquantifiziert über alle Träger und alle Wertevorräte; die Klassenbedingung steht in
der Hypothese und nicht in der Umgebungssprache (siehe Dateikopf).

**Herkunft, ausdrücklich:** das ist Lawveres Diagonalargument, `Mathlib` liefert es als
`Function.exists_fixed_point_of_surjective`. Der Prädikatsbegriff `FixpointFree` stammt
aus `Proemial.RecurringGround` (zwanzigste Schicht) und wird hier **konsumiert, nicht neu
eingeführt**. Neu ist allein die Verschaltung. -/
theorem no_naming_of_fixpointfree {α β : Type*} {g : β → β} (hg : FixpointFree g) :
    ∀ f : α → (α → β), ¬ Surjective f := by
  intro f hf
  obtain ⟨x, hx⟩ := exists_fixed_point_of_surjective f hf g
  exact hg x hx

/-- **Die zweiwertige Instanz — Günthers Negationstafel als Hypothese.** Der Umtausch
`swap = ![1, 0]` auf `Fin 2` ist der involutive, fixpunktfreie Zweiertausch; der Zeuge
dafür liegt seit der zwanzigsten Schicht im Aggregat und wird hier konsumiert.

Über jedem Träger gibt es also keine Benennung der zweiwertigen Relationen durch die
Glieder. **In Satzform: der Umtausch erzwingt die Ordnung.** -/
theorem no_naming_two_valued {α : Type*} :
    ∀ f : α → (α → Fin 2), ¬ Surjective f :=
  no_naming_of_fixpointfree swap_fixpointfree

/-- **Nicht-Vakuanz der armen Klasse.** Ohne die Fixpunktfreiheit verschwindet die
Schranke: über einem einelementigen Wertevorrat existiert die Benennung.

Dieser Zeuge trägt zweierlei. Er zeigt, dass die Hypothese echte Arbeit leistet — die
Schranke hängt am Umtausch und nicht an der blossen Form. **Und er ist der Gegenzeuge,
an dem die wörtliche Fassung der armen Klasse fällt** (Dateikopf): eine Aussage, die das
innerstufige Benennen schlechthin verböte, wäre hier widerlegt. -/
theorem naming_when_fixpoint :
    ∃ (α β : Type) (f : α → (α → β)), Surjective f :=
  ⟨Unit, Unit, fun _ _ => (), fun _ => ⟨(), funext fun _ => Subsingleton.elim _ _⟩⟩

-- ============================================================
-- §II — Die reiche Hälfte: eine Ordnung höher
-- ============================================================

/-! In der Pfeilkategorie `Arrow C` sind die Morphismen von `C` die **Objekte**; ihre
Morphismen sind die kommutativen Quadrate. Das ist die Stelle, an der ein Pfeil ein Glied
wird — und, nach E&W S. 26, die einzige, an der er es werden kann.

Die zwei folgenden Sätze bleiben **getrennt**; zum Grund siehe den Zuschnitt-Vermerk im
Dateikopf. -/

/-- **Der Schnitt.** Die Rückprojektion eines Pfeils auf seine Quelle hat über die
Identitätspfeile einen Schnitt: `x` steigt als `𝟙 x` auf und kommt als `x` zurück.
Definitional, für jedes Objekt jeder Kategorie. -/
theorem arrow_left_id {C : Type*} [Category C] (x : C) :
    Arrow.leftFunc.obj (Arrow.mk (𝟙 x)) = x := rfl

/-- **Das Vergessen.** Dieselbe Rückprojektion ist **nicht** injektiv: über `Bool` teilen
sich die Identität und die Negation die Quelle und sind doch verschiedene Objekte der
Pfeilkategorie. Der Aufstieg ist also mehrdeutig, der Abstieg kanonisch.

Zeuge über einem zweielementigen Typ; choice-frei. -/
theorem arrow_left_not_injective :
    ¬ Function.Injective (fun f : Arrow (Type) => f.left) := by
  intro h
  have h1 : Arrow.mk (↾(id : Bool → Bool)) = Arrow.mk (↾fun b => !b) := h (by rfl)
  have h2 : HEq (Arrow.mk (↾(id : Bool → Bool))).hom (Arrow.mk (↾fun b => !b)).hom := by
    rw [h1]
  have h3 : (↾(id : Bool → Bool) : Bool ⟶ Bool) = ↾fun b => !b := eq_of_heq h2
  have h4 : (↾(id : Bool → Bool) : Bool ⟶ Bool) true = (↾fun b => !b : Bool ⟶ Bool) true := by
    rw [h3]
  simp at h4

-- ============================================================
-- §III — Die Stelle, an der beides zusammentrifft
-- ============================================================

/-- **Das Glied einer Stellung als Objekt.** `Stellung.rel` ist der Morphismus
`L(σ.s) ⟶ σ.k` — und damit ein **Objekt** der Pfeilkategorie über `K`.

Das ist genau die Stelle, an der ein flacher Rollentausch am Typ scheiterte: auf
`Stellung` selbst kann `rel` nicht an die Stelle von `s` oder `k` treten, weil ein
Morphismus kein Objekt ist. Eine Ordnung höher ist er eines — und **nur** dort
(E&W S. 26, Dateikopf).

**Benennung, kein Ertrag** (`CLAUDE.md` §4): die Zeile führt keinen neuen Satzgehalt,
sie benennt die Stelle. Dass dies Günthers Relator-Abstieg *ist*, bleibt Deutung. -/
def arrowOfStellungRel {S K : Type*} [Category S] [Category K]
    {PAS : Reformulation.Proemial.Substantial.ProemialAdjunctionSubstantial S K}
    (σ : Reformulation.Proemial.Substantial.Stellung PAS) : Arrow K :=
  Arrow.mk σ.rel

-- ============================================================
-- §IV — Wachen: Axiom-Profile
-- ============================================================

/-! **Wachen.** Ist-Ausgabe des grünen Builds (v4.30.0-rc2), pro Deklaration eingefroren,
Erwartungstexte verbatim aus der Messung.

**Die arme Hälfte in ihrer generischen Fassung ist axiomfrei** — sie trägt den zweiten der
beiden Ausgabe-Wortlaute (`CLAUDE.md` §8 Fallstrick 15). Ihre zweiwertige Instanz zieht
`[propext]` aus dem `decide` des Zeugen, die Nicht-Vakuanz `[Quot.sound]` aus `funext`.
Die kategoriale Hälfte trägt `[propext, Quot.sound]`; `Classical.choice` erscheint allein
in der Benennung `arrowOfStellungRel` und ist aus der α+γ-Maschinerie geerbt. **Der Weg des
Axioms in den Term ist nicht gemessen** (Fallstrick 10); gemessen ist, welche Deklaration
es trägt und welche nicht. -/

/-- info: 'Reformulation.Proemial.ArrowAscent.no_naming_of_fixpointfree' does not depend on any axioms -/
#guard_msgs in #print axioms no_naming_of_fixpointfree

/-- info: 'Reformulation.Proemial.ArrowAscent.no_naming_two_valued' depends on axioms: [propext] -/
#guard_msgs in #print axioms no_naming_two_valued

/-- info: 'Reformulation.Proemial.ArrowAscent.naming_when_fixpoint' depends on axioms: [Quot.sound] -/
#guard_msgs in #print axioms naming_when_fixpoint

/-- info: 'Reformulation.Proemial.ArrowAscent.arrow_left_id' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms arrow_left_id

/-- info: 'Reformulation.Proemial.ArrowAscent.arrow_left_not_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms arrow_left_not_injective

/-- info: 'Reformulation.Proemial.ArrowAscent.arrowOfStellungRel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms arrowOfStellungRel

end Reformulation.Proemial.ArrowAscent
