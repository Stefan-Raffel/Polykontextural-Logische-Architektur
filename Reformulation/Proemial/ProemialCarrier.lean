import Reformulation.Kenogram.OccupancySeparation
import Reformulation.Proemial.RetractionBracket
import Reformulation.Proemial.TowerAsymmetry
import Reformulation.Proemial.TwoPlaceOccupancy

/-!
# Reformulation.Proemial.ProemialCarrier -- die Verortung des §20-Materials an einer Stelle

**Was diese Datei ist.** Der erste Ort, an dem die verstreuten §20-Teilbefunde des
Bestandes zusammenstehen: die zweistellige kenogrammatische Figur `figNe`, ihre
Faser als Umtausch, die Ordnungslesart derselben zwei Belegungen, der
Stufenaufstieg darueber und die kategoriale Retraktionsseite.

**Was diese Datei nicht ist: ein Traeger fuer §20.** `Carrier` ist eine
Konjunktion aus elf Aussagen, die saemtlich schon im Bestand stehen; neu gebaut
ist nichts. Der Korpus hat die Sprachregel fuer genau diese Gestalt, und sie
steht in `Proemial.TowerAsymmetryProbe`:

> *Die Konjunktion selbst ist trivial, sobald die Teile stehen; ihr Wert liegt
> darin, dass die Merkmale an einem Traeger zusammenkommen. Das ist eine
> Verortung, kein Beweisfortschritt.*

**Kein §20-Anspruch, keine Ledger-Zeile, keine Marke.** §20 bleibt
Quellenparagraph ohne beanspruchten formalen Traeger; die Ledger-Obergrenze
bleibt bei `19 von 20`, und diese Datei ruehrt sie nicht an.

## Vier Gruende, warum die Konjunktion kein Traeger ist

Sie stehen hier, damit die Datei sie selbst fuehrt und niemand sie neu finden muss.

1. **`Carrier` hat keine Argumentstelle.** `RetractionWithoutIso p` ist ein
   Praedikat **ueber einer Abbildung** und war darum mehr als eine Schreibweise:
   es forderte auf der kenogrammatischen Seite einen totalen Schnitt an, den der
   Bestand ohne es nicht trug. `Carrier` ist eine nullstellige Proposition ueber
   festen Objekten; sie kann an nichts geprueft werden und fordert nichts an.
   Das Kriterium steht im Kopf von `Proemial.RetractionBracket`: *fordert sie
   etwas an, oder fasst sie nur zusammen?*

2. **Das elfte Feld liegt auf einem nachweislich getrennten Traeger.**
   `higher_relator_object` erwaehnt `figNe` nicht und beruehrt die
   kenogrammatische Schicht nicht. Die Importhuelle von `Proemial.ArrowAscent`
   enthaelt **null** `Kenogram.*`-Module -- gemessen, und strukturell erzwungen.
   `RetractionBracket` sagt es selbst: dieselbe **Form** gilt ueber beiden, die
   **Gegenstaende** sind nicht dieselben.

3. **Das neunte Feld braucht die Identifikation, die dieser Kopf ausschliesst.**
   `ascent_over_basis` ist eine Aussage ueber die **Stellenzahl**-Achse. Ohne die
   Gleichsetzung RGS-Stufe = Guenthers Relationsordnung sagt es nichts ueber den
   Stufenwechsel von §20 -- und diese Gleichsetzung ist unten ausdruecklich
   ausgeschlossen.

4. **Die Ordnungsseite ist importiert, und das Feld daneben sagt es.**
   `order_actualization` benutzt die Ordnung von `Fin 2`;
   `no_invariant_order_from_fiber` sagt, dass aus der Faser allein kein
   Ordnungsdatum zu gewinnen ist. Beide sind wahr. Zusammen ergeben sie **nicht**
   zwei Aktualisierungen derselben Basis, sondern eine aus der Basis und eine aus
   einem fremden Datum.

## Grenze

Nicht gebaut sind Erkennen/Wollen, die volle Vier-Relata-Simultaneitaet und eine
Identifikation der RGS-Stufe mit Guenthers Relationsordnung. **Und A20-5 -- die
wechselseitige Bedingung -- steht in keinem der elf Felder:** keines sagt, dass
eines der anderen ein anderes bedingt.

Kein `sorry`, kein `axiom`, kein `: True`-Feld, kein `native_decide`.
-/

namespace Reformulation.Proemial.ProemialCarrier

open CategoryTheory
open Reformulation.Kenogram (RGS canonicalize descent)
open Reformulation.Kenogram.OccupancySeparation
open Reformulation.Proemial.RecurringGround (FixpointFree)
open Reformulation.Proemial.ReversibleExchange (Reversible)
open Reformulation.Proemial.RetractionBracket (RetractionWithoutIso)
open Reformulation.Proemial.TwoPlaceOccupancy

-- ============================================================
-- §I -- Die zwei Aktualisierungen derselben Basis
-- ============================================================

/-- Die aufsteigende Belegung, als Punkt der Faser ueber `figNe`. -/
def upActual : DistinctFiber 2 :=
  ⟨upPair, by
    rw [canonicalize_eq_figNe_iff_pointwise]
    decide⟩

/-- Die fallende Belegung, als Punkt derselben Faser ueber `figNe`. -/
def downActual : DistinctFiber 2 :=
  ⟨downPair, by
    rw [canonicalize_eq_figNe_iff_pointwise]
    decide⟩

/-- Die Ordnungsseite in der knappen Form, in der sie vom Traegersatz konsumiert wird. -/
def OrderActualization : Prop :=
  RisingOccupancy upPair ∧ FallingOccupancy downPair

/-- Die Faser liefert kein wertinvariantes Ordnungsdatum. -/
def NoInvariantOrderFromFiber : Prop :=
  ∀ (β : Type) (F : DistinctFiber 2 → β),
    (∀ (π : Equiv.Perm (Fin 2)) (f : DistinctFiber 2), F (permAct π f) = F f) →
      ∀ f g : DistinctFiber 2, F f = F g

-- ============================================================
-- §II -- Der Traeger als Prop
-- ============================================================

/-- Die begrenzte operative Kernform der Proemialrelation.

Alle Felder sind bereits konkrete Saetze ueber die angegebene Basis; die Struktur
fasst sie zusammen, ohne ein `True`-Feld oder eine Setzung einzufuehren. -/
structure Carrier : Prop where
  /-- Die aufsteigende Aktualisierung liegt ueber der zweistelligen Basis. -/
  basis_up : canonicalize upPair = figNe
  /-- Die fallende Aktualisierung liegt ueber derselben Basis. -/
  basis_down : canonicalize downPair = figNe
  /-- Der Faser-Tausch schickt die aufsteigende Aktualisierung auf die fallende. -/
  exchange_up_down : swapOnFiber upActual = downActual
  /-- Und zurueck. -/
  exchange_down_up : swapOnFiber downActual = upActual
  /-- Der Faser-Tausch ist ein Umtausch im Bestandsbegriff. -/
  exchange_reversible : Reversible (swapOnFiber (k := 2))
  /-- Der Faser-Tausch hat keinen Fixpunkt. -/
  exchange_fixpointfree : FixpointFree (swapOnFiber (k := 2))
  /-- Dieselben zwei Punkte tragen die Ordnungslesart. -/
  order_actualization : OrderActualization
  /-- Keine wertpermutations-invariante Faser-Auswertung trennt sie. -/
  no_invariant_order_from_fiber : NoInvariantOrderFromFiber
  /-- Ueber der Basis ist der Stufenaufstieg mehrdeutig. -/
  ascent_over_basis : ∃ a b : RGS 3, a ≠ b ∧ descent a = figNe ∧ descent b = figNe
  /-- Der kenogrammatische Abstieg hat einen Schnitt und ist dennoch kein Iso. -/
  descent_retraction : RetractionWithoutIso (descent : RGS 3 → RGS 2)
  /-- Eine Ordnung hoeher wird ein Pfeil als Objekt gefasst. -/
  higher_relator_object : RetractionWithoutIso (fun f : Arrow Type => f.left)

-- ============================================================
-- §III -- Der Traegersatz
-- ============================================================

/-- **Der §20-Traegersatz.** Die zweistellige kenogrammatische Basis traegt zwei
Aktualisierungen: als Faserpunkte stehen sie im symmetrischen Umtausch, als
Belegungen ueber `Fin 2` in entgegengesetzter Ordnung. Die Ordnung wird nicht aus
der Faser gewonnen (`NoInvariantOrderFromFiber`); der Rollenwechsel erscheint erst
im Stufenaufstieg bzw. eine Ordnung hoeher in der Pfeilkategorie. -/
theorem proemial_carrier : Carrier := by
  refine {
    basis_up := upActual.2
    basis_down := downActual.2
    exchange_up_down := ?_
    exchange_down_up := ?_
    exchange_reversible := swapOnFiber_reversible
    exchange_fixpointfree := swapOnFiber_fixpointfree
    order_actualization := ⟨by decide, by decide⟩
    no_invariant_order_from_fiber := ?_
    ascent_over_basis := Reformulation.Proemial.TowerAsymmetry.ascent_not_determined (by decide) figNe
    descent_retraction := Reformulation.Proemial.RetractionBracket.descent_retraction_zero
    higher_relator_object := Reformulation.Proemial.RetractionBracket.arrow_left_retraction }
  · apply Subtype.ext
    funext i
    match i with
    | ⟨0, _⟩ => rfl
    | ⟨1, _⟩ => rfl
  · apply Subtype.ext
    funext i
    match i with
    | ⟨0, _⟩ => rfl
    | ⟨1, _⟩ => rfl
  · intro β F hF f g
    exact invariant_const_two F hF f g

-- ============================================================
-- §IV -- Wachen: Axiom-Profile
-- ============================================================

/-! **Wachen.** Ist-Ausgabe des gruenen Einzelbuilds. `Classical.choice` kommt
ueber `canonicalize` und die Faserbegriffe herein; die kategoriale und
kenogrammatische Retraktionsseite bleibt in demselben Profil wie ihre
Bestandssaetze. -/

/-- info: 'Reformulation.Proemial.ProemialCarrier.upActual' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms upActual

/-- info: 'Reformulation.Proemial.ProemialCarrier.downActual' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms downActual

/-- info: 'Reformulation.Proemial.ProemialCarrier.proemial_carrier' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms proemial_carrier

end Reformulation.Proemial.ProemialCarrier