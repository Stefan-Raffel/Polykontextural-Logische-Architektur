import Reformulation.Kenogram.Descent
import Reformulation.Proemial.ArrowAscent

/-!
# Reformulation.Proemial.RetractionBracket — eine Beweisform, zwei Zeugen

**Ertrag.** Eine gemeinsame Eigenschaft — *es gibt einen Schnitt, und die Abbildung ist
nicht injektiv* — und zwei Nachweise, je einer aus einem Strang:

* **kategorial** — die Objekt-Projektion der Pfeilkategorie;
* **kenogrammatisch** — der Stufenabstieg auf Restringierten Wachstumsfolgen.

## Warum das keine Umbenennung ist

Eine Aussageform, die zwei vorhandene Sätze zusammenfasst, wäre eine Schreibweise und
kein Gehalt. **Diese hier ist es nicht, und der Grund ist prüfbar:** sie **fordert auf der
kenogrammatischen Seite eine Konstruktion an**, die es ohne sie nicht gäbe — einen totalen
Schnitt (§II). Der Bestand trug ihn nicht, weil er ihn nicht brauchte.

**Genau das ist die Bedingung, unter der eine Aussageform mehr ist als eine Schreibweise:
fordert sie etwas an, oder fasst sie nur zusammen?** Hier ist sie erfüllt und nicht
behauptet.

Die Eigenschaft ist eine `Prop` **über einer Abbildung** — kein Bündel über den beiden
Zeugen. Sie spricht über je eine Abbildung; dass zwei verschiedene sie erfüllen, sagen
zwei Sätze und keine Struktur.

## Die Asymmetrie, die diese Klammer zu benennen hat

**Nicht die Sätze sind verschieden geschnitten, sondern die Aufstiege: einer ist total,
einer partiell.**

Kategorial ist der Aufstieg `x ↦ 𝟙 x` — überall definiert, ohne Wahl. Kenogrammatisch ist
er `extend`, und der nimmt eine Stelle und zwei Beweisargumente: **nicht jede Stelle ist
zulässig, und welche genommen wird, sagt die Struktur nicht.** Der Aufstieg **wählt**, und
eine Wahl hat Argumente.

Beide Sätze fallen dennoch **wörtlich** ein — die kategorialen unverändert, der
kenogrammatische mit einer konstruktiven Umformung seiner zweiten Konjunkte (∃-Form in
`¬ Injective`). Was fehlte, war nie eine Aussage, sondern ein **Träger**.

## Die Willkür der Schnittwahl — bewiesen, nicht vermerkt

`kenoAscentZero` wählt die Stelle `0`, `kenoAscentOne` die Stelle `1`. Beide sind
zulässig, beide sind Schnitte, und `kenoAscents_differ` sagt, dass sie **verschieden**
sind. Damit ist die Willkür ein Satz und keine Doc-Zeile: **eine Markierung ohne Route
driftet, ein Satz nicht.**

**Abgrenzung, weil die Nähe täuscht.** Dieser Satz ist **nicht**
`Kenogram.fiber_nontrivial` in anderen Worten. Jener sagt, dass über *einer Stelle* zwei
Urbilder liegen; dieser sagt, dass zwei **konstruierte Schnitte** auseinanderfallen. Nahe
beieinander, und nicht dasselbe — der eine spricht über Fasern, der andere über
Konstruktionen.

**Und die Eigenschaft gilt für den Abstieg darum zweimal** — einmal je Schnitt. Das ist
kein Zierat: es sagt in Satzform, dass der Schnitt **nicht kanonisch** ist.

## Deutungsgrenzen

* Die Eigenschaft ist eine **Beweisform** und keine Aussage über Günther. Dass die beiden
  Zeugen „dasselbe tun", ist die Behauptung dieses Moduls und gilt für die **Form**, nicht
  für den Gegenstand: eine Pfeilkategorie und eine Folgenschicht sind nicht dieselbe Sache,
  auch wenn dieselbe Form über beiden gilt.
* **Dies ist nicht die proemiale Relation** und kein Teil des vollen ρ.

## Offene Marken, unverändert

* **Die Abstiegs-Richtung** — Relatoren injektiv in die Relata — ist nicht gemessen und
  wird nicht behauptet.
* **Die Vier-Relata-Simultaneität** (E&W S. 29) bleibt offen; dieses Modul trägt eine
  Richtung, nicht die Simultaneität.

## Hebungsvermerk

Der kenogrammatische Zeuge ist über `Kenogram.Descent` erreichbar, gehoben aus
`Proemial.A1DescentProbe` und `Proemial.ProemialInversionProbe`. **Beide Sonden bleiben
byte-unverändert als historische Belege**; die Präzedenz ist `Proemial.ExtensionalCollapse`.

Kein `sorry`, kein `axiom`, kein `: True`-Feld.
-/

namespace Reformulation.Proemial.RetractionBracket

open Function CategoryTheory
open Reformulation.Kenogram (RGS descent extend descent_split_epi_not_iso)

-- ============================================================
-- §I — Die Aussageform
-- ============================================================

/-- **Retraktion ohne Injektivität.** Die Abbildung `p` hat einen Schnitt — eine
Rückrichtung, die sie zur Identität ergänzt — und ist dennoch nicht injektiv.

Abwärts kanonisch, aufwärts mehrdeutig: der Schnitt existiert, aber er ist nicht die
Umkehrung, denn eine Umkehrung gäbe es nur bei Injektivität.

Eine `Prop` über **einer** Abbildung; zum Grund, warum das keine Umbenennung ist, siehe
den Dateikopf. -/
def RetractionWithoutIso {A B : Type*} (p : A → B) : Prop :=
  (∃ s : B → A, ∀ b, p (s b) = b) ∧ ¬ Function.Injective p

-- ============================================================
-- §II — Der kenogrammatische Zeuge
-- ============================================================

/-- Der Aufstieg über die Stelle `0` — ein **totaler** Schnitt des Abstiegs. Die Stelle
`0` ist immer zulässig: sie unterschreitet jedes Präfix-Maximum, und über der leeren Folge
ist sie die geforderte.

**Eine Wahl, keine Kanonik.** Siehe `kenoAscentOne` und `kenoAscents_differ`. -/
def kenoAscentZero (r : RGS 2) : RGS 3 :=
  extend r 0 (Nat.zero_le _) (fun _ => rfl)

/-- Der Aufstieg über die Stelle `1` — ebenso zulässig, ebenso ein Schnitt. Die
Zulässigkeit folgt aus der Länge: eine Folge der Länge zwei ist nicht leer, und ihr
Präfix-Maximum ist mindestens `0`. -/
def kenoAscentOne (r : RGS 2) : RGS 3 :=
  extend r 1
    (by
      have h : r.val.length = 2 := r.property.1
      have : 0 ≤ r.val.foldr max 0 := Nat.zero_le _
      omega)
    (fun he => absurd he (by
      intro hnil
      have h : r.val.length = 2 := r.property.1
      rw [hnil] at h
      simp at h))

/-- Die Nicht-Injektivität des Abstiegs in der Form, die die Eigenschaft verlangt.
Konstruktive Umformung der zweiten Konjunkte von `descent_split_epi_not_iso`; die
Gegenrichtung wäre klassisch und wird nicht gebraucht. -/
theorem descent_not_injective' : ¬ Function.Injective (descent : RGS 3 → RGS 2) := by
  intro h
  obtain ⟨a, b, hne, heq⟩ := descent_split_epi_not_iso.2
  exact hne (h heq)

/-- **Der kenogrammatische Zeuge.** Der Stufenabstieg erfüllt die Eigenschaft, mit dem
Aufstieg über die Stelle `0` als Schnitt. -/
theorem descent_retraction_zero :
    RetractionWithoutIso (descent : RGS 3 → RGS 2) :=
  ⟨⟨kenoAscentZero, fun r => descent_split_epi_not_iso.1 r 0 (Nat.zero_le _) (fun _ => rfl)⟩,
   descent_not_injective'⟩

/-- **Derselbe Zeuge, anderer Schnitt.** Die Eigenschaft gilt für den Abstieg auch mit dem
Aufstieg über die Stelle `1`. Zwei Nachweise derselben Eigenschaft über derselben
Abbildung — das ist die Satzform der Aussage, dass der Schnitt nicht kanonisch ist. -/
theorem descent_retraction_one :
    RetractionWithoutIso (descent : RGS 3 → RGS 2) :=
  ⟨⟨kenoAscentOne, fun r => descent_split_epi_not_iso.1 r 1 _ _⟩, descent_not_injective'⟩

/-- **Die Willkür, als Satz.** Die beiden Schnitte fallen auseinander — an `[0,1] : RGS 2`
entscheidbar belegt.

**Nicht `fiber_nontrivial` in anderen Worten:** jener spricht über zwei Urbilder über
einer Stelle, dieser über zwei **konstruierte** Schnitte. -/
theorem kenoAscents_differ :
    kenoAscentZero ⟨[0, 1], by decide⟩ ≠ kenoAscentOne ⟨[0, 1], by decide⟩ := by decide

-- ============================================================
-- §III — Der kategoriale Zeuge
-- ============================================================

/-- **Der kategoriale Zeuge.** Die Objekt-Projektion der Pfeilkategorie über `Type`
erfüllt die Eigenschaft: die Identitätspfeile bilden den Schnitt, und die Projektion
vergisst.

**Beide Sätze fallen unverändert ein** — `arrow_left_id` an die Schnitt-Stelle,
`arrow_left_not_injective` an die andere. Keine Brücke nötig; der getrennte Zuschnitt des
Ordnungswechsel-Zuges war genau dafür da. -/
theorem arrow_left_retraction :
    RetractionWithoutIso (fun f : Arrow Type => f.left) :=
  ⟨⟨fun x => Arrow.mk (𝟙 x), Reformulation.Proemial.ArrowAscent.arrow_left_id⟩,
   Reformulation.Proemial.ArrowAscent.arrow_left_not_injective⟩

-- ============================================================
-- §IV — Die Klammer
-- ============================================================

/-- **Die Klammer.** Beide Stränge instanziieren dieselbe Beweisform.

**Verschaltung, kein neuer Gehalt** — der Satz konsumiert die beiden Zeugen und behauptet
nichts über sie hinaus; die Form ist die des Verbindungssatzes
`Proemial.TowerAsymmetryProbe.tower_asymmetric`. Sein Ertrag ist, dass die Aussage „beide
tun dasselbe" als **ein** Term dasteht und nicht als zwei nebeneinander.

**Was er nicht sagt:** dass die beiden Gegenstände dasselbe sind. Er sagt, dass dieselbe
**Form** über beiden gilt — und die Dateiköpfe sagen, worin sie sich unterscheiden. -/
theorem both_strands_retract :
    RetractionWithoutIso (fun f : Arrow Type => f.left)
    ∧ RetractionWithoutIso (descent : RGS 3 → RGS 2) :=
  ⟨arrow_left_retraction, descent_retraction_zero⟩

-- ============================================================
-- §V — Wachen: Axiom-Profile
-- ============================================================

/-! **Wachen.** Ist-Ausgabe des grünen Builds (v4.30.0-rc2), pro Deklaration eingefroren.

**Die Aussageform selbst ist axiomfrei**; sie trägt darum den zweiten der beiden
Ausgabe-Wortlaute (`CLAUDE.md` §8 Fallstrick 15). Alle übrigen Deklarationen tragen
`[propext, Quot.sound]` — **kein `Classical.choice` im ganzen Modul**, auf beiden Seiten
der Klammer. -/

/-- info: 'Reformulation.Proemial.RetractionBracket.RetractionWithoutIso' does not depend on any axioms -/
#guard_msgs in #print axioms RetractionWithoutIso

/-- info: 'Reformulation.Proemial.RetractionBracket.kenoAscentZero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms kenoAscentZero

/-- info: 'Reformulation.Proemial.RetractionBracket.kenoAscentOne' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms kenoAscentOne

/-- info: 'Reformulation.Proemial.RetractionBracket.descent_not_injective'' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms descent_not_injective'

/-- info: 'Reformulation.Proemial.RetractionBracket.descent_retraction_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms descent_retraction_zero

/-- info: 'Reformulation.Proemial.RetractionBracket.descent_retraction_one' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms descent_retraction_one

/-- info: 'Reformulation.Proemial.RetractionBracket.kenoAscents_differ' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms kenoAscents_differ

/-- info: 'Reformulation.Proemial.RetractionBracket.arrow_left_retraction' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms arrow_left_retraction

/-- info: 'Reformulation.Proemial.RetractionBracket.both_strands_retract' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms both_strands_retract

end Reformulation.Proemial.RetractionBracket
