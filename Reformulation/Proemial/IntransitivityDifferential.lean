import Mathlib.Order.RelClasses
import Mathlib.Logic.Relation

/-!
# Reformulation.Proemial.IntransitivityDifferential — das Intransitivitäts-Differential (vierzehnte Schicht)

## (1) Quellen-fest

Günther 1937 (*Wahrheit, Wirklichkeit und Zeit*), Druck-Zählung am Roh-PDF
verifiziert:

1. Die Zeit ist von höherer Mächtigkeit als der Wille.
2. Das Denken besitzt höhere Mächtigkeit als die Zeit.
3. Der Wille entwickelt eine höhere Mächtigkeit als das Denken.

Daraus können „niemals drei Aussagegruppen von transitivem Charakter gebildet
werden" — die „mangelnde Transitivität der drei Prinzipien" wörtlich. Die
Reduktion verkettet (2) und (1) gegen (3). Zyklus-Lesefolge
(Denken ≻ Zeit ≻ Wille ≻ Denken) und `cyc3`-Kodierung (0 ≙ Denken, 1 ≙ Zeit,
2 ≙ Wille, erste Stelle dominiert) sind Darstellungs-Wahl dieses Moduls, keine
Quellen-Zählung.

## (2) Term-fest werden hiermit

Beide Hälften des Differentials, in EINER Sprache (Ordnungssprache):

* **arme Klasse** — die strikte Ordnung: Relationen mit `IsTrans` + `Std.Irrefl`
  (= Mathlibs `IsStrictOrder`-Zerlegung in v4.30; `IsIrrefl` ist dort zugunsten
  `Std.Irrefl` deprecated, Asymmetrie folgt). Instanz-quantifiziert über *alle* Träger und *alle*
  Instanzen (`no_cycle_in_strict_order`, `cyc3_not_representable`, `no_return`).
* **reiche Seite** — der Zeuge `cyc3` auf `Fin 3` mit den Ehrlichkeits-Sätzen
  (`cyc3_holds`, `cyc3_irrefl`, `cyc3_not_transitive`): er existiert, ist
  irreflexiv und verlässt die arme Klasse EXAKT an der Transitivität, nirgends
  sonst.

## (3) Marke 3 — Deutung, nicht Behauptung

Die Benennung 0 ≙ Denken, 1 ≙ Zeit, 2 ≙ Wille ist Lesart und lebt nur im
Doc-String. Der Träger `Fin 3` ist neutral; kein Satz dieser Datei kennt sie.

## (4) Abgrenzung

Die reiche Seite ist der *minimale relationale Zeuge*. Ob die modale Triade
selbst den Zyklus trägt, bleibt hier unbehauptet — deren Asymmetrie-Klassifikation
ist Design-Datum (A3 der Gestalt), der zugehörige Swap-Satz ein eigenes Paket
(AP7). Ebenso nicht Teil dieser Schicht: die `ModelTheory`-starke Marke-1-Fassung
(Pfad B, Folge-Paket). Konditional ist hier *nichts*.

## (5) Sorry-Bilanz und Axiom-Stand

0 Sorries. Beide Differential-Hälften sind reine Logik bzw. Kernel-Berechnung
(`decide`); Axiom-Freiheit ist als Nebenbefund erreicht (`#print axioms` am
Datei-Ende: nur die von `decide`/`propext` gezogenen Kern-Axiome, keine
projekteigenen Setzungen).
-/

namespace Reformulation.Proemial.IntransitivityDifferential

/-! ## Teil 1 — Der Zeuge (M1/M4) -/

/-- Der orientierte 3-Zyklus auf `Fin 3`: `cyc3 a b` ↔ `b = a + 1` — die
    Fin-3-Addition zykliert, Paare (0,1), (1,2), (2,0).
    Lesart (Marke 3, NUR Doc-String): erste Stelle dominiert („a ist von
    höherer Mächtigkeit als b"); 0 ≙ Denken, 1 ≙ Zeit, 2 ≙ Wille
    (Günther 1937). Der Träger selbst ist neutral. -/
def cyc3 : Fin 3 → Fin 3 → Prop := fun a b => b = a + 1

instance : DecidableRel cyc3 := fun a b => decEq b (a + 1)

/-- POSITIVE HÄLFTE: der Zyklus-Zeuge existiert als Term. -/
theorem cyc3_holds : cyc3 0 1 ∧ cyc3 1 2 ∧ cyc3 2 0 := by decide

/-- EHRLICHKEIT (1): der Zeuge ist irreflexiv — er verlässt die arme
    Klasse NICHT an der Irreflexivität. (Irreflexivität ausbuchstabiert;
    die benannten Prädikate `Irreflexive`/`Std.Irrefl` sind hier bewusst
    vermieden, siehe Abweichungs-Notiz.) -/
theorem cyc3_irrefl : ∀ a, ¬ cyc3 a a := by decide

/-- EHRLICHKEIT (2): der Zeuge ist nicht transitiv — er verlässt die arme
    Klasse EXAKT an der Transitivität (cyc3 0 1, cyc3 1 2, ¬ cyc3 0 2).
    (Transitivität ausbuchstabiert als `∀ a b c, r a b → r b c → r a c`.) -/
theorem cyc3_not_transitive : ¬ ∀ a b c, cyc3 a b → cyc3 b c → cyc3 a c := by decide

/-! ## Teil 2 — Negative Hälfte, nackte Fassung (M2) -/

/-- NEGATIVE HÄLFTE (nackt), Günthers Reduktion von 1937 gespiegelt:
    in KEINER transitiv-irreflexiven Struktur (strikte Ordnung) existiert
    ein 3-Zyklus. Quantifiziert über alle Träger und alle Instanzen der
    armen Klasse. -/
theorem no_cycle_in_strict_order {α : Type*} (r : α → α → Prop)
    [IsTrans α r] [Std.Irrefl r] :
    ∀ a b c, ¬ (r a b ∧ r b c ∧ r c a) := by
  rintro a b c ⟨hab, hbc, hca⟩
  -- (i) Verkettung — in Günthers Zählung (2) und (1): a ≻ c
  have hac : r a c := trans_of r hab hbc
  -- (ii) Gegenprinzip (3): c ≻ a — steht als hca bereit.
  -- (iii) Asymmetrie-Kollaps: a ≻ c und c ≻ a ergeben a ≻ a,
  --       gegen die Irreflexivität.
  exact irrefl_of r a (trans_of r hac hca)

/-! ## Teil 3 — Negative Hälfte, Darstellbarkeits-Fassung (M3) -/

/-- NEGATIVE HÄLFTE (Darstellbarkeit): es gibt KEIN relations-erhaltendes
    f vom Zyklus in irgendeine strikte Ordnung — auch kollabierende
    Abbildungen scheitern (Kollaps zweier Zyklus-Punkte erzeugt r x x). -/
theorem cyc3_not_representable {α : Type*} (r : α → α → Prop)
    [IsTrans α r] [Std.Irrefl r] :
    ¬ ∃ f : Fin 3 → α, ∀ a b, cyc3 a b → r (f a) (f b) := by
  rintro ⟨f, hf⟩
  exact no_cycle_in_strict_order r (f 0) (f 1) (f 2)
    ⟨hf 0 1 (by decide), hf 1 2 (by decide), hf 2 0 (by decide)⟩

/-! ## Teil 4 — Kür: Zyklen jeder Länge (K1) -/

/-- KÜR: keine Rückkehr in beliebig vielen Schritten — die transitive
    Hülle einer transitiven Relation fällt auf sie zurück. -/
theorem no_return {α : Type*} (r : α → α → Prop)
    [IsTrans α r] [Std.Irrefl r] :
    ∀ a, ¬ Relation.TransGen r a a := by
  intro a h
  have hr : r a a := by rwa [Relation.transGen_eq_self] at h
  exact irrefl_of r a hr

end Reformulation.Proemial.IntransitivityDifferential

/-! ## Axiom-Stand (Nebenbefund) — als Regressions-Wachen gesetzt

Ist-Ausgabe des grünen Builds (v4.30.0-rc2), pro Satz eingefroren. Ab hier bricht jede
Axiom-Drift den Build. `no_cycle_in_strict_order` trägt die Nicht-Abhängigkeits-Form
(axiom-frei), gemessen und nicht nachgebaut. -/

/-- info: 'Reformulation.Proemial.IntransitivityDifferential.cyc3_holds' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Proemial.IntransitivityDifferential.cyc3_holds

/-- info: 'Reformulation.Proemial.IntransitivityDifferential.cyc3_irrefl' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Proemial.IntransitivityDifferential.cyc3_irrefl

/-- info: 'Reformulation.Proemial.IntransitivityDifferential.cyc3_not_transitive' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Proemial.IntransitivityDifferential.cyc3_not_transitive

/-- info: 'Reformulation.Proemial.IntransitivityDifferential.no_cycle_in_strict_order' does not depend on any axioms -/
#guard_msgs in #print axioms Reformulation.Proemial.IntransitivityDifferential.no_cycle_in_strict_order

/-- info: 'Reformulation.Proemial.IntransitivityDifferential.cyc3_not_representable' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Proemial.IntransitivityDifferential.cyc3_not_representable

/-- info: 'Reformulation.Proemial.IntransitivityDifferential.no_return' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.IntransitivityDifferential.no_return
