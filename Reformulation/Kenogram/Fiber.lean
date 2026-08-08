import Mathlib.Data.Fintype.Pi
import Reformulation.Kenogram.Fillability
import Reformulation.Kenogram.Unbounded

/-!
# Kenogram.Fiber — die Faser der Kanonisierung und der zweite Zeuge

**Ertrag, zweifach geschnitten.** Diese Datei löst die beiden freigestellten Kür-Stücke
des Morphogramm-Zugs ein.

- **Die Faser-Aussage** — `fiberEquiv`: für jede zweiwertig besetzbare Klasse der Länge 4
  ist der Urbildtyp **zweielementig**, und zwar als Äquivalenz zu `Bool` und nicht als
  importierte Kardinalzahl. Dazu `card_bool_fun_eq_two_mul`: die Gleichung
  `16 = 2 · 8` zwischen zwei **Korpus**-Kardinalitäten — Günthers eigene Rechnung aus
  `Definitionen.md` §16.
- **Der zweite Zeuge** — `witness_over_three`: `[0,1,2,3]` ist von keinem dreiwertigen,
  wohl aber von einem vierwertigen System besetzbar. Nicht bloss ein zweites
  `¬ MarksLeOne`, sondern die **Trennung der Stufen drei und vier**.

## Warum ein eigenes Modul

`Unbounded` importiert `Fillability` (gemessen an den Kopfzeilen beider Dateien). Der
Zeugensatz braucht `Unbounded.MarksLt`, die Faser-Aussage braucht `Fillability`; stünde
beides in `Fillability`, entstünde ein Importzyklus. Der Slot, den der Kopf von
`Fillability` reserviert hat („soweit nicht die Kür die `n = 4`-Faser als Satz trägt"),
reservierte den **Satz** und nicht die **Datei**; er ist hiermit eingelöst.

## Die Form, und warum sie so gewählt ist

`fiberEquiv` ist eine **Äquivalenz** und keine `Fintype.card`-Gleichung. Der Grund ist
nicht Geschmack: `canonicalize` ist `noncomputable`, und eine Kartenfassung der Faser
bräuchte eine `Fintype`-Instanz über einem unentscheidbaren Prädikat — ohne Not. „Genau
zwei Urbilder" *ist* diese Äquivalenz.

`card_bool_fun_eq_two_mul` steht daneben und **konsumiert `fiberEquiv` nicht im
Beweisterm**: beide Seiten sind Korpus-Kardinalitäten mit bestehenden Instanzen, und der
Weg über eine Sigma-Zerlegung verlangte genau die Fintype-Instanz über der Faser, die die
Äquivalenzform vermeidet. **Die Faser ist der Grund für den Faktor zwei, nicht sein
Beweis** — und das steht hier, statt eine Konsum-Beziehung zu behaupten, die der Term
nicht trägt.

## Die n-Grenze bleibt

Die Faser-Aussage steht für `n = 4`. Die allgemeine `2^(n−1)`-Bijektion ist **Nicht-Ziel**
der Eltern-Spezifikation und wird hier auch dann nicht gebaut, wenn der Beweis sie fast
hergäbe: die Rückrichtung liefe generisch, die Zählung nicht.

## Deutungsgrenzen

Die Tafelnummern `[15]₄` und `[5]₄` sind **Günthers Zählung** aus `Definitionen.md` §16;
die Zuordnung zu unseren Klassen bleibt **Deutung**, wie in L16-8. Kein
Deklarationsname trägt eine Tafelnummer. Die Wahrheitstafel-Lesung setzt die gewählte
Zeilenordnung voraus — unverändert gegenüber der Eltern-Spezifikation.

## Aggregat-Reife

Konsumiert `Fillability` und `Unbounded` — beides Aggregat — sowie Mathlib. Keine Sonde,
keine Setzung.

Kein `sorry`, kein `axiom`, kein `: True`-Feld.
-/

namespace Reformulation.Kenogram.Fiber

open Reformulation.Kenogram
open Reformulation.Kenogram.Fillability (MarksLeOne marksLeOne_iff_fillable
  canonicalize_rgsFun card_rgs_four_fillable)
open Reformulation.Kenogram.Unbounded (MarksLt)

/-! ## Teil 1 — die Faser der Kanonisierung bei `n = 4` -/

/-- Die erste Marke eines RGS ist die Null — als Aussage über `rgsFun`, weil die Faser
sie in dieser Gestalt braucht. Privat; kein eigener Posten. -/
private theorem rgsFun_zero {n : ℕ} (r : RGS n) (h : 0 < n) :
    rgsFun r ⟨0, h⟩ = 0 := by
  show r.1[(0 : ℕ)]'_ = 0
  exact isRGS_head r.2.2 (by rw [r.2.1]; exact h)

/-- Das Musterkriterium der Faser: unter `MarksLeOne` stimmt eine Stelle genau dann mit
der ersten überein, wenn ihre Marke null ist. Privat. -/
private theorem eq_head_iff_mark_zero {n : ℕ} {r : RGS n} (h : 0 < n)
    {f : Fin n → Bool} (hf : canonicalize f = r) (i : Fin n) :
    f i = f ⟨0, h⟩ ↔ rgsFun r i = 0 := by
  have hcan : canonicalize f = canonicalize (rgsFun r) := by
    rw [hf, canonicalize_rgsFun]
  have := (canonicalize_eq_iff f (rgsFun r)).mp hcan i ⟨0, h⟩
  rw [this, rgsFun_zero r h]

/-- **Die Faser-Aussage.** Für jede zweiwertig besetzbare Klasse der Länge 4 ist der
Urbildtyp der Kanonisierung **zweielementig**: die beiden Urbilder unterscheiden sich
genau darin, welchen Wahrheitswert die erste Stelle trägt.

In Bijektionsform und nicht als Kardinalzahl — `canonicalize` ist `noncomputable`, und
die Karte der Faser bräuchte eine Instanz über einem unentscheidbaren Prädikat. -/
def fiberEquiv {r : RGS 4} (hr : MarksLeOne r) :
    {f : Fin 4 → Bool // canonicalize f = r} ≃ Bool where
  toFun f := f.1 ⟨0, by omega⟩
  invFun b :=
    ⟨fun i => if rgsFun r i = 0 then b else !b, by
      have hmem : ∀ i : Fin 4, rgsFun r i ≤ 1 := fun i => hr _ (List.getElem_mem _)
      have hpat : ∀ i j : Fin 4,
          ((if rgsFun r i = 0 then b else !b) = (if rgsFun r j = 0 then b else !b))
            ↔ rgsFun r i = rgsFun r j := by
        intro i j
        have hi := hmem i
        have hj := hmem j
        by_cases h0i : rgsFun r i = 0 <;> by_cases h0j : rgsFun r j = 0 <;>
          simp [h0i, h0j] <;> omega
      calc canonicalize (fun i => if rgsFun r i = 0 then b else !b)
          = canonicalize (rgsFun r) := (canonicalize_eq_iff _ _).mpr hpat
        _ = r := canonicalize_rgsFun r⟩
  left_inv := by
    rintro ⟨f, hf⟩
    apply Subtype.ext
    funext i
    by_cases h0 : rgsFun r i = 0
    · simp only [h0, if_pos]
      exact ((eq_head_iff_mark_zero (by omega) hf i).mpr h0).symm
    · simp only [h0, if_false]
      have hne : f i ≠ f ⟨0, by omega⟩ := fun hc =>
        h0 ((eq_head_iff_mark_zero (by omega) hf i).mp hc)
      cases hfi : f i <;> cases hf0 : f ⟨0, by omega⟩ <;>
        simp_all
  right_inv := by
    intro b
    show (if rgsFun r ⟨0, by omega⟩ = 0 then b else !b) = b
    rw [rgsFun_zero r (by omega), if_pos rfl]

/-- **Die Gleichung `16 = 2 · 8`** — Günthers Rechnung aus `Definitionen.md` §16,
zwischen zwei Kardinalitäten des Korpus: die binären Wahrheitstafeln der Länge 4 links,
die zweiwertig besetzbaren Morphogramme rechts.

Der Faktor zwei ist die Faser aus `fiberEquiv`; **im Beweisterm wird sie nicht
konsumiert** (siehe Modul-Kopf). Beide Seiten tragen bestehende Instanzen; das
Axiomprofil ist das von `card_rgs_four_fillable`, geerbt. -/
theorem card_bool_fun_eq_two_mul :
    Fintype.card (Fin 4 → Bool) = 2 * Fintype.card {r : RGS 4 // MarksLeOne r} := by
  rw [card_rgs_four_fillable]
  decide

/-! ## Teil 2 — der zweite Zeuge, als Trennung der Stufen -/

/-- **Der zweite Zeuge, schärfer als eine blosse Nicht-Besetzbarkeit.** Das Morphogramm
`[0,1,2,3]` — die Normalform der Wertfolge `(1,2,3,4)` — ist von **keinem** dreiwertigen
und von **einem** vierwertigen System besetzbar.

Mit `Unbounded.marksLt_iff_fillable` liest sich das als Aussage über Besetzbarkeit; die
Zuordnung zu Günthers Tafelnummer bleibt **Deutung** und steht in keinem Namen. -/
theorem witness_over_three :
    ¬ MarksLt 3 (⟨[0, 1, 2, 3], by decide⟩ : RGS 4)
      ∧ MarksLt 4 (⟨[0, 1, 2, 3], by decide⟩ : RGS 4) := by
  constructor
  -- `Unbounded` traegt bewusst keine `Decidable`-Instanz fuer `MarksLt` — dort wird
  -- nichts entschieden. Statt eine Instanz nachzureichen, wird die Aussage auf ihre
  -- definitionsgleiche Gestalt gebracht; das ist die `show`-Route des Trakts.
  · show ¬ ∀ v ∈ [0, 1, 2, 3], v < 3
    decide
  · show ∀ v ∈ [0, 1, 2, 3], v < 4
    decide

/-- **Das Gegenstück am Bestandszeugen.** `[0,1,2,0]` ist von keinem zweiwertigen und von
einem dreiwertigen System besetzbar. Zusammen mit `witness_over_three` trennt das
Zeugenpaar die Stufen zwei, drei und vier. -/
theorem witness_over_two :
    ¬ MarksLt 2 (⟨[0, 1, 2, 0], by decide⟩ : RGS 4)
      ∧ MarksLt 3 (⟨[0, 1, 2, 0], by decide⟩ : RGS 4) := by
  constructor
  · show ¬ ∀ v ∈ [0, 1, 2, 0], v < 2
    decide
  · show ∀ v ∈ [0, 1, 2, 0], v < 3
    decide

/-! ## Teil 3 — Statement-Pins

Ein Pin nagelt den vollen Wortlaut fest: ein geschwächter Satz mit gleichem Axiomprofil
käme durch eine Wache hindurch, aber nicht hier vorbei. Namenlose `example`s, keine
Axiom-Wache. -/

-- STATEMENT-PIN
example {r : RGS 4} (hr : MarksLeOne r) :
    {f : Fin 4 → Bool // canonicalize f = r} ≃ Bool := fiberEquiv hr
-- STATEMENT-PIN
example : Fintype.card (Fin 4 → Bool) = 2 * Fintype.card {r : RGS 4 // MarksLeOne r} :=
  card_bool_fun_eq_two_mul
-- STATEMENT-PIN
example :
    ¬ MarksLt 3 (⟨[0, 1, 2, 3], by decide⟩ : RGS 4)
      ∧ MarksLt 4 (⟨[0, 1, 2, 3], by decide⟩ : RGS 4) := witness_over_three

/-! ## Teil 4 — die Axiom-Wachen (Ist-gebunden)

Ist-Ausgabe des grünen Builds (v4.30.0-rc2), je nicht-private Deklaration eingefroren;
die privaten Hilfslemmata tragen nach der Präzedenz des Trakts keine eigene Wache. Die
Wache für `fiberEquiv` steht, weil ein `Equiv`-`def` Beweisanteil in `left_inv` und
`right_inv` trägt — dieselbe Entscheidung wie bei `ChoiceVectors.locallyClassicalEquiv`. -/

/-- info: 'Reformulation.Kenogram.Fiber.fiberEquiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms fiberEquiv

/-- info: 'Reformulation.Kenogram.Fiber.card_bool_fun_eq_two_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms card_bool_fun_eq_two_mul

/-- info: 'Reformulation.Kenogram.Fiber.witness_over_three' does not depend on any axioms -/
#guard_msgs in #print axioms witness_over_three

/-- info: 'Reformulation.Kenogram.Fiber.witness_over_two' does not depend on any axioms -/
#guard_msgs in #print axioms witness_over_two

end Reformulation.Kenogram.Fiber
