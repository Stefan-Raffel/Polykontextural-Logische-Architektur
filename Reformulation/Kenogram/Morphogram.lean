import Reformulation.Kenogram.Bridge
import Reformulation.Kenogram.Operational

/-!
# Reformulation.Kenogram.Morphogram — die Muster-Relation und ihre drei Brücken

**Ertrag, klein.** Die Einzelstücke existieren im Zweig seit S1/S2/S2b — `relabel`
als Normalform, `rgs_unique_of_pattern` als Eindeutigkeit, die Reduktionssemantik
mit `soundness`/`nf_eq_relabel`, die Strom-Brücke `relabelStream_take_eq_relabel`.
Was nicht existierte, ist die **benannte Relation**, die sie verbindet, und die
Sätze, die zeigen, dass drei ganz verschieden gebaute Begriffe dieselbe Relation
sind. Der Dateiname sagt, was gebaut ist: `Morphogram` — nicht `TritoStructure`
und nicht `GuentherMorphogrammatik`.

## Der Dreiklang

| Fassung | Ort |
|---|---|
| `SamePattern xs ys := relabel xs = relabel ys` | Definition (gleiche Normalform) |
| gleiche Länge und gleiches Positionsmuster | `samePattern_iff_pattern` (B1) |
| gemeinsames Reduktionsziel in Normalform | `samePattern_iff_common_nf` (B2) |
| präfixstabil gegen die Strom-Normalform | `samePattern_stream_take` (B3) |

Die Relation ist **heterogen** definiert — `xs : List α`, `ys : List β` —, weil
das Morphogramm gerade die Behauptung ist, dass die Wertsorte nicht zählt:
`[a, b, b, a, c]` und `[x, y, y, x, z]` tragen dasselbe Muster
(`Definitionen.md` §16). Die Äquivalenzeigenschaften stehen darum zweimal:
typübergreifend als `samePattern_refl`/`_symm`/`_trans` (Transitivität über drei
möglicherweise verschiedene Typen), und je festem Typ gebündelt als
`samePattern_equivalence`. Entscheidbar ist die Relation über
`DecidableEq (List ℕ)` auf den Normalformen; die Instanz steht als
`unfold SamePattern; infer_instance` (Fallstrick 2, CLAUDE.md §8: `SamePattern`
ist ein `def` und darum für `decide` opak — die Instanz löst genau das).

## Die Trito-Grenze

Getragen ist die **Positionsmuster-Ebene** (Trito-Struktur als RGS-Normalform).
Die Wertbesetzungs-Fragen von `Definitionen.md` §16 — Achter-Tafel,
trans-klassische Morphogramme, die Wertbesetzungs-Fälle 1 bis 3 — sind **nicht**
formalisiert und werden im Ledger als offen geführt (L16-6). §14
(Zyklus/Selbstzyklus) ist nicht Gegenstand dieser Datei.

**Kein Quotientstyp.** Es gibt keinen `Morphogramm`-Typ als `Quotient` und keine
`Setoid`-Instanz mit Quotient-Konsum. Der Grund ist nicht Scheu vor dem Aufwand
allein, sondern die Reihenfolge: ein Quotient bindet Anschluss- und
Transportaufwand (Lifting jeder Operation, Wohldefiniertheits-Pflichten) an einen
Begriff, dessen Normalformsemantik noch nicht ausgeschöpft ist. Erst stabile
Brückensätze, dann der Quotient — nicht umgekehrt. Deutero- und
Proto-Vergröberungen sind benannter Folge-Posten, kein Versprechen dieser Datei.

## Konsum

- `Kenogram.Basic`: `relabel`, `relabel_length`, `relabel_isRGS`,
  `relabel_getElem?_eq_iff`, `relabel_eq_self_of_isRGS`, `rgs_unique_of_pattern`
  (L16-1/L16-2) — Träger von B1.
- `Kenogram.Operational`: `Reduces` (`↝*`), `soundness`, `nf_eq_relabel` — Träger
  von B2.
- `Kenogram.Stream`: `relabelStream`, `relabelStream_eq_iff` — Träger von B3 und
  der Kür.
- `Kenogram.Bridge`: `relabelStream_take_eq_relabel`, `isRGSStream_take`,
  `take_val_getElem?` — Träger von B3 und der Kür.

Kein Bestandsbeweis ist nachgebaut: weder `rgs_unique_of_pattern` noch
`nf_unique` erscheinen hier in eigener Fassung, sie werden angewandt.

0 Sorries. Axiom-Ist je Satz verwacht (Teil 7): die vier Äquivalenz-Sätze
axiomfrei, die vier Brückensätze `[propext, Classical.choice, Quot.sound]` —
**geerbt, nicht hier erzeugt.** `Classical.choice` tritt in diesem Zweig an
`relabel_isRGS`/`relabel_foldl_spec` ein und stammt dort aus Mathlibs
`List.idxOf?_eq_some_iff`; `rgs_unique_of_pattern` und `relabel_length` sind
selbst classical-frei. Vermeidbar wäre es nur durch einen Nachbau der
Bestandsbeweise, und der wäre kein Konsum.
-/

namespace Reformulation.Kenogram.Morphogram

open Reformulation.Kenogram Reformulation.Kenogram.Stream Reformulation.Kenogram.Bridge

variable {α β γ : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq γ]

/-! ## Teil 1 — die Relation -/

/-- **Muster-Gleichheit (Morphogramm-Identität auf der Trito-Ebene):** zwei Listen
tragen dasselbe Muster, wenn sie dieselbe RGS-Normalform haben. Heterogen in den
Wertsorten — genau das ist die Pointe des Morphogramms. -/
def SamePattern (xs : List α) (ys : List β) : Prop :=
  relabel xs = relabel ys

/-- Entscheidbarkeit über `DecidableEq (List ℕ)`; `unfold` gegen die
`def`-Opazität (Fallstrick 2). -/
instance (xs : List α) (ys : List β) : Decidable (SamePattern xs ys) := by
  unfold SamePattern; infer_instance

/-- Reflexivität. -/
theorem samePattern_refl (xs : List α) : SamePattern xs xs := rfl

/-- Symmetrie, typübergreifend. -/
theorem samePattern_symm {xs : List α} {ys : List β} (h : SamePattern xs ys) :
    SamePattern ys xs := h.symm

/-- Transitivität über **drei** möglicherweise verschiedene Wertsorten — die
Gleichheitskette läuft in `List ℕ`, nicht in den Trägertypen. -/
theorem samePattern_trans {xs : List α} {ys : List β} {zs : List γ}
    (h₁ : SamePattern xs ys) (h₂ : SamePattern ys zs) : SamePattern xs zs :=
  h₁.trans h₂

/-- **Je festem Typ eine Äquivalenzrelation.** Kein `Setoid`, kein Quotient: die
Bündelung sagt, was gilt, und nicht, was daraus gebaut werden soll. -/
theorem samePattern_equivalence (α : Type*) [DecidableEq α] :
    Equivalence (SamePattern (α := α) (β := α)) :=
  ⟨samePattern_refl, samePattern_symm, samePattern_trans⟩

/-! ## Teil 2 — B1: die Muster-Charakterisierung -/

/-- **B1 — Muster-Charakterisierung.** Zwei Listen tragen genau dann dasselbe
Muster, wenn sie gleich lang sind und an denselben Stellenpaaren übereinstimmen.
Verbindet L16-1 (`relabel`) mit L16-2 (`rgs_unique_of_pattern`): die
Hin-Richtung transportiert das Muster über `relabel_getElem?_eq_iff`, die
Rück-Richtung schließt aus Länge und Muster auf Gleichheit der Normalformen. -/
theorem samePattern_iff_pattern (xs : List α) (ys : List β) :
    SamePattern xs ys ↔
      (xs.length = ys.length ∧ ∀ i j : ℕ, xs[i]? = xs[j]? ↔ ys[i]? = ys[j]?) := by
  constructor
  · intro h
    refine ⟨?_, fun i j => ?_⟩
    · have hx := relabel_length xs
      have hy := relabel_length ys
      rw [h] at hx
      omega
    · rw [← relabel_getElem?_eq_iff xs i j, ← relabel_getElem?_eq_iff ys i j, h]
  · rintro ⟨hlen, hpat⟩
    refine rgs_unique_of_pattern (relabel_isRGS xs) (relabel_isRGS ys) ?_ ?_
    · rw [relabel_length, relabel_length, hlen]
    · intro i j
      rw [relabel_getElem?_eq_iff xs i j, relabel_getElem?_eq_iff ys i j]
      exact hpat i j

/-! ## Teil 3 — B2: die operationale Charakterisierung -/

/-- **B2 — operationale Charakterisierung.** Muster-Gleichheit **ist** das
Zusammenlaufen der Reduktion: zwei Listen tragen genau dann dasselbe Muster, wenn
sie ein gemeinsames Reduktionsziel in Normalform haben. Nur über `List ℕ`, weil
die Reduktionssemantik dort lebt. Hin-Richtung über `soundness` mit
`m := relabel l`, Rück-Richtung über `nf_eq_relabel` beidseitig. -/
theorem samePattern_iff_common_nf (l r : List ℕ) :
    SamePattern l r ↔ ∃ m, (l ↝* m) ∧ (r ↝* m) ∧ IsRGS m := by
  constructor
  · intro h
    refine ⟨relabel l, soundness l, ?_, relabel_isRGS l⟩
    have h' : relabel r = relabel l := h.symm
    rw [← h']
    exact soundness r
  · rintro ⟨m, hl, hr, hm⟩
    have h1 : m = relabel l := nf_eq_relabel hl hm
    have h2 : m = relabel r := nf_eq_relabel hr hm
    exact h1.symm.trans h2

/-! ## Teil 4 — B3: Präfix-Verträglichkeit gegen die Strom-Normalform -/

/-- **B3 — Präfixstabilität.** Jedes `n`-Präfix einer Folge trägt dasselbe Muster
wie das `n`-Präfix ihres Kenogramm-Stroms. Konsum der S1↔S2-Brücke
(`relabelStream_take_eq_relabel`) plus `relabel_eq_self_of_isRGS` auf dem
RGS-Präfix (`isRGSStream_take`). -/
theorem samePattern_stream_take (s : Stream' α) (n : ℕ) :
    SamePattern (s.take n) ((relabelStream s).val.take n) := by
  have hrgs : IsRGS ((relabelStream s).val.take n) :=
    isRGSStream_take (relabelStream s).val (relabelStream s).property n
  show relabel (s.take n) = relabel ((relabelStream s).val.take n)
  rw [relabel_eq_self_of_isRGS hrgs, relabelStream_take_eq_relabel]

/-! ## Teil 5 — Kür: alle Präfixe gegen die Strom-Normalform -/

/-- **Kür.** Zwei Folgen haben genau dann durchweg mustergleiche Präfixe, wenn
ihre Kenogramm-Ströme gleich sind. Die Hin-Richtung wählt zu je zwei Stellen das
Präfix `max i j + 1`, das beide enthält; die Rück-Richtung liest das punktweise
Muster aus `relabelStream_eq_iff` und geht über B1 zurück auf die Präfixe. -/
theorem samePattern_take_iff_relabelStream_eq (f g : Stream' α) :
    (∀ n, SamePattern (f.take n) (g.take n)) ↔ relabelStream f = relabelStream g := by
  rw [relabelStream_eq_iff]
  constructor
  · intro h i j
    have hn := ((samePattern_iff_pattern (f.take (max i j + 1))
      (g.take (max i j + 1))).mp (h (max i j + 1))).2 i j
    rw [take_val_getElem?, take_val_getElem?, take_val_getElem?,
      take_val_getElem?] at hn
    rw [if_pos (by omega), if_pos (by omega), if_pos (by omega),
      if_pos (by omega)] at hn
    constructor
    · intro hf; exact Option.some_injective _ (hn.mp (by rw [hf]))
    · intro hg; exact Option.some_injective _ (hn.mpr (by rw [hg]))
  · intro hpat n
    refine (samePattern_iff_pattern (f.take n) (g.take n)).mpr ⟨?_, fun i j => ?_⟩
    · rw [Stream'.length_take, Stream'.length_take]
    · rw [take_val_getElem?, take_val_getElem?, take_val_getElem?,
        take_val_getElem?]
      by_cases hi : i < n
      · by_cases hj : j < n
        · rw [if_pos hi, if_pos hj, if_pos hi, if_pos hj]
          constructor
          · intro hf; rw [(hpat i j).mp (Option.some_injective _ hf)]
          · intro hg; rw [(hpat i j).mpr (Option.some_injective _ hg)]
        · rw [if_pos hi, if_neg hj, if_pos hi, if_neg hj]; simp
      · by_cases hj : j < n
        · rw [if_neg hi, if_pos hj, if_neg hi, if_pos hj]; simp
        · rw [if_neg hi, if_neg hj, if_neg hi, if_neg hj]

/-! ## Teil 6 — Statement-Pins

Voller Wortlaut links, Satz rechts — jede Drift des *Statements* bricht den Build.
Namenlose `example`s für die beiden Charakterisierungen (B1, B2). -/

-- STATEMENT-PIN
example (xs : List α) (ys : List β) :
    SamePattern xs ys ↔
      (xs.length = ys.length ∧ ∀ i j : ℕ, xs[i]? = xs[j]? ↔ ys[i]? = ys[j]?) :=
  samePattern_iff_pattern xs ys

-- STATEMENT-PIN
example (l r : List ℕ) :
    SamePattern l r ↔ ∃ m, (l ↝* m) ∧ (r ↝* m) ∧ IsRGS m :=
  samePattern_iff_common_nf l r

/-! ## Teil 7 — die Axiom-Wachen (Ist-gebunden)

Ist-Ausgabe des grünen Builds (v4.30.0-rc2), pro Satz eingefroren
(Datei-Vollständigkeits-Regel: alle acht Sätze der Datei). **Die vier
Brückensätze ziehen `Classical.choice`** — geerbt, nicht hier erzeugt: die
Quelle liegt in `Basic` (`relabel_isRGS`, `relabel_foldl_spec`) und von dort in
Mathlibs `List.idxOf?_eq_some_iff`; `rgs_unique_of_pattern` selbst ist
classical-frei. Konsum erbt das Profil der Quelle und unterbietet es nicht. Die
vier Äquivalenz-Sätze sind **axiomfrei** — sie laufen über `rfl`/`Eq.symm`/
`Eq.trans` und berühren die `relabel`-Maschinerie nicht. Kein `sorryAx`. -/

/-- info: 'Reformulation.Kenogram.Morphogram.samePattern_refl' does not depend on any axioms -/
#guard_msgs in #print axioms samePattern_refl

/-- info: 'Reformulation.Kenogram.Morphogram.samePattern_symm' does not depend on any axioms -/
#guard_msgs in #print axioms samePattern_symm

/-- info: 'Reformulation.Kenogram.Morphogram.samePattern_trans' does not depend on any axioms -/
#guard_msgs in #print axioms samePattern_trans

/-- info: 'Reformulation.Kenogram.Morphogram.samePattern_equivalence' does not depend on any axioms -/
#guard_msgs in #print axioms samePattern_equivalence

/--
info: 'Reformulation.Kenogram.Morphogram.samePattern_iff_pattern' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms samePattern_iff_pattern

/--
info: 'Reformulation.Kenogram.Morphogram.samePattern_iff_common_nf' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms samePattern_iff_common_nf

/--
info: 'Reformulation.Kenogram.Morphogram.samePattern_stream_take' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms samePattern_stream_take

/--
info: 'Reformulation.Kenogram.Morphogram.samePattern_take_iff_relabelStream_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms samePattern_take_iff_relabelStream_eq

end Reformulation.Kenogram.Morphogram
