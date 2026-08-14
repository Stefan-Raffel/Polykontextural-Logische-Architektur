import Mathlib.Order.Partition.Finpartition
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Reformulation.Kenogram.PartitionDescent — echte Vergröberung senkt die Blockzahl

**Ertrag.** Zwei Sätze über den Partitionsverband einer endlichen Menge:

1. **Der Abstieg** (`card_parts_lt_of_lt`) — verfeinert `P` die Partition `Q`
   **echt**, so hat `P` echt mehr Blöcke. Damit ist die Wohlfundiertheit des
   Verbands in der Form verfügbar, in der eine Rekursion sie braucht:
   `termination_by #p.parts`.
2. **Das Korollar** (`eq_of_le_of_card_eq`) — Verfeinerung bei gleicher Blockzahl
   erzwingt Gleichheit. Es trägt die Antichain-Eigenschaft der Ränge und gehört
   mit dem Satz zusammen geführt.

## Wo die Beweislast sitzt

**Die Ungleichung ist geschenkt.** `Finpartition.card_mono` liefert
`#Q.parts ≤ #P.parts` aus `P ≤ Q`; Mathlib beweist sie über eine **Injektion**
`Q.parts ↪ P.parts`, die jedem `Q`-Block einen darin enthaltenen `P`-Block
zuordnet.

**Die Arbeit liegt im Gleichheitsfall**, und sie läuft so: bei gleicher Blockzahl
ist das Bild jener Injektion ganz `P.parts`; die Summe der Blockgrössen ist auf
beiden Seiten `#s` (`Finpartition.sum_card_parts`, zweimal); daraus folgt
termweise Gleichheit (`Finset.sum_eq_sum_iff_of_le`), also `f q = q` für jeden
`Q`-Block, also `Q ≤ P` und mit der Voraussetzung `P = Q` — im Widerspruch zur
Striktheit.

## Reichweite

Bewiesen fuer `Finpartition` ueber einem `Finset`. Ob die Aussage fuer
`Finpartition` ueber beliebigen Verbaenden gilt, ist **nicht gemessen**:
`sum_card_parts` steht nur im `Finset`-Fall.

## Grenze

Kein Paragraph-20-Anspruch. Der Satz ist die Wohlfundiertheit des
Partitionsverbands in nutzbarer Form und sagt nichts ueber die Proemialrelation.

## Mathlib

Am 14. August 2026 in Mathlib nicht gefunden (`exact?`, Namenssuche
`Finpartition.*card*`). Die monotone Vorstufe steht dort als
`Finpartition.card_mono` (`Order/Partition/Finpartition.lean:311`), die
Traegergroessen-Fassung als `Finpartition.card_parts_le_card` (ebd. 773) — sie
ist dort aus `card_mono` in zwei Zeilen bewiesen. Ob eingereicht wird, ist nicht
entschieden.

## Ablage

Das Modul importiert **kein** `Proemial`-Modul; es importiert überhaupt keinen
`Reformulation`-Bestand, weil es ihn nicht braucht. Die γ-Freiheit des
Kenogram-Zweigs bleibt Datei-Eigenschaft.
-/

namespace Reformulation.Kenogram

open Finset

variable {α : Type*} [DecidableEq α] {s : Finset α}

/-- **Der Abstieg.** Verfeinert `P` die Partition `Q` echt, so hat `P` echt mehr
Blöcke. Der Beweis führt den Gleichheitsfall zum Widerspruch: bei gleicher
Blockzahl fällt die von `card_mono` gelieferte Injektion mit der Identität
zusammen, und dann sind beide Partitionen gleich. -/
theorem card_parts_lt_of_lt {P Q : Finpartition s} (h : P < Q) :
    #Q.parts < #P.parts := by
  rcases lt_or_eq_of_le (Finpartition.card_mono h.le) with hlt | heq
  · exact hlt
  exfalso
  -- zu jedem `Q`-Block ein darin enthaltener `P`-Block
  have hex : ∀ b : {x // x ∈ Q.parts}, ∃ c ∈ P.parts, c ≤ (b : Finset α) :=
    fun b => Finpartition.exists_le_of_le h.le b.2
  choose f hfP hfle using hex
  have hinj : Function.Injective f := by
    intro b c hfe
    apply Subtype.coe_injective
    by_contra hne
    exact P.ne_bot (hfP b) <| disjoint_self.1 <|
      (Q.disjoint b.2 c.2 hne).mono (hfle b) (hfe ▸ hfle c)
  -- bei gleicher Blockzahl ist das Bild ganz `P.parts`
  have himg : Q.parts.attach.image f = P.parts := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp hx
      exact hfP b
    · rw [Finset.card_image_of_injective _ hinj, card_attach, heq]
  -- beide Seiten summieren zu `#s`
  have hsum : ∑ b ∈ Q.parts.attach, #(f b) = #s := by
    rw [← P.sum_card_parts, ← himg, Finset.sum_image]
    intro x _ y _ hxy; exact hinj hxy
  have hsumQ : ∑ b ∈ Q.parts.attach, #(b : Finset α) = #s := by
    rw [Finset.sum_attach _ (fun t => #t)]; exact Q.sum_card_parts
  have hle : ∀ b ∈ Q.parts.attach, #(f b) ≤ #(b : Finset α) :=
    fun b _ => Finset.card_le_card (hfle b)
  have heqterm : ∀ b ∈ Q.parts.attach, #(f b) = #(b : Finset α) :=
    (Finset.sum_eq_sum_iff_of_le hle).mp (by rw [hsum, hsumQ])
  -- termweise Gleichheit macht die Injektion zur Identität
  have hfeq : ∀ b : {x // x ∈ Q.parts}, f b = (b : Finset α) :=
    fun b => Finset.eq_of_subset_of_card_le (hfle b) (le_of_eq (heqterm b (mem_attach _ b)).symm)
  have hPQ : P = Q := by
    apply le_antisymm h.le
    intro q hq
    have hmem := hfP ⟨q, hq⟩
    rw [hfeq ⟨q, hq⟩] at hmem
    exact ⟨q, hmem, le_rfl⟩
  exact h.ne hPQ

/-- **Das Korollar.** Verfeinerung bei gleicher Blockzahl erzwingt Gleichheit:
die Ränge des Partitionsverbands sind Antiketten. -/
theorem eq_of_le_of_card_eq {P Q : Finpartition s} (h : P ≤ Q)
    (hc : #P.parts = #Q.parts) : P = Q := by
  by_contra hne
  have := card_parts_lt_of_lt (lt_of_le_of_ne h hne)
  omega

/-! ## Wachen -/

-- STATEMENT-PIN
example {P Q : Finpartition s} (h : P < Q) : #Q.parts < #P.parts :=
  card_parts_lt_of_lt h

-- STATEMENT-PIN
example {P Q : Finpartition s} (h : P ≤ Q) (hc : #P.parts = #Q.parts) : P = Q :=
  eq_of_le_of_card_eq h hc

/-- info: 'Reformulation.Kenogram.card_parts_lt_of_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms card_parts_lt_of_lt

/-- info: 'Reformulation.Kenogram.eq_of_le_of_card_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms eq_of_le_of_card_eq

end Reformulation.Kenogram
