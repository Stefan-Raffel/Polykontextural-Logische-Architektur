import Reformulation.Proemial.NegationCycleSJT

/-!
# Proemial.NegationCycleLength — die kürzeste Zahl von Negatoren: die Inversionszahl

**FOLGERUNG** (`inv_le_length`, `exists_word_inv`, `inv_is_min_length`), sonst **EICHUNG**
(`eich3`, `eich4`, `genesen_kuerzeste`, `rueckwaerts_vier`). Gebaut auf Anordnung des
Architekten vom 25. September 2026 nach der Sondierung
`KorpusRev2/Sondierung_Minimale_Wortlaenge_Impl.md` und ihrer Begutachtung
`KorpusRev2/Begutachtung_Sondierung_Minimale_Wortlaenge.md` (Mathematiker); die Frage aus
`KorpusRev2/Prompt_Impl_Sondierung_Minimale_Wortlaenge.md`.

* **K1 — Günthers Frage, und warum dieses Modul sie nicht beantwortet.** IGN 1979
  (*Identität, Gegenidentität und Negativsprache*), S. 36 f., Textschicht und Seitenbild
  geprüft: „Da alle anderen logischen Prozeduren sich immer auf Umtauschrelationen reduzieren
  lassen müssen, kann man jeden Begriff dadurch arithmetisch genau definieren, dass man
  angibt, wieviel Umtauschvollzüge notwendig sind, um seinen inneren Aufbau zu verstehen."
  QUELLENFEST. Gebaut wurde das Modul unter der Lesart, „notwendig" heisse minimal
  (Hermeneutes, Y5). **Diese Lesart ist gefallen** (Hermeneutes D1–D3, am Seitenbild): Der
  „notwendig"-Satz, das Zwischenglied und die zwei Tabulierungen auf S. 37 stehen in einem
  Absatz. Günthers Zahl ist die Zählung auf dem alternierenden Weg, und sie unterscheidet
  `K l` (2) von `K r` (4), was die kürzeste Zahl nicht kann. Gebaut ist diese Zählung in
  `NegationCycleCatalog` (`tabulierung1`, `tabulierung2`). `inv_is_min_length` bleibt ein Satz
  über den Bestand — die kürzeste Zahl von Negatoren ist die Inversionszahl —, **ohne Anker an
  S. 37**.
* **K2 — der Satz.** `inv a` zählt die Paare von Stellen in falscher Reihenfolge.
  `inv_le_length`: jedes Negatorwort, das die Anordnung `a` vom Ausgang her erreicht, hat
  mindestens `inv a` Negatoren. `exists_word_inv`: es gibt eines genau dieser Länge.
  `inv_is_min_length`: beides, für jede Anordnung und **jede Wertzahl**. Gebaut ist die
  **Zahl**, nicht der Begriff: Günthers These, man könne „jeden Begriff" so definieren, ist
  kein Satz dieses Moduls.
* **K3 — die Wertsicht.** `negate i` tauscht die **Werte** `i` und `i+1`, wo immer sie
  stehen. Auf einer Anordnung ohne Wiederholung ändert das die Lage genau eines Wertepaars
  (`sw_lt_iff`). Darum zählt `inv` die Anordnung selbst, nicht ihre Umkehrung; vor dem
  Beweis an der Eichung entschieden (`eich3`, `eich4`).
* **K4 — die Genesen sind die kürzesten Wege.** Bei drei Werten erreichen den Rücklauf
  kein Wort kürzer als drei und unter den Worten der Länge drei genau `N1·2·1` und `N2·1·2`
  (`genesen_kuerzeste`) — Günthers zwei „Genesen" (HKN S. 25; Metamorphose der Zahl, PDF-S. 9;
  `NegationCycle.genese_resultat`, Teil 5) sind also **alle** kürzesten Wege, nicht zwei unter vielen. Bei vier Werten sind es
  16 (`rueckwaerts_vier`): dieselbe Menge wie die reduzierten Wörter des längsten Elements,
  die Definitionen §7 als „16 bei vier Werten" führt (Mathematiker, Begutachtung §2) — per
  Definition, und weil der Rücklauf seine eigene Umkehrung ist, gilt das in Wert- und
  Stellensicht zugleich. ZUORDNUNG der Zahl, gerechnet.
* **K5 — Mathlib.** Keine Inversionszahl, kein Coxeter-System auf `Perm (Fin n)`, kein Satz
  „Länge = Inversionen"; vorhanden sind die abstrakte `CoxeterSystem.length` und die Parität
  in `Equiv.Perm.signAux` (Mathlib 83a5988). Daher FOLGERUNG, keine Umbenennung.

**Wie der Beweis läuft.** (≥) — ein Negator ändert `inv` um höchstens eins
(`inv_negate_le`), und `inv (origin m) = 0` (`inv_origin`). (≤) — steht `i+1` vor `i`, so senkt
`negate i` die Zahl um genau eins (`inv_negate_desc`); bei `inv > 0` gibt es ein solches Paar
(`exists_desc`, über die eigene Relation `Before`, mit eigener `Decidable`-Instanz); bei
`inv = 0` ist die Anordnung der Ausgang (`eq_origin_of_inv_zero`); Induktion über `inv`
(`exists_word_inv`).

**Nicht:** kein §20-Anspruch, keine Zuordnung „Begriff = Anordnung". *Im Ledger* trug
`inv_is_min_length` von Rev. 23 bis Rev. 25 die Zeile L21-9; seit Rev. 26 trägt sie die
Tabulierung (`NegationCycleCatalog.tabulierung1`), und `inv_is_min_length` steht dort als
Bestandssatz ohne Anker an S. 37. Die
Ordnung als „Zahlenverhältnis zwischen einer Umtauschrelation und zwei" (IGN S. 34) ist nicht
gebaut. Günthers Katalog (8)–(13) steht seit dem 25.9. in `NegationCycleCatalog`, dort auch die
Verbindung seiner „Zahlenwerte" zu `inv` (`zahlenwerte`, `stationen_zahl`).

## Axiomprofil

Gemessen am grünen Bau, verbatim in den Wachen am Dateiende. **Kein Satz trägt
`Classical.choice`.** Die drei Hauptsätze `inv_le_length`, `exists_word_inv` und
`inv_is_min_length` tragen `[propext, Quot.sound]`, ebenso `genesen_kuerzeste`;
`rueckwaerts_vier` trägt `[propext]`; `eich3` und `eich4` sind axiomfrei.

Die Choice-Freiheit ist eine Bedingung des Baus, keine Gabe der Aussage. Gemieden sind:
`List.pairwise_lt_finRange`, `List.pairwise_lt_range`, `List.filter_eq_nil_iff`,
`List.nodup_finRange` (Mathlib 83a5988, gemessen in der Sondierung) — ersetzt durch
`pairwiseRange`, `len_filter_zero` und `len_filter_zero_inv`; `omega` bekommt nur atomare
Hypothesen (`sw_lt_iff`, Fallstrick 7); `by_contra` über einem `∃` ist durch die Instanz
`decBefore` und eine Fallunterscheidung über `List.finRange` ersetzt (`exists_desc`).
-/

namespace Reformulation.Proemial.NegationCycleLength

open Reformulation.Proemial.NegationCycle
open Reformulation.Proemial.NegationCycleSJT


def inv {n : ℕ} : List (Fin n) → ℕ
  | [] => 0
  | x :: xs => (xs.filter (fun y => decide (y < x))).length + inv xs

variable {m : ℕ}

/-- `sw i` erhält die Ordnung zweier Werte, ausser für das Paar {i, i+1} selbst. -/
theorem sw_lt_iff (i : Fin m) (x y : Fin (m + 1))
    (h : ¬ (x = i.castSucc ∧ y = i.succ) ∧ ¬ (x = i.succ ∧ y = i.castSucc)) :
    sw i y < sw i x ↔ y < x := by
  have hc : i.castSucc.val = i.val := Fin.val_castSucc i
  have hs : i.succ.val = i.val + 1 := Fin.val_succ i
  have h1 : x.val = i.val → y.val ≠ i.val + 1 := fun a b =>
    h.1 ⟨Fin.ext (by rw [hc]; exact a), Fin.ext (by rw [hs]; exact b)⟩
  have h2 : x.val = i.val + 1 → y.val ≠ i.val := fun a b =>
    h.2 ⟨Fin.ext (by rw [hs]; exact a), Fin.ext (by rw [hc]; exact b)⟩
  rw [Fin.lt_def, Fin.lt_def, sw_val, sw_val]
  -- omega darf nur atomare Fakten sehen: eine Implikation in der Hypothese zieht Choice
  by_cases hx1 : x.val = i.val
  · have hy := h1 hx1; clear h1 h2 h
    constructor <;> intro hlt <;> split_ifs at hlt ⊢ <;> omega
  · by_cases hx2 : x.val = i.val + 1
    · have hy := h2 hx2; clear h1 h2 h
      constructor <;> intro hlt <;> split_ifs at hlt ⊢ <;> omega
    · clear h1 h2 h
      constructor <;> intro hlt <;> split_ifs at hlt ⊢ <;> omega

/-- Kommt höchstens einer der zwei getauschten Werte vor, so bleibt `inv` gleich. -/
theorem inv_negate_of_not_both (i : Fin m) :
    ∀ l : List (Fin (m + 1)), (i.castSucc ∉ l ∨ i.succ ∉ l) → inv (negate i l) = inv l
  | [], _ => rfl
  | x :: xs, h => by
    have hxs : i.castSucc ∉ xs ∨ i.succ ∉ xs := by
      rcases h with h | h
      · exact Or.inl (fun hm => h (List.mem_cons_of_mem x hm))
      · exact Or.inr (fun hm => h (List.mem_cons_of_mem x hm))
    have ih := inv_negate_of_not_both i xs hxs
    simp only [negate, List.map_cons, inv] at ih ⊢
    rw [ih]
    congr 1
    rw [List.filter_map, List.length_map]
    congr 1
    apply List.filter_congr
    intro y hy
    simp only [Function.comp_apply, decide_eq_decide]
    apply sw_lt_iff
    constructor
    · rintro ⟨rfl, rfl⟩
      rcases h with h | h
      · exact h (List.mem_cons_self ..)
      · exact h (List.mem_cons_of_mem _ hy)
    · rintro ⟨rfl, rfl⟩
      rcases h with h | h
      · exact h (List.mem_cons_of_mem _ hy)
      · exact h (List.mem_cons_self ..)

/-- Filterlänge ist monoton im Prädikat. -/
theorem len_filter_mono {α : Type} (p q : α → Bool) :
    ∀ l : List α, (∀ y ∈ l, q y = true → p y = true) →
      (l.filter q).length ≤ (l.filter p).length
  | [], _ => Nat.le_refl _
  | y :: ys, h => by
    have ih := len_filter_mono p q ys (fun z hz => h z (List.mem_cons_of_mem y hz))
    have hy := h y (List.mem_cons_self ..)
    cases hq : q y <;> cases hp : p y <;>
      simp only [List.filter_cons, hq, hp, ↓reduceIte, List.length_cons, Bool.false_eq_true] <;>
      first | omega | exact absurd (hy hq) (by rw [hp]; decide)

/-- Mit höchstens einer Ausnahme `s` (wiederholungsfreie Liste) wächst die Filterlänge um
höchstens eins. -/
theorem len_filter_le_succ {α : Type} [DecidableEq α] (p q : α → Bool) (s : α) :
    ∀ l : List α, l.Nodup → (∀ y ∈ l, q y = true → p y = true ∨ y = s) →
      (l.filter q).length ≤ (l.filter p).length + 1
  | [], _, _ => Nat.zero_le _
  | y :: ys, hnd, h => by
    rw [List.nodup_cons] at hnd
    obtain ⟨hyn, hnd⟩ := hnd
    by_cases hys : y = s
    · subst hys
      have hm : (ys.filter q).length ≤ (ys.filter p).length :=
        len_filter_mono p q ys (fun z hz hqz => by
          rcases h z (List.mem_cons_of_mem _ hz) hqz with h' | h'
          · exact h'
          · exact absurd (h' ▸ hz) hyn)
      cases hq : q y <;> cases hp : p y <;>
        simp only [List.filter_cons, hq, hp, ↓reduceIte, List.length_cons, Bool.false_eq_true] <;>
        omega
    · have ih := len_filter_le_succ p q s ys hnd (fun z hz => h z (List.mem_cons_of_mem y hz))
      have hy : q y = true → p y = true := fun hq => by
        rcases h y (List.mem_cons_self ..) hq with h' | h'
        · exact h'
        · exact absurd h' hys
      cases hq : q y <;> cases hp : p y <;>
        simp only [List.filter_cons, hq, hp, ↓reduceIte, List.length_cons, Bool.false_eq_true] <;>
        first | omega | exact absurd (hy hq) (by rw [hp]; decide)

/-- Ein Negator hebt `inv` auf einer Anordnung ohne Wiederholung um höchstens eins. -/
theorem inv_negate_le (i : Fin m) :
    ∀ l : List (Fin (m + 1)), l.Nodup → inv (negate i l) ≤ inv l + 1
  | [], _ => by simp [negate, inv]
  | x :: xs, hnd => by
    rw [List.nodup_cons] at hnd
    obtain ⟨hx, hnd⟩ := hnd
    simp only [negate, List.map_cons, inv]
    rw [List.filter_map, List.length_map]
    by_cases hxa : x = i.castSucc ∨ x = i.succ
    · -- der Kopf ist einer der zwei Werte:  der Rest enthält ihn nicht
      have htail : inv (xs.map (sw i)) = inv xs := by
        have := inv_negate_of_not_both i xs (by
          rcases hxa with rfl | rfl
          · exact Or.inl hx
          · exact Or.inr hx)
        simpa [negate] using this
      rw [htail]
      -- der Kopf-Zähler wächst höchstens um eins:  nur der Partner kann umspringen
      have key : (xs.filter ((fun y => decide (y < sw i x)) ∘ sw i)).length ≤
          (xs.filter (fun y => decide (y < x))).length + 1 := by
        apply len_filter_le_succ _ _ i.succ xs hnd
        intro y hy hq
        simp only [Function.comp_apply, decide_eq_true_eq] at hq
        by_cases hsp : (x = i.castSucc ∧ y = i.succ) ∨ (x = i.succ ∧ y = i.castSucc)
        · rcases hsp with ⟨_, rfl⟩ | ⟨rfl, rfl⟩
          · exact Or.inr rfl
          · -- sw (castSucc) = succ < sw (succ) = castSucc ist falsch
            exfalso
            have hc : i.castSucc.val = i.val := Fin.val_castSucc i
            have hs : i.succ.val = i.val + 1 := Fin.val_succ i
            rw [Fin.lt_def, sw_val, sw_val] at hq
            rw [hc, hs] at hq
            split_ifs at hq <;> omega
        · left
          simp only [decide_eq_true_eq]
          exact (sw_lt_iff i x y ⟨fun h => hsp (Or.inl h), fun h => hsp (Or.inr h)⟩).1 hq
      omega
    · have hne : ¬ (x = i.castSucc) ∧ ¬ (x = i.succ) := not_or.1 hxa
      have ih := inv_negate_le i xs hnd
      simp only [negate] at ih
      have hc : (xs.filter ((fun y => decide (y < sw i x)) ∘ sw i)).length =
          (xs.filter (fun y => decide (y < x))).length := by
        congr 1; apply List.filter_congr; intro y _
        simp only [Function.comp_apply, decide_eq_decide]
        exact sw_lt_iff i x y ⟨fun h => hne.1 h.1, fun h => hne.2 h.1⟩
      omega

/-- `sw i` ist injektiv (Involution). -/
theorem sw_injective (i : Fin m) : Function.Injective (sw i) := fun a b h => by
  rw [← sw_sw i a, h, sw_sw]

theorem negate_nodup (i : Fin m) {l : List (Fin (m + 1))} (h : l.Nodup) : (negate i l).Nodup :=
  List.Nodup.map (sw_injective i) h

/-- **Die untere Schranke, allgemein:** jedes Negatorwort hebt `inv` um höchstens seine Länge. -/
theorem inv_endpoint_le :
    ∀ (w : List (Fin m)) (l : List (Fin (m + 1))), l.Nodup → inv (endpoint w l) ≤ inv l + w.length
  | [], _, _ => Nat.le_add_right _ _
  | i :: is, l, h => by
    have ih := inv_endpoint_le is (negate i l) (negate_nodup i h)
    have hs := inv_negate_le i l h
    simp only [endpoint, List.length_cons]
    omega

/-- `range` ist aufsteigend — ohne `List.pairwise_lt_range`, das `Classical.choice` trägt. -/
theorem pairwiseRange : ∀ n, (List.range n).Pairwise (· < ·)
  | 0 => List.Pairwise.nil
  | n + 1 => by
    rw [List.range_succ, List.pairwise_append]
    refine ⟨pairwiseRange n, List.pairwise_singleton _ _, ?_⟩
    intro a ha b hb
    rw [List.mem_singleton] at hb
    rw [List.mem_range] at ha
    omega

theorem origin_pairwise (m : ℕ) : (origin m).Pairwise (· < ·) := by
  have h := pairwiseRange (m + 1)
  rw [← origin_val m, List.pairwise_map] at h
  exact h.imp (fun hab => Fin.lt_def.2 hab)

theorem len_filter_zero {α : Type} (p : α → Bool) :
    ∀ l : List α, (∀ y ∈ l, p y = false) → (l.filter p).length = 0
  | [], _ => rfl
  | y :: ys, h => by
    rw [List.filter_cons, h y (List.mem_cons_self ..)]
    exact len_filter_zero p ys (fun z hz => h z (List.mem_cons_of_mem y hz))

theorem inv_zero_of_pairwise {n : ℕ} : ∀ l : List (Fin n), l.Pairwise (· < ·) → inv l = 0
  | [], _ => rfl
  | x :: xs, h => by
    rw [List.pairwise_cons] at h
    simp only [inv]
    rw [len_filter_zero _ xs (fun y hy => by
      have := h.1 y hy
      simp only [decide_eq_false_iff_not, Fin.not_lt]
      exact Fin.le_of_lt this), inv_zero_of_pairwise xs h.2]

theorem inv_origin (m : ℕ) : inv (origin m) = 0 := inv_zero_of_pairwise _ (origin_pairwise m)

/-- **(≥) — der eigentliche Satz:** jedes Negatorwort, das die Anordnung `a` erreicht, hat
mindestens `inv a` Negatoren. -/
theorem inv_le_length (w : List (Fin m)) : inv (endpoint w (origin m)) ≤ w.length := by
  have := inv_endpoint_le w (origin m) (origin_nodup m)
  rw [inv_origin] at this
  omega

-- ============================================================
-- (≤) — ein kürzestes Wort existiert
-- ============================================================

/-- `Before x y l`: `x` steht in `l` vor `y`. -/
def Before {α : Type} (x y : α) : List α → Prop
  | [] => False
  | z :: zs => (z = x ∧ y ∈ zs) ∨ Before x y zs

/-- `Before` ist entscheidbar — ohne diese Instanz griffe jede Fallunterscheidung klassisch. -/
instance decBefore {α : Type} [DecidableEq α] (x y : α) : (l : List α) → Decidable (Before x y l)
  | [] => isFalse id
  | z :: zs => by
    have := decBefore x y zs
    unfold Before
    exact inferInstance

theorem Before.mem {α : Type} {x y : α} : ∀ {l : List α}, Before x y l → x ∈ l ∧ y ∈ l
  | [], h => h.elim
  | z :: zs, h => by
    rcases h with ⟨rfl, hy⟩ | h
    · exact ⟨List.mem_cons_self .., List.mem_cons_of_mem _ hy⟩
    · obtain ⟨hx, hy⟩ := Before.mem h
      exact ⟨List.mem_cons_of_mem _ hx, List.mem_cons_of_mem _ hy⟩

theorem Before.ne {α : Type} {x y : α} : ∀ {l : List α}, l.Nodup → Before x y l → x ≠ y
  | [], _, h => h.elim
  | z :: zs, hnd, h => by
    rw [List.nodup_cons] at hnd
    rcases h with ⟨rfl, hy⟩ | h
    · intro hxy; subst hxy; exact hnd.1 hy
    · exact Before.ne hnd.2 h

theorem Before.asymm {α : Type} {x y : α} : ∀ {l : List α}, l.Nodup → Before x y l → ¬ Before y x l
  | [], _, h => h.elim
  | z :: zs, hnd, h => by
    rw [List.nodup_cons] at hnd
    rintro (⟨rfl, hx⟩ | h')
    · rcases h with ⟨rfl, _⟩ | h
      · exact hnd.1 hx
      · exact hnd.1 (Before.mem h).2
    · rcases h with ⟨rfl, _⟩ | h
      · exact hnd.1 (Before.mem h').2
      · exact Before.asymm hnd.2 h h'

theorem Before.trans {α : Type} {x y w : α} : ∀ {l : List α}, l.Nodup →
    Before x y l → Before y w l → Before x w l
  | [], _, h, _ => h.elim
  | z :: zs, hnd, h1, h2 => by
    rw [List.nodup_cons] at hnd
    rcases h1 with ⟨rfl, hy⟩ | h1
    · exact Or.inl ⟨rfl, by
        rcases h2 with ⟨rfl, _⟩ | h2
        · exact absurd hy hnd.1
        · exact (Before.mem h2).2⟩
    · rcases h2 with ⟨rfl, _⟩ | h2
      · exact absurd (Before.mem h1).2 hnd.1
      · exact Or.inr (Before.trans hnd.2 h1 h2)

theorem Before.total {α : Type} {x y : α} : ∀ {l : List α}, x ∈ l → y ∈ l → x ≠ y →
    Before x y l ∨ Before y x l
  | [], hx, _, _ => absurd hx List.not_mem_nil
  | z :: zs, hx, hy, hxy => by
    rcases List.mem_cons.1 hx with rfl | hx'
    · rcases List.mem_cons.1 hy with rfl | hy'
      · exact absurd rfl hxy
      · exact Or.inl (Or.inl ⟨rfl, hy'⟩)
    · rcases List.mem_cons.1 hy with rfl | hy'
      · exact Or.inr (Or.inl ⟨rfl, hx'⟩)
      · rcases Before.total hx' hy' hxy with h | h
        · exact Or.inl (Or.inr h)
        · exact Or.inr (Or.inr h)

/-- Genau ein Element weicht ab: die Filterlänge sinkt um genau eins. -/
theorem len_filter_drop_one {α : Type} [DecidableEq α] (p q : α → Bool) (s : α) :
    ∀ l : List α, l.Nodup → s ∈ l → p s = true → q s = false →
      (∀ y ∈ l, y ≠ s → q y = p y) → (l.filter q).length + 1 = (l.filter p).length
  | [], _, hs, _, _, _ => absurd hs List.not_mem_nil
  | y :: ys, hnd, hs, hp, hq, h => by
    rw [List.nodup_cons] at hnd
    by_cases hys : y = s
    · subst hys
      have heq : (ys.filter q).length = (ys.filter p).length := by
        have e : ys.filter q = ys.filter p := List.filter_congr (fun z hz =>
          h z (List.mem_cons_of_mem _ hz) (fun hzs => hnd.1 (hzs ▸ hz)))
        rw [e]
      simp only [List.filter_cons, hp, hq, ↓reduceIte, List.length_cons, Bool.false_eq_true]
      omega
    · have hs' : s ∈ ys := by
        rcases List.mem_cons.1 hs with h' | h'
        · exact absurd h'.symm hys
        · exact h'
      have ih := len_filter_drop_one p q s ys hnd.2 hs' hp hq
        (fun z hz hzs => h z (List.mem_cons_of_mem _ hz) hzs)
      have hy := h y (List.mem_cons_self ..) hys
      cases hpy : p y <;> rw [hpy] at hy <;>
        simp only [List.filter_cons, hy, hpy, ↓reduceIte, List.length_cons, Bool.false_eq_true] <;>
        omega

/-- **(X) der exakte Abstieg:** steht `i+1` vor `i`, so sinkt `inv` durch `negate i` um eins. -/
theorem inv_negate_desc (i : Fin m) : ∀ l : List (Fin (m + 1)), l.Nodup →
    Before i.succ i.castSucc l → inv (negate i l) + 1 = inv l
  | [], _, h => h.elim
  | x :: xs, hnd, h => by
    rw [List.nodup_cons] at hnd
    obtain ⟨hx, hnd⟩ := hnd
    have hcs : i.castSucc ≠ i.succ := fun e => by
      have := congrArg Fin.val e; rw [Fin.val_castSucc, Fin.val_succ] at this; omega
    simp only [negate, List.map_cons, inv]
    rw [List.filter_map, List.length_map]
    rcases h with ⟨rfl, hc⟩ | h
    · -- Kopf ist i+1, dahinter steht i:  der Kopf-Zähler sinkt um eins, der Rest bleibt
      have htail : inv (xs.map (sw i)) = inv xs := by
        have := inv_negate_of_not_both i xs (Or.inr hx); simpa [negate] using this
      have hhead : (xs.filter ((fun y => decide (y < sw i i.succ)) ∘ sw i)).length + 1 =
          (xs.filter (fun y => decide (y < i.succ))).length := by
        apply len_filter_drop_one _ _ i.castSucc xs hnd hc
        · simp only [decide_eq_true_eq, Fin.lt_def, Fin.val_castSucc, Fin.val_succ]; omega
        · simp only [Function.comp_apply, decide_eq_false_iff_not, Fin.lt_def, sw_val,
            Fin.val_castSucc, Fin.val_succ]
          split_ifs <;> omega
        · intro y hy hyc
          simp only [Function.comp_apply, decide_eq_decide]
          apply sw_lt_iff
          exact ⟨fun h => hcs h.1.symm, fun h => hyc h.2⟩
      rw [htail]; omega
    · -- beide stehen im Rest:  der Kopf ist keiner von beiden
      obtain ⟨hs, hc⟩ := Before.mem h
      have hxs : x ≠ i.succ := fun e => hx (e ▸ hs)
      have hxc : x ≠ i.castSucc := fun e => hx (e ▸ hc)
      have ih := inv_negate_desc i xs hnd h
      simp only [negate] at ih
      have hhead : (xs.filter ((fun y => decide (y < sw i x)) ∘ sw i)).length =
          (xs.filter (fun y => decide (y < x))).length := by
        congr 1; apply List.filter_congr; intro y _
        simp only [Function.comp_apply, decide_eq_decide]
        exact sw_lt_iff i x y ⟨fun h => hxc h.1, fun h => hxs h.1⟩
      omega

theorem len_filter_zero_inv {α : Type} (p : α → Bool) :
    ∀ l : List α, (l.filter p).length = 0 → ∀ y ∈ l, p y = false
  | [], _, y, hy => absurd hy List.not_mem_nil
  | z :: zs, h, y, hy => by
    cases hz : p z
    · rw [List.filter_cons, hz] at h
      simp only [Bool.false_eq_true, ↓reduceIte] at h
      rcases List.mem_cons.1 hy with rfl | hy'
      · exact hz
      · exact len_filter_zero_inv p zs h y hy'
    · rw [List.filter_cons, hz] at h
      simp only [↓reduceIte, List.length_cons] at h
      omega

/-- `inv = 0` auf einer wiederholungsfreien Folge heisst aufsteigend. -/
theorem pairwise_of_inv_zero {n : ℕ} : ∀ l : List (Fin n), l.Nodup → inv l = 0 → l.Pairwise (· < ·)
  | [], _, _ => List.Pairwise.nil
  | x :: xs, hnd, h => by
    rw [List.nodup_cons] at hnd
    simp only [inv] at h
    rw [List.pairwise_cons]
    have h0 : (xs.filter (fun y => decide (y < x))).length = 0 := by omega
    refine ⟨fun y hy => ?_, pairwise_of_inv_zero xs hnd.2 (by omega)⟩
    have hyx := len_filter_zero_inv _ xs h0 y hy
    have hnlt : ¬ y < x := fun hl => by rw [decide_eq_true hl] at hyx; exact Bool.noConfusion hyx
    have hne : x.val ≠ y.val := fun e => hnd.1 (Fin.ext e ▸ hy)
    rw [Fin.lt_def] at hnlt ⊢
    omega

/-- (Z) der Anfang:  eine vollständige wiederholungsfreie Folge mit `inv = 0` ist `origin`. -/
theorem eq_origin_of_inv_zero {l : List (Fin (m + 1))} (hnd : l.Nodup) (hall : ∀ v, v ∈ l)
    (h : inv l = 0) : l = origin m := by
  have hperm : l.Perm (origin m) :=
    (List.perm_ext_iff_of_nodup hnd (origin_nodup m)).2
      (fun a => ⟨fun _ => List.mem_finRange a, fun _ => hall a⟩)
  exact List.Perm.eq_of_pairwise (fun a b _ _ h1 h2 => by
      rw [Fin.lt_def] at h1 h2; omega)
    (pairwise_of_inv_zero l hnd h) (origin_pairwise m) hperm

/-- Steht jedes frühere Element unter jedem späteren, so ist die Folge aufsteigend. -/
theorem pairwise_of_before {n : ℕ} : ∀ l : List (Fin n),
    (∀ x y, Before x y l → x < y) → l.Pairwise (· < ·)
  | [], _ => List.Pairwise.nil
  | z :: zs, hord => by
    rw [List.pairwise_cons]
    exact ⟨fun y hy => hord z y (Or.inl ⟨rfl, hy⟩),
      pairwise_of_before zs (fun x y hb => hord x y (Or.inr hb))⟩

/-- (Y) steht kein `i+1` vor `i`, so ist die Folge aufsteigend. -/
theorem exists_desc {l : List (Fin (m + 1))} (hnd : l.Nodup) (hall : ∀ v, v ∈ l)
    (h : 0 < inv l) : ∃ i : Fin m, Before i.succ i.castSucc l := by
  -- entscheidbar über die endliche Liste der Negatoren, nicht per `by_contra`
  by_cases hyes : ∃ i ∈ List.finRange m, Before i.succ i.castSucc l
  · obtain ⟨i, _, hi⟩ := hyes; exact ⟨i, hi⟩
  exfalso
  have hasc : ∀ i : Fin m, Before i.castSucc i.succ l := fun i => by
    have hcs : i.castSucc ≠ i.succ := fun e => by
      have := congrArg Fin.val e; rw [Fin.val_castSucc, Fin.val_succ] at this; omega
    rcases Before.total (hall _) (hall _) hcs with h' | h'
    · exact h'
    · exact absurd ⟨i, List.mem_finRange i, h'⟩ hyes
  -- Anfang:  Nachbarwerte stehen in Ordnung
  have base : ∀ v w : Fin (m + 1), w.val = v.val + 1 → Before v w l := by
    intro v w hw
    have hv : v.val < m := by have := w.isLt; omega
    have := hasc ⟨v.val, hv⟩
    have e1 : (⟨v.val, hv⟩ : Fin m).castSucc = v := Fin.ext (Fin.val_castSucc _)
    have e2 : (⟨v.val, hv⟩ : Fin m).succ = w := Fin.ext (by rw [Fin.val_succ]; exact hw.symm)
    rwa [e1, e2] at this
  -- Kette:  v < w  ⇒  v vor w
  have chain : ∀ d : ℕ, ∀ v w : Fin (m + 1), w.val = v.val + d + 1 → Before v w l := by
    intro d
    induction d with
    | zero => intro v w hw; exact base v w (by omega)
    | succ d ih =>
      intro v w hw
      have hu : v.val + d + 1 < m + 1 := by have := w.isLt; omega
      exact Before.trans hnd (ih v ⟨v.val + d + 1, hu⟩ rfl) (base ⟨v.val + d + 1, hu⟩ w (by
        show w.val = v.val + d + 1 + 1; omega))
  have hord : ∀ x y, Before x y l → x < y := by
    intro x y hxy
    rcases Nat.lt_trichotomy x.val y.val with hlt | heq | hgt
    · exact Fin.lt_def.2 hlt
    · exact absurd (Fin.ext heq) (Before.ne hnd hxy)
    · exact absurd (chain (x.val - y.val - 1) y x (by omega)) (Before.asymm hnd hxy)
  have := inv_zero_of_pairwise l (pairwise_of_before l hord)
  omega

theorem negate_all (i : Fin m) {l : List (Fin (m + 1))} (hall : ∀ v, v ∈ l) :
    ∀ v, v ∈ negate i l :=
  fun v => List.mem_map.2 ⟨sw i v, hall _, sw_sw i v⟩

/-- **(≤) — ein Wort der Länge `inv`:** zu jeder vollständigen wiederholungsfreien Folge gibt es
ein Negatorwort genau der Länge `inv l`, das sie vom Ausgang her erreicht. -/
theorem exists_word_inv : ∀ (n : ℕ) (l : List (Fin (m + 1))), l.Nodup → (∀ v, v ∈ l) →
    inv l = n → ∃ w : List (Fin m), w.length = n ∧ endpoint w (origin m) = l
  | 0, l, hnd, hall, h => ⟨[], rfl, (eq_origin_of_inv_zero hnd hall h).symm⟩
  | n + 1, l, hnd, hall, h => by
    obtain ⟨i, hi⟩ := exists_desc hnd hall (by omega)
    have hdesc := inv_negate_desc i l hnd hi
    obtain ⟨w, hw, hend⟩ := exists_word_inv n (negate i l) (negate_nodup i hnd)
      (negate_all i hall) (by omega)
    refine ⟨w ++ [i], by simp [hw], ?_⟩
    rw [endpoint_append, hend, negate_negate]

/-- **Die minimale Wortlänge:** für jede Anordnung `a` gibt es ein Negatorwort der Länge
`inv a`, und jedes Wort zu `a` ist mindestens so lang. -/
theorem inv_is_min_length (a : List (Fin (m + 1))) (ha : a ∈ (origin m).permutations') :
    (∃ w : List (Fin m), w.length = inv a ∧ endpoint w (origin m) = a) ∧
      ∀ w : List (Fin m), endpoint w (origin m) = a → inv a ≤ w.length := by
  have hp := List.mem_permutations'.1 ha
  have hnd : a.Nodup := hp.nodup_iff.2 (origin_nodup m)
  have hall : ∀ v, v ∈ a := fun v => hp.mem_iff.2 (List.mem_finRange v)
  exact ⟨exists_word_inv _ a hnd hall rfl, fun w hw => hw ▸ inv_le_length w⟩

-- ============================================================
-- Eichung — gegen eine vollständige Aufzählung der Negatorworte
-- ============================================================

/-- Alle Negatorworte der Länge `k`. -/
def words (m : ℕ) : ℕ → List (List (Fin m))
  | 0 => [[]]
  | k + 1 => (words m k).flatMap (fun w => (List.finRange m).map (fun i => i :: w))

/-- `words m k` zählt genau die Worte der Länge `k` auf — die Eichung vergleicht also mit
allen Worten, nicht mit einer Auswahl. -/
theorem mem_words (m : ℕ) : ∀ (k : ℕ) (w : List (Fin m)), w ∈ words m k ↔ w.length = k
  | 0, w => by
    cases w with
    | nil => exact ⟨fun _ => rfl, fun _ => List.mem_singleton_self _⟩
    | cons x xs => exact ⟨fun h => (by cases List.mem_singleton.1 h), fun h => (by cases h)⟩
  | k + 1, w => by
    simp only [words, List.mem_flatMap, List.mem_map]
    constructor
    · rintro ⟨v, hv, i, _, rfl⟩
      rw [List.length_cons, (mem_words m k v).1 hv]
    · intro h
      cases w with
      | nil => cases h
      | cons x xs =>
        exact ⟨xs, (mem_words m k xs).2 (by simpa using h), x, List.mem_finRange x, rfl⟩

/-- Die kürzeste Länge eines Worts zu `a`, gesucht bis `bound`;  `bound + 1` heisst: nicht
gefunden. -/
def minLen (m bound : ℕ) (a : List (Fin (m + 1))) : ℕ :=
  ((List.range (bound + 1)).find? (fun k => (words m k).any (fun w => endpoint w (origin m) == a))).getD
    (bound + 1)

/-- Eichung bei drei Werten:  `inv` ist die gesuchte kürzeste Länge. -/
theorem eich3 : ∀ a ∈ (origin 2).permutations', inv a = minLen 2 3 a := by decide +kernel

/-- Eichung bei vier Werten. -/
theorem eich4 : ∀ a ∈ (origin 3).permutations', inv a = minLen 3 6 a := by decide +kernel

-- ============================================================
-- Die Genesen sind die kürzesten Wege zum Rücklauf
-- ============================================================

/-- **Bei drei Werten sind die kürzesten Worte zum Rücklauf genau Günthers zwei Genesen**
`N1·2·1` und `N2·1·2` (HKN S. 25):  kein Wort zum Rücklauf ist kürzer als drei, und unter den
Worten der Länge drei erreichen genau diese zwei ihn. -/
theorem genesen_kuerzeste :
    (∀ w : List (Fin 2), endpoint w (origin 2) = [2, 1, 0] → 3 ≤ w.length) ∧
    (∀ a b c : Fin 2, endpoint [a, b, c] (origin 2) = [2, 1, 0] ↔
      ([a, b, c] = [0, 1, 0] ∨ [a, b, c] = [1, 0, 1])) := by
  refine ⟨fun w hw => ?_, by decide⟩
  have := inv_le_length w
  rw [hw] at this
  exact this

/-- Eichung:  bei vier Werten gibt es 16 kürzeste Worte zum Rücklauf (Länge 6) und keines
kürzer. -/
theorem rueckwaerts_vier :
    ((words 3 6).filter (fun w => endpoint w (origin 3) == [3, 2, 1, 0])).length = 16 ∧
    ∀ k < 6, (words 3 k).all (fun w => endpoint w (origin 3) != [3, 2, 1, 0]) = true := by
  decide +kernel

-- ============================================================
-- Wachen
-- ============================================================

/-- info: 'Reformulation.Proemial.NegationCycleLength.sw_lt_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms sw_lt_iff

/-- info: 'Reformulation.Proemial.NegationCycleLength.inv_negate_of_not_both' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms inv_negate_of_not_both

/-- info: 'Reformulation.Proemial.NegationCycleLength.len_filter_mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms len_filter_mono

/-- info: 'Reformulation.Proemial.NegationCycleLength.len_filter_le_succ' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms len_filter_le_succ

/-- info: 'Reformulation.Proemial.NegationCycleLength.inv_negate_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms inv_negate_le

/-- info: 'Reformulation.Proemial.NegationCycleLength.sw_injective' depends on axioms: [propext] -/
#guard_msgs in #print axioms sw_injective

/-- info: 'Reformulation.Proemial.NegationCycleLength.negate_nodup' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms negate_nodup

/-- info: 'Reformulation.Proemial.NegationCycleLength.inv_endpoint_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms inv_endpoint_le

/-- info: 'Reformulation.Proemial.NegationCycleLength.pairwiseRange' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms pairwiseRange

/-- info: 'Reformulation.Proemial.NegationCycleLength.origin_pairwise' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms origin_pairwise

/-- info: 'Reformulation.Proemial.NegationCycleLength.len_filter_zero' depends on axioms: [propext] -/
#guard_msgs in #print axioms len_filter_zero

/-- info: 'Reformulation.Proemial.NegationCycleLength.inv_zero_of_pairwise' depends on axioms: [propext] -/
#guard_msgs in #print axioms inv_zero_of_pairwise

/-- info: 'Reformulation.Proemial.NegationCycleLength.inv_origin' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms inv_origin

/-- info: 'Reformulation.Proemial.NegationCycleLength.inv_le_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms inv_le_length

/-- info: 'Reformulation.Proemial.NegationCycleLength.Before.mem' does not depend on any axioms -/
#guard_msgs in #print axioms Before.mem

/-- info: 'Reformulation.Proemial.NegationCycleLength.Before.ne' depends on axioms: [propext] -/
#guard_msgs in #print axioms Before.ne

/-- info: 'Reformulation.Proemial.NegationCycleLength.Before.asymm' depends on axioms: [propext] -/
#guard_msgs in #print axioms Before.asymm

/-- info: 'Reformulation.Proemial.NegationCycleLength.Before.trans' depends on axioms: [propext] -/
#guard_msgs in #print axioms Before.trans

/-- info: 'Reformulation.Proemial.NegationCycleLength.Before.total' depends on axioms: [propext] -/
#guard_msgs in #print axioms Before.total

/-- info: 'Reformulation.Proemial.NegationCycleLength.len_filter_drop_one' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms len_filter_drop_one

/-- info: 'Reformulation.Proemial.NegationCycleLength.inv_negate_desc' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms inv_negate_desc

/-- info: 'Reformulation.Proemial.NegationCycleLength.len_filter_zero_inv' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms len_filter_zero_inv

/-- info: 'Reformulation.Proemial.NegationCycleLength.pairwise_of_inv_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms pairwise_of_inv_zero

/-- info: 'Reformulation.Proemial.NegationCycleLength.eq_origin_of_inv_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms eq_origin_of_inv_zero

/-- info: 'Reformulation.Proemial.NegationCycleLength.pairwise_of_before' depends on axioms: [propext] -/
#guard_msgs in #print axioms pairwise_of_before

/-- info: 'Reformulation.Proemial.NegationCycleLength.exists_desc' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms exists_desc

/-- info: 'Reformulation.Proemial.NegationCycleLength.negate_all' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms negate_all

/-- info: 'Reformulation.Proemial.NegationCycleLength.exists_word_inv' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms exists_word_inv

/-- info: 'Reformulation.Proemial.NegationCycleLength.inv_is_min_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms inv_is_min_length

/-- info: 'Reformulation.Proemial.NegationCycleLength.mem_words' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms mem_words

/-- info: 'Reformulation.Proemial.NegationCycleLength.eich3' does not depend on any axioms -/
#guard_msgs in #print axioms eich3

/-- info: 'Reformulation.Proemial.NegationCycleLength.eich4' does not depend on any axioms -/
#guard_msgs in #print axioms eich4

/-- info: 'Reformulation.Proemial.NegationCycleLength.genesen_kuerzeste' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms genesen_kuerzeste

/-- info: 'Reformulation.Proemial.NegationCycleLength.rueckwaerts_vier' depends on axioms: [propext] -/
#guard_msgs in #print axioms rueckwaerts_vier

end Reformulation.Proemial.NegationCycleLength
