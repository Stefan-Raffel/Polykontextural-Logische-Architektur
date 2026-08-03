import Reformulation.Proemial.StageAscent

/-!
# Proemial.ChoiceVectors — die lokal klassischen Operationen als Wahlvektoren

**Der Name meint Guenther-seitige Wahlvektoren, nicht das Auswahlaxiom.** `ChoiceVectors`
uebersetzt den Terminus der E1-Reihe („Wahlmuster"): eine lokal klassische Operation waehlt
auf jeder Elementarkontextur zwischen Konjunktion und Disjunktion, und die Datei zeigt, dass
sie **nichts weiter** ist als diese Wahl. Mit `Classical.choice` hat der Name nichts zu tun;
wo das Axiom auftritt, sagt es der Abschnitt „Zum Axiom-Profil" unten, gemessen und mit
Herkunft.

## Was bewiesen ist

* **R0 `card_pairs`** — der Traeger der Wahl hat `C(m,2)` Stellen: so viele geordnete Paare
  `p.1 < p.2` gibt es auf `Fin m`.
* **R1 `ofChoices_locallyClassical` und `locallyClassicalEquiv`** — das Theorem der Datei:
  jeder Wahlvektor liefert eine lokal klassische Operation, und die Zuordnung ist eine
  **Bijektion**. Damit ist „lokal klassisch" nicht blosse Eigenschaft, sondern Bauplan.
* **R2 `card_locallyClassical`** — die Zahl, als Korollar: es gibt genau `2^C(m,2)` lokal
  klassische Operationen auf `Fin m`.
* **R3 `clone_locallyClassical_eq`** — die Erreichbarkeits-Seite, als Mengengleichheit: ab
  `m ≥ 4` sind von all diesen genau zwei im Klon von `{∧, ∨, ¬}`, naemlich Minimum und
  Maximum, und die beiden sind verschieden (`min_ne_max`). Reiner Konsum der E3-Iff und der
  beiden Erzeugbarkeits-Saetze; kein eigener Schranken-Beweis.
* **R4 `card_locallyClassical_lt`** — das Wachstum am Gegenstand: von Stufe zu Stufe wird
  die Zahl echt groesser. Ueber R2 auf beiden Seiten und `SAsc.choose_two_succ`.
* **Zugabe `two_lt_card_locallyClassical`** — ab `m ≥ 3` sind es mehr als zwei. Das ist die
  quantitative Form des Ueberschusses, die R2 und R3 zusammen tragen.

## Die Staffel der Anfaenge, und was an ihr Deutung ist

Bei `m = 2` gibt es genau ein Paar, also `2^1 = 2` lokal klassische Operationen — Minimum
und Maximum, und beide sind erzeugbar: **der zweite Wert liefert nichts Neues**, es gibt
keinen Ueberschuss. Bei `m = 3` sind es acht, und nach E1 sind vier davon erzeugbar
(`NUCB.four_of_eight_generatable`); ab `m = 4` sind es `2^C(m,2)`, und erreichbar bleiben
**zwei**. Die Zahlen 8, 64, 1024 des Arbeitspapiers sind damit Instanzen von R2 und keine
eigenen Marken; sie stehen hier als Prosa und nicht als Satz.

**Deutung, markiert:** dass darin „wachsender struktureller Reichtum bei konstanter
Erreichbarkeit" liegt, ist eine Lesart des Paars R2/R3 samt R4. Sie steht in keinem Namen
und in keinem Satzwortlaut. Bewiesen sind eine Bijektion, eine Kardinalitaet, eine
Mengengleichheit und eine Ungleichung.

## Verhaeltnis zu E2 — dieselbe Gestalt bei festem m, hier uniform

`QCB.ofC` ist der Wahlvektor bei `m = 4`, ausgeschrieben als sechs `Bool`-Argumente (so
verlangt es dort Fallstrick 3), und `QCB.two_of_sixtyfour_generatable` teilt ihn in „genau
zwei von `2^6`". Diese Datei baut dieselbe Gestalt **uniform in m** und als Bijektion; sie
kopiert nichts und aendert nichts an E2. Die Zahlen treffen sich, und das ist die
Gegenprobe: `C(4,2) = 6`, also `2^6 = 64` — R2 bei `m = 4` liefert dieselben 64, die E2 von
der anderen Seite teilt.

## Grenzen

1. **Kein Satz ueber die Def6-Totalitaet.** Die Ledger-Zeile L06-1 bleibt `Offen`; diese
   Datei traegt eine Zaehlung, kein Weltbild.
2. **Die Klon-Reihe bleibt unberuehrt und choice-frei.** `GeneralCloneBound`, `StageAscent`
   und `NonUniformCloneBound` sind nicht angefasst; R3 konsumiert sie, mehr nicht.
3. **L03-3 wird nicht entschieden.** Die C(m,2)-Zaehlung dieser Datei ist die
   Korpuszaehlung der Wert-Zweiermengen; die zweite Zaehlfunktion aus Grenznotiz A bleibt,
   wo sie steht.
4. **Keine Karte ueber dem Klon-Praedikat.** R3 ist Mengengleichheit und nicht
   Kardinalitaet — „im Klon liegen" ist nicht entscheidbar, und eine `Fintype`-Form darueber
   braeuchte klassische Instanzen ohne Not. Die „Zwei" steht als Paar plus `min_ne_max`.

## Robustheit (`CLAUDE.md` §9) ist hier gegenstandslos

Diese Datei zieht **keine** neue Nicht-Erzeugbarkeits-Schranke; sie zaehlt, und sie
konsumiert eine bestehende. Deren Robustheit gegen Signatur-Erweiterung ist im Bestand
gefuehrt und dort gemessen (`GCB.constant_clone_min_or_max`, Invariante `R m` reflexiv nach
`GCB.R_diag`). Hier ist nichts zu pruefen, und das steht hier, damit niemand eine Pruefung
vermisst, die es nicht zu fuehren gibt.

## Zum Axiom-Profil — die Schichtgrenze, gemessen und anders als erwartet

Die Erwartung war: Aequivalenz-Schicht choice-frei, Zaehl-Schicht mit `Classical.choice`
ueber die `Fintype`-Kette des Funktionsraums. **Gemessen laeuft die Grenze woanders**, und
zwar quer durch die Aequivalenz-Schicht:

| Schicht | Profil |
|---|---|
| `Pairs` | axiomfrei |
| `ofChoices`, `ofChoices_pair`, `ofChoices_diag`, `ofChoices_locallyClassical`, `min/max_locallyClassical`, die drei `Decidable`-Instanzen | `[propext]` |
| `min_ne_max_of_ne`, `min_ne_max`, `clone_locallyClassical_eq` | `[propext, Quot.sound]` |
| `locallyClassicalEquiv`, `card_pairs`, `card_locallyClassical`, `card_locallyClassical_lt`, `two_lt_card_locallyClassical` | `[propext, Classical.choice, Quot.sound]` |

**Die positive Haelfte von R1 ist choice-frei** (`ofChoices_locallyClassical`,
`[propext]`); die **Bijektion** ist es nicht. Herkunft, an vier Punkten gemessen: die
`Bool`-Konversion `==` auf `Fin m` laeuft ueber `LawfulBEq`/`ReflBEq`, und diese loesen
gegen Mathlibs `Std.LawfulBEqOrd`-Instanz auf, die aus der `LinearOrder`-Vergleichsfunktion
kommt. Gemessen: `Ord (Fin m)` axiomfrei, `Std.LawfulBEqOrd (Fin m)` und daraus
`LawfulBEq`/`ReflBEq` mit `Classical.choice`; die allgemeinen Lemmata `beq_iff_eq` und
`beq_self_eq_true` sind fuer sich axiomfrei und ziehen es erst an dieser Instanz. Der
Choice-Anteil sitzt damit **nicht** in den Schranken und nicht erst im Zaehlen, sondern in
der Konversion nach `Bool`.

Gemessen sind die Profile und die Trennlinie entlang dessen, was die Deklarationen nennen.
**Nicht** gemessen ist der Weg des Axioms in den Term; die Herkunftsangabe oben ist eine
Kette gemessener Instanz-Profile, keine Ableitung.

**Ablage:** setzungsfrei, ohne offene Stelle, konsumiert nur Aggregat-Inhalt — Aggregat.
-/

open FirstOrder Language

namespace Reformulation.Proemial.ChoiceVectors

open Reformulation.Proemial.TransjunctionCloneBound (L)
open Reformulation.Proemial.GeneralCloneBound
open Reformulation.Proemial.StageAscent (choose_two_succ)

/-! ## Teil 1 — der Traeger der Wahl und seine Karte

`Pairs m` sind die geordneten Paare auf `Fin m` — je eines pro Elementarkontextur. Als
`abbrev` gebaut, damit die Instanzensuche durchgreift (Fallstrick 2 in der Gestalt, in der
er hier auftraete). -/

/-- **Der Traeger der Wahl:** die geordneten Paare auf `Fin m`. Je eines steht fuer eine
Elementarkontextur `{x, y}`, mit fester Reihenfolge als Repraesentant. -/
abbrev Pairs (m : ℕ) := { p : Fin m × Fin m // p.1 < p.2 }

/-- **R0 — die Karte des Traegers:** es gibt `C(m,2)` geordnete Paare. Ueber die Zerlegung
nach der groesseren Komponente und die Gauss-Summe, die hier per Induktion aus
`SAsc.choose_two_succ` gewonnen wird statt zitiert. -/
theorem card_pairs (m : ℕ) : Fintype.card (Pairs m) = m.choose 2 := by
  have hsum : ∀ n : ℕ, ∑ i ∈ Finset.range n, i = n.choose 2 := by
    intro n
    induction n with
    | zero => simp
    | succ k ih => rw [Finset.sum_range_succ, ih, choose_two_succ]
  have e : Pairs m ≃ Σ b : Fin m, Fin b.val :=
    { toFun := fun p => ⟨p.1.2, ⟨p.1.1.val, p.2⟩⟩
      invFun := fun q => ⟨(⟨q.2.val, lt_trans q.2.isLt q.1.isLt⟩, q.1), q.2.isLt⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Fintype.card_congr e, Fintype.card_sigma]
  simp only [Fintype.card_fin]
  rw [Fin.sum_univ_eq_sum_range (fun i => i) m, hsum]

/-! ## Teil 2 — der Bauplan und drei Hilfslemmata

`ofChoices` liest den Wahlvektor: auf jedem Paar Maximum oder Minimum, auf der Diagonale die
Identitaet. Die Fallunterscheidung laeuft ueber die Ordnung von `Fin m` und nicht ueber die
`Fin`-Subtraktion (Fallstrick 1); es wird nirgends ueber einen Funktionsraum quantifiziert
(Fallstrick 3). -/

/-- **Der Bauplan:** aus einem Wahlvektor die Operation. Auf dem Paar `{a,b}` wirkt sie als
Maximum, wenn der Vektor dort `true` sagt, sonst als Minimum; auf der Diagonale als
Identitaet. -/
def ofChoices (m : ℕ) (c : Pairs m → Bool) : Fin m → Fin m → Fin m :=
  fun a b =>
    if h : a < b then (if c ⟨(a, b), h⟩ then max a b else min a b)
    else if h' : b < a then (if c ⟨(b, a), h'⟩ then max a b else min a b)
    else a

/-- **Hilfslemma 1 — Disjunkt-Eindeutigkeit am Punkt.** An zwei verschiedenen Stellen
fallen Minimum und Maximum auseinander. Das ist der Grund, warum eine Operation auf einer
Elementarkontextur nicht zugleich als Konjunktion und als Disjunktion wirken kann, und
damit der Grund, warum die Ablesung in `locallyClassicalEquiv` wohldefiniert ist. -/
theorem min_ne_max_of_ne {m : ℕ} {a b : Fin m} (h : a ≠ b) : min a b ≠ max a b := by
  intro hE
  have hv := congrArg Fin.val hE
  simp only [Fin.coe_min, Fin.coe_max] at hv
  exact h (Fin.eq_of_val_eq (by omega))

/-- **Hilfslemma 2 — der Wert des Bauplans auf einem Paar, in beiden Reihenfolgen.** Die
Operation ist auf `{x,y}` symmetrisch bestimmt: derselbe Eintrag des Wahlvektors entscheidet
beide Argumentreihenfolgen. -/
theorem ofChoices_pair (m : ℕ) (c : Pairs m → Bool) {x y : Fin m} (h : x < y) :
    ofChoices m c x y = (if c ⟨(x, y), h⟩ then max x y else min x y) ∧
      ofChoices m c y x = (if c ⟨(x, y), h⟩ then max x y else min x y) := by
  constructor
  · unfold ofChoices; rw [dif_pos h]
  · unfold ofChoices; rw [dif_neg (asymm h), dif_pos h, max_comm y x, min_comm y x]

/-- **Hilfslemma 3 — der Wert des Bauplans auf der Diagonale.** Kein Wahlvektor kann sie
bewegen; sie ist durch die Gestalt der Definition festgelegt. -/
theorem ofChoices_diag (m : ℕ) (c : Pairs m → Bool) (a : Fin m) :
    ofChoices m c a a = a := by
  unfold ofChoices; rw [dif_neg (lt_irrefl a), dif_neg (lt_irrefl a)]

/-! ## Teil 3 — R1: die Aequivalenz

Zuerst die positive Haelfte: jeder Wahlvektor liefert eine lokal klassische Operation. Die
Wahl zwischen den beiden Disjunkten faellt am Konstruktor und nicht ueber `omega`
(Fallstrick 7: ein Disjunktions-Ziel zoege `Classical.choice`).

Dann die Bijektion. Die Hinrichtung liest je Paar ab, ob die Operation dort als Maximum
wirkt; die Rueckrichtung ist `ofChoices`. Dass beide Wege sich aufheben, haengt an drei
Stellen: am Paar (Hilfslemma 2), an der Diagonale (Hilfslemma 3 und die Erzwingung
`f a a = a`, die aus der lokalen Klassizitaet folgt) und an der Eindeutigkeit des Disjunkts
(Hilfslemma 1). -/

/-- **R1, positive Haelfte — jeder Wahlvektor ist lokal klassisch.** Fuer jedes `m` und
ohne Schranke; bei `m ≤ 1` ist die Aussage leer. -/
theorem ofChoices_locallyClassical (m : ℕ) (c : Pairs m → Bool) :
    LocallyClassical (ofChoices m c) := by
  intro x y hxy
  rcases lt_or_gt_of_ne hxy with h | h
  · obtain ⟨e1, e2⟩ := ofChoices_pair m c h
    rcases Bool.eq_false_or_eq_true (c ⟨(x, y), h⟩) with hc | hc <;> rw [hc] at e1 e2
    · rw [if_pos rfl] at e1 e2
      refine Or.inr ?_
      rintro a b (rfl | rfl) (rfl | rfl)
      · rw [ofChoices_diag, max_self]
      · exact e1
      · rw [max_comm]; exact e2
      · rw [ofChoices_diag, max_self]
    · rw [if_neg Bool.false_ne_true] at e1 e2
      refine Or.inl ?_
      rintro a b (rfl | rfl) (rfl | rfl)
      · rw [ofChoices_diag, min_self]
      · exact e1
      · rw [min_comm]; exact e2
      · rw [ofChoices_diag, min_self]
  · obtain ⟨e1, e2⟩ := ofChoices_pair m c h
    rcases Bool.eq_false_or_eq_true (c ⟨(y, x), h⟩) with hc | hc <;> rw [hc] at e1 e2
    · rw [if_pos rfl] at e1 e2
      refine Or.inr ?_
      rintro a b (rfl | rfl) (rfl | rfl)
      · rw [ofChoices_diag, max_self]
      · rw [max_comm]; exact e2
      · exact e1
      · rw [ofChoices_diag, max_self]
    · rw [if_neg Bool.false_ne_true] at e1 e2
      refine Or.inl ?_
      rintro a b (rfl | rfl) (rfl | rfl)
      · rw [ofChoices_diag, min_self]
      · rw [min_comm]; exact e2
      · exact e1
      · rw [ofChoices_diag, min_self]

/-- **R1 — die Aequivalenz (das Theorem der Datei).** Die lokal klassischen Operationen auf
`Fin m` stehen in Bijektion zu den Wahlvektoren ueber den geordneten Paaren. Die Hinrichtung
liest je Paar ab, ob die Operation dort als Maximum wirkt; die Rueckrichtung ist der
Bauplan. -/
def locallyClassicalEquiv (m : ℕ) :
    { f : Fin m → Fin m → Fin m // LocallyClassical f } ≃ (Pairs m → Bool) where
  toFun f p := f.1 p.1.1 p.1.2 == max p.1.1 p.1.2
  invFun c := ⟨ofChoices m c, ofChoices_locallyClassical m c⟩
  left_inv := by
    rintro ⟨f, hf⟩
    apply Subtype.ext
    funext a b
    show ofChoices m (fun p : Pairs m => f p.1.1 p.1.2 == max p.1.1 p.1.2) a b = f a b
    have hdiag : ∀ a : Fin m, f a a = a := by
      intro a
      rcases Nat.lt_or_ge m 2 with hm | hm
      · have : Subsingleton (Fin m) := Fin.subsingleton_iff_le_one.mpr (by omega)
        exact Subsingleton.elim _ _
      · have hne : ∃ y : Fin m, y ≠ a := by
          by_cases h0 : a.val = 0
          · refine ⟨⟨1, by omega⟩, fun hc => ?_⟩
            have h1 : (1 : ℕ) = a.val := congrArg Fin.val hc
            omega
          · refine ⟨⟨0, by omega⟩, fun hc => ?_⟩
            have h1 : (0 : ℕ) = a.val := congrArg Fin.val hc
            omega
        obtain ⟨y, hy⟩ := hne
        rcases hf y a hy with h1 | h2
        · exact (h1 a a (Or.inr rfl) (Or.inr rfl)).trans (min_self a)
        · exact (h2 a a (Or.inr rfl) (Or.inr rfl)).trans (max_self a)
    by_cases hab : a < b
    · obtain ⟨e1, -⟩ := ofChoices_pair m (fun p => f p.1.1 p.1.2 == max p.1.1 p.1.2) hab
      rw [e1]
      by_cases hc : (f a b == max a b) = true
      · rw [if_pos hc]; exact (beq_iff_eq.mp hc).symm
      · rw [if_neg hc]
        rcases hf a b (ne_of_lt hab) with h1 | h2
        · exact (h1 a b (Or.inl rfl) (Or.inr rfl)).symm
        · exact absurd (beq_iff_eq.mpr (h2 a b (Or.inl rfl) (Or.inr rfl))) hc
    · by_cases hba : b < a
      · obtain ⟨-, e2⟩ := ofChoices_pair m (fun p => f p.1.1 p.1.2 == max p.1.1 p.1.2) hba
        rw [e2]
        by_cases hc : (f b a == max b a) = true
        · rw [if_pos hc]
          rcases hf b a (ne_of_lt hba) with h1 | h2
          · exact absurd ((h1 b a (Or.inl rfl) (Or.inr rfl)).symm.trans (beq_iff_eq.mp hc))
              (min_ne_max_of_ne (ne_of_lt hba))
          · rw [max_comm]; exact (h2 a b (Or.inr rfl) (Or.inl rfl)).symm
        · rw [if_neg hc]
          rcases hf b a (ne_of_lt hba) with h1 | h2
          · rw [min_comm]; exact (h1 a b (Or.inr rfl) (Or.inl rfl)).symm
          · exact absurd (beq_iff_eq.mpr (h2 b a (Or.inl rfl) (Or.inr rfl))) hc
      · have hEq : a = b := le_antisymm (not_lt.mp hba) (not_lt.mp hab)
        subst hEq
        rw [ofChoices_diag]
        exact (hdiag a).symm
  right_inv := by
    intro c
    funext p
    show (ofChoices m c p.1.1 p.1.2 == max p.1.1 p.1.2) = c p
    obtain ⟨e1, -⟩ := ofChoices_pair m c p.2
    have hp : (⟨(p.1.1, p.1.2), p.2⟩ : Pairs m) = p := rfl
    rw [e1, hp]
    rcases Bool.eq_false_or_eq_true (c p) with hc | hc <;> rw [hc]
    · rw [if_pos rfl]; exact beq_self_eq_true _
    · rw [if_neg Bool.false_ne_true]
      exact beq_eq_false_iff_ne.mpr (min_ne_max_of_ne (ne_of_lt p.2))

/-! ## Teil 4 — R2: die Zahl

Drei Entscheidbarkeits-Instanzen, und keine weitere: `Subtype.fintype` ueber der
`Pi`-Instanz braucht `DecidablePred LocallyClassical`, und die `Prop`-Definitionen des
Bestands sind fuer die Instanzensuche opak (Fallstrick 2), darum `inferInstanceAs`. -/

instance instDecidableActsAsMin {m : ℕ} (f : Fin m → Fin m → Fin m) (x y : Fin m) :
    Decidable (ActsAsMin f x y) :=
  inferInstanceAs (Decidable (∀ a b : Fin m, (a = x ∨ a = y) → (b = x ∨ b = y) →
    f a b = min a b))

instance instDecidableActsAsMax {m : ℕ} (f : Fin m → Fin m → Fin m) (x y : Fin m) :
    Decidable (ActsAsMax f x y) :=
  inferInstanceAs (Decidable (∀ a b : Fin m, (a = x ∨ a = y) → (b = x ∨ b = y) →
    f a b = max a b))

instance instDecidableLocallyClassical {m : ℕ} (f : Fin m → Fin m → Fin m) :
    Decidable (LocallyClassical f) :=
  inferInstanceAs (Decidable (∀ x y : Fin m, x ≠ y → ActsAsMin f x y ∨ ActsAsMax f x y))

/-- **R2 — die Zahl.** Auf `Fin m` gibt es genau `2^C(m,2)` lokal klassische Operationen —
eine je Wahlvektor. Korollar von R1 und R0 ueber die Karte des Funktionsraums; die Marken
`8`, `64`, `1024` des Arbeitspapiers sind Instanzen dieses Satzes und keine eigenen
Zaehlungen. -/
theorem card_locallyClassical (m : ℕ) :
    Fintype.card { f : Fin m → Fin m → Fin m // LocallyClassical f } = 2 ^ m.choose 2 := by
  rw [Fintype.card_congr (locallyClassicalEquiv m), Fintype.card_fun, Fintype.card_bool,
    card_pairs]

/-! ## Teil 5 — R3: die Erreichbarkeits-Seite, als Mengengleichheit

Beidseitiger Konsum: die Hinrichtung ist die E3-Iff, die Rueckrichtung sind
`GCB.min_in_clone` und `GCB.max_in_clone` samt den beiden Klassizitaets-Saetzen. Bewusst
keine Kardinalitaet — „im Klon liegen" ist nicht entscheidbar (Dateikopf, Grenze 4). -/

/-- Das Minimum ist lokal klassisch — auf jeder Elementarkontextur wirkt es als
Konjunktion. -/
theorem min_locallyClassical (m : ℕ) : LocallyClassical (fun a b : Fin m => min a b) :=
  fun _ _ _ => Or.inl (fun _ _ _ _ => rfl)

/-- Das Maximum ist lokal klassisch. -/
theorem max_locallyClassical (m : ℕ) : LocallyClassical (fun a b : Fin m => max a b) :=
  fun _ _ _ => Or.inr (fun _ _ _ _ => rfl)

section
variable {m : ℕ}

/-- **Die „Zwei" ist wirklich zwei.** Minimum und Maximum fallen ab zwei Werten
auseinander; Widerlegungspunkt `(0,1)`. Ohne diesen Satz waere die Mengengleichheit von R3
mit einer einelementigen Menge vertraeglich. -/
theorem min_ne_max (hm : 2 ≤ m) :
    (fun a b : Fin m => min a b) ≠ (fun a b : Fin m => max a b) := by
  intro hE
  have h := congrFun (congrFun hE ⟨0, by omega⟩) ⟨1, by omega⟩
  have hv := congrArg Fin.val h
  simp only [Fin.coe_min, Fin.coe_max] at hv
  omega

/-- **R3 — die Erreichbarkeits-Seite.** Ab `m ≥ 4` sind von den `2^C(m,2)` lokal
klassischen Operationen genau zwei im Klon von `{∧, ∨, ¬}`: Minimum und Maximum. Als
Mengengleichheit und nicht als Zahl; dass die beiden verschieden sind, sagt
`min_ne_max`. -/
theorem clone_locallyClassical_eq (hm : 4 ≤ m) :
    { f : Fin m → Fin m → Fin m | LocallyClassical f ∧
        ∃ t : L.Term (Fin 2), ∀ v : Fin 2 → Fin m, t.realize v = f (v 0) (v 1) }
      = { fun a b => min a b, fun a b => max a b } := by
  ext f
  constructor
  · rintro ⟨hlc, ht⟩
    rcases (locally_classical_in_clone_iff hm f hlc).mp ht with h | h
    · exact Or.inl h
    · exact Or.inr h
  · rintro (rfl | rfl)
    · exact ⟨min_locallyClassical m, min_in_clone⟩
    · exact ⟨max_locallyClassical m, max_in_clone⟩

end

/-! ## Teil 6 — R4: das Wachstum, und der Ueberschuss

Beide Saetze rechnen auf R2. Die Schranke `1 ≤ m` in R4 ist scharf: bei `m = 0` sind beide
Exponenten `0`, und beide Seiten stehen auf `1`. -/

/-- **R4 — das Wachstum am Gegenstand.** Von Stufe zu Stufe wird die Zahl der lokal
klassischen Operationen echt groesser. Ueber R2 auf beiden Seiten und
`SAsc.choose_two_succ`; die Voraussetzung `1 ≤ m` ist scharf, bei `m = 0` stehen beide
Seiten auf `1`. -/
theorem card_locallyClassical_lt (m : ℕ) (hm : 1 ≤ m) :
    Fintype.card { f : Fin m → Fin m → Fin m // LocallyClassical f }
      < Fintype.card { f : Fin (m + 1) → Fin (m + 1) → Fin (m + 1) // LocallyClassical f } := by
  rw [card_locallyClassical, card_locallyClassical]
  refine Nat.pow_lt_pow_right (by omega) ?_
  rw [choose_two_succ]
  omega

/-- **Zugabe — der Ueberschuss, quantitativ.** Ab `m ≥ 3` gibt es mehr als zwei lokal
klassische Operationen. Zusammen mit R3 ist das die Aussage, dass ab `m ≥ 4` echt mehr
existieren als erreichbar sind; bei `m = 2` gilt sie nicht und soll nicht gelten — dort ist
alles, was es gibt, auch erzeugbar. -/
theorem two_lt_card_locallyClassical (m : ℕ) (hm : 3 ≤ m) :
    2 < Fintype.card { f : Fin m → Fin m → Fin m // LocallyClassical f } := by
  rw [card_locallyClassical]
  have h3 : 3 ≤ m.choose 2 := Nat.choose_le_choose 2 hm
  calc (2 : ℕ) = 2 ^ 1 := rfl
    _ < 2 ^ m.choose 2 := Nat.pow_lt_pow_right (by omega) (by omega)

/-! **Statement-Pins.** Voller Wortlaut links, Satz rechts — jede Drift des *Statements*
bricht den Build. Namenlose `example`s, keine Axiom-Wache. -/

-- STATEMENT-PIN
example (m : ℕ) :
    { f : Fin m → Fin m → Fin m // LocallyClassical f } ≃ (Pairs m → Bool) :=
  locallyClassicalEquiv m
-- STATEMENT-PIN
example (m : ℕ) :
    Fintype.card { f : Fin m → Fin m → Fin m // LocallyClassical f } = 2 ^ m.choose 2 :=
  card_locallyClassical m
-- STATEMENT-PIN
example {m : ℕ} (hm : 4 ≤ m) :
    { f : Fin m → Fin m → Fin m | LocallyClassical f ∧
        ∃ t : L.Term (Fin 2), ∀ v : Fin 2 → Fin m, t.realize v = f (v 0) (v 1) }
      = { fun a b => min a b, fun a b => max a b } :=
  clone_locallyClassical_eq hm
-- STATEMENT-PIN
example (m : ℕ) (hm : 1 ≤ m) :
    Fintype.card { f : Fin m → Fin m → Fin m // LocallyClassical f }
      < Fintype.card { f : Fin (m + 1) → Fin (m + 1) → Fin (m + 1) // LocallyClassical f } :=
  card_locallyClassical_lt m hm

/-! ## Teil 7 — die Axiom-Wachen (Ist-gebunden)

Ist-Ausgabe des gruenen Builds (v4.30.0-rc2), pro Deklaration eingefroren
(Datei-Vollstaendigkeits-Regel, einschliesslich der drei Definitionen, der drei
Hilfslemmata und der drei Instanzen). Die Schichtgrenze und ihre gemessene Herkunft stehen
im Dateikopf. -/

/-- info: 'Reformulation.Proemial.ChoiceVectors.Pairs' does not depend on any axioms -/
#guard_msgs in #print axioms Pairs

/-- info: 'Reformulation.Proemial.ChoiceVectors.card_pairs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms card_pairs

/-- info: 'Reformulation.Proemial.ChoiceVectors.ofChoices' depends on axioms: [propext] -/
#guard_msgs in #print axioms ofChoices

/-- info: 'Reformulation.Proemial.ChoiceVectors.min_ne_max_of_ne' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms min_ne_max_of_ne

/-- info: 'Reformulation.Proemial.ChoiceVectors.ofChoices_pair' depends on axioms: [propext] -/
#guard_msgs in #print axioms ofChoices_pair

/-- info: 'Reformulation.Proemial.ChoiceVectors.ofChoices_diag' depends on axioms: [propext] -/
#guard_msgs in #print axioms ofChoices_diag

/-- info: 'Reformulation.Proemial.ChoiceVectors.ofChoices_locallyClassical' depends on axioms: [propext] -/
#guard_msgs in #print axioms ofChoices_locallyClassical

/-- info: 'Reformulation.Proemial.ChoiceVectors.locallyClassicalEquiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms locallyClassicalEquiv

/-- info: 'Reformulation.Proemial.ChoiceVectors.instDecidableActsAsMin' depends on axioms: [propext] -/
#guard_msgs in #print axioms instDecidableActsAsMin

/-- info: 'Reformulation.Proemial.ChoiceVectors.instDecidableActsAsMax' depends on axioms: [propext] -/
#guard_msgs in #print axioms instDecidableActsAsMax

/-- info: 'Reformulation.Proemial.ChoiceVectors.instDecidableLocallyClassical' depends on axioms: [propext] -/
#guard_msgs in #print axioms instDecidableLocallyClassical

/-- info: 'Reformulation.Proemial.ChoiceVectors.card_locallyClassical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms card_locallyClassical

/-- info: 'Reformulation.Proemial.ChoiceVectors.min_locallyClassical' depends on axioms: [propext] -/
#guard_msgs in #print axioms min_locallyClassical

/-- info: 'Reformulation.Proemial.ChoiceVectors.max_locallyClassical' depends on axioms: [propext] -/
#guard_msgs in #print axioms max_locallyClassical

/-- info: 'Reformulation.Proemial.ChoiceVectors.min_ne_max' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms min_ne_max

/-- info: 'Reformulation.Proemial.ChoiceVectors.clone_locallyClassical_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms clone_locallyClassical_eq

/-- info: 'Reformulation.Proemial.ChoiceVectors.card_locallyClassical_lt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms card_locallyClassical_lt

/-- info: 'Reformulation.Proemial.ChoiceVectors.two_lt_card_locallyClassical' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms two_lt_card_locallyClassical

end Reformulation.Proemial.ChoiceVectors
