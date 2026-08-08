import Reformulation.Kenogram.PlaceSwap

/-!
# Reformulation.Kenogram.JointClosure — gemeinsame Abgeschlossenheit und ihre Untergrenze

**Ertrag.** Eine Definition mit ihren beiden Konsumenten: Mengen von Reihen, die
sowohl unter dem **Stellentausch** als auch unter dem **Abstieg** abgeschlossen sind,
haben eine angebbare Untergrenze — und sie wird von zwei Dreiermengen angenommen.

1. **Z1** (`hull_le_of_jointlyClosed`) — enthält eine gemeinsam abgeschlossene Menge
   eine RGS-Reihe der Länge mindestens zwei, so enthält sie `{[], [0], [0,0]}` oder
   `{[], [0], [0,1]}` **ganz**. Ohne Längenschranke.
2. **Z2** (`jointlyClosed_hull_pair`) — beide Dreiermengen sind selbst gemeinsam
   abgeschlossen.

**Bewiesen ist eine Invarianz-Untergrenze; keine Priorität, kein Grund.** Zusammen
sagen Z1 und Z2: unterhalb der beiden Dreiermengen liegt nichts, was eine RGS-Reihe
der Länge ≥ 2 enthielte, und beide kommen vor.

## Die Indexschranke in der Definition — gemessene Abweichung von der Vorgabe

Die Vorgabe quantifizierte `∀ i j` ohne Schranke. **Eine Vorprobe am Quelltext hat
das widerlegt, und der Bau meldet es, statt die Zielsätze anzupassen.** `swapPlaces`
ist über `List.set` und `List.getD` gebaut:

```
swapPlaces i j l = (l.set i (l.getD j 0)).set j (l.getD i 0)
```

Liegt **genau ein** Index ausserhalb, so liefert `getD` die Vorgabe `0` und `set`
schreibt sie: der Aufruf setzt eine Stelle auf `0`, statt zwei Stellen zu tauschen.
Gemessen (`#eval`, beide Richtungen):

```
exchangeAt 1 5 [0,1] = [0,0]        exchangeAt 5 1 [0,1] = [0,0]
exchangeAt 0 1 [0,1] = [0,1]        exchangeAt 7 9 [0,1] = [0,1]
```

**Ohne Schranke wäre `{[], [0], [0,1]}` nicht abgeschlossen** und Z2 falsch; die
gemessenen Hüllen wären `{[], [0], [0,0]}` und `{[], [0], [0,0], [0,1]}`, und es gäbe
**eine** minimale Menge statt zweier.

**Die Schranke verengt den Tausch nicht, sie schliesst aus, was keiner ist.** Ein
Aufruf mit einem Index ausserhalb der Reihe vertauscht keine Stellen; er überschreibt
eine. Die Schranke ist damit die getreue Fassung von *Stellentausch* und keine
Bequemlichkeit — und sie ist genau die Schranke, unter der die Sondierung gerechnet
hat, deren Messung dieser Zug auf alle Längen hebt.

## Was Z1 verbraucht, und was nicht

**Z1 konsumiert nur die Abstiegs-Hälfte** der Definition; die Tausch-Hälfte geht in
seinen Beweis nicht ein. Das steht hier, weil die Voraussetzung sonst stärker
aussähe, als sie ist. **Z2 verbraucht beide.** Die Definition bekommt ihre
Ledger-Zeile, weil Z1 und Z2 sie konsumieren.

## Deutungsgrenzen

**Dies ist keine Aussage über Herkunft.** Bewiesen ist ein **Enthaltensein** — eine
`⊆`-Untergrenze über zwei Operationsfamilien. Kein Name und keine Aussage dieses
Moduls trägt ein Deutungswort.

*Deutung, mit Herkunft und mit ihrer Grenze im selben Absatz:* der
`Kenogrammatischer_Invariantenschnitt_Befund.md` (§6) hält eine Übereinstimmung
zwischen den beiden Erzeugern dieses Moduls und Günthers Angabe fest, die proemiale
Relation sei auf der kenogrammatischen Ebene verortet und *mit zwei Kenogrammen*
geschrieben. **Das ist eine Übereinstimmung und kein Satz.** Und daneben, wörtlich
aus §8 desselben Befunds: **eine Kopplung ist kein Grund.** Wer diesen Kopf liest,
hat beides in einem Blick.

## Aggregat-Reife

Ein Import: `Kenogram.PlaceSwap` (der `Kenogram.Basic` transitiv trägt — die Vorgabe
nannte beide, die zweite Zeile wäre über die transitive Hülle hinaus). Keine Sonde,
keine Setzung.

Kein `sorry`, kein `axiom`, kein `: True`-Feld, kein `native_decide`.
-/

namespace Reformulation.Kenogram

/-! ## Teil 1 — die Definition -/

/-- **Gemeinsame Abgeschlossenheit.** Eine Menge von Reihen ist gemeinsam
abgeschlossen, wenn sie unter jedem Stellentausch *innerhalb der Reihe* und unter dem
Abstieg abgeschlossen ist. Zur Indexschranke siehe den Dateikopf: ein Aufruf mit einem
Index ausserhalb der Reihe ist kein Stellentausch. -/
def JointlyClosed (S : Set (List ℕ)) : Prop :=
  (∀ l ∈ S, ∀ i j, i < l.length → j < l.length → exchangeAt i j l ∈ S) ∧
  (∀ l ∈ S, l.dropLast ∈ S)

/-! ## Teil 2 — der Abstieg bis zur Länge zwei -/

/-- Der iterierte Abstieg führt jede Reihe der Länge mindestens zwei auf ihr
Zweier-Anfangsstück. Privat; kein eigener Posten. -/
private theorem take_two_mem {S : Set (List ℕ)}
    (hd : ∀ l ∈ S, l.dropLast ∈ S) :
    ∀ (n : ℕ) (l : List ℕ), l.length = n → 2 ≤ n → l ∈ S → l.take 2 ∈ S := by
  intro n
  induction n with
  | zero => intro l _ h2 _; omega
  | succ m ih =>
    intro l hlen h2 hmem
    rcases Nat.lt_or_ge m 2 with hm | hm
    · have hl2 : l.length ≤ 2 := by omega
      rwa [List.take_of_length_le hl2]
    · have hdl : l.dropLast.length = m := by
        rw [List.length_dropLast, hlen]; omega
      have hmin : min 2 (l.length - 1) = 2 := by omega
      have hrw : l.dropLast.take 2 = l.take 2 := by
        rw [List.dropLast_eq_take, List.take_take, hmin]
      rw [← hrw]
      exact ih l.dropLast hdl hm (hd l hmem)

/-! ## Teil 3 — die zwei Gestalten der Länge zwei -/

/-- Eine RGS-Reihe der Länge zwei ist `[0,0]` oder `[0,1]`: der Kopf ist `0`, und die
zweite Stelle überschreitet das laufende Maximum um höchstens eins. Privat. -/
private theorem rgs_length_two {l : List ℕ} (h : IsRGS l) (hlen : l.length = 2) :
    l = [0, 0] ∨ l = [0, 1] := by
  match l, hlen with
  | [a, b], _ =>
    rw [isRGS_iff] at h
    obtain ⟨h0, h1⟩ := h
    have ha : a = 0 := h0 (by simp)
    subst ha
    have hb : b ≤ 1 := by simpa using h1 0 (by simp)
    have hb' : b = 0 ∨ b = 1 := by omega
    rcases hb' with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl

/-! ## Teil 4 — Z1, die ⊆-Untergrenze über alle Längen -/

/-- **Z1.** Enthält eine gemeinsam abgeschlossene Menge eine RGS-Reihe der Länge
mindestens zwei, so enthält sie eine der beiden Dreiermengen **ganz**. Ohne
Längenschranke; die Aufzählung der Sondierung (Längen 0–6) ist Illustration und nicht
Geltungsbereich. Verbraucht nur die Abstiegs-Hälfte der Voraussetzung. -/
theorem hull_le_of_jointlyClosed {S : Set (List ℕ)} (h : JointlyClosed S)
    {l : List ℕ} (hl : l ∈ S) (hr : IsRGS l) (h2 : 2 ≤ l.length) :
    ({[], [0], [0, 0]} : Set (List ℕ)) ⊆ S ∨
    ({[], [0], [0, 1]} : Set (List ℕ)) ⊆ S := by
  obtain ⟨-, hd⟩ := h
  have hmem : l.take 2 ∈ S := take_two_mem hd l.length l rfl h2 hl
  have hrgs : IsRGS (l.take 2) := isRGS_take hr 2
  have hlen : (l.take 2).length = 2 := by
    rw [List.length_take]; omega
  rcases rgs_length_two hrgs hlen with hcase | hcase
  · left
    rw [hcase] at hmem
    have h1 : ([0] : List ℕ) ∈ S := hd _ hmem
    have h0 : ([] : List ℕ) ∈ S := hd _ h1
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl <;> assumption
  · right
    rw [hcase] at hmem
    have h1 : ([0] : List ℕ) ∈ S := hd _ hmem
    have h0 : ([] : List ℕ) ∈ S := hd _ h1
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl <;> assumption

/-! ## Teil 5 — Z2, die Untergrenze wird angenommen -/

/-- **Z2.** Beide Dreiermengen sind selbst gemeinsam abgeschlossen. Endliche
Fallarbeit über Längen ≤ 2; verbraucht beide Hälften der Definition. -/
theorem jointlyClosed_hull_pair :
    JointlyClosed ({[], [0], [0, 0]} : Set (List ℕ)) ∧
    JointlyClosed ({[], [0], [0, 1]} : Set (List ℕ)) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · intro l hl i j hi hj
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hl
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    rcases hl with rfl | rfl | rfl
    · simp at hi
    · have hi0 : i = 0 := by simp only [List.length_cons, List.length_nil] at hi; omega
      have hj0 : j = 0 := by simp only [List.length_cons, List.length_nil] at hj; omega
      subst hi0; subst hj0; decide
    · have hi' : i = 0 ∨ i = 1 := by
        simp only [List.length_cons, List.length_nil] at hi; omega
      have hj' : j = 0 ∨ j = 1 := by
        simp only [List.length_cons, List.length_nil] at hj; omega
      rcases hi' with rfl | rfl <;> rcases hj' with rfl | rfl <;> decide
  · intro l hl
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hl
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    rcases hl with rfl | rfl | rfl <;> decide
  · intro l hl i j hi hj
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hl
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    rcases hl with rfl | rfl | rfl
    · simp at hi
    · have hi0 : i = 0 := by simp only [List.length_cons, List.length_nil] at hi; omega
      have hj0 : j = 0 := by simp only [List.length_cons, List.length_nil] at hj; omega
      subst hi0; subst hj0; decide
    · have hi' : i = 0 ∨ i = 1 := by
        simp only [List.length_cons, List.length_nil] at hi; omega
      have hj' : j = 0 ∨ j = 1 := by
        simp only [List.length_cons, List.length_nil] at hj; omega
      rcases hi' with rfl | rfl <;> rcases hj' with rfl | rfl <;> decide
  · intro l hl
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hl
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    rcases hl with rfl | rfl | rfl <;> decide

/-! ## Teil 6 — Statement-Pins

Voller Wortlaut links, Satz rechts — jede Drift des *Statements* bricht den Bau. -/

-- STATEMENT-PIN
example {S : Set (List ℕ)} (h : JointlyClosed S) {l : List ℕ}
    (hl : l ∈ S) (hr : IsRGS l) (h2 : 2 ≤ l.length) :
    ({[], [0], [0, 0]} : Set (List ℕ)) ⊆ S ∨
    ({[], [0], [0, 1]} : Set (List ℕ)) ⊆ S :=
  hull_le_of_jointlyClosed h hl hr h2

-- STATEMENT-PIN
example :
    JointlyClosed ({[], [0], [0, 0]} : Set (List ℕ)) ∧
    JointlyClosed ({[], [0], [0, 1]} : Set (List ℕ)) :=
  jointlyClosed_hull_pair

/-! ## Teil 7 — die Axiom-Wachen (Ist-gebunden)

Ist-Ausgabe des grünen Builds. `Classical.choice` in Z1 ist **geerbt**: der Beweis
konsumiert `isRGS_take`, das über `relabel_eq_self_of_isRGS` und `relabel_isRGS`
läuft, und beide tragen ihn (gemessen). Z2 kommt ohne ihn aus — seine Fallarbeit ist
endlich und entscheidbar. -/

/-- info: 'Reformulation.Kenogram.JointlyClosed' depends on axioms: [propext] -/
#guard_msgs in #print axioms JointlyClosed

/-- info: 'Reformulation.Kenogram.hull_le_of_jointlyClosed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hull_le_of_jointlyClosed

/-- info: 'Reformulation.Kenogram.jointlyClosed_hull_pair' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms jointlyClosed_hull_pair

end Reformulation.Kenogram
