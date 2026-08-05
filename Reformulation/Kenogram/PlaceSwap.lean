import Reformulation.Kenogram.Basic

/-!
# Reformulation.Kenogram.PlaceSwap — Stellen-Tausch und Stufenabstieg

**Ertrag.** Zwei Sätze über das Verhältnis von **Stellen-Vertauschung** und
**Stufenabstieg** (dem Streichen der letzten Stelle) auf kenogrammatischen
Normalformen, dazu das Präfix-Lemma der Kanonisierung, das beide tragen und das der
Schicht bisher fehlte.

1. **Kommutation** (`dropLast_exchangeAt`) — berührt der Tausch die letzte Stelle nicht,
   so vertauscht er sich mit dem Abstieg.
2. **Charakterisierung** (`dropLast_exchangeAt_last_iff`) — berührt er sie, so bleibt der
   Abstieg **genau dann** gleich, wenn `preservesPrefixPattern` gilt.

Damit ist die letzte Stelle als diejenige bestimmt, deren Vertauschung mit dem Abstieg
**nicht** kommutiert — abgelesen aus dem Verhältnis von Umtausch und Stufe, nicht gesetzt.

## Statusgrenze

Beide Sätze sind hier **generisch bewiesen**. Ihre Vorarbeit war eine erschöpfende
Rechnung **bis Länge acht** ausserhalb des Korpus; jene Prüfzahlen sind kein Beweis und
stehen darum nicht hier, sondern im Befund der Erhebung. Was in diesem Modul steht, ist
der Satz.

## Deutungsgrenze

Bewiesen sind eine **Kommutationsregel** und eine **Charakterisierung über Folgen**. Dass
eine Stelle, die der Kommutation widersteht, ein *Relator* im Sinne Günthers sei, ist
**Deutung** und wird hier nicht behauptet. **Dies ist nicht die proemiale Relation**,
sondern eine Kopplung von Umtausch und Stufe auf dem kenogrammatischen Grund.

## Warum `swapPlaces` und nicht `swapVals`

Der Name `swapVals` ist in dieser Schicht besetzt — `Kenogram.swapVals a b l = l.map
(swap a b)` vertauscht zwei **Werte** überall, und `Kenogram.relabel_swapVals` beweist,
dass die Kanonisierung das nicht sieht. **Mit jener Operation wären beide Sätze dieses
Moduls trivial:** `relabel ∘ swapVals` ist auf Normalformen die Identität, die
Kommutation gälte geschenkt und die Charakterisierung wäre falsch — bei grünem Bau. Das
ist der gemessene Grund für den anderen Namen und nicht eine Frage des Geschmacks.

Ebenso ausgeschlossen ist `swapAt`: `Array.swapAt` und `Vector.swapAt` tun etwas anderes —
sie **setzen** einen Wert und geben den alten zurück.

## Dublette

`Proemial.K3CouplingProbe.swapVals` ist zeichengleich mit `swapPlaces` hier. Die Sonde
bleibt unangetastet; eine Zusammenlegung berührte ihre Wachen. **Auslösebedingung für die
Zusammenlegung: der erste Zug, in dem eine Aggregat-Datei die Stellen-Vertauschung erneut
definiert oder die Sonde konsumiert.**

*Warum nicht mehr die Import-Hülle.* Die frühere Fassung lautete „der erste Zug, in dem
beide in einer Import-Hülle liegen". Sie ist beim Klammer-Zug **nicht ausgelöst worden**,
obwohl der Zug stattfand — weil die Hausform der Hebung das **Neubauen** ist:
`Kenogram/Descent.lean` baut die Sätze der Sonden neu, statt sie zu importieren, und damit
kommt `K3CouplingProbe` gar nicht erst in die Hülle. Die Bedingung war weder eingelöst noch
vertagt, sondern **wirkungslos** — sie kannte die Baupraxis nicht, unter der sie stand. Die
neue Fassung nennt den Sachverhalt statt des Trägers.

## Die Seite des Präfix-Lemmas gehört zur Aussage

`relabel_take` gilt für **Präfixe**. Für Suffixe ist die entsprechende Aussage **falsch**:
`relabel ([0,1].drop 1) = [0]`, aber `(relabel [0,1]).drop 1 = [1]`. Eine Formulierung, die
„verträglich mit dem Abschneiden" sagt, ohne die Seite zu nennen, wäre zur Hälfte falsch.

Kein `sorry`, kein `axiom`, kein `: True`-Feld.
-/

namespace Reformulation.Kenogram

-- ============================================================
-- §I — Das Präfix-Lemma der Kanonisierung
-- ============================================================

variable {α : Type*} [DecidableEq α]

/-- Der `relabel`-Faltzustand wächst nur am Ende: `relabelStep` hängt an und ändert
Bestehendes nicht. Trägt das Präfix-Lemma. -/
theorem relabelStep_foldl_append (l : List α) (st : List ℕ × List α) :
    ∃ t : List ℕ, (l.foldl relabelStep st).1 = st.1 ++ t := by
  induction l generalizing st with
  | nil => exact ⟨[], by simp⟩
  | cons x xs ih =>
      obtain ⟨t, ht⟩ := ih (relabelStep st x)
      refine ⟨(match (st.2.idxOf? x) with | some k => [k] | none => [st.2.length]) ++ t, ?_⟩
      rw [List.foldl_cons, ht]
      cases hc : st.2.idxOf? x <;> simp [relabelStep, hc]

/-- **Präfix-Verträglichkeit der Kanonisierung** (endliche Fassung). Die Normalform eines
Präfixes ist das Präfix der Normalform.

Der Bestand trug diese Aussage bisher nur für **Ströme**
(`Bridge.relabelStream_take_eq_relabel`); die endliche Fassung fehlte. Für **Suffixe** ist
sie falsch, siehe Dateikopf. -/
theorem relabel_take (l : List α) (k : ℕ) :
    relabel (l.take k) = (relabel l).take k := by
  rcases Nat.lt_or_ge l.length k with hk | hk
  case inl =>
    rw [List.take_of_length_le (Nat.le_of_lt hk),
        List.take_of_length_le (by rw [relabel_length]; exact Nat.le_of_lt hk)]
  have hsplit : relabel l
      = ((l.drop k).foldl relabelStep ((l.take k).foldl relabelStep ([], []))).1 := by
    conv_lhs => rw [relabel_eq_foldl, ← List.take_append_drop k l]
    rw [List.foldl_append]
  obtain ⟨t, ht⟩ := relabelStep_foldl_append (l.drop k) ((l.take k).foldl relabelStep ([], []))
  have hpre : ((l.take k).foldl relabelStep ([], [])).1 = relabel (l.take k) :=
    (relabel_eq_foldl (l.take k)).symm
  rw [hsplit, ht, hpre]
  exact (List.take_left' (by rw [relabel_length, List.length_take, min_eq_left hk])).symm

/-- Die `dropLast`-Fassung des Präfix-Lemmas. -/
theorem relabel_dropLast (l : List α) : relabel l.dropLast = (relabel l).dropLast := by
  rw [List.dropLast_eq_take, relabel_take, List.dropLast_eq_take, relabel_length]

/-- Präfixe von Normalformen sind Normalformen — Folgerung aus dem Präfix-Lemma und
darum ohne eigene Induktion. -/
theorem isRGS_take {l : List ℕ} (h : IsRGS l) (k : ℕ) : IsRGS (l.take k) := by
  have he : relabel (l.take k) = l.take k := by
    rw [relabel_take, relabel_eq_self_of_isRGS h]
  rw [← he]; exact relabel_isRGS _

/-- `IsRGS` unter dem Abstieg. -/
theorem isRGS_dropLast' {l : List ℕ} (h : IsRGS l) : IsRGS l.dropLast := by
  rw [List.dropLast_eq_take]; exact isRGS_take h _

-- ============================================================
-- §II — Der Stellen-Tausch
-- ============================================================

/-- **Vertauschung der Einträge an zwei Stellen.** Beide `getD` beziehen sich auf das
Original; ausserhalb des Bereichs ist `List.set` ein No-op. Zum Namen siehe Dateikopf. -/
def swapPlaces (i j : ℕ) (l : List ℕ) : List ℕ :=
  (l.set i (l.getD j 0)).set j (l.getD i 0)

@[simp] theorem swapPlaces_length (i j : ℕ) (l : List ℕ) :
    (swapPlaces i j l).length = l.length := by simp [swapPlaces]

/-- **Der Umtausch**: Stellen-Tausch mit anschliessender Kanonisierung. Ohne `relabel`
verliesse der Tausch die Normalform. -/
def exchangeAt (i j : ℕ) (l : List ℕ) : List ℕ := relabel (swapPlaces i j l)

/-- Berühren beide Stellen die letzte nicht, so verträgt sich der Stellen-Tausch mit dem
Streichen der letzten Stelle. -/
theorem dropLast_swapPlaces {i j : ℕ} {l : List ℕ}
    (hi : i < l.length - 1) (hj : j < l.length - 1) :
    (swapPlaces i j l).dropLast = swapPlaces i j l.dropLast := by
  apply List.ext_getElem?
  intro p
  have hlen : l.dropLast.length = l.length - 1 := List.length_dropLast
  simp only [swapPlaces, List.getElem?_dropLast, List.getElem?_set, List.length_set, hlen,
    List.getD_eq_getElem?_getD, List.getElem?_dropLast]
  by_cases hp : p < l.length - 1
  · have hpl : p < l.length := by omega
    by_cases hij : i = j <;> simp_all
  · have hjp : ¬ (j = p) := by omega
    have hip : ¬ (i = p) := by omega
    simp only [if_neg hp, if_neg hjp, if_neg hip]

/-- Berührt der Tausch die letzte Stelle, so ist der Abstieg das Präfix mit dem Wert der
letzten Stelle an der Stelle `i`. -/
theorem dropLast_swapPlaces_last {i : ℕ} {l : List ℕ} (hi : i < l.length - 1) :
    (swapPlaces i (l.length - 1) l).dropLast
      = l.dropLast.set i (l.getD (l.length - 1) 0) := by
  apply List.ext_getElem?
  intro p
  have hlen : l.dropLast.length = l.length - 1 := List.length_dropLast
  simp only [swapPlaces, List.getElem?_dropLast, List.getElem?_set, List.length_set, hlen,
    List.getD_eq_getElem?_getD, List.getElem?_dropLast]
  by_cases hp : p < l.length - 1
  · have hpl : p < l.length := by omega
    have hlp : ¬ (l.length - 1 = p) := by omega
    simp only [if_neg hlp, if_pos hp, if_pos hpl]
    by_cases hip : i = p <;> simp [hip, hpl, hp]
  · have hip : ¬ (i = p) := by omega
    simp only [if_neg hp, if_neg hip]

-- ============================================================
-- §III — Satz 1: die Kommutation
-- ============================================================

/-- **Satz 1 (Kommutation).** Berührt der Tausch die letzte Stelle nicht, so vertauscht er
sich mit dem Abstieg.

**Nicht „unverändert".** Die Sonde `Proemial.K3CouplingProbe.decoupled_commutes` sagt an
ihrem Zeugen `[0,1,1]`, der Abstieg bleibe *gleich*; das gilt dort nur, weil das getauschte
Präfix zufällig dasselbe Muster trägt. Generisch gilt **Kommutation** und nicht Invarianz —
wer den Sondensatz verallgemeinert, schreibt einen falschen Satz hin, und er sähe der Sonde
ähnlich genug, um durchzugehen.

Der Satz braucht **keine** RGS-Voraussetzung: er gilt für beliebige Listen. -/
theorem dropLast_exchangeAt {i j : ℕ} {l : List ℕ}
    (hi : i < l.length - 1) (hj : j < l.length - 1) :
    (exchangeAt i j l).dropLast = exchangeAt i j l.dropLast := by
  rw [exchangeAt, exchangeAt, ← relabel_dropLast, dropLast_swapPlaces hi hj]

-- ============================================================
-- §IV — Die Bedingung und Satz 2
-- ============================================================

/-- Brücke: an einer besetzten Stelle ist `List.count` genau dann eins, wenn diese Stelle
die einzige mit diesem Wert ist. Mathlib führt kein `count_eq_one`. -/
theorem count_eq_one_iff_unique {p : List ℕ} {i : ℕ} (hi : i < p.length) :
    List.count p[i] p = 1 ↔ ∀ b, ∀ _ : b < p.length, p[b] = p[i] → b = i := by
  obtain ⟨v, hv⟩ : ∃ v, p[i] = v := ⟨_, rfl⟩
  have hsplit : p = p.take i ++ v :: p.drop (i + 1) := by
    conv_lhs => rw [← List.take_append_drop i p]
    rw [List.drop_eq_getElem_cons hi, hv]
  rw [hv]
  simp only [hv] at *
  constructor
  · intro hc b hb hbv
    by_contra hne
    have hmem : v ∈ p.take i ∨ v ∈ p.drop (i + 1) := by
      rcases Nat.lt_or_ge b i with h | h
      · left
        rw [List.mem_iff_getElem]
        exact ⟨b, by simp [List.length_take]; omega, by rw [List.getElem_take]; exact hbv⟩
      · right
        rw [List.mem_iff_getElem]
        refine ⟨b - (i + 1), by simp [List.length_drop]; omega, ?_⟩
        rw [List.getElem_drop]
        have hb' : i + 1 + (b - (i + 1)) = b := by omega
        simp only [hb']; exact hbv
    have hge : 2 ≤ List.count v p := by
      conv_rhs => rw [hsplit]
      rw [List.count_append, List.count_cons_self]
      rcases hmem with h | h
      · have := List.count_pos_iff.mpr h; omega
      · have := List.count_pos_iff.mpr h; omega
    omega
  · intro hu
    conv_lhs => rw [hsplit]
    rw [List.count_append, List.count_cons_self]
    have h1 : List.count v (p.take i) = 0 := by
      rw [List.count_eq_zero]
      intro hm
      obtain ⟨c, hc, hcv⟩ := List.mem_iff_getElem.mp hm
      have hcl : c < i := by simp [List.length_take] at hc; omega
      rw [List.getElem_take] at hcv
      have := hu c (by omega) hcv
      omega
    have h2 : List.count v (p.drop (i + 1)) = 0 := by
      rw [List.count_eq_zero]
      intro hm
      obtain ⟨c, hc, hcv⟩ := List.mem_iff_getElem.mp hm
      have hcl : c < p.length - (i + 1) := by simpa [List.length_drop] using hc
      rw [List.getElem_drop] at hcv
      have := hu (i + 1 + c) (by omega) hcv
      omega
    omega

private theorem set_getElem?_val {p : List ℕ} {i v a : ℕ} (ha : a < p.length) :
    (p.set i v)[a]? = some (if i = a then v else p[a]) := by
  rw [List.getElem?_set]
  by_cases h : i = a
  · simp [h, ha]
  · simp [h, List.getElem?_eq_getElem ha]

private theorem set_getElem?_none {p : List ℕ} {i v a : ℕ} (ha : ¬ a < p.length) :
    (p.set i v)[a]? = none := by
  rw [List.getElem?_eq_none_iff.mpr (by rw [List.length_set]; omega)]

/-- **Der Musterkern.** Das Ersetzen des Wertes an der Stelle `i` durch `v` lässt das
Gleichheitsmuster genau dann unverändert, wenn `v` der alte Wert ist — oder wenn der alte
Wert dort einmalig ist **und** `v` überhaupt nicht vorkommt. -/
theorem set_pattern_iff {p : List ℕ} {i : ℕ} (hi : i < p.length) (v : ℕ) :
    (∀ a b : ℕ, (p.set i v)[a]? = (p.set i v)[b]? ↔ p[a]? = p[b]?)
      ↔ (v = p[i] ∨ (List.count p[i] p = 1 ∧ v ∉ p)) := by
  constructor
  · intro hpat
    by_cases hv : v = p[i]
    · exact Or.inl hv
    right
    have hvnot : v ∉ p := by
      intro hm
      obtain ⟨b, hb, hbv⟩ := List.mem_iff_getElem.mp hm
      have hbi : i ≠ b := by rintro rfl; exact hv hbv.symm
      have h1 : (p.set i v)[i]? = (p.set i v)[b]? := by
        rw [set_getElem?_val hi, set_getElem?_val hb, if_pos rfl, if_neg hbi, hbv]
      have h2 := (hpat i b).mp h1
      rw [List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hb] at h2
      injection h2 with h3
      exact hv (by rw [h3, hbv])
    refine ⟨(count_eq_one_iff_unique hi).mpr ?_, hvnot⟩
    intro b hb hbv
    by_contra hbi
    have h2 : p[i]? = p[b]? := by
      rw [List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hb, hbv]
    have h3 := (hpat i b).mpr h2
    rw [set_getElem?_val hi, set_getElem?_val hb, if_pos rfl,
      if_neg (fun h => hbi h.symm)] at h3
    injection h3 with h4
    exact hv (by rw [h4, hbv])
  · rintro (hv | ⟨hc, hvnot⟩) a b
    · subst hv; rw [List.set_getElem_self hi]
    · have huniq := (count_eq_one_iff_unique hi).mp hc
      by_cases ha : a < p.length <;> by_cases hb : b < p.length
      · rw [set_getElem?_val ha, set_getElem?_val hb,
          List.getElem?_eq_getElem ha, List.getElem?_eq_getElem hb]
        simp only [Option.some.injEq]
        by_cases hia : i = a <;> by_cases hib : i = b
        · subst hia; subst hib; simp
        · subst hia
          simp only [if_pos rfl, if_neg hib]
          constructor
          · intro h; exact absurd (List.mem_iff_getElem.mpr ⟨b, hb, h.symm⟩) hvnot
          · intro h; exact absurd (huniq b hb h.symm).symm hib
        · subst hib
          simp only [if_pos rfl, if_neg hia]
          constructor
          · intro h; exact absurd (List.mem_iff_getElem.mpr ⟨a, ha, h⟩) hvnot
          · intro h; exact absurd (huniq a ha h).symm hia
        · simp only [if_neg hia, if_neg hib]
      · have h1 : p[b]? = none := List.getElem?_eq_none_iff.mpr (by omega)
        rw [set_getElem?_none hb, set_getElem?_val ha, h1, List.getElem?_eq_getElem ha]
        simp
      · have h1 : p[a]? = none := List.getElem?_eq_none_iff.mpr (by omega)
        rw [set_getElem?_none ha, set_getElem?_val hb, h1, List.getElem?_eq_getElem hb]
        simp
      · have h1 : p[a]? = none := List.getElem?_eq_none_iff.mpr (by omega)
        have h2 : p[b]? = none := List.getElem?_eq_none_iff.mpr (by omega)
        rw [set_getElem?_none ha, set_getElem?_none hb, h1, h2]

/-- Normalform-Gleichheit ist Muster-Gleichheit. -/
theorem relabel_eq_iff_pattern {q p : List ℕ} (hp : IsRGS p) (hlen : q.length = p.length) :
    relabel q = p ↔ ∀ a b : ℕ, q[a]? = q[b]? ↔ p[a]? = p[b]? := by
  constructor
  · intro h a b
    rw [← relabel_getElem?_eq_iff q a b, h]
  · intro h
    exact rgs_unique_of_pattern (relabel_isRGS q) hp (by rw [relabel_length, hlen])
      (fun a b => (relabel_getElem?_eq_iff q a b).trans (h a b))

/-- **Die Bedingung.** Der Tausch der Stelle `i` mit der letzten lässt das
Gleichheitsmuster des Präfixes unverändert.

**Eine Disjunktion mit zwei Gliedern, das zweite eine Konjunktion aus zweien — und jedes
Glied ist unentbehrlich:**

* **(a)** die beiden Werte stimmen überein — der Tausch ist auf dem Muster keiner;
* **(b1)** der Wert an der Stelle `i` kommt im Präfix **genau einmal** vor, **und**
* **(b2)** der Wert der letzten Stelle kommt im Präfix **gar nicht** vor.

Ohne (a) bleiben Ausnahmen; ohne (b) ebenso; und **keine der beiden Hälften von (b)
impliziert die andere** — `[0,1,0]` mit `i = 1` erfüllt (b1) ohne (b2), `[0,0,1]` mit
`i = 0` erfüllt (b2) ohne (b1). Wer die Bedingung beim Zitieren verkürzt, verkürzt sie
falsch.

*Hier stand eine Fallzahl, und sie ging nicht auf.* Der Text kündigte vier Fälle an und
zählte drei auf; die Zahl stammte aus der Prosa der Spezifikation und war aus einer
Messung destilliert, die etwas anderes zählte — drei Varianten der Konjunktion
gegeneinander. **Die Zahl fällt und wird nicht auf drei gesetzt: eine Zahl, die nie eine
Route hatte, bekommt durch Korrektur keine.** Route statt Liste. -/
def preservesPrefixPattern (l : List ℕ) (i : ℕ) : Prop :=
  l.getD (l.length - 1) 0 = l.dropLast.getD i 0
  ∨ (List.count (l.dropLast.getD i 0) l.dropLast = 1
      ∧ l.getD (l.length - 1) 0 ∉ l.dropLast)

/-- **Satz 2 (Charakterisierung).** Berührt der Tausch die letzte Stelle, so bleibt der
Abstieg **genau dann** gleich, wenn `preservesPrefixPattern` gilt.

Als Genau-dann-wenn und nicht als zwei Implikationen: die blosse **Existenz** eines Bruchs
steht bereits als `Proemial.K3CouplingProbe.coupling_fires` in der Sonde und wird hier
nicht nachgebaut. Der Ertrag ist, dass **genau hier** bricht und sonst nicht. -/
theorem dropLast_exchangeAt_last_iff {l : List ℕ} (hl : IsRGS l) {i : ℕ}
    (hi : i < l.length - 1) :
    (exchangeAt i (l.length - 1) l).dropLast = l.dropLast ↔ preservesPrefixPattern l i := by
  have hp : IsRGS l.dropLast := isRGS_dropLast' hl
  have hlen : l.dropLast.length = l.length - 1 := List.length_dropLast
  have hi' : i < l.dropLast.length := by omega
  have hgi : l.dropLast.getD i 0 = l.dropLast[i] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi']; rfl
  rw [exchangeAt, ← relabel_dropLast, dropLast_swapPlaces_last hi,
    relabel_eq_iff_pattern hp (by rw [List.length_set]),
    set_pattern_iff hi', preservesPrefixPattern, hgi]

-- ============================================================
-- §V — Statement-Pin
-- ============================================================

/-! **Statement-Pin für Satz 2.** Er ist eine Charakterisierung; eine Schwächung der
rechten Seite — etwa das Weglassen eines der beiden Konjunkte in (b) — käme durch eine
Axiom-Wache hindurch, weil sie nur das Profil und nicht die Aussage prüft. Der Pin friert
die Aussage ein. -/

-- STATEMENT-PIN
example : ∀ {l : List ℕ}, IsRGS l → ∀ {i : ℕ}, i < l.length - 1 →
    ((exchangeAt i (l.length - 1) l).dropLast = l.dropLast
      ↔ (l.getD (l.length - 1) 0 = l.dropLast.getD i 0
          ∨ (List.count (l.dropLast.getD i 0) l.dropLast = 1
              ∧ l.getD (l.length - 1) 0 ∉ l.dropLast))) :=
  fun {_l} hl {_i} hi => dropLast_exchangeAt_last_iff hl hi

-- ============================================================
-- §VI — Wachen: Axiom-Profile
-- ============================================================

/-! **Wachen.** Ist-Ausgabe des grünen Builds (v4.30.0-rc2), pro Deklaration eingefroren,
Erwartungstexte verbatim aus der Messung.

**Zur Klassik.** Die beiden tragenden Sätze über Listen — `relabel_take` und
`dropLast_exchangeAt` — sind **choice-frei**. `Classical.choice` tritt erst dort auf, wo
über `IsRGS` oder über `List.count` gearbeitet wird; `isRGS_take` erbt es aus
`relabel_eq_self_of_isRGS`, die `count`-Kette aus der Zählmaschinerie. **Der Weg des
Axioms in den Term ist nicht gemessen** (`CLAUDE.md` §8 Fallstrick 10); gemessen ist, welche
Sätze es tragen und welche nicht.

Die beiden `private`-Hilfssätze `set_getElem?_val` und `set_getElem?_none` tragen keine
eigene Wache: ihr Profil ist über die Hülle von `set_pattern_iff` mitgesichert
(`CLAUDE.md` §3). -/

/-- info: 'Reformulation.Kenogram.relabelStep_foldl_append' depends on axioms: [propext] -/
#guard_msgs in #print axioms relabelStep_foldl_append

/-- info: 'Reformulation.Kenogram.relabel_take' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms relabel_take

/-- info: 'Reformulation.Kenogram.relabel_dropLast' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms relabel_dropLast

/-- info: 'Reformulation.Kenogram.isRGS_take' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms isRGS_take

/-- info: 'Reformulation.Kenogram.isRGS_dropLast'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms isRGS_dropLast'

/-- info: 'Reformulation.Kenogram.swapPlaces' depends on axioms: [propext] -/
#guard_msgs in #print axioms swapPlaces

/-- info: 'Reformulation.Kenogram.swapPlaces_length' depends on axioms: [propext] -/
#guard_msgs in #print axioms swapPlaces_length

/-- info: 'Reformulation.Kenogram.exchangeAt' depends on axioms: [propext] -/
#guard_msgs in #print axioms exchangeAt

/-- info: 'Reformulation.Kenogram.dropLast_swapPlaces' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms dropLast_swapPlaces

/-- info: 'Reformulation.Kenogram.dropLast_swapPlaces_last' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms dropLast_swapPlaces_last

/-- info: 'Reformulation.Kenogram.dropLast_exchangeAt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms dropLast_exchangeAt

/-- info: 'Reformulation.Kenogram.count_eq_one_iff_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms count_eq_one_iff_unique

/-- info: 'Reformulation.Kenogram.set_pattern_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms set_pattern_iff

/-- info: 'Reformulation.Kenogram.relabel_eq_iff_pattern' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms relabel_eq_iff_pattern

/-- info: 'Reformulation.Kenogram.preservesPrefixPattern' depends on axioms: [propext] -/
#guard_msgs in #print axioms preservesPrefixPattern

/-- info: 'Reformulation.Kenogram.dropLast_exchangeAt_last_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms dropLast_exchangeAt_last_iff

end Reformulation.Kenogram
