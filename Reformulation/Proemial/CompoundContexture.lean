import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Choose.Basic
import Reformulation.Proemial.ContextureOverlap
import Reformulation.Proemial.IntervalBackbone

/-!
# Proemial.CompoundContexture — die Verbundkontextur als Struktur, nicht als Zahlenreihe

**Ertrag.** `Definitionen.md` §3 führt die Verbundkontextur als *Struktur, die aus
dem transkontexturellen Zusammenschluss mehrerer Elementarkontexturen entsteht und
Vermittlung zwischen diesen realisiert*, mit der Bedingung *sie erfordert mindestens
drei Werte*. Im Korpus stand davon bisher nur die **Arithmetik**: die Dreieckszahl-
Folge, deren Exponent seit dem Wahlvektor-Zug ein Satz ist. Diese Datei macht die
**Zusammenschluss-Seite** satzförmig, über dem Bestandsbegriff
`ContextureOverlap.IsElemContexture` (die Wert-Zweiermenge).

Vier Zielsätze, in zwei Gruppen.

## Die Struktur über der Überlappung

- `two_elem_contextures_iff` — *mehrere* Elementarkontexturen, also überhaupt etwas,
  das zusammengeschlossen werden könnte, gibt es **genau ab drei Werten**. Das ist die
  formale Gestalt von Günthers Begründung der Mindestdreiwertigkeit: bei zwei Werten
  existiert genau **eine** Zweiermenge, und der zweite Wert steht dem ersten
  „unvermittelt gegenüber" — es gibt kein Zwischen.
- `overlap_or_third_touches` — je zwei verschiedene Elementarkontexturen überlappen,
  oder es gibt eine **dritte**, die beide berührt. Ohne Schranke an `m`: sind die
  beiden disjunkt, liegen vier Werte vor, und ein Kreuzpaar existiert.
- `disjoint_elem_contextures_iff` — disjunkte Elementarkontexturen, also der Fall, in
  dem der Zusammenhang **echt** über eine dritte läuft, gibt es **genau ab vier
  Werten**.

## Die zwei Zählfunktionen

`verbundWertzahl`, `guentherZaehlung`, `korpusZaehlung` und

- `zaehlungen_nirgends_gleich` — die beiden Zählungen der Grenznotiz A stimmen an
  **keiner** Stelle überein, und zwar richtungstreu: die Korpuszählung liegt stets
  echt über Günthers Zählung. Bisher stand das dort als Rechnung; jetzt als Satz.

## Deutungsgrenzen — beide markiert, beide bleiben

1. **Dass die Berührungsstruktur Günthers *Vermittlung* ist, ist Deutung.** Günthers
   Vermittlung involviert nach seinem eigenen §3-Kommentar die **zweite Negation**
   (ebenso §11), und die trägt diese Datei **ausdrücklich nicht**. Was hier steht,
   ist: die Elementarkontexturen einer Wertlage hängen über Überlappung zusammen.
   Kein Deklarationsname dieser Datei trägt darum „Vermittlung" oder „Mediation";
   die Namen sagen die Sache — Überlappung, dritte Berührung, Schwelle, Zählung.
2. **Die Zuordnung „Index = Themenzahl" bleibt Deutung**, unverändert wie in
   Grenznotiz A des Ledgers. `verbundWertzahl` definiert **keine** neue Arithmetik,
   sondern konsumiert `IntervalBackbone.intervalStart` mit **ausgeschriebenem
   Index-Versatz** `+2`. Der Grund ist die Rücknahme in L03-2: dieselbe Arithmetik
   trägt bei verschobenem Index die Ontologien-Folge (§18), und sie darf nicht unter
   zwei Paragraphen stehen. Sichtbarer Versatz statt stiller Doppelbelegung.

## Anschluss, in Prosa und nicht als Satz

`disjoint_elem_contextures_iff` gibt `RegimeThreshold.regime_threshold_at_four` seinen
begrifflichen Rahmen: **dieselbe Schwelle `3 → 4`**, dort als Erzeugbarkeitskippe der
gemischten lokal klassischen Operation, hier als der Punkt, ab dem zwei
Elementarkontexturen überhaupt disjunkt sein können. Ein **gemeinsamer Satz wird nicht gebaut** — eine Konjunktion
aus beiden wäre Verpackung ohne Satzgehalt, und der Kopf von `RegimeThreshold` warnt
sinngemäss vor genau dieser Verkonjunktion.

Nachbarschaft, nicht konsumiert: `ChoiceVectors.card_pairs` (die Zahl der
Elementarkontexturen einer Wertlage), `ElementaryCycle.exists_involutive_orb_eq` (die
Zweierbahn-Brücke), `RegimeThreshold.regime_threshold_at_four` (die Schwelle).

## Ein Korrekturvermerk, weil er zur Sache gehört

Die Options-Evaluation, aus der diese Datei hervorging, schrieb, zwei disjunkte
Elementarkontexturen seien „durch **genau eine** dritte" vermittelt. **Die
Eindeutigkeit ist falsch:** für disjunkte `{a,b}`, `{c,d}` berühren alle vier
Kreuzpaare beide Seiten, unabhängig von `m` (gerechnet, ausserhalb des Korpus).
`overlap_or_third_touches` ist darum als **Existenz** gefasst. Die exakte Vier ist
nicht gebaut und hier auch nicht behauptet.

## Aggregat-Reife

Konsumiert `ContextureOverlap` und `IntervalBackbone` — beides Aggregat — sowie
Mathlib. Keine Sonde, keine Setzung.

Kein `sorry`, kein `axiom`, kein `: True`-Feld.
-/

open Finset

namespace Reformulation.Proemial.CompoundContexture

open Reformulation.Proemial.ContextureOverlap
open Reformulation.Proemial.IntervalBackbone

/-! ## Teil 1 — die Struktur über der Überlappung -/

/-- **Mindestdreiwertigkeit als Satz.** Zwei *verschiedene* Elementarkontexturen —
also überhaupt mehrere, die zusammenkommen könnten — existieren genau ab drei Werten.

Die ∃-Form ist gewählt und nicht die `Fintype.card`-Form: sie braucht keine
Zählmaschinerie. Wer die Zahl will, hat sie in `ChoiceVectors.card_pairs`. -/
theorem two_elem_contextures_iff (m : ℕ) :
    (∃ A B : Finset (Fin m), IsElemContexture A ∧ IsElemContexture B ∧ A ≠ B)
      ↔ 3 ≤ m := by
  constructor
  · rintro ⟨A, B, hA, hB, hAB⟩
    -- Aus `A ≠ B` bei gleicher Karte: ein Element von `B` liegt nicht in `A`.
    have hnsub : ¬ B ⊆ A := fun h =>
      hAB (Finset.eq_of_subset_of_card_le h (by rw [hA, hB])).symm
    obtain ⟨b, _, hbA⟩ := Finset.not_subset.mp hnsub
    have hcard : (insert b A).card = 3 := by
      rw [Finset.card_insert_of_notMem hbA, hA]
    have hle : (insert b A).card ≤ m := by
      simpa [Finset.card_univ, Fintype.card_fin] using
        Finset.card_le_card (Finset.subset_univ (insert b A))
    omega
  · intro hm
    refine ⟨{⟨0, by omega⟩, ⟨1, by omega⟩}, {⟨1, by omega⟩, ⟨2, by omega⟩}, ?_, ?_, ?_⟩
    · rw [IsElemContexture, Finset.card_insert_of_notMem (by simp [Fin.ext_iff]),
        Finset.card_singleton]
    · rw [IsElemContexture, Finset.card_insert_of_notMem (by simp [Fin.ext_iff]),
        Finset.card_singleton]
    · intro h
      have h0 : (⟨0, by omega⟩ : Fin m) ∈ ({⟨1, by omega⟩, ⟨2, by omega⟩} : Finset (Fin m)) := by
        rw [← h]; simp
      simp [Fin.ext_iff] at h0

/-- **Der Zusammenhang: überlappend oder über eine dritte.** Je zwei verschiedene
Elementarkontexturen überlappen — oder es gibt eine dritte Elementarkontextur, die
beide berührt.

Als **Existenz** gefasst, nicht als Eindeutigkeit: für disjunkte `{a,b}`, `{c,d}`
berühren alle vier Kreuzpaare beide Seiten. -/
theorem overlap_or_third_touches {m : ℕ} {A B : Finset (Fin m)}
    (hA : IsElemContexture A) (hB : IsElemContexture B) (hAB : A ≠ B) :
    (A ∩ B).Nonempty ∨
      ∃ C : Finset (Fin m), IsElemContexture C ∧ C ≠ A ∧ C ≠ B ∧
        (C ∩ A).Nonempty ∧ (C ∩ B).Nonempty := by
  rcases Finset.eq_empty_or_nonempty (A ∩ B) with hdis | hov
  · right
    obtain ⟨a₁, a₂, ha, rfl⟩ := Finset.card_eq_two.mp hA
    obtain ⟨b₁, b₂, hb, rfl⟩ := Finset.card_eq_two.mp hB
    have hmem : ∀ x ∈ ({a₁, a₂} : Finset (Fin m)),
        x ∉ ({b₁, b₂} : Finset (Fin m)) := by
      intro x hx hx'
      have hx'' : x ∈ ({a₁, a₂} : Finset (Fin m)) ∩ ({b₁, b₂} : Finset (Fin m)) :=
        Finset.mem_inter.mpr ⟨hx, hx'⟩
      rw [hdis] at hx''
      exact Finset.notMem_empty x hx''
    have ha₁b₁ : a₁ ≠ b₁ := by
      intro h; exact hmem a₁ (by simp) (by simp [h])
    refine ⟨{a₁, b₁}, ?_, ?_, ?_, ?_, ?_⟩
    · rw [IsElemContexture, Finset.card_insert_of_notMem (by simpa using ha₁b₁),
        Finset.card_singleton]
    · intro h
      exact hmem b₁ (h ▸ (by simp : b₁ ∈ ({a₁, b₁} : Finset (Fin m)))) (by simp)
    · intro h
      exact hmem a₁ (by simp) (h ▸ (by simp : a₁ ∈ ({a₁, b₁} : Finset (Fin m))))
    · exact ⟨a₁, Finset.mem_inter.mpr ⟨by simp, by simp⟩⟩
    · exact ⟨b₁, Finset.mem_inter.mpr ⟨by simp, by simp⟩⟩
  · exact Or.inl hov

/-- **Die Schwelle.** Disjunkte Elementarkontexturen — der Fall, in dem der
Zusammenhang echt über eine dritte läuft — existieren genau ab vier Werten.

Diese Iff-Fassung enthält als Negat die Aussage, dass bei drei Werten *alle*
Elementarkontexturen paarweise überlappen; das ist die Abzählaussage
`ContextureOverlap.three_contextures_overlap` in allgemeiner Gestalt. -/
theorem disjoint_elem_contextures_iff (m : ℕ) :
    (∃ A B : Finset (Fin m), IsElemContexture A ∧ IsElemContexture B ∧ A ∩ B = ∅)
      ↔ 4 ≤ m := by
  constructor
  · rintro ⟨A, B, hA, hB, hdis⟩
    have hdisj : Disjoint A B := Finset.disjoint_iff_inter_eq_empty.mpr hdis
    have hcard : (A ∪ B).card = 4 := by
      rw [Finset.card_union_of_disjoint hdisj, hA, hB]
    have hle : (A ∪ B).card ≤ m := by
      simpa [Finset.card_univ, Fintype.card_fin] using
        Finset.card_le_card (Finset.subset_univ (A ∪ B))
    omega
  · intro hm
    refine ⟨{⟨0, by omega⟩, ⟨1, by omega⟩}, {⟨2, by omega⟩, ⟨3, by omega⟩}, ?_, ?_, ?_⟩
    · rw [IsElemContexture, Finset.card_insert_of_notMem (by simp [Fin.ext_iff]),
        Finset.card_singleton]
    · rw [IsElemContexture, Finset.card_insert_of_notMem (by simp [Fin.ext_iff]),
        Finset.card_singleton]
    · ext x
      simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton,
        Finset.notMem_empty, iff_false, not_and, Fin.ext_iff]
      omega

/-! ## Teil 2 — die zwei Zählfunktionen (Grenznotiz A) -/

/-- Aufspaltung des nichtlinearen Schritts, damit `omega` greift — dieselbe
Bauform wie `IntervalBackbone.succ_mul_succ_succ` und aus demselben Grund: ohne
sie sind `(k+2)*(k+3)` und `k*k` zwei unverbundene Atome. Kein eigener Posten. -/
private theorem dreieck_split (k : ℕ) :
    (k + 2) * (k + 2 + 1) = 2 * (k + 2) + (k * k + 3 * k + 2) := by
  simp [Nat.add_mul, Nat.mul_add]
  omega

/-- **Wertzahl der `k`-ten Verbundkontextur**, `k = 0` die dreiwertige.

Konsumiert die Ontologien-Arithmetik `IntervalBackbone.intervalStart`; der
Index-Versatz `+2` ist die **Indexbrücke** der Grenznotiz A, hier ausgeschrieben
statt still. Das ist die Form, die die Rücknahme in L03-2 verlangt: dieselbe
Arithmetik darf nicht unter zwei Paragraphen stehen, wohl aber ihr Bild mit
sichtbarem Versatz. -/
def verbundWertzahl (k : ℕ) : ℕ := intervalStart (k + 2)

/-- **Günthers Zählung** (`Definitionen.md` §3: die Anzahl der zusammenkommenden
Elementarkontexturen „beträgt `n`"). -/
def guentherZaehlung (k : ℕ) : ℕ := k + 2

/-- **Korpuszählung**: die Wert-Zweiermengen der `k`-ten Verbundkontextur. -/
def korpusZaehlung (k : ℕ) : ℕ := (verbundWertzahl k).choose 2

/-- Die Wertzahl der `k`-ten Verbundkontextur liegt über Günthers Zählung — das
Zwischenglied der Ungleichung, eigenständig brauchbar. -/
theorem guentherZaehlung_lt_verbundWertzahl (k : ℕ) :
    guentherZaehlung k < verbundWertzahl k := by
  have h := two_mul_intervalStart (k + 2)
  rw [dreieck_split k] at h
  simp only [verbundWertzahl, guentherZaehlung]
  omega

/-- **Die beiden Zählungen stimmen an keiner Stelle überein**, und zwar
richtungstreu: die Korpuszählung liegt stets echt über Günthers Zählung.

Stärker als das „stimmen an keiner Stelle überein" der Grenznotiz A, die die Sache
bisher nur gerechnet führte. -/
theorem zaehlungen_nirgends_gleich (k : ℕ) :
    guentherZaehlung k < korpusZaehlung k := by
  have hv : guentherZaehlung k < verbundWertzahl k :=
    guentherZaehlung_lt_verbundWertzahl k
  have h3 : 3 ≤ verbundWertzahl k := by
    simp only [guentherZaehlung] at hv; omega
  have hch : verbundWertzahl k ≤ korpusZaehlung k := by
    simp only [korpusZaehlung, Nat.choose_two_right]
    rw [Nat.le_div_iff_mul_le (by omega : 0 < 2)]
    exact Nat.mul_le_mul_left _ (by omega)
  omega

/-! ## Teil 3 — Statement-Pins

Ein Pin nagelt den vollen Wortlaut fest: ein geschwächter Satz mit gleichem
Axiomprofil käme durch eine Wache hindurch, aber nicht hier vorbei. Namenlose
`example`s, keine Axiom-Wache. -/

-- STATEMENT-PIN
example (m : ℕ) :
    (∃ A B : Finset (Fin m), IsElemContexture A ∧ IsElemContexture B ∧ A ≠ B)
      ↔ 3 ≤ m := two_elem_contextures_iff m
-- STATEMENT-PIN
example {m : ℕ} {A B : Finset (Fin m)}
    (hA : IsElemContexture A) (hB : IsElemContexture B) (hAB : A ≠ B) :
    (A ∩ B).Nonempty ∨
      ∃ C : Finset (Fin m), IsElemContexture C ∧ C ≠ A ∧ C ≠ B ∧
        (C ∩ A).Nonempty ∧ (C ∩ B).Nonempty := overlap_or_third_touches hA hB hAB
-- STATEMENT-PIN
example (m : ℕ) :
    (∃ A B : Finset (Fin m), IsElemContexture A ∧ IsElemContexture B ∧ A ∩ B = ∅)
      ↔ 4 ≤ m := disjoint_elem_contextures_iff m
-- STATEMENT-PIN
example (k : ℕ) : guentherZaehlung k < korpusZaehlung k := zaehlungen_nirgends_gleich k

/-! ## Teil 4 — die Axiom-Wachen (Ist-gebunden)

Ist-Ausgabe des grünen Builds (v4.30.0-rc2), je Deklaration eingefroren —
**gemessen und nicht erwartet**, und die Erwartung war an beiden Stellen falsch.

Die drei `Finset`-Sätze ziehen **`Classical.choice`**, nicht nur `Quot.sound`.
Gemessen an drei unabhängigen Routen, die alle dasselbe liefern:
`card_le_card ∘ subset_univ`, `card_le_univ` und `card_eq_two`. Das bestätigt den
Vermerk im Kopf von `ContextureOverlap`, dessen konkreter Satz die `Finset`-
Entscheidung eigens meidet und darum `Classical`-frei bleibt: **in der
`Finset`-Gestalt ist Choice in dieser Mathlib-Fassung nicht zu umgehen.**

Die beiden Zählsätze sind **nicht** axiomfrei, sondern erben `[propext,
Quot.sound]` aus `IntervalBackbone.two_mul_intervalStart` — Hüllen-Lehre:
Konsum erbt das Profil der Quelle und unterbietet es nie. -/

/--
info: 'Reformulation.Proemial.CompoundContexture.two_elem_contextures_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms two_elem_contextures_iff

/--
info: 'Reformulation.Proemial.CompoundContexture.overlap_or_third_touches' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms overlap_or_third_touches

/--
info: 'Reformulation.Proemial.CompoundContexture.disjoint_elem_contextures_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms disjoint_elem_contextures_iff

/-- info: 'Reformulation.Proemial.CompoundContexture.guentherZaehlung_lt_verbundWertzahl' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms guentherZaehlung_lt_verbundWertzahl

/-- info: 'Reformulation.Proemial.CompoundContexture.zaehlungen_nirgends_gleich' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms zaehlungen_nirgends_gleich

end Reformulation.Proemial.CompoundContexture
