import Reformulation.Proemial.NonUniformCloneBound

/-!
# Proemial.QuaternaryCloneBound — die Charakterisierung bei m = 4 (Kairos, E2)

**Ertrag.** Der Zielsatz (`locally_classical_in_clone_iff4`) ist die Verschärfung von E1
(`NonUniformCloneBound.four_of_eight_generatable`) auf den vierwertigen Träger:

> Eine lokal-klassische Operation auf `Fin 4` liegt **genau dann** im Klon von
> `{min, max, neg}`, wenn sie `min` oder `max` ist.

Bei `m = 3` waren vier der acht Wahlmuster erzeugbar; hier sind es allein die beiden
Basiselemente selbst — aus der Existenzaussage (E1) wird eine Charakterisierung (E2).
Der Satz ist eine Iff-Aussage, keine Zählung; in Zähl-Form liegt er als Bijektions-Paar
`two_of_sixtyfour_generatable` + `ofC_injective` im Korpus (CLAUDE.md §6), die Zahlen
62/64 selbst stehen in Sonde 17 und bleiben dort.

## Beweismittel: die Invariante `R₄` (Sonde 17, gegengerechnet)

`R₄ = {(0,0), (1,0), (1,1), (1,2), (2,1), (2,2), (2,3), (3,3)}` — begrifflich die
Nachbarschaftsrelation `|a−b| ≤ 1` der linearen Ordnung, an beiden Enden um die
Randpaare `(0,1)` und `(3,2)` gebrochen (`r4_neighbor`). Die Basis erhält `R₄`
(`min_pres`/`max_pres`/`neg_pres`), also erhält jeder Term `R₄` (`r4_is_invariant`,
dieselbe `Term.realize_mem`-Verschaltung wie `rho_is_invariant` — keine eigene
Induktion). Jede gemischte Wahl bricht `R₄` (`mixed_breaks`): **ein** `decide` erledigt
alle gemischten Fälle zugleich — das Beweis-Schema, das Sonde 17 vorhergesagt hat.

**Fallstrick, im Bau beachtet:** in `Fin 4` ist die Subtraktion **modular**; `|a − b| ≤ 1`
darf nicht direkt über `Fin`-Subtraktion geschrieben werden (es wäre eine andere
Relation). `r4B` ist darum die explizite Tafel über `.val`; die begriffliche Lesart
steht als Satz `r4_neighbor` — über `ℕ`-Ungleichungen an `.val`, nicht über `Fin`-`−`.

## Bauform: sechs Bool-Argumente, nicht `Fin 6 → Bool`

Der Wahlvektor `ofC` nimmt **sechs einzelne Bool-Argumente** `c0 … c5`. Die
Funktionsraum-Form `c : Fin 6 → Bool` zöge über die Fintype-Instanz `Classical.choice`
in jedes `decide` (gemessen, nicht geschätzt — dasselbe Muster wie bei `vec_eta`/
`realize_eq_of_pointwise` in E1); die Sechs-Argument-Form hält `mixed_breaks` bei
`[propext]`. **Die Kontextur-Reihenfolge ist festgelegt und darf nicht verändert
werden:** `c0 … c5` gehören zu `{0,1} {0,2} {0,3} {1,2} {1,3} {2,3}`, lexikographisch.
(In Sonde 17 hat genau eine abweichende Reihenfolge einen Fehlbefund erzeugt; die
Reihenfolge gehört darum hierher, nicht in eine Fußnote.)

## Robustheit: die Schranke überlebt Konstanten

`R₄` ist reflexiv (`r4_diag`); darum bleibt `R₄` auch unter der um **alle vier
Konstanten** erweiterten Signatur `Lc` eine Invariante, und die Schranke besteht fort
(`mixed_not_in_constant_clone`). Das ist der Kontrast zu Test 2b in
`TransjunctionCloneBound`: dort **verschwand** die `{0,2}`-Schranke bei Hinzunahme der
`1`-Konstante (`no_substructure_with_const`) — die `R₄`-Schranke hängt nicht am
Konstanten-Verbot der Basis. Dem naheliegendsten Einwand ist damit die Grundlage
genommen.

**Wortlaut-Grenzen (verbindlich):**

1. **Keine Zähl-Behauptung im Korpus.** Der Zielsatz ist ein Iff; die Teilung „genau 2
   von 2^6" liegt als Bijektions-Paar (`two_of_sixtyfour_generatable` +
   `ofC_injective`) im Korpus, alle übrigen Zahlen der Sonde 17 (62 Zeugen, 35
   basis-erhaltene Relationen, Klon-Größe 82) bleiben außerhalb (Wolfram, unabhängig
   in Python gegengerechnet).
2. **Die uniforme Formel `R_m` wird hier nicht behauptet.** Diese Datei baut `R₄` für
   `m = 4`. Dass dieselbe Bauform für `m = 3, 5, 6` trägt, ist gemessen (Sonde 17,
   gegengerechnet) und ist Gegenstand von E3 — nicht dieser Datei.
3. **Keine Vermittlungs-These (Marke 3).** Ob kontextur-relative Operationswahl
   Günthers *Vermittlung* ist, entscheidet auch dieser Bau nicht. Der Dateiname sagt
   `QuaternaryCloneBound`, nicht `Mediation`.
-/

open FirstOrder Language

namespace Reformulation.Proemial.QuaternaryCloneBound

open Reformulation.Proemial.TransjunctionCloneBound
open Reformulation.Proemial.NonUniformCloneBound

/-! ## Teil 1 — die Struktur auf `Fin 4`

Dieselbe Sprache `L` wie in `TransjunctionCloneBound` (Symbole `¬`, `∧`, `∨`), neue
Trägermenge: `∧ = min`, `∨ = max` über dem `LinearOrder` von `Fin 4`, `¬ = negFin4`
(die ordnungsumkehrende Negation `a ↦ 3 − a` über `.val` — nicht über die modulare
`Fin`-Subtraktion). -/

/-- Die ordnungsumkehrende Negation auf `Fin 4` (`0 ↦ 3, 1 ↦ 2, 2 ↦ 1, 3 ↦ 0`),
über `.val` gebaut (die `Fin`-Subtraktion wäre modular). -/
def negFin4 (a : Fin 4) : Fin 4 := ⟨3 - a.val, by omega⟩

/-- Die Interpretation auf `Fin 4`: `∧ = min`, `∨ = max`, `¬ = negFin4` — das
`m = 4`-Gegenstück zu `struc`. -/
instance struc4 : L.Structure (Fin 4) where
  funMap := fun {n} =>
    match n with
    | 1 => fun _ x => negFin4 (x 0)
    | 2 => fun f x => match f with
        | .and => min (x 0) (x 1)
        | .or => max (x 0) (x 1)
    | 0 => fun f _ => nomatch f
    | (_ + 3) => fun f _ => nomatch f
  RelMap := fun r _ => nomatch r

/-! ## Teil 2 — die sechs Elementarkontexturen und die lokalen Prädikate

Die Elementarkontexturen bei `m = 4` sind die sechs Zweierteilmengen von `{0,1,2,3}`.
Prädikate nach der E1-Schablone, `Decidable` per `inferInstanceAs` (die
`Prop`-Definition ist für die Instanz-Synthese opak — Feedback „Decidable bei
Prop-def"). -/

/-- `f` erhält die Elementarkontextur `{x, y}`: Werte aus `{x,y}` führen nie hinaus. -/
def PreservesPair4 (f : Fin 4 → Fin 4 → Fin 4) (x y : Fin 4) : Prop :=
  ∀ a b : Fin 4, (a = x ∨ a = y) → (b = x ∨ b = y) → (f a b = x ∨ f a b = y)

instance (f : Fin 4 → Fin 4 → Fin 4) (x y : Fin 4) : Decidable (PreservesPair4 f x y) :=
  inferInstanceAs (Decidable (∀ a b : Fin 4,
    (a = x ∨ a = y) → (b = x ∨ b = y) → (f a b = x ∨ f a b = y)))

/-- `f` wirkt auf `{x, y}` als Konjunktion: dort ist `f = min`. -/
def ActsAsMin4 (f : Fin 4 → Fin 4 → Fin 4) (x y : Fin 4) : Prop :=
  ∀ a b : Fin 4, (a = x ∨ a = y) → (b = x ∨ b = y) → f a b = min a b

instance (f : Fin 4 → Fin 4 → Fin 4) (x y : Fin 4) : Decidable (ActsAsMin4 f x y) :=
  inferInstanceAs (Decidable (∀ a b : Fin 4,
    (a = x ∨ a = y) → (b = x ∨ b = y) → f a b = min a b))

/-- `f` wirkt auf `{x, y}` als Disjunktion: dort ist `f = max`. -/
def ActsAsMax4 (f : Fin 4 → Fin 4 → Fin 4) (x y : Fin 4) : Prop :=
  ∀ a b : Fin 4, (a = x ∨ a = y) → (b = x ∨ b = y) → f a b = max a b

instance (f : Fin 4 → Fin 4 → Fin 4) (x y : Fin 4) : Decidable (ActsAsMax4 f x y) :=
  inferInstanceAs (Decidable (∀ a b : Fin 4,
    (a = x ∨ a = y) → (b = x ∨ b = y) → f a b = max a b))

/-- Kontexturtreue: `f` erhält alle sechs Elementarkontexturen
(Reihenfolge lexikographisch: `{0,1} {0,2} {0,3} {1,2} {1,3} {2,3}`). -/
def ContextureFaithful4 (f : Fin 4 → Fin 4 → Fin 4) : Prop :=
  PreservesPair4 f 0 1 ∧ PreservesPair4 f 0 2 ∧ PreservesPair4 f 0 3 ∧
    PreservesPair4 f 1 2 ∧ PreservesPair4 f 1 3 ∧ PreservesPair4 f 2 3

instance (f : Fin 4 → Fin 4 → Fin 4) : Decidable (ContextureFaithful4 f) :=
  inferInstanceAs (Decidable (PreservesPair4 f 0 1 ∧ PreservesPair4 f 0 2 ∧
    PreservesPair4 f 0 3 ∧ PreservesPair4 f 1 2 ∧ PreservesPair4 f 1 3 ∧
    PreservesPair4 f 2 3))

/-- Lokale Klassizität: auf jeder der sechs Kontexturen wirkt `f` wie `min` oder wie
`max` (dieselbe lexikographische Reihenfolge wie `ContextureFaithful4`). -/
def LocallyClassical4 (f : Fin 4 → Fin 4 → Fin 4) : Prop :=
  (ActsAsMin4 f 0 1 ∨ ActsAsMax4 f 0 1) ∧ (ActsAsMin4 f 0 2 ∨ ActsAsMax4 f 0 2) ∧
    (ActsAsMin4 f 0 3 ∨ ActsAsMax4 f 0 3) ∧ (ActsAsMin4 f 1 2 ∨ ActsAsMax4 f 1 2) ∧
    (ActsAsMin4 f 1 3 ∨ ActsAsMax4 f 1 3) ∧ (ActsAsMin4 f 2 3 ∨ ActsAsMax4 f 2 3)

instance (f : Fin 4 → Fin 4 → Fin 4) : Decidable (LocallyClassical4 f) :=
  inferInstanceAs (Decidable ((ActsAsMin4 f 0 1 ∨ ActsAsMax4 f 0 1) ∧
    (ActsAsMin4 f 0 2 ∨ ActsAsMax4 f 0 2) ∧ (ActsAsMin4 f 0 3 ∨ ActsAsMax4 f 0 3) ∧
    (ActsAsMin4 f 1 2 ∨ ActsAsMax4 f 1 2) ∧ (ActsAsMin4 f 1 3 ∨ ActsAsMax4 f 1 3) ∧
    (ActsAsMin4 f 2 3 ∨ ActsAsMax4 f 2 3)))

/-! ## Teil 3 — der Wahlvektor und der Struktursatz

Der Struktursatz der Sonde 16/17 für `m = 4`: eine lokal-klassische Operation ist
genau ein Wahlvektor `ofC c0 … c5` (`true` = Disjunktion, `false` = Konjunktion).
Zusammen mit `ofC_injective` liegt die Zählung „genau `2^6`" als Bijektions-Paar im
Korpus. **Bauform-Entscheid:** sechs Bool-Argumente statt `Fin 6 → Bool` — die
Fintype-Instanz über dem Funktionsraum zöge `Classical.choice` (gemessen). -/

/-- Der Wahlvektor als Operation. **Kontextur-Reihenfolge lexikographisch und
verbindlich:** `c0 ↦ {0,1}`, `c1 ↦ {0,2}`, `c2 ↦ {0,3}`, `c3 ↦ {1,2}`, `c4 ↦ {1,3}`,
`c5 ↦ {2,3}` (`true` = `max`, `false` = `min`); die Diagonale ist unter beiden Wahlen
dieselbe. Jeder Punkt `(a,b)` mit `a ≠ b` liegt in genau einer Kontextur. -/
def ofC (c0 c1 c2 c3 c4 c5 : Bool) (a b : Fin 4) : Fin 4 :=
  if a = b then a else
  match a.val, b.val with
  | 0, 1 | 1, 0 => if c0 then max a b else min a b
  | 0, 2 | 2, 0 => if c1 then max a b else min a b
  | 0, 3 | 3, 0 => if c2 then max a b else min a b
  | 1, 2 | 2, 1 => if c3 then max a b else min a b
  | 1, 3 | 3, 1 => if c4 then max a b else min a b
  | _, _        => if c5 then max a b else min a b

/-- **Jeder Wahlvektor ist lokal klassisch** (die eine Richtung des Struktursatzes). -/
theorem ofC_locally_classical : ∀ c0 c1 c2 c3 c4 c5 : Bool,
    LocallyClassical4 (ofC c0 c1 c2 c3 c4 c5) := by decide

/-- **Die Wahlvektoren sind paarweise verschieden** (Injektivität; die zweite Hälfte
der Zählung). Über sechs Auswertungspunkte — je einer pro Kontextur — statt über
Funktionsraum-`decide` (das zöge `Classical.choice`). -/
theorem ofC_injective :
    ∀ c0 c1 c2 c3 c4 c5 d0 d1 d2 d3 d4 d5 : Bool,
      ofC c0 c1 c2 c3 c4 c5 = ofC d0 d1 d2 d3 d4 d5 →
      c0 = d0 ∧ c1 = d1 ∧ c2 = d2 ∧ c3 = d3 ∧ c4 = d4 ∧ c5 = d5 := by
  intro c0 c1 c2 c3 c4 c5 d0 d1 d2 d3 d4 d5 h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  -- Pro Koordinate: Auswertung am Kontextur-Punkt; die Mischfälle sind per defeq
  -- (`show`) auf einen konkreten `Fin`-Widerspruch reduziert — kein `decide` über
  -- freien Rest-Bools (Frei-Variablen-Sperre) und kein 4096-Kombo-`+revert` (whnf-
  -- Timeout, gemessen).
  · have h01 := congrFun (congrFun h 0) 1
    cases c0 <;> cases d0
    · rfl
    · exact absurd (show (0 : Fin 4) = 1 from h01) (by decide)
    · exact absurd (show (1 : Fin 4) = 0 from h01) (by decide)
    · rfl
  · have h02 := congrFun (congrFun h 0) 2
    cases c1 <;> cases d1
    · rfl
    · exact absurd (show (0 : Fin 4) = 2 from h02) (by decide)
    · exact absurd (show (2 : Fin 4) = 0 from h02) (by decide)
    · rfl
  · have h03 := congrFun (congrFun h 0) 3
    cases c2 <;> cases d2
    · rfl
    · exact absurd (show (0 : Fin 4) = 3 from h03) (by decide)
    · exact absurd (show (3 : Fin 4) = 0 from h03) (by decide)
    · rfl
  · have h12 := congrFun (congrFun h 1) 2
    cases c3 <;> cases d3
    · rfl
    · exact absurd (show (1 : Fin 4) = 2 from h12) (by decide)
    · exact absurd (show (2 : Fin 4) = 1 from h12) (by decide)
    · rfl
  · have h13 := congrFun (congrFun h 1) 3
    cases c4 <;> cases d4
    · rfl
    · exact absurd (show (1 : Fin 4) = 3 from h13) (by decide)
    · exact absurd (show (3 : Fin 4) = 1 from h13) (by decide)
    · rfl
  · have h23 := congrFun (congrFun h 2) 3
    cases c5 <;> cases d5
    · rfl
    · exact absurd (show (2 : Fin 4) = 3 from h23) (by decide)
    · exact absurd (show (3 : Fin 4) = 2 from h23) (by decide)
    · rfl

/-- **Jede lokal-klassische Operation ist ein Wahlvektor** (die andere Richtung, die
Rekonstruktion — der aufwendigste Teil, weil über beliebige `f` quantifiziert und darum
nicht `decide`-bar): aus den sechs lokalen Wahlen wird der Vektor abgelesen, die
Gleichheit punktweise über die sechs `ActsAs`-Hypothesen geschlossen (E1-Beweismuster,
`locally_classical_reconstruct`). -/
theorem locally_classical_reconstruct4 (f : Fin 4 → Fin 4 → Fin 4)
    (h : LocallyClassical4 f) :
    ∃ c0 c1 c2 c3 c4 c5 : Bool, f = ofC c0 c1 c2 c3 c4 c5 := by
  obtain ⟨h01, h02, h03, h12, h13, h23⟩ := h
  have H0 : ∃ c : Bool, ∀ a b : Fin 4, (a = 0 ∨ a = 1) → (b = 0 ∨ b = 1) →
      f a b = cond c (max a b) (min a b) :=
    h01.elim (fun hm => ⟨false, hm⟩) (fun hM => ⟨true, hM⟩)
  have H1 : ∃ c : Bool, ∀ a b : Fin 4, (a = 0 ∨ a = 2) → (b = 0 ∨ b = 2) →
      f a b = cond c (max a b) (min a b) :=
    h02.elim (fun hm => ⟨false, hm⟩) (fun hM => ⟨true, hM⟩)
  have H2 : ∃ c : Bool, ∀ a b : Fin 4, (a = 0 ∨ a = 3) → (b = 0 ∨ b = 3) →
      f a b = cond c (max a b) (min a b) :=
    h03.elim (fun hm => ⟨false, hm⟩) (fun hM => ⟨true, hM⟩)
  have H3 : ∃ c : Bool, ∀ a b : Fin 4, (a = 1 ∨ a = 2) → (b = 1 ∨ b = 2) →
      f a b = cond c (max a b) (min a b) :=
    h12.elim (fun hm => ⟨false, hm⟩) (fun hM => ⟨true, hM⟩)
  have H4 : ∃ c : Bool, ∀ a b : Fin 4, (a = 1 ∨ a = 3) → (b = 1 ∨ b = 3) →
      f a b = cond c (max a b) (min a b) :=
    h13.elim (fun hm => ⟨false, hm⟩) (fun hM => ⟨true, hM⟩)
  have H5 : ∃ c : Bool, ∀ a b : Fin 4, (a = 2 ∨ a = 3) → (b = 2 ∨ b = 3) →
      f a b = cond c (max a b) (min a b) :=
    h23.elim (fun hm => ⟨false, hm⟩) (fun hM => ⟨true, hM⟩)
  obtain ⟨c0, H0⟩ := H0
  obtain ⟨c1, H1⟩ := H1
  obtain ⟨c2, H2⟩ := H2
  obtain ⟨c3, H3⟩ := H3
  obtain ⟨c4, H4⟩ := H4
  obtain ⟨c5, H5⟩ := H5
  refine ⟨c0, c1, c2, c3, c4, c5, ?_⟩
  -- Abdeckung: jeder Punkt liegt in einer der sechs Kontexturen (Classical-frei, kein
  -- `fin_cases` — das zöge über die Fintype-Maschinerie `Classical.choice`).
  have hcov : ∀ a b : Fin 4,
      ((a = 0 ∨ a = 1) ∧ (b = 0 ∨ b = 1)) ∨ ((a = 0 ∨ a = 2) ∧ (b = 0 ∨ b = 2)) ∨
        ((a = 0 ∨ a = 3) ∧ (b = 0 ∨ b = 3)) ∨ ((a = 1 ∨ a = 2) ∧ (b = 1 ∨ b = 2)) ∨
        ((a = 1 ∨ a = 3) ∧ (b = 1 ∨ b = 3)) ∨ ((a = 2 ∨ a = 3) ∧ (b = 2 ∨ b = 3)) := by
    decide
  funext a b
  rcases hcov a b with ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩
  -- Nach dem `rw` ist das Ziel `f`-frei; `clear` kappt die `f`-Abhängigkeiten, damit
  -- `decide +revert` nur die sechs Bools revertiert (sonst kaskadiert die Revertierung
  -- über die `H`-Hypothesen bis `f` und das Ziel wird unentscheidbar — gemessen).
  · rw [H0 a b ha hb]
    clear H0 H1 H2 H3 H4 H5 hcov h01 h02 h03 h12 h13 h23 f
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> decide +revert
  · rw [H1 a b ha hb]
    clear H0 H1 H2 H3 H4 H5 hcov h01 h02 h03 h12 h13 h23 f
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> decide +revert
  · rw [H2 a b ha hb]
    clear H0 H1 H2 H3 H4 H5 hcov h01 h02 h03 h12 h13 h23 f
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> decide +revert
  · rw [H3 a b ha hb]
    clear H0 H1 H2 H3 H4 H5 hcov h01 h02 h03 h12 h13 h23 f
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> decide +revert
  · rw [H4 a b ha hb]
    clear H0 H1 H2 H3 H4 H5 hcov h01 h02 h03 h12 h13 h23 f
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> decide +revert
  · rw [H5 a b ha hb]
    clear H0 H1 H2 H3 H4 H5 hcov h01 h02 h03 h12 h13 h23 f
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> decide +revert

/-- **Der Struktursatz (m = 4).** Lokal klassisch ⟺ Wahlvektor. Mit `ofC_injective`
zusammen: es gibt *genau* `2^6` lokal-klassische Operationen — die Zählung der
Sonde 17 im Korpus, in Bijektions-Form. -/
theorem locally_classical_iff4 (f : Fin 4 → Fin 4 → Fin 4) :
    LocallyClassical4 f ↔ ∃ c0 c1 c2 c3 c4 c5 : Bool, f = ofC c0 c1 c2 c3 c4 c5 := by
  constructor
  · exact locally_classical_reconstruct4 f
  · rintro ⟨c0, c1, c2, c3, c4, c5, rfl⟩
    exact ofC_locally_classical c0 c1 c2 c3 c4 c5

/-- **Lokale Klassizität erzwingt Kontexturtreue** — wie bei `m = 3` ist die zweite
Vorbedingung der Sonde aus der ersten ableitbar; die Klasse ist durch lokale
Klassizität allein bestimmt. -/
theorem locally_classical_faithful4 (f : Fin 4 → Fin 4 → Fin 4)
    (h : LocallyClassical4 f) : ContextureFaithful4 f := by
  obtain ⟨c0, c1, c2, c3, c4, c5, rfl⟩ := locally_classical_reconstruct4 f h
  revert c0 c1 c2 c3 c4 c5
  decide

/-- **Der Null-Vektor ist `min`.** -/
theorem all_false_is_min :
    ofC false false false false false false = fun a b => min a b := by
  funext a b; revert a b; decide

/-- **Der Eins-Vektor ist `max`.** -/
theorem all_true_is_max :
    ofC true true true true true true = fun a b => max a b := by
  funext a b; revert a b; decide

/-! ## Teil 4 — die Invariante `R₄` und ihre Klon-Invarianz

Nach der `rhoB`/`Rho`-Schablone Bool-getragen. Die Klon-Ebene (`r4_is_invariant`) ist
dieselbe Verschaltung wie `rho_is_invariant`: `R₄` als Substruktur des Produkts
(`r4Sub`, über einer komponentenweisen Produkt-Struktur), `Term.realize_mem` hält die
Paar-Realisierung darin, `fstHom4`/`sndHom4` zerlegen sie — keine eigene
Term-Induktion. -/

/-- Die Invariante `R₄` als Bool-Träger: die explizite Tafel der acht Paare
`{(0,0), (1,0), (1,1), (1,2), (2,1), (2,2), (2,3), (3,3)}`. **Bewusst als Tafel über
`.val`, nicht als `|a − b| ≤ 1`-Formel** — die `Fin`-Subtraktion ist modular und ergäbe
eine andere Relation; die begriffliche Lesart steht in `r4_neighbor`. -/
def r4B (x y : Fin 4) : Bool :=
  (x.val == 0 && y.val == 0) ||
  (x.val == 1 && (y.val == 0 || y.val == 1 || y.val == 2)) ||
  (x.val == 2 && (y.val == 1 || y.val == 2 || y.val == 3)) ||
  (x.val == 3 && y.val == 3)

/-- `R₄(x, y)` — Nachbarschaft in der linearen Ordnung, an beiden Enden gebrochen. -/
def R4 (x y : Fin 4) : Prop := r4B x y = true

/-- `R4` ist entscheidbar (defeq zur Bool-Gleichheit); trägt alle `by decide`-Sätze. -/
instance instDecidableR4 (x y : Fin 4) : Decidable (R4 x y) :=
  inferInstanceAs (Decidable (r4B x y = true))

/-- **Die Lesart von `R₄`, bewiesen statt behauptet:** `R₄` ist die
Nachbarschaftsrelation `|x − y| ≤ 1` der linearen Ordnung **ohne** die beiden
Randpaare `(0,1)` und `(3,2)` — formuliert über `ℕ`-Ungleichungen an `.val` (nicht
über die modulare `Fin`-Subtraktion). Die Brechung der Ränder erzeugt die Asymmetrie,
an der eine kontextur-uneinheitliche Wahl scheitert. -/
theorem r4_neighbor : ∀ x y : Fin 4,
    R4 x y ↔ ((x.val ≤ y.val + 1 ∧ y.val ≤ x.val + 1) ∧
      ¬(x.val = 0 ∧ y.val = 1) ∧ ¬(x.val = 3 ∧ y.val = 2)) := by decide

/-- **`R₄` ist echt (Nichttrivialitäts-Beleg):** weder leer (`R₄ 1 0`) noch die
Allrelation — und die zwei fehlenden Paare sind genau die gebrochenen Ränder
(`¬ R₄ 0 1`, `¬ R₄ 3 2`), nicht etwa Fern-Paare allein. Ohne diesen Beleg wäre jede
Erhaltungs-Aussage über `R₄` wertlos. -/
theorem r4_proper : R4 1 0 ∧ ¬ R4 0 1 ∧ ¬ R4 3 2 ∧ ¬ R4 0 2 := by decide

/-- **`R₄` ist reflexiv:** die Diagonale liegt ganz in `R₄`. Der Träger der
Robustheit (Teil 6): Konstanten können `R₄` nicht brechen. -/
theorem r4_diag : ∀ a : Fin 4, R4 a a := by decide

/-- `f` erhält `R₄` (das binäre Erhaltungs-Prädikat). `abbrev` statt `def` ist
notwendig: bei `def` findet die Instanzensuche die `Decidable`-Instanz nicht
(gemessen: Fehlschlag). -/
abbrev PreservesR4 (f : Fin 4 → Fin 4 → Fin 4) : Prop :=
  ∀ x y u v : Fin 4, R4 x y → R4 u v → R4 (f x u) (f y v)

/-- **`min` (`∧`) erhält `R₄`.** -/
theorem min_pres : PreservesR4 (fun a b => min a b) := by decide

/-- **`max` (`∨`) erhält `R₄`.** -/
theorem max_pres : PreservesR4 (fun a b => max a b) := by decide

/-- **`negFin4` (`¬`) erhält `R₄`.** -/
theorem neg_pres : ∀ a c : Fin 4, R4 a c → R4 (negFin4 a) (negFin4 c) := by decide

/-- Die komponentenweise Produkt-Struktur auf `Fin 4 × Fin 4`, nach der
`prodStruc`-Schablone (generisch statt symbolweise, damit die Projektions-`map_fun'`
definitional durchgehen). -/
instance prodStruc4 : L.Structure (Fin 4 × Fin 4) where
  funMap := fun {_n} f x =>
    (Structure.funMap f (fun i => (x i).1), Structure.funMap f (fun i => (x i).2))
  RelMap r _ := nomatch r

/-- Die Invariante `R₄` als Substruktur des Produkts `Fin 4 × Fin 4` (Träger
`{p | R4 p.1 p.2}`), nach der `rhoSub`-Schablone. Die `fun_mem`-Verpflichtung ist
wörtlich `min_pres`/`max_pres`/`neg_pres`. -/
def r4Sub : L.Substructure (Fin 4 × Fin 4) where
  carrier := {p | R4 p.1 p.2}
  fun_mem := by
    intro n f
    match n, f with
    | 1, .neg =>
        intro x hx
        exact neg_pres (x 0).1 (x 0).2 (hx 0)
    | 2, .and =>
        intro x hx
        exact min_pres (x 0).1 (x 0).2 (x 1).1 (x 1).2 (hx 0) (hx 1)
    | 2, .or =>
        intro x hx
        exact max_pres (x 0).1 (x 0).2 (x 1).1 (x 1).2 (hx 0) (hx 1)

/-- Die erste Projektion `Fin 4 × Fin 4 → Fin 4` als `L`-Homomorphismus (`map_fun'`
definitional bei komponentenweiser Produkt-Struktur). -/
def fstHom4 : (Fin 4 × Fin 4) →[L] (Fin 4) where
  toFun := Prod.fst
  map_fun' := fun _ _ => rfl
  map_rel' := fun r => nomatch r

/-- Die zweite Projektion `Fin 4 × Fin 4 → Fin 4` als `L`-Homomorphismus. -/
def sndHom4 : (Fin 4 × Fin 4) →[L] (Fin 4) where
  toFun := Prod.snd
  map_fun' := fun _ _ => rfl
  map_rel' := fun r => nomatch r

/-- **Jeder Term erhält `R₄` (Klon-Ebene).** Stimmen zwei Belegungen `v`, `w`
argumentweise in `R₄` überein, so auch die Realisierungen jedes Terms. Dieselbe
Verschaltung wie `rho_is_invariant`: `Term.realize_mem` hält das Paar in `r4Sub`,
`HomClass.realize_term` zerlegt über `fstHom4`/`sndHom4` — keine eigene Induktion. -/
theorem r4_is_invariant (t : L.Term (Fin 2)) (v w : Fin 2 → Fin 4)
    (h : ∀ i, R4 (v i) (w i)) : R4 (t.realize v) (t.realize w) := by
  have hmem : t.realize (fun i => (v i, w i)) ∈ r4Sub :=
    Term.realize_mem t (fun i => (v i, w i)) (fun i =>
      show (v i, w i) ∈ ({p | R4 p.1 p.2} : Set (Fin 4 × Fin 4)) from h i)
  have hmem' : R4 (t.realize (fun i => (v i, w i))).1
      (t.realize (fun i => (v i, w i))).2 := hmem
  have hv : t.realize v = (t.realize (fun i => (v i, w i))).1 :=
    HomClass.realize_term fstHom4 (t := t) (v := fun i => (v i, w i))
  have hw : t.realize w = (t.realize (fun i => (v i, w i))).2 :=
    HomClass.realize_term sndHom4 (t := t) (v := fun i => (v i, w i))
  rw [hv, hw]; exact hmem'

/-! ## Teil 5 — die Schranke und der Zielsatz

`mixed_breaks` ist der Kern: **alle** gemischten Wahlvektoren brechen `R₄`, in einem
`decide` — kein Einzelbeweis pro Zeuge (das Beweis-Schema statt der 62 Einzelfälle,
Sonde 17 §6). Zusammen mit der Klon-Invarianz (`r4_is_invariant` via
`in_clone_preservesR4`) liegt keine gemischte Wahl im Klon; die Gegenrichtung sind
die beiden expliziten Terme `x ∧ y` und `x ∨ y`. -/

/-- **Jede erzeugbare Operation erhält `R₄`** — die Konsum-Form der Klon-Invarianz:
liegt `f` im Klon (realisiert ein Term `t` die Operation `f`), so erbt `f` die
Erhaltung von den Belegungs-Paaren `![x,u]`, `![y,v]`. -/
theorem in_clone_preservesR4 (f : Fin 4 → Fin 4 → Fin 4)
    (h : ∃ t : L.Term (Fin 2), ∀ v : Fin 2 → Fin 4, t.realize v = f (v 0) (v 1)) :
    PreservesR4 f := by
  obtain ⟨t, ht⟩ := h
  intro x y u v hxy huv
  have hinv : R4 (t.realize ![x, u]) (t.realize ![y, v]) :=
    r4_is_invariant t ![x, u] ![y, v] (fun i =>
      Fin.cases hxy (fun j => Fin.cases huv (fun k => k.elim0) j) i)
  rw [ht (![x, u]), ht (![y, v])] at hinv
  exact hinv

/-- **Der Kern von E2: jede gemischte Wahl bricht `R₄`.** Ein Wahlvektor, der weder
der Null-Vektor (`min`) noch der Eins-Vektor (`max`) ist, erhält `R₄` nicht — alle
gemischten Fälle in **einem** `decide`, ohne `Classical.choice` (Sechs-Argument-
Bauform; die `Fin 6 → Bool`-Form zöge es über die Fintype-Instanz). -/
theorem mixed_breaks : ∀ c0 c1 c2 c3 c4 c5 : Bool,
    (c0 || c1 || c2 || c3 || c4 || c5) = true →
    (c0 && c1 && c2 && c3 && c4 && c5) = false →
    ¬ PreservesR4 (ofC c0 c1 c2 c3 c4 c5) := by decide

/-- **Keine gemischte Wahl liegt im Klon** — `mixed_breaks` durch die Klon-Invarianz
gezogen: die Schranke für alle Zeugen zugleich, ohne Einzelbeweis pro Zeuge. -/
theorem mixed_not_in_clone : ∀ c0 c1 c2 c3 c4 c5 : Bool,
    (c0 || c1 || c2 || c3 || c4 || c5) = true →
    (c0 && c1 && c2 && c3 && c4 && c5) = false →
    ¬ ∃ t : L.Term (Fin 2), ∀ v : Fin 2 → Fin 4,
        t.realize v = ofC c0 c1 c2 c3 c4 c5 (v 0) (v 1) := by
  intro c0 c1 c2 c3 c4 c5 h1 h2 ht
  exact mixed_breaks c0 c1 c2 c3 c4 c5 h1 h2 (in_clone_preservesR4 _ ht)

/-- Eta-Gesetz für Zweier-Belegungen nach `Fin 4` — per `Fin.cases`, nicht per
`fin_cases`/`decide` über dem Funktionsraum (das zöge `Classical.choice`). -/
lemma vec_eta4 (v : Fin 2 → Fin 4) : v = ![v 0, v 1] := by
  funext i
  exact Fin.cases rfl (fun j => Fin.cases rfl (fun k => k.elim0) j) i

/-- Brücke von der punktweisen zur Belegungs-Form: genügt die Realisierung an allen
Paar-Belegungen `![a, b]`, so an jeder Belegung. Hält die `in_clone`-Beweise beim
punktweisen `decide` (16 Fälle) statt beim Funktionsraum-`decide`. -/
lemma realize_eq_of_pointwise4 (t : L.Term (Fin 2)) (g : Fin 4 → Fin 4 → Fin 4)
    (h : ∀ a b : Fin 4, t.realize ![a, b] = g a b) (v : Fin 2 → Fin 4) :
    t.realize v = g (v 0) (v 1) := by
  conv_lhs => rw [vec_eta4 v]
  exact h (v 0) (v 1)

/-- **`min` ist erzeugbar:** der Term `x ∧ y`. -/
theorem min_in_clone4 :
    ∃ t : L.Term (Fin 2), ∀ v : Fin 2 → Fin 4, t.realize v = min (v 0) (v 1) :=
  ⟨tand varX varY, realize_eq_of_pointwise4 _ _ (by decide)⟩

/-- **`max` ist erzeugbar:** der Term `x ∨ y`. -/
theorem max_in_clone4 :
    ∃ t : L.Term (Fin 2), ∀ v : Fin 2 → Fin 4, t.realize v = max (v 0) (v 1) :=
  ⟨tor varX varY, realize_eq_of_pointwise4 _ _ (by decide)⟩

/-- **Der Null-Vektor ist erzeugbar** (Tafel-Gleichheit gegen den Wahlvektor). -/
theorem ofC_min_in_clone :
    ∃ t : L.Term (Fin 2), ∀ v : Fin 2 → Fin 4,
      t.realize v = ofC false false false false false false (v 0) (v 1) :=
  ⟨tand varX varY, realize_eq_of_pointwise4 _ _ (by decide)⟩

/-- **Der Eins-Vektor ist erzeugbar.** -/
theorem ofC_max_in_clone :
    ∃ t : L.Term (Fin 2), ∀ v : Fin 2 → Fin 4,
      t.realize v = ofC true true true true true true (v 0) (v 1) :=
  ⟨tor varX varY, realize_eq_of_pointwise4 _ _ (by decide)⟩

/-- **Die Wahlvektor-Fassung der Charakterisierung.** Ein Wahlvektor ist genau dann
erzeugbar, wenn er der Null-Vektor oder der Eins-Vektor ist — das `m = 4`-Gegenstück
zu `four_of_eight_generatable`, mit `ofC_injective` die Teilung „genau 2 von `2^6`"
in Bijektions-Form. Die Hinrichtung ist **ein** Beweismittel (`mixed_breaks` über
`R₄`), keine 62 Einzelbeweise. -/
theorem two_of_sixtyfour_generatable :
    ∀ c0 c1 c2 c3 c4 c5 : Bool,
      (∃ t : L.Term (Fin 2), ∀ v : Fin 2 → Fin 4,
          t.realize v = ofC c0 c1 c2 c3 c4 c5 (v 0) (v 1))
        ↔ ((c0 && c1 && c2 && c3 && c4 && c5) = true
            ∨ (c0 || c1 || c2 || c3 || c4 || c5) = false) := by
  intro c0 c1 c2 c3 c4 c5
  constructor
  · intro hf
    have hpres := in_clone_preservesR4 _ hf
    cases c0 <;> cases c1 <;> cases c2 <;> cases c3 <;> cases c4 <;> cases c5 <;>
      first
        | exact Or.inl rfl
        | exact Or.inr rfl
        | exact absurd hpres (mixed_breaks _ _ _ _ _ _ rfl rfl)
  · intro h
    cases c0 <;> cases c1 <;> cases c2 <;> cases c3 <;> cases c4 <;> cases c5 <;>
      first
        | exact ofC_min_in_clone
        | exact ofC_max_in_clone
        | (rcases h with h | h <;> exact absurd h (by decide))

/-- **Der Zielsatz (E2): die Charakterisierung bei m = 4.** Eine lokal-klassische
Operation auf `Fin 4` liegt **genau dann** im Klon von `{min, max, neg}`, wenn sie
`min` oder `max` ist. (Kontexturtreue ist nach `locally_classical_faithful4` in der
lokalen Klassizität enthalten.) Die Verschärfung von E1: bei `m = 3` waren vier der
acht Wahlmuster erzeugbar, hier allein die beiden Basiselemente — aus der
Existenzaussage wird eine Charakterisierung. -/
theorem locally_classical_in_clone_iff4 (f : Fin 4 → Fin 4 → Fin 4)
    (h : LocallyClassical4 f) :
    (∃ t : L.Term (Fin 2), ∀ v : Fin 2 → Fin 4, t.realize v = f (v 0) (v 1))
      ↔ ((f = fun a b => min a b) ∨ (f = fun a b => max a b)) := by
  constructor
  · intro hf
    obtain ⟨c0, c1, c2, c3, c4, c5, rfl⟩ := locally_classical_reconstruct4 f h
    have hpres := in_clone_preservesR4 _ hf
    cases c0 <;> cases c1 <;> cases c2 <;> cases c3 <;> cases c4 <;> cases c5 <;>
      first
        | exact Or.inl all_false_is_min
        | exact Or.inr all_true_is_max
        | exact absurd hpres (mixed_breaks _ _ _ _ _ _ rfl rfl)
  · rintro (rfl | rfl)
    · exact min_in_clone4
    · exact max_in_clone4

/-! ## Teil 6 — Robustheit: die Schranke überlebt Konstanten

In `TransjunctionCloneBound` (Test 2b) **verschwand** die `{0,2}`-Schranke, sobald die
`1`-Konstante zur Basis trat (`no_substructure_with_const`) — sie hing am
Konstanten-Verbot. Die `R₄`-Schranke ist von anderer Art: `R₄` ist **reflexiv**
(`r4_diag`), also erhält jede Konstante `R₄`, und die Schranke besteht auch über der
um **alle vier** Konstanten erweiterten Sprache `Lc` fort. Der naheliegendste Einwand
(„die Charakterisierung ist ein Artefakt der konstantenfreien Signatur") ist damit
grundlos. Bauweise: Kopie der Teil-4-Verschaltung mit einem zusätzlichen
`fun_mem`-Fall für die Konstanten. -/

/-- Die um alle vier Konstanten erweiterte Sprache (`Functions 0 = Fin 4`). -/
def Lc : Language where
  Functions := fun
    | 0 => Fin 4
    | 1 => UnaryFun
    | 2 => BinaryFun
    | _ => Empty
  Relations := fun _ => Empty

/-- Interpretation für `Lc`: wie `struc4`, plus jede Konstante `k ↦ k`. -/
instance strucC : Lc.Structure (Fin 4) where
  funMap := fun {n} =>
    match n with
    | 0 => fun k _ => k
    | 1 => fun _ x => negFin4 (x 0)
    | 2 => fun f x => match f with
        | .and => min (x 0) (x 1)
        | .or => max (x 0) (x 1)
    | (_ + 3) => fun f _ => nomatch f
  RelMap := fun r _ => nomatch r

/-- Die komponentenweise Produkt-Struktur auf `Fin 4 × Fin 4` über `Lc`. -/
instance prodStrucC : Lc.Structure (Fin 4 × Fin 4) where
  funMap := fun {_n} f x =>
    (Structure.funMap f (fun i => (x i).1), Structure.funMap f (fun i => (x i).2))
  RelMap r _ := nomatch r

/-- `R₄` als Substruktur des Produkts über `Lc`: der Konstanten-Fall ist genau die
Reflexivität `r4_diag` — jede Konstante realisiert das Diagonal-Paar `(k, k) ∈ R₄`. -/
def r4SubC : Lc.Substructure (Fin 4 × Fin 4) where
  carrier := {p | R4 p.1 p.2}
  fun_mem := by
    intro n f
    match n, f with
    | 0, k =>
        intro _ _
        exact r4_diag k
    | 1, .neg =>
        intro x hx
        exact neg_pres (x 0).1 (x 0).2 (hx 0)
    | 2, .and =>
        intro x hx
        exact min_pres (x 0).1 (x 0).2 (x 1).1 (x 1).2 (hx 0) (hx 1)
    | 2, .or =>
        intro x hx
        exact max_pres (x 0).1 (x 0).2 (x 1).1 (x 1).2 (hx 0) (hx 1)

/-- Die erste Projektion als `Lc`-Homomorphismus. -/
def fstHomC : (Fin 4 × Fin 4) →[Lc] (Fin 4) where
  toFun := Prod.fst
  map_fun' := fun _ _ => rfl
  map_rel' := fun r => nomatch r

/-- Die zweite Projektion als `Lc`-Homomorphismus. -/
def sndHomC : (Fin 4 × Fin 4) →[Lc] (Fin 4) where
  toFun := Prod.snd
  map_fun' := fun _ _ => rfl
  map_rel' := fun r => nomatch r

/-- **Jeder `Lc`-Term erhält `R₄`** — die Klon-Invarianz überlebt die Konstanten
(Verschaltung wie `r4_is_invariant`, mit `r4SubC`). -/
theorem r4_is_invariantC (t : Lc.Term (Fin 2)) (v w : Fin 2 → Fin 4)
    (h : ∀ i, R4 (v i) (w i)) : R4 (t.realize v) (t.realize w) := by
  have hmem : t.realize (fun i => (v i, w i)) ∈ r4SubC :=
    Term.realize_mem t (fun i => (v i, w i)) (fun i =>
      show (v i, w i) ∈ ({p | R4 p.1 p.2} : Set (Fin 4 × Fin 4)) from h i)
  have hmem' : R4 (t.realize (fun i => (v i, w i))).1
      (t.realize (fun i => (v i, w i))).2 := hmem
  have hv : t.realize v = (t.realize (fun i => (v i, w i))).1 :=
    HomClass.realize_term fstHomC (t := t) (v := fun i => (v i, w i))
  have hw : t.realize w = (t.realize (fun i => (v i, w i))).2 :=
    HomClass.realize_term sndHomC (t := t) (v := fun i => (v i, w i))
  rw [hv, hw]; exact hmem'

/-- Konsum-Form über `Lc`: auch mit Konstanten erhält jede erzeugbare Operation `R₄`. -/
theorem in_cloneC_preservesR4 (f : Fin 4 → Fin 4 → Fin 4)
    (h : ∃ t : Lc.Term (Fin 2), ∀ v : Fin 2 → Fin 4, t.realize v = f (v 0) (v 1)) :
    PreservesR4 f := by
  obtain ⟨t, ht⟩ := h
  intro x y u v hxy huv
  have hinv : R4 (t.realize ![x, u]) (t.realize ![y, v]) :=
    r4_is_invariantC t ![x, u] ![y, v] (fun i =>
      Fin.cases hxy (fun j => Fin.cases huv (fun k => k.elim0) j) i)
  rw [ht (![x, u]), ht (![y, v])] at hinv
  exact hinv

/-- **Der Robustheitssatz.** Keine gemischte Wahl liegt im Klon — auch dann nicht,
wenn die Basis um alle vier Konstanten erweitert wird. Der Kontrast zu Test 2b
(`no_substructure_with_const`): die `{0,2}`-Schranke fiel an der Konstante, die
`R₄`-Schranke nicht — denn `R₄` ist reflexiv (`r4_diag`). -/
theorem mixed_not_in_constant_clone : ∀ c0 c1 c2 c3 c4 c5 : Bool,
    (c0 || c1 || c2 || c3 || c4 || c5) = true →
    (c0 && c1 && c2 && c3 && c4 && c5) = false →
    ¬ ∃ t : Lc.Term (Fin 2), ∀ v : Fin 2 → Fin 4,
        t.realize v = ofC c0 c1 c2 c3 c4 c5 (v 0) (v 1) := by
  intro c0 c1 c2 c3 c4 c5 h1 h2 ht
  exact mixed_breaks c0 c1 c2 c3 c4 c5 h1 h2 (in_cloneC_preservesR4 _ ht)

/-! **Statement-Pins.** Voller Wortlaut links, Satz rechts — jede Drift des
*Statements* bricht den Build. Namenlose `example`s, keine Axiom-Wache. -/

example (f : Fin 4 → Fin 4 → Fin 4) :
    LocallyClassical4 f ↔ ∃ c0 c1 c2 c3 c4 c5 : Bool, f = ofC c0 c1 c2 c3 c4 c5 :=
  locally_classical_iff4 f

example (t : L.Term (Fin 2)) (v w : Fin 2 → Fin 4) (h : ∀ i, R4 (v i) (w i)) :
    R4 (t.realize v) (t.realize w) := r4_is_invariant t v w h

example : ∀ c0 c1 c2 c3 c4 c5 : Bool,
    (c0 || c1 || c2 || c3 || c4 || c5) = true →
    (c0 && c1 && c2 && c3 && c4 && c5) = false →
    ¬ PreservesR4 (ofC c0 c1 c2 c3 c4 c5) := mixed_breaks

example : ∀ c0 c1 c2 c3 c4 c5 : Bool,
    (∃ t : L.Term (Fin 2), ∀ v : Fin 2 → Fin 4,
        t.realize v = ofC c0 c1 c2 c3 c4 c5 (v 0) (v 1))
      ↔ ((c0 && c1 && c2 && c3 && c4 && c5) = true
          ∨ (c0 || c1 || c2 || c3 || c4 || c5) = false) :=
  two_of_sixtyfour_generatable

example (f : Fin 4 → Fin 4 → Fin 4) (h : LocallyClassical4 f) :
    (∃ t : L.Term (Fin 2), ∀ v : Fin 2 → Fin 4, t.realize v = f (v 0) (v 1))
      ↔ ((f = fun a b => min a b) ∨ (f = fun a b => max a b)) :=
  locally_classical_in_clone_iff4 f h

example : ∀ c0 c1 c2 c3 c4 c5 : Bool,
    (c0 || c1 || c2 || c3 || c4 || c5) = true →
    (c0 && c1 && c2 && c3 && c4 && c5) = false →
    ¬ ∃ t : Lc.Term (Fin 2), ∀ v : Fin 2 → Fin 4,
        t.realize v = ofC c0 c1 c2 c3 c4 c5 (v 0) (v 1) :=
  mixed_not_in_constant_clone

/-! ## Teil 7 — die Axiom-Wachen (Ist-gebunden)

Ist-Ausgabe des grünen Builds (v4.30.0-rc2), pro Satz als Regressions-Wache eingefroren
(Datei-Vollständigkeits-Regel: alle Sätze der Datei; `realize_eq_of_pointwise4` als
Träger der Classical-Freiheit mitgewacht, wie `realize_eq_of_pointwise` in E1). Ab hier
bricht jede Axiom-Drift den Build. **Kein Satz zieht `Classical.choice` oder
`sorryAx`** — die Fintype-Pi-Fallen (Funktionsraum-`decide`, `fin_cases`) sind bewusst
umgangen (Sechs-Argument-`ofC`, Abdeckungs-Route, `congrFun`-Punkte,
`vec_eta4`/`realize_eq_of_pointwise4`). Besonders `mixed_breaks`: sein `[propext]` ist
das Ergebnis der Sechs-Argument-Bauform und muss brechen, wenn jemand sie rückgängig
macht. `r4_neighbor` und `r4_diag` sind axiom-frei. -/

/-- info: 'Reformulation.Proemial.QuaternaryCloneBound.ofC_locally_classical' depends on axioms: [propext] -/
#guard_msgs in #print axioms ofC_locally_classical

/-- info: 'Reformulation.Proemial.QuaternaryCloneBound.ofC_injective' depends on axioms: [propext] -/
#guard_msgs in #print axioms ofC_injective

/-- info: 'Reformulation.Proemial.QuaternaryCloneBound.locally_classical_reconstruct4' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms locally_classical_reconstruct4

/-- info: 'Reformulation.Proemial.QuaternaryCloneBound.locally_classical_iff4' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms locally_classical_iff4

/-- info: 'Reformulation.Proemial.QuaternaryCloneBound.locally_classical_faithful4' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms locally_classical_faithful4

/-- info: 'Reformulation.Proemial.QuaternaryCloneBound.all_false_is_min' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms all_false_is_min

/-- info: 'Reformulation.Proemial.QuaternaryCloneBound.all_true_is_max' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms all_true_is_max

/-- info: 'Reformulation.Proemial.QuaternaryCloneBound.r4_neighbor' does not depend on any axioms -/
#guard_msgs in #print axioms r4_neighbor

/-- info: 'Reformulation.Proemial.QuaternaryCloneBound.r4_proper' depends on axioms: [propext] -/
#guard_msgs in #print axioms r4_proper

/-- info: 'Reformulation.Proemial.QuaternaryCloneBound.r4_diag' does not depend on any axioms -/
#guard_msgs in #print axioms r4_diag

/-- info: 'Reformulation.Proemial.QuaternaryCloneBound.min_pres' depends on axioms: [propext] -/
#guard_msgs in #print axioms min_pres

/-- info: 'Reformulation.Proemial.QuaternaryCloneBound.max_pres' depends on axioms: [propext] -/
#guard_msgs in #print axioms max_pres

/-- info: 'Reformulation.Proemial.QuaternaryCloneBound.neg_pres' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms neg_pres

/-- info: 'Reformulation.Proemial.QuaternaryCloneBound.r4_is_invariant' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms r4_is_invariant

/-- info: 'Reformulation.Proemial.QuaternaryCloneBound.in_clone_preservesR4' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms in_clone_preservesR4

/-- info: 'Reformulation.Proemial.QuaternaryCloneBound.mixed_breaks' depends on axioms: [propext] -/
#guard_msgs in #print axioms mixed_breaks

/-- info: 'Reformulation.Proemial.QuaternaryCloneBound.mixed_not_in_clone' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms mixed_not_in_clone

/-- info: 'Reformulation.Proemial.QuaternaryCloneBound.realize_eq_of_pointwise4' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms realize_eq_of_pointwise4

/-- info: 'Reformulation.Proemial.QuaternaryCloneBound.min_in_clone4' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms min_in_clone4

/-- info: 'Reformulation.Proemial.QuaternaryCloneBound.max_in_clone4' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms max_in_clone4

/-- info: 'Reformulation.Proemial.QuaternaryCloneBound.ofC_min_in_clone' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ofC_min_in_clone

/-- info: 'Reformulation.Proemial.QuaternaryCloneBound.ofC_max_in_clone' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ofC_max_in_clone

/-- info: 'Reformulation.Proemial.QuaternaryCloneBound.two_of_sixtyfour_generatable' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms two_of_sixtyfour_generatable

/-- info: 'Reformulation.Proemial.QuaternaryCloneBound.locally_classical_in_clone_iff4' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms locally_classical_in_clone_iff4

/-- info: 'Reformulation.Proemial.QuaternaryCloneBound.r4_is_invariantC' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms r4_is_invariantC

/-- info: 'Reformulation.Proemial.QuaternaryCloneBound.in_cloneC_preservesR4' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms in_cloneC_preservesR4

/-- info: 'Reformulation.Proemial.QuaternaryCloneBound.mixed_not_in_constant_clone' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms mixed_not_in_constant_clone

end Reformulation.Proemial.QuaternaryCloneBound
