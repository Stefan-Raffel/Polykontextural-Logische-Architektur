import Mathlib.Data.List.Permutation
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Range

/-!
# Proemial.NegationCycle — Negationsfolgen, die jede Wertfolge genau einmal durchlaufen (Günthers Hamiltonkreise, Stufe 1)

**BENENNUNG mit Zeugen-Sätzen und einem kleinen Ertrag.** Gebaut auf Anordnung des
Architekten vom 21. September 2026 nach `KorpusRev2/Vorprobe_Hamiltonkreise_Impl.md`
(Stufe 1 der dortigen Empfehlung). Bis zu diesem Modul trug das Repo zum Gegenstand nichts;
die Grenznotiz C des Ledgers sagt: „Zyklentheorie ist nicht gebaut und war nicht Auftrag."

Der Träger ist der schmalste, der die Sache fasst: eine **Wertfolge** ist eine Liste über
`Fin (m + 1)`, ein **Negator** `N_{i+1}` tauscht in ihr die Werte `i` und `i + 1` (`sw`,
`negate`), eine **Negationsfolge** ist eine Liste von Negator-Indizes. `stations` führt die
durchlaufenen Wertfolgen, `endpoint` die erreichte. `IsFullCycle seq` sagt in vier Feldern,
was Günther einen *vollständigen Hamiltonkreis* nennt: die Folge kehrt zum Ausgang zurück,
keine Station kehrt wieder, jede Station ist eine Anordnung aller Werte, und jede Anordnung
aller Werte ist Station. Das Prädikat ist entscheidbar; die Zeugen-Sätze gehen durch `decide`.

Die Sätze:

* `sw_sw`, `negate_negate` — der Negator ist eine Involution (Günther: die Negation,
  „auf sich selbst angewendet, annulliert ihre Negationswirkung").
* `tafelVI4_full`, `tafelVI5_full`, `tafelVI5_eq_reverse` — dreiwertig: die zwei Folgen
  (4) und (5) sind Vollkreise, und die eine ist die andere rückwärts gelesen.
* `triadic_unique` — **der kleine Ertrag**: unter allen Negationsfolgen der Länge sechs über
  zwei Negatoren sind (4) und (5) die einzigen Vollkreise. Günther sagt es ohne Beweis
  (IGN S. 43: „Die triadische Wertordnung besaß nur einen einzigen solchen Kreis, der je nach
  der Wertordnung entweder im Uhrzeigersinn oder im Gegensinn durchlaufen werden konnte").
* `kreis1_full`, `kreis2_full`, `kreis3_full` — vierwertig: Günthers drei ausgeschriebene
  Beispielkreise sind Vollkreise; `kreis1_family` (10-9-5), `kreis2_family` (9-6-9),
  `kreis3_family` (6-12-6) — die Operatorhäufigkeiten, nach denen er die drei Familien
  unterscheidet. `kreis3` ist zugleich die Negatorfolge über **Tafel IV** des Aufsatzes von
  1980.
* `kreis1_reverse_full`, `kreis2_reverse_full`, `kreis3_reverse_full` — der Gegen-Drehsinn
  ist wieder ein Vollkreis. `kreis1_mirror_full`, `kreis1_mirror_family` — die Spiegelung
  `N₁ ↔ N₃` führt 10-9-5 in 5-9-10 über; Günther rechnet beide zur selben Familie.
* `pseudo_closes`, `pseudo_family`, `pseudo_half`, `pseudo_not_full` — Günthers eigenes
  Gegenbeispiel, die Folge (23): `N₁·₂·₃` achtmal kehrt zurück und verteilt die Operatoren
  8-8-8, durchläuft aber in der zweiten Hälfte noch einmal die erste — eine
  „Pseudoäquivalenz", ein „partieller Hamiltonkreis mit einem Bestand von nur zwölf
  Wertkolonnen".
* `visits_every_arrangement` — der Anschluss an `List.Perm`: ein Vollkreis trifft jede
  Liste, die eine Permutation des Ausgangs ist.

**Warum überwiegend Benennung:** die Zeugen-Sätze rechnen nach, was Günther ausschreibt;
neuen Satzgehalt trägt allein `triadic_unique`, und der ist eine endliche Fallarbeit über
64 Folgen.

## Quellenlage

Härte-Marke durchweg **GEMESSEN** (CLAUDE.md §6), gelesen an der Textschicht der PDF
(`pypdf`; die Seiten liessen sich nicht rendern — der Druck ist **nicht** eingesehen):

* **IGN** = *Identität, Gegenidentität und Negativsprache* (1979),
  `KorpusRev1/gunther_identitaet.pdf`, Seitenzahl = PDF-Seite.
  S. 18: die Folgen (4) `p ≡ N₁·₂·₁·₂·₁·₂ p` und (5) `p ≡ N₂·₁·₂·₁·₂·₁ p`, Tafel VI —
  „Wertpermutationen, die Hamilton-Kreise bilden". S. 41: N₃ als Umtausch zwischen drittem
  und viertem Wert. S. 43: die drei Familien nach Operatorhäufigkeit. S. 44: der erste und
  der zweite Beispielkreis, Tafel XI und XII. S. 45: der dritte, und die Folge (23) mit
  Tafel XIV. S. 46: „Pseudoäquivalenz", „partieller Hamiltonkreis".
* **Heidegger 1980** = *Martin Heidegger und die Weltgeschichte des Nichts*,
  `KorpusRev1/gg_heidegger-weltgeschichte-nichts.pdf`, S. 20: Tafel IV mit Negatorfolge
  und 25 Wertspalten; „alle überhaupt möglichen Permutationen einmal und nur einmal".

**Drei Textbefunde, gemeldet und nicht geheilt** (Hermeneutes):

1. IGN S. 44 druckt den zweiten Kreis mit **22** Negatoren
   (`1·2·3·1·3·2·1·3·1·2·3·1·3·2·1·3·1·2·3·1·3·2`); die Folge schliesst so nicht und verteilt
   8-6-8. `kreis2` ist die um `·1·3` **ergänzte** Folge (dreimal `1·2·3·1·3·2·1·3`). Die
   Ergänzung ist nicht meine Vermutung allein: Günther nennt an der Stelle die Verteilung
   neun-sechs-neun, und die 25 Wertspalten von Tafel XII folgen der ergänzten Folge in 24
   von 25 Spalten.
2. Tafel XII, Spalte 18, lautet in der Textschicht `2 3 □ 2`; die Folge verlangt `2 3 □ 1`.
3. Tafel IV (1980), Spalte 17, lautet `1 4 2 1`; die Folge verlangt `1 4 2 3`.

## Lesart, im Kopf festgelegt und nicht stillschweigend

* **Der Negator wirkt auf WERTE** (`sw` tauscht die Werte `i` und `i + 1`, wo immer sie
  stehen), nicht auf Stellen. So liest Günther (S. 41: „Umtauschverhältnis zwischen dem
  dritten und vierten Wert"), und so reproduzieren seine Tafeln. Der Stellen-Tausch gäbe
  einen isomorphen Graphen und andere Tafeln.
* **Null-Indizierung.** Günthers Werte `1 … 4` sind hier `0 … 3`, seine Negatoren
  `N₁, N₂, N₃` die Indizes `0, 1, 2`.
* **„Hamiltonkreis" ist Günthers Wort** und steht darum im Titel. Den Graphenbegriff führt
  dieses Modul nicht. Dass `kreis1` ein `SimpleGraph.Walk.IsHamiltonianCycle` im Sinn von
  Mathlib ist, ist **gemessen und nicht im Repo**: die Probe steht mit Quelltext in der
  Vorprobe-Notiz (Anhang A). Sie liegt ausserhalb, weil die Graphenbibliothek eine
  Importhülle nachzieht, die das Aggregat sonst nicht trägt, und weil keines der
  bestehenden Targets sie ihrem Zweck nach aufnimmt — das ist eine Entscheidung des
  Architekten, keine des Baus.

## Was dieses Modul NICHT sagt

* **Nicht die 44 und nicht Tafel XX.** Günthers Zahl der vierwertigen Vollkreise (IGN S. 41,
  1980 S. 20) und die Kreiszahlen je Umfang (IGN S. 50) sind ausserhalb des Korpus
  nachgerechnet und stimmen (Vorprobe §2); in den Korpus gehörten sie nur in Bijektions-
  oder Iff-Form (CLAUDE.md §6), und die ist Stufe 2 und nicht gebaut.
* **Nicht, dass kein Vollkreis 8-8-8 verteilt.** Günther sagt „niemals" (IGN S. 43); dieses
  Modul zeigt an **einer** Folge, seiner eigenen, dass 8-8-8 scheitern *kann*. Die
  Unmöglichkeit ist ausserhalb nachgezählt und hier kein Satz.
* **Nichts über Proemialrelation, Paragraph 20 oder die Zeit.** Günther selbst schreibt
  (IGN S. 58), wer sich mit der Rückkehr des Vollkreises zufriedengebe, habe „völlig das
  Zeitproblem ignoriert". Keine Ledger-Zeile; ob L14-1 (Zyklus) hier einen Träger findet,
  entscheidet Custos mit Hermeneutes.
* **Nichts über „Negativsprache", „Wörterbuch", „Totaläquivalenz".** Das sind Günthers
  Deutungen der Kreise; formalisiert sind die Kreise.
* **Keine Drehsinn-Aussage im Allgemeinen.** Dass die Umkehrung *jedes* Vollkreises ein
  Vollkreis ist, steht hier nur an den drei Beispielen.

## Axiomprofil

Gemessen und am Dateiende gewacht. Die Zeugen-Sätze und `triadic_unique` tragen `[propext]`
— **ohne `Classical.choice`**: der Listen-Träger braucht `DecidableEq`, keine
`Fintype`-Instanz. (Über `Equiv.Perm (Fin 4)` gemessen zieht derselbe Inhalt das volle
Profil, siehe Vorprobe §3.) `negate_negate` trägt zusätzlich `Quot.sound` (`funext` unter
`List.map`), `visits_every_arrangement` trägt, was `List.mem_permutations'` trägt.
`List.permutations` reduziert unter `decide` nicht; darum die strukturelle Fassung
`List.permutations'`.
-/

namespace Reformulation.Proemial.NegationCycle

-- ============================================================
-- Teil 1 — Negator, Negationsfolge, Vollkreis
-- ============================================================

/-- Der Umtausch der Werte `i` und `i + 1`; alle anderen Werte bleiben. -/
def sw {m : ℕ} (i : Fin m) (v : Fin (m + 1)) : Fin (m + 1) :=
  if v = i.castSucc then i.succ else if v = i.succ then i.castSucc else v

/-- Der Negator `N_{i+1}` auf einer Wertfolge: der Werte-Umtausch an jeder Stelle. -/
def negate {m : ℕ} (i : Fin m) (l : List (Fin (m + 1))) : List (Fin (m + 1)) := l.map (sw i)

/-- Die Stationen einer Negationsfolge vom Ausgang `l` an, ohne die zuletzt erreichte. -/
def stations {m : ℕ} : List (Fin m) → List (Fin (m + 1)) → List (List (Fin (m + 1)))
  | [], _ => []
  | i :: is, l => l :: stations is (negate i l)

/-- Die Wertfolge, die eine Negationsfolge vom Ausgang `l` aus erreicht. -/
def endpoint {m : ℕ} : List (Fin m) → List (Fin (m + 1)) → List (Fin (m + 1))
  | [], l => l
  | i :: is, l => endpoint is (negate i l)

/-- Der Ausgang: die Werte in ihrer Ordnung (Günthers `p`). -/
def origin (m : ℕ) : List (Fin (m + 1)) := List.finRange (m + 1)

/-- Eine Negationsfolge ist ein **Vollkreis**, wenn sie zum Ausgang zurückkehrt und dabei
jede Anordnung aller Werte einmal und nur einmal durchläuft. -/
structure IsFullCycle {m : ℕ} (seq : List (Fin m)) : Prop where
  /-- Die Folge kehrt zum Ausgang zurück. -/
  closes : endpoint seq (origin m) = origin m
  /-- Keine Station kehrt wieder. -/
  nodup : (stations seq (origin m)).Nodup
  /-- Jede Station ist eine Anordnung aller Werte. -/
  only_arrangements : ∀ l ∈ stations seq (origin m), l ∈ (origin m).permutations'
  /-- Jede Anordnung aller Werte ist Station. -/
  all_arrangements : ∀ l ∈ (origin m).permutations', l ∈ stations seq (origin m)

instance {m : ℕ} (seq : List (Fin m)) : Decidable (IsFullCycle seq) :=
  decidable_of_iff
    (endpoint seq (origin m) = origin m ∧ (stations seq (origin m)).Nodup ∧
      (∀ l ∈ stations seq (origin m), l ∈ (origin m).permutations') ∧
      (∀ l ∈ (origin m).permutations', l ∈ stations seq (origin m)))
    ⟨fun ⟨a, b, c, d⟩ => ⟨a, b, c, d⟩, fun ⟨a, b, c, d⟩ => ⟨a, b, c, d⟩⟩

/-- Der Werte-Umtausch ist eine Involution. -/
theorem sw_sw {m : ℕ} (i : Fin m) (v : Fin (m + 1)) : sw i (sw i v) = v := by
  unfold sw
  have h : i.castSucc ≠ i.succ := Fin.ne_of_lt Fin.castSucc_lt_succ
  by_cases h1 : v = i.castSucc
  · simp [h1, h.symm]
  · by_cases h2 : v = i.succ
    · simp [h2]
    · simp [h1, h2]

/-- Der Negator, auf sich selbst angewendet, hebt sich auf. -/
theorem negate_negate {m : ℕ} (i : Fin m) (l : List (Fin (m + 1))) :
    negate i (negate i l) = l := by
  simp [negate, List.map_map, Function.comp_def, sw_sw]

/-- Ein Vollkreis trifft jede Permutation des Ausgangs. -/
theorem visits_every_arrangement {m : ℕ} {seq : List (Fin m)} (h : IsFullCycle seq)
    {l : List (Fin (m + 1))} (hl : l.Perm (origin m)) : l ∈ stations seq (origin m) :=
  h.all_arrangements l (List.mem_permutations'.mpr hl)

-- ============================================================
-- Teil 2 — dreiwertig: Tafel VI (IGN S. 18)
-- ============================================================

/-- Folge (4): `p ≡ N₁·₂·₁·₂·₁·₂ p`. -/
def tafelVI4 : List (Fin 2) := [0, 1, 0, 1, 0, 1]

/-- Folge (5): `p ≡ N₂·₁·₂·₁·₂·₁ p`. -/
def tafelVI5 : List (Fin 2) := [1, 0, 1, 0, 1, 0]

theorem tafelVI4_full : IsFullCycle tafelVI4 := by decide

theorem tafelVI5_full : IsFullCycle tafelVI5 := by decide

/-- Die zwei Folgen sind ein Kreis in zwei Drehsinnen. -/
theorem tafelVI5_eq_reverse : tafelVI5 = tafelVI4.reverse := by decide

/-- **Dreiwertig gibt es nur diesen einen Kreis.** Unter allen Negationsfolgen der Länge
sechs sind (4) und (5) die einzigen Vollkreise. -/
theorem triadic_unique : ∀ a b c d e f : Fin 2, IsFullCycle [a, b, c, d, e, f] →
    [a, b, c, d, e, f] = tafelVI4 ∨ [a, b, c, d, e, f] = tafelVI5 := by decide

-- ============================================================
-- Teil 3 — vierwertig: die drei Beispielkreise (IGN S. 44–45; 1980 Tafel IV)
-- ============================================================

/-- IGN S. 44, „Unser erster Hamiltonkreis". -/
def kreis1 : List (Fin 3) :=
  [0, 1, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 2, 1, 0, 1, 0, 1, 2, 1, 0, 2]

/-- IGN S. 44, der zweite Kreis — **um `·1·3` ergänzt**, siehe Kopf, Textbefund 1. -/
def kreis2 : List (Fin 3) :=
  [0, 1, 2, 0, 2, 1, 0, 2, 0, 1, 2, 0, 2, 1, 0, 2, 0, 1, 2, 0, 2, 1, 0, 2]

/-- IGN S. 45, der dritte Kreis; zugleich die Negatorfolge über Tafel IV (1980, S. 20). -/
def kreis3 : List (Fin 3) :=
  [0, 1, 2, 1, 2, 1, 0, 1, 0, 1, 2, 1, 2, 1, 0, 1, 0, 1, 2, 1, 2, 1, 0, 1]

set_option maxRecDepth 100000 in
theorem kreis1_full : IsFullCycle kreis1 := by decide

set_option maxRecDepth 100000 in
theorem kreis2_full : IsFullCycle kreis2 := by decide

set_option maxRecDepth 100000 in
theorem kreis3_full : IsFullCycle kreis3 := by decide

/-- Familie 10-9-5. -/
theorem kreis1_family : kreis1.count 0 = 10 ∧ kreis1.count 1 = 9 ∧ kreis1.count 2 = 5 := by
  decide

/-- Familie 9-6-9. -/
theorem kreis2_family : kreis2.count 0 = 9 ∧ kreis2.count 1 = 6 ∧ kreis2.count 2 = 9 := by
  decide

/-- Familie 6-12-6. -/
theorem kreis3_family : kreis3.count 0 = 6 ∧ kreis3.count 1 = 12 ∧ kreis3.count 2 = 6 := by
  decide

set_option maxRecDepth 100000 in
theorem kreis1_reverse_full : IsFullCycle kreis1.reverse := by decide

set_option maxRecDepth 100000 in
theorem kreis2_reverse_full : IsFullCycle kreis2.reverse := by decide

set_option maxRecDepth 100000 in
theorem kreis3_reverse_full : IsFullCycle kreis3.reverse := by decide

set_option maxRecDepth 100000 in
/-- Die Spiegelung `N₁ ↔ N₃` eines Vollkreises, am ersten Beispiel. -/
theorem kreis1_mirror_full : IsFullCycle (kreis1.map Fin.rev) := by decide

/-- Die Spiegelung führt 10-9-5 in 5-9-10 über. -/
theorem kreis1_mirror_family :
    (kreis1.map Fin.rev).count 0 = 5 ∧ (kreis1.map Fin.rev).count 1 = 9 ∧
      (kreis1.map Fin.rev).count 2 = 10 := by
  decide

-- ============================================================
-- Teil 4 — Günthers Gegenbeispiel: die Folge (23) (IGN S. 45–46)
-- ============================================================

/-- Folge (23): `N₁·₂·₃`, achtmal. -/
def pseudo : List (Fin 3) :=
  [0, 1, 2, 0, 1, 2, 0, 1, 2, 0, 1, 2, 0, 1, 2, 0, 1, 2, 0, 1, 2, 0, 1, 2]

/-- Die Folge kehrt zum Ausgang zurück … -/
theorem pseudo_closes : endpoint pseudo (origin 3) = origin 3 := by decide

/-- … verteilt die Operatoren gleich … -/
theorem pseudo_family : pseudo.count 0 = 8 ∧ pseudo.count 1 = 8 ∧ pseudo.count 2 = 8 := by
  decide

/-- … durchläuft aber in der zweiten Hälfte noch einmal die erste … -/
theorem pseudo_half :
    stations (pseudo.take 12) (origin 3) =
      stations (pseudo.drop 12) (endpoint (pseudo.take 12) (origin 3)) := by
  decide

set_option maxRecDepth 100000 in
/-- … und ist darum kein Vollkreis. -/
theorem pseudo_not_full : ¬ IsFullCycle pseudo := by decide

-- ============================================================
-- Wachen
-- ============================================================

/-- info: 'Reformulation.Proemial.NegationCycle.sw_sw' depends on axioms: [propext] -/
#guard_msgs in #print axioms sw_sw

/-- info: 'Reformulation.Proemial.NegationCycle.negate_negate' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms negate_negate

/-- info: 'Reformulation.Proemial.NegationCycle.visits_every_arrangement' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms visits_every_arrangement

/-- info: 'Reformulation.Proemial.NegationCycle.tafelVI4_full' depends on axioms: [propext] -/
#guard_msgs in #print axioms tafelVI4_full

/-- info: 'Reformulation.Proemial.NegationCycle.tafelVI5_full' depends on axioms: [propext] -/
#guard_msgs in #print axioms tafelVI5_full

/-- info: 'Reformulation.Proemial.NegationCycle.tafelVI5_eq_reverse' depends on axioms: [propext] -/
#guard_msgs in #print axioms tafelVI5_eq_reverse

/-- info: 'Reformulation.Proemial.NegationCycle.triadic_unique' depends on axioms: [propext] -/
#guard_msgs in #print axioms triadic_unique

/-- info: 'Reformulation.Proemial.NegationCycle.kreis1_full' depends on axioms: [propext] -/
#guard_msgs in #print axioms kreis1_full

/-- info: 'Reformulation.Proemial.NegationCycle.kreis2_full' depends on axioms: [propext] -/
#guard_msgs in #print axioms kreis2_full

/-- info: 'Reformulation.Proemial.NegationCycle.kreis3_full' depends on axioms: [propext] -/
#guard_msgs in #print axioms kreis3_full

/-- info: 'Reformulation.Proemial.NegationCycle.kreis1_family' depends on axioms: [propext] -/
#guard_msgs in #print axioms kreis1_family

/-- info: 'Reformulation.Proemial.NegationCycle.kreis2_family' depends on axioms: [propext] -/
#guard_msgs in #print axioms kreis2_family

/-- info: 'Reformulation.Proemial.NegationCycle.kreis3_family' depends on axioms: [propext] -/
#guard_msgs in #print axioms kreis3_family

/-- info: 'Reformulation.Proemial.NegationCycle.kreis1_reverse_full' depends on axioms: [propext] -/
#guard_msgs in #print axioms kreis1_reverse_full

/-- info: 'Reformulation.Proemial.NegationCycle.kreis2_reverse_full' depends on axioms: [propext] -/
#guard_msgs in #print axioms kreis2_reverse_full

/-- info: 'Reformulation.Proemial.NegationCycle.kreis3_reverse_full' depends on axioms: [propext] -/
#guard_msgs in #print axioms kreis3_reverse_full

/-- info: 'Reformulation.Proemial.NegationCycle.kreis1_mirror_full' depends on axioms: [propext] -/
#guard_msgs in #print axioms kreis1_mirror_full

/-- info: 'Reformulation.Proemial.NegationCycle.kreis1_mirror_family' depends on axioms: [propext] -/
#guard_msgs in #print axioms kreis1_mirror_family

/-- info: 'Reformulation.Proemial.NegationCycle.pseudo_closes' depends on axioms: [propext] -/
#guard_msgs in #print axioms pseudo_closes

/-- info: 'Reformulation.Proemial.NegationCycle.pseudo_family' depends on axioms: [propext] -/
#guard_msgs in #print axioms pseudo_family

/-- info: 'Reformulation.Proemial.NegationCycle.pseudo_half' depends on axioms: [propext] -/
#guard_msgs in #print axioms pseudo_half

/-- info: 'Reformulation.Proemial.NegationCycle.pseudo_not_full' depends on axioms: [propext] -/
#guard_msgs in #print axioms pseudo_not_full

end Reformulation.Proemial.NegationCycle
