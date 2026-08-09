import Mathlib.Order.Hom.Basic
import Reformulation.Kenogram.Basic

/-!
# Kenogram.OccupancySeparation — was die Normalform zweier Stellen nicht trennt

**Ertrag, dreifach geschnitten.**

* **T1 — die Blindheit der Normalform.** `canonicalize_eq_of_ne`: über **zwei**
  Stellen haben je zwei Belegungen mit verschiedenen Werten **dieselbe**
  RGS-Normalform, heterogen über beliebigen Trägern mit entscheidbarer
  Gleichheit. Daneben `canonicalize_comp_swap`: der Tausch der beiden Stellen
  ist für die Normalform unsichtbar, und zwar ohne Voraussetzung an die
  Belegung.
* **T2/T3 — ein Kriterium an der Belegung.** `RisingOccupancy` gegen
  `FallingOccupancy` über einem `LinearOrder`, mit `occupancy_exclusive`,
  `occupancy_total` und `no_occupancy_of_eq`: über zwei verschiedenen Werten
  trennen die beiden Fälle einander vollständig, über zwei gleichen Werten ist
  keiner von beiden realisierbar.
* **Der Klassifikationssatz.** `separation_is_the_order`: **jedes** Kriterienpaar
  an einer Zweistellen-Belegung, das unter Ordnungseinbettungen des Trägers
  stabil ist und die verschiedenwertigen Belegungen ausschliessend und
  vollständig teilt, **ist** dieses Paar — bis auf die Benennung, welche Hälfte
  welche heisst.

## Die Grenzformel

**Bewiesen ist, dass die Normalform zweier Stellen die Alternative nicht trennt
und ein Kriterium an der Belegung sie trennt.**

Und hinzu kommt, was der Klassifikationssatz misst und die Grenzformel nicht
sagt: **das trennende Kriterium ist die Ordnung selbst.** Über zwei Stellen und
einem blossen `LinearOrder` gibt es kein anderes; wer trennen will, benennt die
Ordnungsrelation um. Das ist keine Schwäche der hier gewählten Fassung, sondern
eine Eigenschaft des Rahmens — und der Satz ist der Beleg dafür, dass sie nicht
an der Wahl liegt.

## Der Anlass, als Zitat mit Herkunft

Günther, *Cognition and Volition*, S. 22 (Figur auf S. 21; Druck- und PDF-Seite
fallen zusammen, an der Quelle geprüft):

> „where the two empty squares represent kenograms which can either be filled in
> such a way that the value occupancy represents a symmetrical exchange relation
> or in a way that the relation assumes the character of an order."

**Das ist ein Zitat und keine Behauptung dieses Korpus.** Was hier bewiesen wird,
ist nicht, dass Günther recht hat, und nicht, was er gemeint hat.

## Deutungsgrenzen

**Eine Kopplung ist kein Grund.** Diese Sätze konstituieren **keine**
Proemialrelation; sie sagen nichts über den Wechsel von Relator und Relatum,
nichts über Erkennen und Wollen und nichts über ein „voraus".

**Welche Besetzung das Umtauschverhältnis trägt und welche die Ordnung, wird hier
nicht gesagt** — die Quelle sagt es an dieser Stelle nicht, und der
Klassifikationssatz zeigt darüber hinaus, dass die Zuordnung durch die
Trennleistung **nicht bestimmt** ist: die beiden Zweige seiner Konklusion sind
gleichberechtigt. Darum heissen die zwei Prädikate nach dem, was an ihnen
bewiesen ist — die Werte steigen oder fallen längs der beiden Stellen —, und
nicht nach den zwei Fällen der Quelle. **Kein Deklarationsname dieses Moduls
trägt eines der beiden Fallwörter der Quelle**; `Occupancy` benennt den
Gegenstand — die Besetzung zweier Stellen mit Werten — und nicht seine
Deutung.

## Was der Klassifikationssatz voraussetzt, und was ausserhalb bleibt

Er redet über Kriterien, die (a) über **zwei** Stellen entscheiden, (b) über
einem **blossen** `LinearOrder` formuliert sind, (c) in `Type` liegen und (d)
unter Ordnungseinbettungen des Trägers **stabil** sind. Bedingung (d) ist die
formale Fassung von „das Kriterium sieht nur die beiden Werte und ihre Lage
zueinander, nicht die Gestalt des umgebenden Trägers"; ein Kriterium ohne sie
entscheidet an Werten, die in der Belegung nicht vorkommen.

**Ausserhalb bleibt damit ausdrücklich:** mehr als zwei Stellen, und mehr
Struktur auf dem Träger als eine lineare Ordnung. Der Satz sagt nicht, dass es
kein substantielles Wertkriterium gibt; er sagt, dass es in **diesem** Rahmen
keines gibt.

## Profil

`Classical.choice` tragen genau die drei Sätze, die die Normalform berühren —
T1, `canonicalize_comp_swap` und `both_cases_realized`. Er ist dort **geerbt**
und nicht hier erzeugt: `canonicalize_eq_iff` trägt ihn (gemessen), und alle
drei gehen über ihn. **Der ganze Klassifikationsteil ist choice-frei**, und der
Weg dorthin ist gemessen und nicht geschätzt: `fin_cases` und `simp_all` ziehen
den Choice über `Fin 2`, die Handzerlegung `fin2_cases` nicht; die
Fallunterscheidung des Hauptsatzes läuft über die Vollständigkeits-
Voraussetzung statt über `by_cases`.

## Warum das Modul im Kenogram-Zweig liegt

Gemessen an den Kopfzeilen: der Proemial-Zweig importiert `Kenogram`, der
Kenogram-Zweig importiert **nie** `Proemial`. Dieses Modul konsumiert
`Kenogram.Basic` und aus Mathlib nur die Ordnungs-Einbettungen; nichts aus
`Proemial` geht ein. Der Ort ist damit durch die Importrichtung bestimmt und
nicht gewählt.

## Aggregat-Reife

Konsumiert `Kenogram.Basic` — Aggregat — sowie Mathlib. Keine Sonde, keine
Setzung.

Kein `sorry`, kein `axiom`, kein `: True`-Feld.
-/

namespace Reformulation.Kenogram.OccupancySeparation

open Reformulation.Kenogram

/-! ## Teil 1 — T1: die Normalform zweier Stellen trennt nicht -/

/-- **T1.** Über zwei Stellen haben je zwei Belegungen mit **verschiedenen**
Werten dieselbe RGS-Normalform — heterogen: die beiden Belegungen dürfen über
verschiedenen Trägern laufen. Das Gleichheitsmuster über zwei Stellen leistet
genau eine Unterscheidung, und `canonicalize` sieht nur dieses Muster. -/
theorem canonicalize_eq_of_ne {α β : Type*} [DecidableEq α] [DecidableEq β]
    {f : Fin 2 → α} {g : Fin 2 → β} (hf : f 0 ≠ f 1) (hg : g 0 ≠ g 1) :
    canonicalize f = canonicalize g := by
  refine (canonicalize_eq_iff f g).mpr ?_
  intro i j
  fin_cases i <;> fin_cases j <;> simp_all [eq_comm]

/-- Der **Tausch der beiden Stellen** ist für die Normalform unsichtbar, und
zwar ohne jede Voraussetzung an die Belegung — auch über gleichen Werten. Die
Stellenvertauschung ist hier `Equiv.swap` auf dem Index und nicht die
Listenoperation `swapPlaces` des Bestandes; beide meinen dieselbe Sache an
verschiedenen Gegenständen. -/
theorem canonicalize_comp_swap {α : Type*} [DecidableEq α] (f : Fin 2 → α) :
    canonicalize (f ∘ Equiv.swap (0 : Fin 2) 1) = canonicalize f := by
  refine (canonicalize_eq_iff _ _).mpr ?_
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [Function.comp, Equiv.swap_apply_left, Equiv.swap_apply_right, eq_comm]

/-! ## Teil 2 — die zwei Prädikate an der Belegung

Beide sind **ohne** Rückgriff auf die Normalform formuliert und unter
`LinearOrder` entscheidbar; die zwei `Decidable`-Instanzen unten sind die
Satzform dieser zweiten Eigenschaft. -/

variable {α : Type*} [LinearOrder α]

/-- Die Werte **steigen** längs der beiden Stellen. -/
def RisingOccupancy (f : Fin 2 → α) : Prop := f 0 < f 1

/-- Die Werte **fallen** längs der beiden Stellen. -/
def FallingOccupancy (f : Fin 2 → α) : Prop := f 1 < f 0

instance (f : Fin 2 → α) : Decidable (RisingOccupancy f) :=
  inferInstanceAs (Decidable (f 0 < f 1))

instance (f : Fin 2 → α) : Decidable (FallingOccupancy f) :=
  inferInstanceAs (Decidable (f 1 < f 0))

/-! ## Teil 3 — T2 und T3: die Trennung und ihre Grenze -/

/-- **T2, erste Hälfte.** Die beiden Fälle schliessen einander aus. **Die
Voraussetzung `f 0 ≠ f 1` wird nicht gebraucht** — der Ausschluss folgt schon
aus der Irreflexivität. Die Vorgabe führt sie mit; sie ist entbehrlich, und der
Satz steht darum in der stärkeren Fassung. -/
theorem occupancy_exclusive (f : Fin 2 → α) :
    ¬ (RisingOccupancy f ∧ FallingOccupancy f) :=
  fun h => absurd (h.1.trans h.2) (lt_irrefl _)

/-- **T2, zweite Hälfte.** Über zwei verschiedenen Werten tritt einer der beiden
Fälle ein. Hier ist die Voraussetzung tragend. -/
theorem occupancy_total {f : Fin 2 → α} (h : f 0 ≠ f 1) :
    RisingOccupancy f ∨ FallingOccupancy f :=
  lt_or_gt_of_ne h

/-- **T3.** Über zwei **gleichen** Werten ist keiner der beiden Fälle
realisierbar. Damit steht die Asymmetrie der beiden Erzeuger aus `JointClosure`
auch wertseitig: das Muster `[0,1]` trägt beide Möglichkeiten, `[0,0]` keine. -/
theorem no_occupancy_of_eq {f : Fin 2 → α} (h : f 0 = f 1) :
    ¬ RisingOccupancy f ∧ ¬ FallingOccupancy f :=
  ⟨by simp [RisingOccupancy, h], by simp [FallingOccupancy, h]⟩

/-! ## Teil 4 — die zwei Musterbelegungen über `Fin 2`

Sie sind die Zeugen von Teil 3 und zugleich die beiden Punkte, auf die der
Klassifikationssatz jede Belegung zurückführt. -/

/-- Die Belegung zweier Stellen mit zwei angegebenen Werten. `abbrev`, damit
`decide` sie sieht. -/
abbrev pairMap {α : Type*} (a b : α) : Fin 2 → α := fun i => if i = 0 then a else b

/-- Die aufsteigende Musterbelegung. -/
abbrev upPair : Fin 2 → Fin 2 := pairMap 0 1

/-- Die absteigende Musterbelegung. -/
abbrev downPair : Fin 2 → Fin 2 := pairMap 1 0

/-- Die einwertige Belegung — zwei Stellen über einem einelementigen Träger. -/
abbrev flatPair : Fin 2 → Fin 1 := fun _ => 0

/-- **Beide Fälle sind besetzt, und beide liegen über derselben Normalform.**
Die formale Fassung des Arguments, aus dem dieses Modul entstanden ist: über
zwei Stellen liegt Günthers Alternative über **einem** Muster. -/
theorem both_cases_realized :
    RisingOccupancy upPair ∧ FallingOccupancy downPair ∧
      canonicalize upPair = canonicalize downPair :=
  ⟨by decide, by decide, canonicalize_eq_of_ne (by decide) (by decide)⟩

/-! ## Teil 5 — der Klassifikationssatz

Ein **Kriterium an der Belegung zweier Stellen** ist eine Eigenschaft solcher
Belegungen über beliebigen linear geordneten Trägern, die eine
Ordnungseinbettung des Trägers nicht bemerkt. Die Stabilität ist die formale
Fassung davon, dass das Kriterium an der Belegung entscheidet und nicht an der
Gestalt des Trägers. -/

/-- Über `Fin 2` gibt es genau zwei Stellen. Handzerlegung statt `fin_cases`:
der Taktikweg zieht `Classical.choice`, dieser nicht (gemessen). -/
private theorem fin2_cases (i : Fin 2) : i = 0 ∨ i = 1 := by
  by_cases h0 : i.val = 0
  · exact Or.inl (Fin.ext h0)
  · exact Or.inr (Fin.ext (by have := i.isLt; omega))

private theorem pair_strictMono {α : Type} [LinearOrder α] {a b : α} (h : a < b) :
    StrictMono (pairMap a b) := by
  intro i j hij
  rcases fin2_cases i with hi | hi <;> rcases fin2_cases j with hj | hj <;>
    subst hi <;> subst hj
  · exact absurd hij (lt_irrefl _)
  · exact h
  · exact absurd hij (by decide)
  · exact absurd hij (lt_irrefl _)

private theorem point_strictMono {α : Type} [LinearOrder α] (a : α) :
    StrictMono (fun _ : Fin 1 => a) := by
  intro i j hij
  exact absurd (Fin.lt_def.mp hij) (by have := i.isLt; have := j.isLt; omega)

/-- Zwei aufsteigende Werte spannen eine Ordnungseinbettung `Fin 2 ↪o α`. -/
private def pairEmb {α : Type} [LinearOrder α] {a b : α} (h : a < b) : Fin 2 ↪o α :=
  OrderEmbedding.ofStrictMono (pairMap a b) (pair_strictMono h)

/-- Ein Wert spannt eine Ordnungseinbettung `Fin 1 ↪o α`. -/
private def pointEmb {α : Type} [LinearOrder α] (a : α) : Fin 1 ↪o α :=
  OrderEmbedding.ofStrictMono (fun _ => a) (point_strictMono a)

/-- Ein **Kriterium an der Belegung zweier Stellen**: eine Eigenschaft von
Belegungen über beliebigen linear geordneten Trägern in `Type`, die unter
Ordnungseinbettungen des Trägers unverändert bleibt. -/
structure OccupancyCriterion where
  /-- Die Eigenschaft, über jedem linear geordneten Träger. -/
  holds : {α : Type} → [LinearOrder α] → (Fin 2 → α) → Prop
  /-- Eine Ordnungseinbettung des Trägers ändert nichts. -/
  stable : ∀ {α β : Type} [LinearOrder α] [LinearOrder β] (φ : α ↪o β) (f : Fin 2 → α),
      holds (fun i => φ (f i)) ↔ holds f

/-- Jede aufsteigende Belegung wird auf die aufsteigende Musterbelegung
zurückgeführt. -/
theorem holds_iff_upPair (C : OccupancyCriterion) {α : Type} [LinearOrder α]
    {f : Fin 2 → α} (h : f 0 < f 1) : C.holds f ↔ C.holds upPair := by
  have hst := C.stable (pairEmb h) upPair
  have hfun : (fun i => (pairEmb h) (upPair i)) = f := by
    funext i
    rcases fin2_cases i with hi | hi <;> subst hi <;> rfl
  rw [hfun] at hst
  exact hst

/-- Jede absteigende Belegung wird auf die absteigende Musterbelegung
zurückgeführt. -/
theorem holds_iff_downPair (C : OccupancyCriterion) {α : Type} [LinearOrder α]
    {f : Fin 2 → α} (h : f 1 < f 0) : C.holds f ↔ C.holds downPair := by
  have hst := C.stable (pairEmb h) downPair
  have hfun : (fun i => (pairEmb h) (downPair i)) = f := by
    funext i
    rcases fin2_cases i with hi | hi <;> subst hi <;> rfl
  rw [hfun] at hst
  exact hst

/-- Jede gleichwertige Belegung wird auf die einwertige Belegung
zurückgeführt. -/
theorem holds_iff_flatPair (C : OccupancyCriterion) {α : Type} [LinearOrder α]
    {f : Fin 2 → α} (h : f 0 = f 1) : C.holds f ↔ C.holds flatPair := by
  have hst := C.stable (pointEmb (f 0)) flatPair
  have hfun : (fun i => (pointEmb (f 0)) (flatPair i)) = f := by
    funext i
    rcases fin2_cases i with hi | hi <;> subst hi
    · rfl
    · exact h
  rw [hfun] at hst
  exact hst

/-- Das aufsteigende Prädikat **ist** ein Kriterium in diesem Sinn. -/
def risingCriterion : OccupancyCriterion where
  holds := fun {_} _ f => f 0 < f 1
  stable := fun φ _ => φ.lt_iff_lt

/-- Das absteigende Prädikat **ist** ein Kriterium in diesem Sinn. -/
def fallingCriterion : OccupancyCriterion where
  holds := fun {_} _ f => f 1 < f 0
  stable := fun φ _ => φ.lt_iff_lt

/-- **Der Klassifikationssatz.** Trennen zwei Kriterien die verschiedenwertigen
Belegungen ausschliessend und vollständig, und ist keines von beiden auf den
zwei Musterbelegungen leer, so **ist** das Paar das Ordnungspaar — in einer der
beiden Benennungen, und in keiner dritten Gestalt.

Damit ist gemessen, was sonst nur behauptet werden könnte: über zwei Stellen und
einem blossen `LinearOrder` gibt es kein Kriterium, das die Alternative trennt,
**ohne** die Ordnungsrelation umzubenennen. Die Nichtentartungs-Voraussetzungen
stehen an den zwei Musterbelegungen; nach `holds_iff_upPair` und
`holds_iff_downPair` ist das keine Einschränkung. -/
theorem separation_is_the_order (S O : OccupancyCriterion)
    (hex : ∀ (α : Type) [LinearOrder α] (f : Fin 2 → α), f 0 ≠ f 1 →
      ¬ (S.holds f ∧ O.holds f))
    (htot : ∀ (α : Type) [LinearOrder α] (f : Fin 2 → α), f 0 ≠ f 1 →
      S.holds f ∨ O.holds f)
    (hS : S.holds upPair ∨ S.holds downPair)
    (hO : O.holds upPair ∨ O.holds downPair) :
    (∀ (α : Type) [LinearOrder α] (f : Fin 2 → α), f 0 ≠ f 1 →
        (S.holds f ↔ RisingOccupancy f) ∧ (O.holds f ↔ FallingOccupancy f))
    ∨ (∀ (α : Type) [LinearOrder α] (f : Fin 2 → α), f 0 ≠ f 1 →
        (S.holds f ↔ FallingOccupancy f) ∧ (O.holds f ↔ RisingOccupancy f)) := by
  have hUne : (upPair 0 : Fin 2) ≠ upPair 1 := by decide
  have hDne : (downPair 0 : Fin 2) ≠ downPair 1 := by decide
  have hexU := hex (Fin 2) upPair hUne
  have hexD := hex (Fin 2) downPair hDne
  rcases htot (Fin 2) upPair hUne with hSU | hOU
  · have hOU : ¬ O.holds upPair := fun h => hexU ⟨hSU, h⟩
    have hOD : O.holds downPair := hO.resolve_left hOU
    have hSD : ¬ S.holds downPair := fun h => hexD ⟨h, hOD⟩
    left
    intro α _ f hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact ⟨(holds_iff_upPair S hlt).trans (iff_of_true hSU hlt),
        (holds_iff_upPair O hlt).trans (iff_of_false hOU (asymm hlt))⟩
    · exact ⟨(holds_iff_downPair S hgt).trans (iff_of_false hSD (asymm hgt)),
        (holds_iff_downPair O hgt).trans (iff_of_true hOD hgt)⟩
  · have hSU : ¬ S.holds upPair := fun h => hexU ⟨h, hOU⟩
    have hSD : S.holds downPair := hS.resolve_left hSU
    have hOD : ¬ O.holds downPair := fun h => hexD ⟨hSD, h⟩
    right
    intro α _ f hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact ⟨(holds_iff_upPair S hlt).trans (iff_of_false hSU (asymm hlt)),
        (holds_iff_upPair O hlt).trans (iff_of_true hOU hlt)⟩
    · exact ⟨(holds_iff_downPair S hgt).trans (iff_of_true hSD hgt),
        (holds_iff_downPair O hgt).trans (iff_of_false hOD (asymm hgt))⟩

/-- Die Klasse ist nicht leer, und der Klassifikationssatz ist nicht
gegenstandslos: das Ordnungspaar erfüllt seine vier Voraussetzungen. -/
theorem order_pair_is_separating :
    (∀ (α : Type) [LinearOrder α] (f : Fin 2 → α), f 0 ≠ f 1 →
        ¬ (risingCriterion.holds f ∧ fallingCriterion.holds f))
    ∧ (∀ (α : Type) [LinearOrder α] (f : Fin 2 → α), f 0 ≠ f 1 →
        risingCriterion.holds f ∨ fallingCriterion.holds f)
    ∧ (risingCriterion.holds upPair ∨ risingCriterion.holds downPair)
    ∧ (fallingCriterion.holds upPair ∨ fallingCriterion.holds downPair) :=
  ⟨fun _ _ f _ => occupancy_exclusive f, fun _ _ _ h => occupancy_total h,
    Or.inl (show (upPair 0 : Fin 2) < upPair 1 by decide),
    Or.inr (show (downPair 1 : Fin 2) < downPair 0 by decide)⟩

/-! ## Teil 6 — Statement-Pins

Voller Wortlaut links, Satz rechts — jede Drift des *Statements* bricht den Bau. -/

-- STATEMENT-PIN
example {α β : Type} [DecidableEq α] [DecidableEq β] (f : Fin 2 → α) (g : Fin 2 → β)
    (hf : f 0 ≠ f 1) (hg : g 0 ≠ g 1) : canonicalize f = canonicalize g :=
  canonicalize_eq_of_ne hf hg

-- STATEMENT-PIN
example {α : Type} [LinearOrder α] (f : Fin 2 → α) (h : f 0 ≠ f 1) :
    ¬ (f 0 < f 1 ∧ f 1 < f 0) ∧ (f 0 < f 1 ∨ f 1 < f 0) :=
  ⟨occupancy_exclusive f, occupancy_total h⟩

-- STATEMENT-PIN
example {α : Type} [LinearOrder α] (f : Fin 2 → α) (h : f 0 = f 1) :
    ¬ (f 0 < f 1) ∧ ¬ (f 1 < f 0) :=
  no_occupancy_of_eq h

-- STATEMENT-PIN
example (S O : OccupancyCriterion)
    (hex : ∀ (α : Type) [LinearOrder α] (f : Fin 2 → α), f 0 ≠ f 1 →
      ¬ (S.holds f ∧ O.holds f))
    (htot : ∀ (α : Type) [LinearOrder α] (f : Fin 2 → α), f 0 ≠ f 1 →
      S.holds f ∨ O.holds f)
    (hS : S.holds upPair ∨ S.holds downPair)
    (hO : O.holds upPair ∨ O.holds downPair) :
    (∀ (α : Type) [LinearOrder α] (f : Fin 2 → α), f 0 ≠ f 1 →
        (S.holds f ↔ f 0 < f 1) ∧ (O.holds f ↔ f 1 < f 0))
    ∨ (∀ (α : Type) [LinearOrder α] (f : Fin 2 → α), f 0 ≠ f 1 →
        (S.holds f ↔ f 1 < f 0) ∧ (O.holds f ↔ f 0 < f 1)) :=
  separation_is_the_order S O hex htot hS hO

/-! ## Teil 7 — die Axiom-Wachen (Ist-gebunden)

Ist-Ausgabe des grünen Builds. `Classical.choice` in den ersten beiden Sätzen
ist geerbt, siehe Kopf. -/

/-- info: 'Reformulation.Kenogram.OccupancySeparation.canonicalize_eq_of_ne' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms canonicalize_eq_of_ne

/-- info: 'Reformulation.Kenogram.OccupancySeparation.canonicalize_comp_swap' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms canonicalize_comp_swap

/-- info: 'Reformulation.Kenogram.OccupancySeparation.occupancy_exclusive' depends on axioms: [propext] -/
#guard_msgs in #print axioms occupancy_exclusive

/-- info: 'Reformulation.Kenogram.OccupancySeparation.occupancy_total' depends on axioms: [propext] -/
#guard_msgs in #print axioms occupancy_total

/-- info: 'Reformulation.Kenogram.OccupancySeparation.no_occupancy_of_eq' depends on axioms: [propext] -/
#guard_msgs in #print axioms no_occupancy_of_eq

/-- info: 'Reformulation.Kenogram.OccupancySeparation.both_cases_realized' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms both_cases_realized

/-- info: 'Reformulation.Kenogram.OccupancySeparation.holds_iff_upPair' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms holds_iff_upPair

/-- info: 'Reformulation.Kenogram.OccupancySeparation.holds_iff_downPair' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms holds_iff_downPair

/-- info: 'Reformulation.Kenogram.OccupancySeparation.holds_iff_flatPair' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms holds_iff_flatPair

/-- info: 'Reformulation.Kenogram.OccupancySeparation.separation_is_the_order' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms separation_is_the_order

/-- info: 'Reformulation.Kenogram.OccupancySeparation.order_pair_is_separating' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms order_pair_is_separating

end Reformulation.Kenogram.OccupancySeparation
