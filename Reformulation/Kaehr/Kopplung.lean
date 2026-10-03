import Reformulation.Kenogram.Basic
import Reformulation.Proemial.IntransitivityDifferential

/-!
# Reformulation.Kaehr.Kopplung — Kaehrs Kopplung, verifiziert

**Was das Modul ist (CLAUDE.md §4):** ERTRAG im Kleinen. Kaehrs Behauptungen von 1993 über die
Kopplung zweier Anwendungen werden als Sätze nachprüfbar: die Zählung, die These „nicht aus der
Termstruktur" und die Stufung. Mathematisch sind die Sätze klein (K7).

## K1 · Herkunft, Zeile für Zeile

```text
NACH KAEHR   die Kopplung zweier Anwendungen (f x), (g y):  gekoppelt (x und g dasselbe Objekt),
             geschlossen (zudem y und f), selbstgekoppelt (alle vier) — Mahler & Kaehr 1993,
             S. 226, 231;  die Zählung 15/5/2/1 auf den Mustern der Länge 4 — S. 233 f.;
             die These, die Art sei "nicht aus der Termstruktur sondern nur aus der Struktur von
             Zeigergleichheit" zu ermitteln — S. 233 f.;  Disseminatorik 1993, S. 15;  die
             Dissertation von 1978 nach Kaehrs Verweis S. 5 f., NICHT GELESEN
GÜNTHER      der Index R(i+1) über x(i) der offenen Kette — C&V S. 21 / E&W S. 27
UNSER        die Lean-Gestalt (Terme, Knoten mit Kennung, Abwicklung mit Brennstoff), die Brücken
             K-B und K-B′, die Allgemeinheit von geschlossen_ungestuft und offene_kette_k, der
             Rangsatz rang_zyklenfrei (Proemial/IntransitivityDifferential, Kopf §(6))
```

## K2 · Die Grenze (B)

Die Selbigkeit IST hier die Kennung `Fin k`: vorausgesetzt, nicht gewonnen. So sagen es
Mahler & Kaehr von ihrem eigenen Modell (S. 235 f.). Der Bau überwindet diese Grenze nicht;
er macht sie nachprüfbar.

## K3 · Kaehrs Gestalt einer Kopplung

Was hier steht, ist Kaehrs Gestalt einer Kopplung und kein Satz über Günthers Relation vor
jeder Trennung von Operator und Operand (Mahler & Kaehr S. 236, mit Günther C&V S. 33 der
deutschen Fassung zitiert). Kein Name, Kopf oder Titel dieses Verzeichnisses trägt Günthers
Wort für jene Relation (Register KA21 (d), Custos KC1 (b)).

## K4 · Die zwei Grenzen nicht verwechseln

`kopplung_nicht_aus_abwicklung` zeigt die Grenze (B), Gleichheit gegen Selbigkeit, IN DIESEM
MODELL: Die Terme bestimmen nicht, ob zwei Stellen dasselbe Vorkommen sind; das sagt nur die
Kennung. Er zeigt NICHT die Grenze (A) der Extension und sagt nichts über Lean im
Allgemeinen. Für (A) siehe `Proemial/ExtensionalCollapse.lean`, `higher_sees_only_table`.

## K5 · Gestuft und ungestuft — die Differenz Günther/Kaehr

Die offene Kette ist gestuft (`offene_kette_k`), wie Günthers Index; die geschlossene
Kopplung ist ungestuft (`geschlossen_ungestuft`), Kaehrs „neben-geordnet" (Kaehr 1990,
S. 11). Dass das die Differenz zwischen beiden IST, ist ZUORDNUNG. Die Sätze sind UNSER,
die zwei Formen NACH KAEHR. `geschlossen_ungestuft` gilt allgemein: Jede geschlossene
Kopplung in jedem Graphen macht ihn ungestuft. `offene_kette_k` dagegen spricht über die
Kette selbst. Eine offene Kopplung in einem Graphen mit anderen Zyklen ist nicht gestuft.

*Zum Rangsatz.* `gestuft G` sagt: `ueber G` hat eine Rangfunktion. Nach `rang_zyklenfrei`
ist das dasselbe wie Zyklenfreiheit. **Im Term verbraucht dieses Modul den Rangsatz nicht.**
`geschlossen_ungestuft` ist direkt bewiesen (zwei Ungleichungen), weil der Weg über
`rang_zyklenfrei` bei `V = Fin k` über `Fin.fintype` `Classical.choice` zöge (gemessen
3.10.2026, Mathlib 83a5988; Kopf §(6) von IntransitivityDifferential). Der Import steht für
die Zusammengehörigkeit, die der Kopf dort nennt (Custos KC2).

## K6 · Die Choice-Stellen, begründet

Choice tragen genau zwei Satzgruppen, beide geerbt:
* `art_nur_am_muster` (K-I) aus `canonicalize`. Bekannt: „alles, was `canonicalize` berührt,
  erbt `Classical.choice`" (Kopf von `Proemial/TwoPlaceOccupancy.lean`).
* K-B′ (`normalform_mem`, `normalform_stelle_iff` und die drei `…_normalform`) aus
  `relabel_getElem?_eq_iff` bzw. `mem_rgsList_iff` (`Kenogram/Basic`).
Alle übrigen Sätze sind choice-frei, und der Rangsatz ist es auch.

## K7 · Das Gewicht

Die Sätze sind mathematisch klein. Ihr Gewicht ist, dass sie Kaehrs Behauptungen von 1993
als Sätze nachprüfbar machen. Der Kopf sagt das, statt es zu verschweigen (Plan R3).

## Stufen (Ertrags-Skala, CLAUDE.md §4)

```text
kopplung_zaehlung              EICHUNG an Mahler & Kaehr 1993, S. 233 f.
art_nur_am_muster              INSTANZIIERUNG von canonicalize_eq_iff (K-I)
gekoppelt_iff, geschlossen_iff, selbstgekoppelt_iff        FOLGERUNG, dünn (K-B)
normalform_stelle_iff, normalform_mem, …_normalform        ZUSAMMENSTELLUNG (K-B′:  relabel + Bestand)
kopplung_nicht_aus_abwicklung  EICHUNG an Mahler & Kaehr S. 233 f. ("nicht aus der Termstruktur")
geschlossen_ungestuft          FOLGERUNG, über Kaehrs Begriff, allgemein
offene_kette_k                 FOLGERUNG:  Günthers Index für offene Ketten jeder Länge
kette_zwei, offene_kette_gestuft  EICHUNG an Mahler & Kaehr Abb. 3.1 / Kaehr 1982 S. 28
```

0 Sorries. Gemessene Profile verbatim in den Wachen am Dateiende.
-/

namespace Reformulation.Kaehr

open Reformulation.Kenogram

/-! ## A1 — das Modell -/

/-- Terme mit Anwendung -/
inductive Tm | var (n : ℕ) | app (a b : Tm) deriving DecidableEq

/-- ein Knoten: ein Etikett, oder die Anwendung zweier Knoten, über ihre KENNUNGEN -/
inductive Knoten (k : ℕ) | var (n : ℕ) | app (op arg : Fin k) deriving DecidableEq

/-- ein Graph: jede Kennung trägt einen Knoten. Die Selbigkeit ist die Kennung (K2). -/
abbrev Graph (k : ℕ) := Fin k → Knoten k

/-- die Abwicklung zum Term, mit Brennstoff -/
def abwicklung {k : ℕ} (G : Graph k) : ℕ → Fin k → Tm
  | 0, _ => .var 0
  | fuel + 1, i => match G i with
    | .var n => .var n
    | .app o a => .app (abwicklung G fuel o) (abwicklung G fuel a)

/-- `i` ist die Anwendung (f x) -/
def anw {k : ℕ} (G : Graph k) (i f x : Fin k) : Prop := G i = .app f x

/-- (f x) und (g y) sind gekoppelt:  x und g dasselbe Objekt (Mahler & Kaehr S. 231) -/
def gekoppelt {k : ℕ} (G : Graph k) (a b : Fin k) : Prop :=
  match G a, G b with
  | .app _ x, .app g _ => x = g
  | _, _ => False

/-- geschlossen:  zudem y und f dasselbe Objekt -/
def geschlossen {k : ℕ} (G : Graph k) (a b : Fin k) : Prop :=
  match G a, G b with
  | .app f x, .app g y => x = g ∧ y = f
  | _, _ => False

/-- selbstgekoppelt:  alle vier dasselbe Objekt -/
def selbstgekoppelt {k : ℕ} (G : Graph k) (a b : Fin k) : Prop :=
  match G a, G b with
  | .app f x, .app g y => f = x ∧ x = g ∧ g = y
  | _, _ => False

instance {k : ℕ} (G : Graph k) (a b : Fin k) : Decidable (gekoppelt G a b) := by
  unfold gekoppelt; split <;> infer_instance
instance {k : ℕ} (G : Graph k) (a b : Fin k) : Decidable (geschlossen G a b) := by
  unfold geschlossen; split <;> infer_instance
instance {k : ℕ} (G : Graph k) (a b : Fin k) : Decidable (selbstgekoppelt G a b) := by
  unfold selbstgekoppelt; split <;> infer_instance

/-- die vier Stellen (f, x, g, y) zweier Anwendungen, in Kaehrs Reihenfolge (S. 231) -/
def stellenmuster {k : ℕ} (f x g y : Fin k) : Fin 4 → Fin k
  | ⟨0, _⟩ => f
  | ⟨1, _⟩ => x
  | ⟨2, _⟩ => g
  | ⟨3, _⟩ => y

/-! ## A2 — die Gestalt -/

/-- die Stellenbedingungen auf Listen:  Stelle 1 = Stelle 2 -/
def istGekoppelt (l : List ℕ) : Bool := l.getD 1 0 == l.getD 2 0
/-- zudem Stelle 3 = Stelle 0 -/
def istGeschlossen (l : List ℕ) : Bool := istGekoppelt l && l.getD 3 0 == l.getD 0 0
/-- alle vier gleich -/
def istSelbstgekoppelt (l : List ℕ) : Bool :=
  l.getD 0 0 == l.getD 1 0 && l.getD 1 0 == l.getD 2 0 && l.getD 2 0 == l.getD 3 0

/-- K-Z:  15 Muster der Länge 4, davon 5 gekoppelt, 2 geschlossen, 1 selbstgekoppelt
    (Mahler & Kaehr 1993, S. 233 f.). -/
theorem kopplung_zaehlung :
    (rgsList 4).length = 15 ∧ ((rgsList 4).filter istGekoppelt).length = 5 ∧
    ((rgsList 4).filter istGeschlossen).length = 2 ∧
    ((rgsList 4).filter istSelbstgekoppelt).length = 1 := by decide

/-- K-I:  die Art einer Kopplung hängt nur am Stellenmuster, invariant unter jeder Umbenennung
    der Kennungen. -/
theorem art_nur_am_muster {α β : Type*} [DecidableEq α] [DecidableEq β]
    (f : Fin 4 → α) (g : Fin 4 → β) (h : canonicalize f = canonicalize g) :
    (f 1 = f 2 ↔ g 1 = g 2) ∧ (f 0 = f 3 ↔ g 0 = g 3) :=
  ⟨(canonicalize_eq_iff f g).mp h 1 2, (canonicalize_eq_iff f g).mp h 0 3⟩

/-- K-B:  die Brücke vom Graphen zum Muster, gekoppelt -/
theorem gekoppelt_iff {k : ℕ} {G : Graph k} {a b f x g y : Fin k}
    (ha : anw G a f x) (hb : anw G b g y) :
    gekoppelt G a b ↔ stellenmuster f x g y 1 = stellenmuster f x g y 2 := by
  unfold anw at ha hb; simp only [gekoppelt, ha, hb]; rfl

/-- K-B, geschlossen -/
theorem geschlossen_iff {k : ℕ} {G : Graph k} {a b f x g y : Fin k}
    (ha : anw G a f x) (hb : anw G b g y) :
    geschlossen G a b ↔ stellenmuster f x g y 1 = stellenmuster f x g y 2 ∧
      stellenmuster f x g y 3 = stellenmuster f x g y 0 := by
  unfold anw at ha hb; simp only [geschlossen, ha, hb]; rfl

/-- K-B, selbstgekoppelt -/
theorem selbstgekoppelt_iff {k : ℕ} {G : Graph k} {a b f x g y : Fin k}
    (ha : anw G a f x) (hb : anw G b g y) :
    selbstgekoppelt G a b ↔ stellenmuster f x g y 0 = stellenmuster f x g y 1 ∧
      stellenmuster f x g y 1 = stellenmuster f x g y 2 ∧
      stellenmuster f x g y 2 = stellenmuster f x g y 3 := by
  unfold anw at ha hb; simp only [selbstgekoppelt, ha, hb]; rfl

/-- die Normalform des Stellenmusters zweier Anwendungen -/
def normalform {k : ℕ} (f x g y : Fin k) : List ℕ := relabel (List.ofFn (stellenmuster f x g y))

/-- K-B′:  die Normalform ist eines der 15 Muster, die K-Z zählt -/
theorem normalform_mem {k : ℕ} (f x g y : Fin k) : normalform f x g y ∈ rgsList 4 :=
  mem_rgsList_iff.mpr ⟨by rw [normalform, relabel_length, List.length_ofFn], relabel_isRGS _⟩

/-- K-B′:  an der Normalform sind dieselben Stellen gleich wie im Muster -/
theorem normalform_stelle_iff {k : ℕ} (f x g y : Fin k) (i j : Fin 4) :
    (normalform f x g y).getD i 0 = (normalform f x g y).getD j 0 ↔
      stellenmuster f x g y i = stellenmuster f x g y j := by
  have hl : (normalform f x g y).length = 4 := by
    rw [normalform, relabel_length, List.length_ofFn]
  have h := relabel_getElem?_eq_iff (List.ofFn (stellenmuster f x g y)) i j
  rw [List.getElem?_ofFn, List.getElem?_ofFn] at h
  simp only [i.isLt, j.isLt, dite_true, Option.some.injEq, Fin.eta] at h
  rw [← h]
  simp only [normalform, List.getD_eq_getElem?_getD]
  rw [List.getElem?_eq_getElem (by rw [← normalform, hl]; exact i.isLt),
    List.getElem?_eq_getElem (by rw [← normalform, hl]; exact j.isLt)]
  simp only [Option.getD_some, Option.some.injEq]

/-- K-B′:  gekoppelt genau dann, wenn die Normalform als gekoppelt gezählt wird -/
theorem gekoppelt_normalform {k : ℕ} {G : Graph k} {a b f x g y : Fin k}
    (ha : anw G a f x) (hb : anw G b g y) :
    gekoppelt G a b ↔ istGekoppelt (normalform f x g y) = true := by
  rw [gekoppelt_iff ha hb, ← normalform_stelle_iff f x g y 1 2]
  simp only [istGekoppelt, beq_iff_eq]; rfl

/-- K-B′:  geschlossen genau dann, wenn die Normalform als geschlossen gezählt wird -/
theorem geschlossen_normalform {k : ℕ} {G : Graph k} {a b f x g y : Fin k}
    (ha : anw G a f x) (hb : anw G b g y) :
    geschlossen G a b ↔ istGeschlossen (normalform f x g y) = true := by
  rw [geschlossen_iff ha hb, ← normalform_stelle_iff f x g y 1 2,
    ← normalform_stelle_iff f x g y 3 0]
  simp only [istGeschlossen, istGekoppelt, Bool.and_eq_true, beq_iff_eq]; rfl

/-- K-B′:  selbstgekoppelt genau dann, wenn die Normalform als selbstgekoppelt gezählt wird -/
theorem selbstgekoppelt_normalform {k : ℕ} {G : Graph k} {a b f x g y : Fin k}
    (ha : anw G a f x) (hb : anw G b g y) :
    selbstgekoppelt G a b ↔ istSelbstgekoppelt (normalform f x g y) = true := by
  rw [selbstgekoppelt_iff ha hb, ← normalform_stelle_iff f x g y 0 1,
    ← normalform_stelle_iff f x g y 1 2, ← normalform_stelle_iff f x g y 2 3]
  simp only [istSelbstgekoppelt, Bool.and_eq_true, beq_iff_eq, and_assoc]; rfl

/-! ## A3 (1) — die Kopplung folgt nicht aus der Abwicklung -/

/-- x und g sind EIN Knoten:  0 = f, 1 = x = g, 2 = y, 3 = (f x), 4 = (g y) -/
def beispiel_geteilt : Graph 5
  | ⟨0, _⟩ => .var 0
  | ⟨1, _⟩ => .var 1
  | ⟨2, _⟩ => .var 2
  | ⟨3, _⟩ => .app 0 1
  | ⟨4, _⟩ => .app 1 2

/-- wie `beispiel_geteilt`, aber g = Knoten 5, ein EIGENER Knoten mit demselben Etikett -/
def beispiel_getrennt : Graph 6
  | ⟨0, _⟩ => .var 0
  | ⟨1, _⟩ => .var 1
  | ⟨2, _⟩ => .var 2
  | ⟨3, _⟩ => .app 0 1
  | ⟨4, _⟩ => .app 5 2
  | ⟨5, _⟩ => .var 1

/-- A3 (1):  für JEDEN Brennstoff dieselben Terme an beiden Anwendungen, und doch ist die eine
    Kopplung gekoppelt und die andere nicht (Mahler & Kaehr S. 233 f.;  K4). -/
theorem kopplung_nicht_aus_abwicklung :
    (∀ n, abwicklung beispiel_geteilt n 3 = abwicklung beispiel_getrennt n 3) ∧
    (∀ n, abwicklung beispiel_geteilt n 4 = abwicklung beispiel_getrennt n 4) ∧
    gekoppelt beispiel_geteilt 3 4 ∧ ¬ gekoppelt beispiel_getrennt 3 4 := by
  refine ⟨?_, ?_, by decide, by decide⟩
  · intro n
    match n with
    | 0 => rfl
    | 1 => rfl
    | _ + 2 => rfl
  · intro n
    match n with
    | 0 => rfl
    | 1 => rfl
    | _ + 2 => rfl

/-! ## A3 (2) — geschlossen heisst ungestuft -/

/-- `o` steht als Operator über dem Operanden `a` -/
def ueber {k : ℕ} (G : Graph k) (o a : Fin k) : Prop := ∃ i, G i = .app o a

/-- gestuft:  `ueber G` hat eine Rangfunktion (vgl. `rang_zyklenfrei`, K5) -/
def gestuft {k : ℕ} (G : Graph k) : Prop := ∃ ρ : Fin k → ℕ, ∀ o a, ueber G o a → ρ a < ρ o

/-- A3 (2) (c):  JEDE geschlossene Kopplung macht ihren Graphen ungestuft — f über x und x über f -/
theorem geschlossen_ungestuft {k : ℕ} (G : Graph k) (a b : Fin k) (h : geschlossen G a b) :
    ¬ gestuft G := by
  rintro ⟨ρ, hρ⟩
  unfold geschlossen at h
  split at h
  · rename_i f x g y ha hb
    obtain ⟨hxg, hyf⟩ := h
    have h1 := hρ f x ⟨a, ha⟩
    have h2 := hρ g y ⟨b, hb⟩
    rw [← hxg, hyf] at h2
    exact Nat.lt_asymm h1 h2
  · exact h.elim

/-- die offene Kette der Länge `m`:  Knoten 0..m die Operatoren R_m..R_0 (Etikett `m − i`),
    Knoten m+1+j die Anwendung (R_{m−j} R_{m−j−1}) — der Operand x_i ist R_i selbst -/
def kette (m : ℕ) : Graph (2 * m + 1) := fun i =>
  if h : m < i.val then .app ⟨i.val - m - 1, by omega⟩ ⟨i.val - m, by omega⟩
  else .var (m - i.val)

/-- A3 (2) (e):  die offene Kette JEDER Länge ist gestuft — Günthers Index -/
theorem offene_kette_k (m : ℕ) : gestuft (kette m) := by
  refine ⟨fun i => 2 * m + 1 - i.val, ?_⟩
  rintro o a ⟨i, hi⟩
  unfold kette at hi
  split at hi
  · simp only [Knoten.app.injEq] at hi
    obtain ⟨rfl, rfl⟩ := hi
    show 2 * m + 1 - (i.val - m) < 2 * m + 1 - (i.val - m - 1)
    have := i.isLt
    omega
  · simp only [reduceCtorEq] at hi

/-- die offene Kette aus Mahler & Kaehr Abb. 3.1:  0 = R2, 1 = x1 ≡ R1, 2 = x0,
    3 = (R2 x1), 4 = (R1 x0) -/
def offeneKette : Graph 5
  | ⟨0, _⟩ => .var 2
  | ⟨1, _⟩ => .var 1
  | ⟨2, _⟩ => .var 0
  | ⟨3, _⟩ => .app 0 1
  | ⟨4, _⟩ => .app 1 2

/-- die Tafel ist die Kette der Länge 2 -/
theorem kette_zwei : kette 2 = offeneKette := by
  funext i; match i with | 0 | 1 | 2 | 3 | 4 => rfl

/-- A3 (2) (d):  die offene Kette aus Abb. 3.1 ist gestuft (Eichung; Instanz von (e)) -/
theorem offene_kette_gestuft : gestuft offeneKette := kette_zwei ▸ offene_kette_k 2

end Reformulation.Kaehr

/-! ## Axiom-Stand — als Regressions-Wachen gesetzt (alle Sätze des Moduls) -/

/-- info: 'Reformulation.Kaehr.kopplung_zaehlung' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Kaehr.kopplung_zaehlung

/-- info: 'Reformulation.Kaehr.art_nur_am_muster' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Kaehr.art_nur_am_muster

/-- info: 'Reformulation.Kaehr.gekoppelt_iff' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Kaehr.gekoppelt_iff

/-- info: 'Reformulation.Kaehr.geschlossen_iff' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Kaehr.geschlossen_iff

/-- info: 'Reformulation.Kaehr.selbstgekoppelt_iff' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Kaehr.selbstgekoppelt_iff

/-- info: 'Reformulation.Kaehr.normalform_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Kaehr.normalform_mem

/-- info: 'Reformulation.Kaehr.normalform_stelle_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Kaehr.normalform_stelle_iff

/-- info: 'Reformulation.Kaehr.gekoppelt_normalform' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Kaehr.gekoppelt_normalform

/-- info: 'Reformulation.Kaehr.geschlossen_normalform' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Kaehr.geschlossen_normalform

/-- info: 'Reformulation.Kaehr.selbstgekoppelt_normalform' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Kaehr.selbstgekoppelt_normalform

/-- info: 'Reformulation.Kaehr.kopplung_nicht_aus_abwicklung' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Kaehr.kopplung_nicht_aus_abwicklung

/-- info: 'Reformulation.Kaehr.geschlossen_ungestuft' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Kaehr.geschlossen_ungestuft

/-- info: 'Reformulation.Kaehr.offene_kette_k' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Kaehr.offene_kette_k

/-- info: 'Reformulation.Kaehr.kette_zwei' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Kaehr.kette_zwei

/-- info: 'Reformulation.Kaehr.offene_kette_gestuft' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Kaehr.offene_kette_gestuft
