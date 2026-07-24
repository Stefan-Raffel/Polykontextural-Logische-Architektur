import Mathlib.ModelTheory.Substructures

/-!
# Proemial.TransjunctionCloneBound — die Transjunktion als bewiesene Klon-Schranke (D)

Diese Datei legt **D** nieder: die Transjunktion als bewiesene Klon- bzw.
Definierbarkeits-Schranke. Eine konkrete Transjunktion `T` auf `Fin 3` liegt **nicht** im Klon, der von
den intra-kontexturalen Junktoren `{∧, ∨, ¬}` erzeugt wird. Das trägt die *negative*
Seite der Akkretion (Horistês: Transzendenz — die Operation gehört dem intra-kontexturalen
System nicht an) deutungsdicht, ohne `True`-Feld.

## Verschaltung, nicht Eigenbau

Der harte Teil ist in Mathlib bereits bewiesen und wird konsumiert:

* `FirstOrder.Language` (`Functions : ℕ → Type`) — die Junktoren-Basis.
* `Language.Term` (`var` = Projektion, `func` = Komposition) — die erzeugten Operationen.
* `Structure.funMap`, `Term.realize` — `min`/`max`/`¬` auf `Fin 3`.
* `ClosedUnder f s` — das Erhaltungs-Prädikat (`preserves f R`, unär).
* `Substructure` (Feld `fun_mem`) — „`R` erhält die ganze Basis".
* `Term.realize_mem` — **das Erhaltungs-Lemma per Term-Induktion (der harte Teil, frei)**:
  jeder Term erhält `R`, sofern die Basis `R` erhält. Die Induktion ist schon geführt;
  `T_not_in_clone` konsumiert dieses Lemma, baut es nicht nach.

D ist damit strukturanalog zur C-Soundness auf `rgs_unique_of_pattern`.

## Die `T`-Vollbelegung (K-D.3, am Term erprobt)

Gewählt: `T a b = if (a, b) = (0, 2) then 1 else max a b` — die *asymmetrische* Form
(rejektiv nur am Punkt `(0,2)`), nicht die symmetrische (rejektiv auch bei `(2,0)`).
Begründung: `T` ist die minimale Abweichung von `max` (dem intra-kontexturalen `∨`) — auf
allen Argumenten klassisch (`= ∨`), rejektiv allein an dem einen überschreitenden Punkt.
Das ist die *plausibelste* Transjunktion: die Rejektion sitzt genau dort, wo die zwei
unterschiedlichen kontexturalen Werte (`0 ≠ 2`) zusammentreffen, und transzendiert in den
dritten, rejektiven Wert `1`. Der rejektive Kern `T 0 2 = 1` ist die einzige für die
Schranke nötige Festlegung; die symmetrische Form wurde verworfen, weil sie nichts
hinzufügt und die Schranke nicht trägt, was die asymmetrische nicht schon trägt.

## Die Deutungs-Tests (K-D.4) als Term-Beleg der Transzendenz

Die kontexturale Deutung der Schranke („`T` transzendiert die Kontextur") wird *am Term
geprüft*, nicht behauptet:

* **Test 1 (`test1_*`):** `{0,2}` unter `{min, max, ¬}` ist isomorph zur klassischen
  zweiwertigen Booleschen Algebra (`0 ↦ falsch`, `2 ↦ wahr`; `min ↦ ∧`, `max ↦ ∨`,
  `¬ ↦ not`) — expliziter Iso `phi` mit Operations-Verträglichkeit, Injektivität und
  Surjektivität. Die Basis *ist* die intra-kontexturale klassische Logik *einer* Kontextur.
* **Test 2a (`term_preserves_contextur` + `T_leaves_contextur`):** auf `{0,2}` greift
  *keine* Schranke — jeder Term erhält `{0,2}` (das ist `Term.realize_mem`), während `T`
  die Kontextur am Punkt `(0,2)` *verlässt* (`T 0 2 = 1 ∉ {0,2}`). Die Transzendenz ist
  genau das Verlassen, nicht eine Schranke *innerhalb* der Kontextur.
* **Test 2b (`const_not_closedUnder` + `no_substructure_with_const`):** erweitert man die
  Basis um die `1`-produzierende Konstante (Sprache `L'`), ist `{0,2}` keine Substruktur
  mehr und die Schranke verschwindet. Die Schranke hängt an der Kontextur-Treue der Basis,
  nicht an einem Artefakt von `R`. Das *ist* zugleich die Konstanten-Entscheidung K-D.2:
  keine `1`-Konstante in der Basis.

## Die positive Seite (nicht im Korpus, K-D.5)

D trägt die **Transzendenz**-Seite (beweisbar, `T_not_in_clone`). Die **Neuheits**-Seite
(`T` „setzt Neues" im güntherschen Sinn) trägt D **nicht**: Nicht-Erzeugbarkeit ist nicht
Produktion des Neuen. Sie erscheint nicht im Korpus — kein `axiom`, kein `True`-Feld, kein
getarntes Theorem. Sie ist eine hermeneutische Aussage über den Begriff, hier nicht
formalisiert und (in dieser Lesart) nicht formalisierbar; ein `axiom` ohne fassbaren Inhalt
wäre selbst eine Über-Markierung. Hier endet das Theorem, dort begänne die Setzung.

Für die *Schranke* `T_not_in_clone` allein ist höher-stellige Pol-Inv- bzw. Klon-Theorie
*nicht* nötig: die unäre `R = {0,2}` genügt. Für die *Verortung* auf Klon-Ebene (Teil 7) führt
das Modul dagegen eine **binäre** Invariante `ρ*` (Substruktur des Produkts `Fin 3 × Fin 3`).
Vorhanden in Mathlib und konsumiert: `HomClass.realize_term` (die Term-Induktion, dort geführt)
und `Term.realize_mem`. *Nicht* vorhanden und daher selbst definiert: eine Produkt-Struktur
`L.Structure (M × N)` (in `ModelTheory/` liegt nur die Ultraprodukt-Instanz).
-/

open FirstOrder Language

namespace Reformulation.Proemial.TransjunctionCloneBound

/-! ## Teil 1 — Sprache und Struktur -/

/-- Die unäre Junktor-Basis: ein Symbol `¬`. -/
inductive UnaryFun
  | neg
  deriving DecidableEq

/-- Die binäre Junktor-Basis: zwei Symbole `∧`, `∨`. -/
inductive BinaryFun
  | and
  | or
  deriving DecidableEq

/-- Die Basis-Sprache `L`: `Functions 1 = {¬}`, `Functions 2 = {∧, ∨}`, sonst leer; keine
Relationen. `Language.mk₂` ist im Ziel-Commit nicht vorhanden — `L` wird direkt über
`Language` hand-definiert (K-D.2: keine Konstante in der Basis). -/
def L : Language where
  Functions := fun
    | 1 => UnaryFun
    | 2 => BinaryFun
    | _ => Empty
  Relations := fun _ => Empty

/-- Die ordnungsumkehrende Negation auf `Fin 3` (`0 ↦ 2, 1 ↦ 1, 2 ↦ 0`). -/
def negFin (a : Fin 3) : Fin 3 := ⟨2 - a.val, by omega⟩

/-- Die Interpretation: `∧ = min`, `∨ = max` (über `Fin 3`s `LinearOrder`), `¬ = negFin`. -/
instance struc : L.Structure (Fin 3) where
  funMap := fun {n} =>
    match n with
    | 1 => fun _ x => negFin (x 0)
    | 2 => fun f x => match f with
        | .and => min (x 0) (x 1)
        | .or => max (x 0) (x 1)
    | 0 => fun f _ => nomatch f
    | (_ + 3) => fun f _ => nomatch f
  RelMap := fun r _ => nomatch r

@[simp] lemma funMap_neg (x : Fin 1 → Fin 3) :
    @Structure.funMap L (Fin 3) _ 1 UnaryFun.neg x = negFin (x 0) := rfl

@[simp] lemma funMap_and (x : Fin 2 → Fin 3) :
    @Structure.funMap L (Fin 3) _ 2 BinaryFun.and x = min (x 0) (x 1) := rfl

@[simp] lemma funMap_or (x : Fin 2 → Fin 3) :
    @Structure.funMap L (Fin 3) _ 2 BinaryFun.or x = max (x 0) (x 1) := rfl

/-! ## Teil 2 — die Kontextur als Substruktur -/

/-- Mitgliedschaft in der Kontextur `{0,2}` als entscheidbare Disjunktion. -/
lemma mem_pair (a : Fin 3) : a ∈ ({0, 2} : Set (Fin 3)) ↔ a = 0 ∨ a = 2 := by
  simp [Set.mem_insert_iff, Set.mem_singleton_iff]

/-- Die Kontextur `{0,2}` als Substruktur von `Fin 3` über `L`: abgeschlossen unter jedem
Junktor-Symbol (`fun_mem` per Fall-Erprobung am Symbol, `decide` an den Werten). -/
def S : L.Substructure (Fin 3) where
  carrier := {0, 2}
  fun_mem := by
    intro n f
    match n, f with
    | 1, .neg =>
        intro x hx
        have h0 := (mem_pair _).1 (hx 0); rw [mem_pair]
        rcases h0 with h0 | h0 <;> simp only [funMap_neg, h0] <;> decide
    | 2, .and =>
        intro x hx
        have h0 := (mem_pair _).1 (hx 0); have h1 := (mem_pair _).1 (hx 1); rw [mem_pair]
        rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1 <;>
          simp only [funMap_and, h0, h1] <;> decide
    | 2, .or =>
        intro x hx
        have h0 := (mem_pair _).1 (hx 0); have h1 := (mem_pair _).1 (hx 1); rw [mem_pair]
        rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1 <;>
          simp only [funMap_or, h0, h1] <;> decide

/-- Mitgliedschaft in der Substruktur `S` als entscheidbare Disjunktion (defeq zu `mem_pair`). -/
lemma mem_S (a : Fin 3) : a ∈ S ↔ a = 0 ∨ a = 2 := mem_pair a

/-! ## Teil 3 — die Transjunktion und die Schranke -/

/-- Die Transjunktion `T` (K-D.3): klassisch (`= max`) überall, rejektiv (`= 1`) allein am
überschreitenden Punkt `(0, 2)`. -/
def T (a b : Fin 3) : Fin 3 := if a = 0 ∧ b = 2 then 1 else max a b

/-- Der rejektive Kern: `T` produziert am überschreitenden Punkt den dritten Wert. -/
theorem T_rejective : T 0 2 = 1 := by decide

/-- **Die Klon-Schranke (der tragende Satz, K-D / §II).** Es gibt keinen Term
`t : L.Term (Fin 2)`, dessen Realisierung die Transjunktion `T` ist — `T` liegt nicht im
von `{∧, ∨, ¬}` erzeugten Klon.

Beweis: angenommen `⟨t, ht⟩`. Mit `v₀ = ![0, 2]` (beide Werte in `S = {0,2}`) liefert
`Term.realize_mem` (das konsumierte Erhaltungs-Lemma) `t.realize v₀ ∈ S`. Nach `ht` ist
`t.realize v₀ = T 0 2 = 1`, aber `1 ∉ {0,2}`. Widerspruch. -/
theorem T_not_in_clone :
    ¬ ∃ t : L.Term (Fin 2), ∀ v : Fin 2 → Fin 3, t.realize v = T (v 0) (v 1) := by
  rintro ⟨t, ht⟩
  have hmem : t.realize (![0, 2]) ∈ S := by
    apply Term.realize_mem t (![0, 2])
    intro a
    rw [mem_S]
    revert a
    decide
  have hT : t.realize (![0, 2]) = (1 : Fin 3) := by rw [ht (![0, 2])]; decide
  rw [hT, mem_S] at hmem
  rcases hmem with h | h <;> exact absurd h (by decide)

/-- **Klon-Nichttrivialität (F-D.1).** Der erzeugte Klon ist *nicht* dürftig: `max` (das
intra-kontexturale `∨`) liegt drin, bezeugt durch den `∨`-Symbol-Term
`func .or ![var 0, var 1]`. Damit ist `T_not_in_clone` nachweislich eine gehaltvolle Aussage
über einen nicht-leeren Klon — die Schranke hängt nicht an einem leeren Klon. Das ist die
D-Entsprechung der C-Naht „Step nicht-vakuant". -/
theorem max_in_clone :
    ∃ t : L.Term (Fin 2), ∀ v : Fin 2 → Fin 3, t.realize v = max (v 0) (v 1) :=
  ⟨Term.func (l := 2) (BinaryFun.or : L.Functions 2) ![Term.var 0, Term.var 1], fun v => by
    simp [Term.realize]⟩

/-- **`T` ist die Beinahe-Operation (F-D.1, Schärfung).** `T` stimmt mit dem erzeugbaren
`max` *überall* überein außer am einen rejektiven Punkt `(0,2)`: die Abweichung vom Klon
sitzt an genau einem Argument. -/
theorem T_agrees_max_off_diagonal :
    ∀ a b : Fin 3, (a, b) ≠ (0, 2) → T a b = max a b := by decide

/-! ## Teil 4 — die Deutungs-Tests (§V), Term-Beleg der Transzendenz -/

/-- Der Iso `{0,2} → Bool` der Kontextur-Treue: `0 ↦ falsch`, `2 ↦ wahr`. -/
def phi (a : Fin 3) : Bool := decide (a = 2)

/-- **Test 1 (Werte):** `phi` bildet die zwei Kontextur-Werte korrekt ab. -/
theorem test1_values : phi 0 = false ∧ phi 2 = true := by decide

/-- **Test 1 (Verträglichkeit von `min`/`max`):** auf `{0,2}` ist `min ↦ ∧`, `max ↦ ∨`. -/
theorem test1_min_max (a b : Fin 3) (ha : a = 0 ∨ a = 2) (hb : b = 0 ∨ b = 2) :
    phi (min a b) = (phi a && phi b) ∧ phi (max a b) = (phi a || phi b) := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> decide

/-- **Test 1 (Verträglichkeit von `¬`):** auf `{0,2}` ist `negFin ↦ not`. -/
theorem test1_neg (a : Fin 3) (ha : a = 0 ∨ a = 2) : phi (negFin a) = !(phi a) := by
  rcases ha with rfl | rfl <;> decide

/-- **Test 1 (Injektivität):** `phi` ist auf `{0,2}` injektiv. -/
theorem test1_injective (a b : Fin 3) (ha : a = 0 ∨ a = 2) (hb : b = 0 ∨ b = 2)
    (h : phi a = phi b) : a = b := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> revert h <;> decide

/-- **Test 1 (Surjektivität):** `phi` trifft auf `{0,2}` jeden Wahrheitswert. Zusammen mit
`test1_injective` der Bijektions-Beleg: `{0,2}` *ist* die zweiwertige Boolesche Algebra. -/
theorem test1_surjective (c : Bool) : ∃ a : Fin 3, (a = 0 ∨ a = 2) ∧ phi a = c := by
  cases c with
  | false => exact ⟨0, Or.inl rfl, rfl⟩
  | true => exact ⟨2, Or.inr rfl, rfl⟩

/-- **Test 2a (keine Schranke innerhalb):** jeder Term erhält die Kontextur `{0,2}` — die
direkte Spezialisierung von `Term.realize_mem`. Innerhalb von `{0,2}` ist nichts blockiert;
ein Term verlässt `{0,2}` nie. -/
theorem term_preserves_contextur (t : L.Term (Fin 2)) (v : Fin 2 → Fin 3)
    (hv : ∀ i, v i = 0 ∨ v i = 2) : t.realize v = 0 ∨ t.realize v = 2 :=
  (mem_S _).1 (Term.realize_mem t v fun a => (mem_S _).2 (hv a))

/-- **Test 2a (das Verlassen):** `T` nimmt zwei Kontextur-Werte (`0, 2 ∈ {0,2}`) und
*verlässt* die Kontextur (`T 0 2 = 1 ∉ {0,2}`). Mit `term_preserves_contextur` zusammen:
die Schranke ist das *Verlassen*, nicht eine Schranke *innerhalb* der Kontextur. -/
theorem T_leaves_contextur :
    (0 : Fin 3) ∈ ({0, 2} : Set (Fin 3)) ∧ (2 : Fin 3) ∈ ({0, 2} : Set (Fin 3)) ∧
      T 0 2 ∉ ({0, 2} : Set (Fin 3)) := by
  refine ⟨(mem_pair _).2 (by decide), (mem_pair _).2 (by decide), ?_⟩
  rw [mem_pair]; decide

/-- Die um die `1`-produzierende Konstante erweiterte Sprache (`Functions 0 = {1}`). Dient
allein Test 2b: sie zerstört die Kontextur-Treue der Basis. -/
def L' : Language where
  Functions := fun
    | 0 => Unit
    | 1 => UnaryFun
    | 2 => BinaryFun
    | _ => Empty
  Relations := fun _ => Empty

/-- Interpretation für `L'`: wie `struc`, plus die Konstante `↦ 1`. -/
instance struc' : L'.Structure (Fin 3) where
  funMap := fun {n} =>
    match n with
    | 0 => fun _ _ => (1 : Fin 3)
    | 1 => fun _ x => negFin (x 0)
    | 2 => fun f x => match f with
        | .and => min (x 0) (x 1)
        | .or => max (x 0) (x 1)
    | (_ + 3) => fun f _ => nomatch f
  RelMap := fun r _ => nomatch r

/-- **Test 2b (Bruch der Kontextur-Treue):** `{0,2}` ist *nicht* abgeschlossen unter der
`1`-Konstante (denn `1 ∉ {0,2}`). -/
theorem const_not_closedUnder :
    ¬ ClosedUnder (L := L') (M := Fin 3) (n := 0) (() : L'.Functions 0)
        ({0, 2} : Set (Fin 3)) := by
  intro h
  have hmem : (1 : Fin 3) ∈ ({0, 2} : Set (Fin 3)) := h ![] (by intro i; exact i.elim0)
  rw [mem_pair] at hmem
  rcases hmem with h | h <;> exact absurd h (by decide)

/-- **Test 2b (die Schranke verschwindet):** über `L'` gibt es keine Substruktur mit
Träger `{0,2}` — die Voraussetzung von `Term.realize_mem` (Substruktur-Sein) fällt weg, und
mit ihr die Schranke. Die Schranke hängt an der Kontextur-Treue der Basis (K-D.2: keine
`1`-Konstante), nicht an einem Artefakt von `R`. -/
theorem no_substructure_with_const :
    ¬ ∃ S' : L'.Substructure (Fin 3), S'.carrier = ({0, 2} : Set (Fin 3)) := by
  rintro ⟨S', hS'⟩
  apply const_not_closedUnder
  have := S'.fun_mem (n := 0) (() : L'.Functions 0)
  rwa [hS'] at this

/-! ## Teil 6 — die Erhaltungs-Seite: `T` bricht genau eine der drei maximalen Grenzen

Der billige, sichere Teil des Klon-Verortungs-Befunds (Kairos K2), an den Term gebracht:
`T` liegt nicht *irgendwo* außerhalb des Klons, sondern **an einem benannten Ort**. `T`
erhält die beiden Invarianten mit Zentrum im mittleren Wert `1` — die Toleranz-Relation `ρ*`
(„nie beide Extreme zugleich") und die Fixpunkt-Invariante `{1}` — und verletzt allein die
Boolesche `{0,2}`. Die Basis-Operationen `min`, `max`, `negFin` erhalten alle drei. Alles
`decide`-bar (höchstens 81 Fälle).

**Wortlaut-Grenzen (Nicht-Söll, verbindlich — gehören in den Doc-String, nicht in eine
Fußnote):**

1. **Was hier steht, ist Generator-Ebene.** Aus „`min`, `max`, `negFin`, `T` erhalten `ρ*`"
   folgt für sich noch nicht, dass *jeder* Term aus diesen Operationen `ρ*` erhält — das ist
   die Term-Induktion. Sie ist **in Teil 7 geführt** (`tolerance_is_invariant` für `ρ*`,
   `term_preserves_one` für `{1}`), ohne eigene Induktion, durch Verschaltung von
   `HomClass.realize_term` und `Term.realize_mem`; für `{0,2}` trägt sie schon
   `term_preserves_contextur`. Die Klon-Ebene steht damit im Verortungs-Satz
   `term_clone_localization`.
2. **„Maximaler Klon" ist ein Literatur-Verweis, kein Theorem dieser Datei.** Bewiesen sind
   Reflexivität (`tol_refl`), Symmetrie (`tol_symm`) und die Zentralität von `1`
   (`tol_center_one`). Dass `Pol(ρ*)` deshalb nach der Standard-Klassifikation der maximalen
   Klone auf endlichen Mengen maximal *ist*, steht hier als **Verweis** (klar markiert),
   nicht als Satz und nicht als „bewiesen". Die Referenz härtet Hermeneutês vor jeder
   Außen-Verwendung.
3. **Keine Erschöpfungs-Behauptung.** Der Korpus sagt an keiner Stelle, `T` erzeuge „alles
   unterhalb" der beiden erhaltenen Grenzen. Diese Gleichheit ist bislang nur außerhalb des
   Korpus gerechnet und hier **nicht** Gegenstand.
-/

/-- Die Toleranz-Relation `ρ*` als Bool-Träger: `false` genau an den beiden Extrem-Paaren
`(0,2)` und `(2,0)`. Bool-getragen, damit `Decidable` ohne Instanz-Bastelei greift. -/
def tolB (x y : Fin 3) : Bool := !((x == 0 && y == 2) || (x == 2 && y == 0))

/-- `ρ*(x, y)` — „nie beide Extreme zugleich": **nicht** `((x=0 ∧ y=2) ∨ (x=2 ∧ y=0))`. -/
def Tol (x y : Fin 3) : Prop := tolB x y = true

/-- `Tol` ist entscheidbar (defeq zur Bool-Gleichheit `tolB x y = true`); trägt alle
`by decide`-Sätze unten. -/
instance instDecidableTol (x y : Fin 3) : Decidable (Tol x y) :=
  inferInstanceAs (Decidable (tolB x y = true))

/-- **(a) `ρ*` ist reflexiv** — trägt die Rede von einer *zentralen* Relation. -/
theorem tol_refl : ∀ x : Fin 3, Tol x x := by decide

/-- **(a) `ρ*` ist symmetrisch.** -/
theorem tol_symm : ∀ x y : Fin 3, Tol x y → Tol y x := by decide

/-- **(a) `1` ist zentral:** `ρ*` hält zwischen `1` und jedem Wert, in beiden Richtungen. -/
theorem tol_center_one : ∀ x : Fin 3, Tol 1 x ∧ Tol x 1 := by decide

/-- **(a) `ρ*` ist echt (Nichttrivialitäts-Beleg):** weder leer (`ρ* 0 1`) noch die
Allrelation (`¬ ρ* 0 2`). Die Entsprechung zu `max_in_clone` und **nicht optional**: ohne
diesen Beleg wäre jede Erhaltungs-Aussage über `ρ*` wertlos. -/
theorem tol_proper : Tol 0 1 ∧ ¬ Tol 0 2 := by decide

/-- **(b) `min` (`∧`) erhält `ρ*`.** -/
theorem min_preserves_tol :
    ∀ a b c d : Fin 3, Tol a c → Tol b d → Tol (min a b) (min c d) := by decide

/-- **(b) `max` (`∨`) erhält `ρ*`.** -/
theorem max_preserves_tol :
    ∀ a b c d : Fin 3, Tol a c → Tol b d → Tol (max a b) (max c d) := by decide

/-- **(b) `negFin` (`¬`) erhält `ρ*`.** -/
theorem negFin_preserves_tol :
    ∀ a c : Fin 3, Tol a c → Tol (negFin a) (negFin c) := by decide

/-- **(b) `min` erhält die Fixpunkt-Invariante `{1}`.** -/
theorem min_preserves_one : min (1 : Fin 3) 1 = 1 := by decide

/-- **(b) `max` erhält `{1}`.** -/
theorem max_preserves_one : max (1 : Fin 3) 1 = 1 := by decide

/-- **(b) `negFin` erhält `{1}`.** -/
theorem negFin_preserves_one : negFin 1 = 1 := by decide

/-- **(c) `T` erhält `ρ*`.** Die zwei Kontextur-Extreme werden nie gemeinsam getroffen —
`T` bleibt Toleranz-treu, obwohl es die Boolesche `{0,2}` verlässt. -/
theorem T_preserves_tol :
    ∀ a b c d : Fin 3, Tol a c → Tol b d → Tol (T a b) (T c d) := by decide

/-- **(c) `T` erhält die Fixpunkt-Invariante `{1}`.** -/
theorem T_preserves_one : T 1 1 = 1 := by decide

/-- **(d) Der Bogen-Satz — die eigentliche Aussage des Zugs.** Von den drei Invarianten der
Basis bricht `T` genau die Boolesche `{0,2}` und erhält die beiden Zentrum-`1`-Invarianten:
`T` verlässt `{0,2}` (erste Konjunktion, wiederverwendet aus `T_leaves_contextur`), erhält
`{1}` (`T_preserves_one`) und erhält `ρ*` (`T_preserves_tol`). Das ist die Verortung: nicht
„irgendwo draußen", sondern der Bruch *genau einer* benannten maximalen Grenze. -/
theorem T_crosses_exactly_one :
    (T 0 2 ∉ ({0, 2} : Set (Fin 3)))
      ∧ (T 1 1 = 1)
      ∧ (∀ a b c d : Fin 3, Tol a c → Tol b d → Tol (T a b) (T c d)) :=
  ⟨T_leaves_contextur.2.2, T_preserves_one, T_preserves_tol⟩

/-! **Statement-Pins (Pilot eines neuen Wachen-Typs, §6).** Voller Wortlaut links, Satz
rechts — jede Drift des *Statements* (nicht nur des Axiom-Profils) bricht damit den Build.
Es sind `example`s ohne Namen und brauchen keine Axiom-Wache. -/

-- STATEMENT-PIN
example : Tol 0 1 ∧ ¬ Tol 0 2 := tol_proper
-- STATEMENT-PIN
example : ∀ a b c d : Fin 3, Tol a c → Tol b d → Tol (T a b) (T c d) := T_preserves_tol
-- STATEMENT-PIN
example : T 1 1 = 1 := T_preserves_one
-- STATEMENT-PIN
example :
    (T 0 2 ∉ ({0, 2} : Set (Fin 3)))
      ∧ (T 1 1 = 1)
      ∧ (∀ a b c d : Fin 3, Tol a c → Tol b d → Tol (T a b) (T c d)) :=
  T_crosses_exactly_one

/-! ## Teil 7 — die Erhaltung auf Klon-Ebene: jeder Term erhält die zentralen Invarianten

Teil 6 zeigte die Erhaltung von `ρ*` und `{1}` auf **Generator**-Ebene (`min`, `max`,
`negFin`, `T` je einzeln). Dieser Teil hebt sie auf **Klon**-Ebene: *jeder* Term über der
Basis erhält `ρ*` (`tolerance_is_invariant`) und `{1}` (`term_preserves_one`) — ohne eigene
Induktion, durch Verschaltung der vorhandenen Mathlib-Sätze `HomClass.realize_term` (die
Induktion ist dort geführt, wir konsumieren sie) und `Term.realize_mem`. Damit trägt der
Verortungs-Satz (`term_clone_localization`) die Rede von den „drei Grenzen, die der Klon
respektiert" — nicht mehr nur auf der Generator-Ebene.

Der Standard-Übersetzungsschritt der universellen Algebra: eine binäre Invariante auf `A` ist
eine Substruktur von `A × A`. `tolSub` ist `ρ*` als Substruktur des Produkts `Fin 3 × Fin 3`;
ihre `fun_mem`-Verpflichtung ist wörtlich `min`/`max`/`negFin_preserves_tol` aus Teil 6 — die
drei Sätze des vorigen Zugs sind das Material dieses Schritts. Die Projektionen
`fstHom`/`sndHom` zerlegen die Produkt-Realisierung in das Paar der Einzel-Realisierungen;
`Term.realize_mem` hält sie in `tolSub`. (Die Produkt-Struktur `prodStruc` ist selbst
definiert: in `ModelTheory/` liegt nur die Ultraprodukt-Instanz, keine `L.Structure (M × N)`.)

**Grenzen (unverändert in Kraft, hier nachgeführt):**

* **Keine Erschöpfungs-Behauptung.** Auch hier sagt der Korpus nicht, `T` erzeuge „alles
  unterhalb" der beiden erhaltenen Grenzen. Erhaltung ist nicht Erzeugung; die
  Erschöpfungs-Gleichheit bleibt außerhalb des Korpus und ist hier **nicht** Gegenstand.
* **„Maximaler Klon" bleibt Literatur-Verweis**, kein Theorem dieser Datei. Bewiesen ist die
  Erhaltung dreier Invarianten durch jeden Term und der Bruch genau einer durch `T` — nicht,
  dass `Pol(ρ*)` nach der Standard-Klassifikation maximal *ist*.
-/

/-- Die komponentenweise Produkt-Struktur auf `Fin 3 × Fin 3`: `funMap` wirkt auf beiden
Komponenten zugleich (generisch statt symbolweise, damit die Projektions-`map_fun'`
definitional durchgehen). Reine Definition — keine `L.Structure (M × N)` in Mathlib. -/
instance prodStruc : L.Structure (Fin 3 × Fin 3) where
  funMap := fun {_n} f x =>
    (Structure.funMap f (fun i => (x i).1), Structure.funMap f (fun i => (x i).2))
  RelMap r _ := nomatch r

/-- Die Toleranz `ρ*` als Substruktur des Produkts `Fin 3 × Fin 3` (Träger `{p | Tol p.1 p.2}`).
Die `fun_mem`-Verpflichtung ist wörtlich `min`/`max`/`negFin_preserves_tol` aus Teil 6. -/
def tolSub : L.Substructure (Fin 3 × Fin 3) where
  carrier := {p | Tol p.1 p.2}
  fun_mem := by
    intro n f
    match n, f with
    | 1, .neg =>
        intro x hx
        exact negFin_preserves_tol (x 0).1 (x 0).2 (hx 0)
    | 2, .and =>
        intro x hx
        exact min_preserves_tol (x 0).1 (x 1).1 (x 0).2 (x 1).2 (hx 0) (hx 1)
    | 2, .or =>
        intro x hx
        exact max_preserves_tol (x 0).1 (x 1).1 (x 0).2 (x 1).2 (hx 0) (hx 1)

/-- Die erste Projektion `Fin 3 × Fin 3 → Fin 3` als `L`-Homomorphismus. `map_fun'` geht bei
komponentenweiser Produkt-Struktur definitional durch (`rfl`); keine Relationen (`nomatch`). -/
def fstHom : (Fin 3 × Fin 3) →[L] (Fin 3) where
  toFun := Prod.fst
  map_fun' := fun _ _ => rfl
  map_rel' := fun r => nomatch r

/-- Die zweite Projektion `Fin 3 × Fin 3 → Fin 3` als `L`-Homomorphismus. -/
def sndHom : (Fin 3 × Fin 3) →[L] (Fin 3) where
  toFun := Prod.snd
  map_fun' := fun _ _ => rfl
  map_rel' := fun r => nomatch r

/-- Die Fixpunkt-Invariante `{1}` als Substruktur von `Fin 3` (Träger `{1}`), nach der
Schablone von `S`. Trägt `term_preserves_one` direkt über `Term.realize_mem`. -/
def Sone : L.Substructure (Fin 3) where
  carrier := {1}
  fun_mem := by
    intro n f
    match n, f with
    | 1, .neg =>
        intro x hx
        have h0 : x 0 = 1 := Set.mem_singleton_iff.mp (hx 0)
        simp only [Set.mem_singleton_iff, funMap_neg, h0]; decide
    | 2, .and =>
        intro x hx
        have h0 : x 0 = 1 := Set.mem_singleton_iff.mp (hx 0)
        have h1 : x 1 = 1 := Set.mem_singleton_iff.mp (hx 1)
        simp only [Set.mem_singleton_iff, funMap_and, h0, h1]; decide
    | 2, .or =>
        intro x hx
        have h0 : x 0 = 1 := Set.mem_singleton_iff.mp (hx 0)
        have h1 : x 1 = 1 := Set.mem_singleton_iff.mp (hx 1)
        simp only [Set.mem_singleton_iff, funMap_or, h0, h1]; decide

/-- **(a) Jeder Term erhält `ρ*` (Klon-Ebene).** Stimmen zwei Belegungen `v`, `w`
argumentweise in `ρ*` überein, so auch die Realisierungen jedes Terms. Ohne eigene Induktion:
`Term.realize_mem` hält das Paar `(v i, w i)` in `tolSub`, `HomClass.realize_term` zerlegt die
Produkt-Realisierung über `fstHom`/`sndHom` in die beiden Einzel-Realisierungen. Die
Variablen-Sorte `Fin 2` spiegelt `term_preserves_contextur`. -/
theorem tolerance_is_invariant (t : L.Term (Fin 2)) (v w : Fin 2 → Fin 3)
    (h : ∀ i, Tol (v i) (w i)) : Tol (t.realize v) (t.realize w) := by
  have hmem : t.realize (fun i => (v i, w i)) ∈ tolSub :=
    Term.realize_mem t (fun i => (v i, w i)) (fun i =>
      show (v i, w i) ∈ ({p | Tol p.1 p.2} : Set (Fin 3 × Fin 3)) from h i)
  have hmem' : Tol (t.realize (fun i => (v i, w i))).1
      (t.realize (fun i => (v i, w i))).2 := hmem
  have hv : t.realize v = (t.realize (fun i => (v i, w i))).1 :=
    HomClass.realize_term fstHom (t := t) (v := fun i => (v i, w i))
  have hw : t.realize w = (t.realize (fun i => (v i, w i))).2 :=
    HomClass.realize_term sndHom (t := t) (v := fun i => (v i, w i))
  rw [hv, hw]; exact hmem'

/-- **(b) Jeder Term erhält die Fixpunkt-Invariante `{1}` (Klon-Ebene).** Billig und ohne
Produkt-Umweg: `{1}` ist selbst Substruktur von `Fin 3` (`Sone`), also greift `Term.realize_mem`
direkt — exakt wie `term_preserves_contextur` für `{0,2}`. -/
theorem term_preserves_one (t : L.Term (Fin 2)) (v : Fin 2 → Fin 3)
    (hv : ∀ i, v i = 1) : t.realize v = 1 := by
  have hmem : t.realize v ∈ Sone :=
    Term.realize_mem t v (fun i =>
      show v i ∈ ({1} : Set (Fin 3)) from Set.mem_singleton_iff.mpr (hv i))
  have hmem' : t.realize v ∈ ({1} : Set (Fin 3)) := hmem
  exact Set.mem_singleton_iff.mp hmem'

/-- **(c) Der Verortungs-Satz auf Klon-Ebene.** Jeder Term über der Basis erhält alle drei
Invarianten — `{0,2}` (`term_preserves_contextur`), `{1}` (`term_preserves_one`), `ρ*`
(`tolerance_is_invariant`) —, und `T` erhält `{1}` und `ρ*`, verletzt aber `{0,2}`. Damit
steht die Verortung auf Klon-Ebene: `T` liegt nicht irgendwo außerhalb, sondern **außerhalb
genau einer der drei Grenzen, die der Klon respektiert**. Aus den vorhandenen Teilen
zusammengesetzt, nicht neu bewiesen. -/
theorem term_clone_localization :
    (∀ (t : L.Term (Fin 2)) (v : Fin 2 → Fin 3), (∀ i, v i = 0 ∨ v i = 2) →
        t.realize v = 0 ∨ t.realize v = 2)
      ∧ (∀ (t : L.Term (Fin 2)) (v : Fin 2 → Fin 3), (∀ i, v i = 1) → t.realize v = 1)
      ∧ (∀ (t : L.Term (Fin 2)) (v w : Fin 2 → Fin 3), (∀ i, Tol (v i) (w i)) →
          Tol (t.realize v) (t.realize w))
      ∧ (T 1 1 = 1)
      ∧ (∀ a b c d : Fin 3, Tol a c → Tol b d → Tol (T a b) (T c d))
      ∧ (T 0 2 ∉ ({0, 2} : Set (Fin 3))) :=
  ⟨term_preserves_contextur, term_preserves_one, tolerance_is_invariant,
    T_preserves_one, T_preserves_tol, T_leaves_contextur.2.2⟩

/-! **Statement-Pins (Teil 7).** Voller Wortlaut links, Satz rechts — wie in Teil 6; sichern
gegen defeq-Drift des Statements (nicht Syntax-Drift). Namenlose `example`s, keine Wache. -/

-- STATEMENT-PIN
example (t : L.Term (Fin 2)) (v w : Fin 2 → Fin 3) (h : ∀ i, Tol (v i) (w i)) :
    Tol (t.realize v) (t.realize w) := tolerance_is_invariant t v w h
-- STATEMENT-PIN
example (t : L.Term (Fin 2)) (v : Fin 2 → Fin 3) (hv : ∀ i, v i = 1) :
    t.realize v = 1 := term_preserves_one t v hv
-- STATEMENT-PIN
example :
    (∀ (t : L.Term (Fin 2)) (v : Fin 2 → Fin 3), (∀ i, v i = 0 ∨ v i = 2) →
        t.realize v = 0 ∨ t.realize v = 2)
      ∧ (∀ (t : L.Term (Fin 2)) (v : Fin 2 → Fin 3), (∀ i, v i = 1) → t.realize v = 1)
      ∧ (∀ (t : L.Term (Fin 2)) (v w : Fin 2 → Fin 3), (∀ i, Tol (v i) (w i)) →
          Tol (t.realize v) (t.realize w))
      ∧ (T 1 1 = 1)
      ∧ (∀ a b c d : Fin 3, Tol a c → Tol b d → Tol (T a b) (T c d))
      ∧ (T 0 2 ∉ ({0, 2} : Set (Fin 3))) :=
  term_clone_localization

/-! ## Teil 5 — die Axiom-Wachen (Ist-gebunden)

Ist-Ausgabe des grünen Builds (v4.30.0-rc2), pro Satz als Regressions-Wache
eingefroren. Ab hier bricht jede Axiom-Drift den Build. Nach der
Datei-Vollständigkeits-Regel (Zug „Wachen-Vollzug", 19. Juli 2026) tragen jetzt
**alle** Sätze der Datei eine Wache — die fünf Schranken-tragenden Sätze
(`T_not_in_clone` und `max_in_clone` werden im Außentext namentlich vorgezeigt)
samt den zuvor nur aufgelisteten übrigen (`test1_*`, `term_preserves_contextur`,
`const_not_closedUnder`, `no_substructure_with_const`), den dreizehn
Erhaltungs-Sätzen aus Teil 6 (`tol_refl`, `tol_symm`, `tol_center_one`,
`tol_proper`; `min`/`max`/`negFin`-`preserves_tol`/`preserves_one`;
`T_preserves_tol`, `T_preserves_one`, `T_crosses_exactly_one`) und den drei
Klon-Ebenen-Sätzen aus Teil 7 (`tolerance_is_invariant`, `term_preserves_one`,
`term_clone_localization`). -/

/-- info: 'Reformulation.Proemial.TransjunctionCloneBound.T_rejective' depends on axioms: [propext] -/
#guard_msgs in #print axioms T_rejective

/-- info: 'Reformulation.Proemial.TransjunctionCloneBound.T_not_in_clone' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms T_not_in_clone

/-- info: 'Reformulation.Proemial.TransjunctionCloneBound.max_in_clone' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms max_in_clone

/-- info: 'Reformulation.Proemial.TransjunctionCloneBound.T_agrees_max_off_diagonal' depends on axioms: [propext] -/
#guard_msgs in #print axioms T_agrees_max_off_diagonal

/-- info: 'Reformulation.Proemial.TransjunctionCloneBound.T_leaves_contextur' depends on axioms: [propext] -/
#guard_msgs in #print axioms T_leaves_contextur

/-- info: 'Reformulation.Proemial.TransjunctionCloneBound.test1_values' depends on axioms: [propext] -/
#guard_msgs in #print axioms test1_values

/-- info: 'Reformulation.Proemial.TransjunctionCloneBound.test1_min_max' depends on axioms: [propext] -/
#guard_msgs in #print axioms test1_min_max

/-- info: 'Reformulation.Proemial.TransjunctionCloneBound.test1_neg' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms test1_neg

/-- info: 'Reformulation.Proemial.TransjunctionCloneBound.test1_injective' depends on axioms: [propext] -/
#guard_msgs in #print axioms test1_injective

/-- info: 'Reformulation.Proemial.TransjunctionCloneBound.test1_surjective' depends on axioms: [propext] -/
#guard_msgs in #print axioms test1_surjective

/-- info: 'Reformulation.Proemial.TransjunctionCloneBound.term_preserves_contextur' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms term_preserves_contextur

/-- info: 'Reformulation.Proemial.TransjunctionCloneBound.const_not_closedUnder' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms const_not_closedUnder

/-- info: 'Reformulation.Proemial.TransjunctionCloneBound.no_substructure_with_const' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms no_substructure_with_const

/-- info: 'Reformulation.Proemial.TransjunctionCloneBound.tol_refl' depends on axioms: [propext] -/
#guard_msgs in #print axioms tol_refl

/-- info: 'Reformulation.Proemial.TransjunctionCloneBound.tol_symm' depends on axioms: [propext] -/
#guard_msgs in #print axioms tol_symm

/-- info: 'Reformulation.Proemial.TransjunctionCloneBound.tol_center_one' depends on axioms: [propext] -/
#guard_msgs in #print axioms tol_center_one

/-- info: 'Reformulation.Proemial.TransjunctionCloneBound.tol_proper' depends on axioms: [propext] -/
#guard_msgs in #print axioms tol_proper

/-- info: 'Reformulation.Proemial.TransjunctionCloneBound.min_preserves_tol' depends on axioms: [propext] -/
#guard_msgs in #print axioms min_preserves_tol

/-- info: 'Reformulation.Proemial.TransjunctionCloneBound.max_preserves_tol' depends on axioms: [propext] -/
#guard_msgs in #print axioms max_preserves_tol

/-- info: 'Reformulation.Proemial.TransjunctionCloneBound.negFin_preserves_tol' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms negFin_preserves_tol

/-- info: 'Reformulation.Proemial.TransjunctionCloneBound.min_preserves_one' depends on axioms: [propext] -/
#guard_msgs in #print axioms min_preserves_one

/-- info: 'Reformulation.Proemial.TransjunctionCloneBound.max_preserves_one' depends on axioms: [propext] -/
#guard_msgs in #print axioms max_preserves_one

/-- info: 'Reformulation.Proemial.TransjunctionCloneBound.negFin_preserves_one' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms negFin_preserves_one

/-- info: 'Reformulation.Proemial.TransjunctionCloneBound.T_preserves_tol' depends on axioms: [propext] -/
#guard_msgs in #print axioms T_preserves_tol

/-- info: 'Reformulation.Proemial.TransjunctionCloneBound.T_preserves_one' depends on axioms: [propext] -/
#guard_msgs in #print axioms T_preserves_one

/-- info: 'Reformulation.Proemial.TransjunctionCloneBound.T_crosses_exactly_one' depends on axioms: [propext] -/
#guard_msgs in #print axioms T_crosses_exactly_one

/-- info: 'Reformulation.Proemial.TransjunctionCloneBound.tolerance_is_invariant' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms tolerance_is_invariant

/-- info: 'Reformulation.Proemial.TransjunctionCloneBound.term_preserves_one' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms term_preserves_one

/-- info: 'Reformulation.Proemial.TransjunctionCloneBound.term_clone_localization' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms term_clone_localization

end Reformulation.Proemial.TransjunctionCloneBound
