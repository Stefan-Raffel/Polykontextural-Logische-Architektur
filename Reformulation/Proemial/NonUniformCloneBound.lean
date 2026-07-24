import Reformulation.Proemial.TransjunctionCloneBound

/-!
# Proemial.NonUniformCloneBound — der zweite Zeuge: Nicht-Internalität ohne Transzendenz (Kairos, Sonde 15)

Diese Datei legt den **zweiten Zeugen** der Klon-Schranke nieder (Sonde 15, „Vermittlung ohne
Transzendenz", 22. Juli 2026). Der erste Zeuge (`TransjunctionCloneBound.T_not_in_clone`) liegt
nicht im Klon, **weil er die Kontextur verlässt** (`T 0 2 = 1 ∉ {0,2}`) — die Nicht-Internalität
steckt dort schon im Begriff der Transjunktion. Der zweite Zeuge `W` ist von anderer Art:

* `W` **erhält alle drei Elementarkontexturen** `{0,1}`, `{1,2}`, `{0,2}`
  (`W_contexture_faithful`) — kein Verlassen, keine Transzendenz;
* `W` wirkt **auf jeder Kontextur klassisch** — als `min` auf `{0,1}` und `{0,2}`, als `max`
  auf `{1,2}` (`W_min_01`, `W_max_12`, `W_min_02`);
* und `W` liegt **trotzdem nicht im Klon** von `{min, max, negFin}` (`W_not_in_clone`).

Der Grund der Nicht-Erzeugbarkeit ist nicht Transzendenz, sondern **Uneinheitlichkeit**: `W`
wählt in verschiedenen Kontexturen verschiedene klassische Operationen (`W_uneven` — auf
`{1,2}` echt `max`, auf `{0,2}` echt `min`). Anders als beim ersten Zeugen steckt die
Nicht-Reduzierbarkeit hier nicht schon im Begriff der Operation (Wertung der Sonde 15, §4;
Deutung, kein Satz dieser Datei) — das endliche Gegenstück zu Günthers Satz, der Übergang
von einer Kontextur zur anderen bedeute den Wechsel eines Strukturprinzips: das
Strukturprinzip (Konjunktion oder Disjunktion) wechselt beim Kontexturwechsel, ohne dass
eine Grenze verletzt wird.

## Beweismittel: die Begleit-Relation `ρ`

Da `W` alle drei Kontexturen erhält, trägt die `R = {0,2}`-Route des ersten Zeugen hier
nicht. Die Schranke läuft stattdessen über die binäre **Begleit-Relation**

`ρ(x, y) ⟺ (y = 0 ∧ x ≠ 2) ∨ (y = 2 ∧ x ≠ 0)`

— „`y` ist ein Extrem und `x` liegt in der *gemischten* Kontextur von `y`" (`rho_companion`:
für `y = 0` heißt das `x ∈ {0,1}`, für `y = 2` heißt das `x ∈ {1,2}`). Die Basis erhält `ρ`
(`min`/`max`/`negFin_preserves_rho`), also erhält jeder Term `ρ` (`rho_is_invariant`, per
`Term.realize_mem` über die Produkt-Struktur — dieselbe Verschaltung wie
`tolerance_is_invariant`, kein Eigenbau). `W` bricht `ρ` genau an der Uneinheitlichkeits-
Stelle (`rho_breaks_at_uneven_site`): die Argumente `(1,0)` und `(2,2)` sind `ρ`-verbunden,
die Ergebnisse `(W 1 2, W 0 2) = (2, 0)` sind es nicht — die `max`-Wahl auf `{1,2}` und die
`min`-Wahl auf `{0,2}` kollidieren. Der Bruch *ist* die Uneinheitlichkeit, am Term.

## Die Gegenrichtung (Schärfung)

Damit der Satz nicht nach „alles ist nicht-erzeugbar" aussieht: vier Wahlmuster **sind**
erzeugbar, mit expliziten Termen vorgezeigt (`pattern_*_in_clone`): min/min/min (`∧`),
max/max/max (`∨`), max/min/min und max/min/max (echte Term-Kompositionen). Der Zeuge `W`
trägt das Muster min/max/min.

## E1 — die vollständige Klassifikation (Nachzug, Rev2-Einheit E1 nach Sonde 16)

Die Teile 6–8 heben die Existenz-Aussage zur **Klassifikation**: die drei übrigen Zeugen
`W2` (min/min/max), `W3` (min/max/max), `W4` (max/max/min); die `neg`-Konjugation `conj`
mit dem Abschluss-Lemma `clone_closed_under_conj` (der Klon ist unter `conj` abgeschlossen
— per Term-Konstruktion `¬ t[¬x, ¬y]`, nicht per Zählung) und dem Transport
`not_in_clone_conj`; der Struktursatz `locally_classical_iff` (jede lokal-klassische
Operation ist ein Wahlvektor `ofChoices c01 c12 c02`, die Zählung `2^3 = 8` liegt damit
im Korpus als Bijektions-Paar iff + `ofChoices_injective`); und der Hauptsatz
`four_of_eight_generatable`: **von den acht Wahlmustern sind genau vier erzeugbar und
genau vier nicht** — mit `locally_classical_dichotomy` als Ops-Fassung (jede
lokal-klassische Operation ist erzeugbar oder einer der vier Zeugen).

Die `neg`-Konjugation ist dabei tragend, nicht dekorativ: `W3` und `W4` erhalten ihre
Schranke **per Transport** (`conj W = W3`, `conj W2 = W4`, `not_in_clone_conj`), nicht
durch Beweiskopien — die Symmetrie der 4/4-Teilung (Strukturbefund der Sonde 15) wird
damit konsumiert statt nur behauptet. Nur `W2` trägt einen zweiten direkten `ρ`-Beweis
(Bruchstelle `rho_breaks_at_uneven_site_W2`: min-Wahl auf `{0,1}` gegen max-Wahl auf
`{0,2}`).

**Wortlaut-Grenzen (verbindlich):**

1. **Zähl-Behauptungen im Korpus nur in Bijektions-Form.** Im Korpus steht die Zählung
   der lokal-klassischen Operationen (`locally_classical_iff` + `ofChoices_injective`:
   genau die `2^3` Wahlvektoren) und die Teilung genau 4 / genau 4
   (`four_of_eight_generatable`). **Nicht** im Korpus: die übrigen Zahlen der Sonden 15/16
   (19683 binäre Operationen, 64 kontexturtreue, Klon-Größe 82, die Befunde für `m ≥ 4`
   — dort sind nach Sonde 16 nur `min` und `max` erzeugbar, hier nicht Gegenstand).
   Alle außerhalb gerechnet (Wolfram, unabhängig in Python bestätigt).
2. **`ρ` ist Beweismittel, nicht Begriff.** Die Begleit-Relation ist eine unter mehreren
   trennenden Invarianten (die Rechnung fand 5 binäre); ihre Kanonizität wird nicht
   behauptet. Kanonisch sind allein die beiden Vorbedingungen des Zeugen — Kontexturtreue
   und lokale Klassizität —, beide aus der Kontexturstruktur, keine gewählt.
3. **Keine Vermittlungs-These.** Ob die Zuordnung *kontextur-relative Operationswahl =
   Günthers Vermittlung* trägt, entscheidet diese Datei nicht (Sonde 15, §6: Marke 3;
   Sonde 16, Vorbehalt vier). Der Dateiname sagt darum Uneinheitlichkeit (`NonUniform`),
   nicht Vermittlung.
-/

open FirstOrder Language

namespace Reformulation.Proemial.NonUniformCloneBound

open Reformulation.Proemial.TransjunctionCloneBound

/-! ## Teil 1 — die drei Elementarkontexturen und die lokalen Prädikate

Die drei Elementarkontexturen bei `m = 3` sind die drei Zweierteilmengen `{0,1}`, `{1,2}`,
`{0,2}` (Günthers drei Elementarkontexturen, die drei Transpositionen). Die Prädikate sind
über dem Paar `(x, y)` parametrisiert und `Decidable` per `inferInstanceAs` (die
`Prop`-Definition ist für die Instanz-Synthese opak — Feedback „Decidable bei Prop-def"). -/

/-- `f` erhält die Elementarkontextur `{x, y}`: Werte aus `{x,y}` führen nie hinaus. -/
def PreservesPair (f : Fin 3 → Fin 3 → Fin 3) (x y : Fin 3) : Prop :=
  ∀ a b : Fin 3, (a = x ∨ a = y) → (b = x ∨ b = y) → (f a b = x ∨ f a b = y)

instance (f : Fin 3 → Fin 3 → Fin 3) (x y : Fin 3) : Decidable (PreservesPair f x y) :=
  inferInstanceAs (Decidable (∀ a b : Fin 3,
    (a = x ∨ a = y) → (b = x ∨ b = y) → (f a b = x ∨ f a b = y)))

/-- `f` wirkt auf `{x, y}` als Konjunktion: dort ist `f = min`. -/
def ActsAsMin (f : Fin 3 → Fin 3 → Fin 3) (x y : Fin 3) : Prop :=
  ∀ a b : Fin 3, (a = x ∨ a = y) → (b = x ∨ b = y) → f a b = min a b

instance (f : Fin 3 → Fin 3 → Fin 3) (x y : Fin 3) : Decidable (ActsAsMin f x y) :=
  inferInstanceAs (Decidable (∀ a b : Fin 3,
    (a = x ∨ a = y) → (b = x ∨ b = y) → f a b = min a b))

/-- `f` wirkt auf `{x, y}` als Disjunktion: dort ist `f = max`. -/
def ActsAsMax (f : Fin 3 → Fin 3 → Fin 3) (x y : Fin 3) : Prop :=
  ∀ a b : Fin 3, (a = x ∨ a = y) → (b = x ∨ b = y) → f a b = max a b

instance (f : Fin 3 → Fin 3 → Fin 3) (x y : Fin 3) : Decidable (ActsAsMax f x y) :=
  inferInstanceAs (Decidable (∀ a b : Fin 3,
    (a = x ∨ a = y) → (b = x ∨ b = y) → f a b = max a b))

/-- Kontexturtreue: `f` erhält alle drei Elementarkontexturen. -/
def ContextureFaithful (f : Fin 3 → Fin 3 → Fin 3) : Prop :=
  PreservesPair f 0 1 ∧ PreservesPair f 1 2 ∧ PreservesPair f 0 2

instance (f : Fin 3 → Fin 3 → Fin 3) : Decidable (ContextureFaithful f) :=
  inferInstanceAs (Decidable (PreservesPair f 0 1 ∧ PreservesPair f 1 2 ∧ PreservesPair f 0 2))

/-- Lokale Klassizität: auf jeder der drei Kontexturen wirkt `f` wie `min` oder wie `max`. -/
def LocallyClassical (f : Fin 3 → Fin 3 → Fin 3) : Prop :=
  (ActsAsMin f 0 1 ∨ ActsAsMax f 0 1) ∧ (ActsAsMin f 1 2 ∨ ActsAsMax f 1 2) ∧
    (ActsAsMin f 0 2 ∨ ActsAsMax f 0 2)

instance (f : Fin 3 → Fin 3 → Fin 3) : Decidable (LocallyClassical f) :=
  inferInstanceAs (Decidable ((ActsAsMin f 0 1 ∨ ActsAsMax f 0 1) ∧
    (ActsAsMin f 1 2 ∨ ActsAsMax f 1 2) ∧ (ActsAsMin f 0 2 ∨ ActsAsMax f 0 2)))

/-! ## Teil 2 — der Zeuge `W` (Muster min/max/min) -/

/-- Der Zeuge `W`: minimale Abweichung von `min` (dem intra-kontexturalen `∧`) — klassisch
(`= ∧`) überall, nur auf der gemischten Kontextur `{1,2}` die *andere* klassische Wahl
(`= ∨`). Spiegelbildlich zur `T`-Definition (minimale Abweichung von `max`, rejektiv an
einem Punkt): `W` weicht nicht in einen dritten Wert aus, sondern in die andere klassische
Operation. Tafel (Zeile `a`, Spalte `b`): `0 0 0 | 0 1 2 | 0 2 2`. -/
def W (a b : Fin 3) : Fin 3 :=
  if (a = 1 ∧ b = 2) ∨ (a = 2 ∧ b = 1) then max a b else min a b

/-- **`W` ist kontexturtreu** — der Kontrast zur Transjunktion (`T_leaves_contextur`):
`W` verlässt *keine* der drei Elementarkontexturen. Keine Transzendenz. -/
theorem W_contexture_faithful : ContextureFaithful W := by decide

/-- **`W` auf `{0,1}`: Konjunktion.** -/
theorem W_min_01 : ActsAsMin W 0 1 := by decide

/-- **`W` auf `{1,2}`: Disjunktion.** -/
theorem W_max_12 : ActsAsMax W 1 2 := by decide

/-- **`W` auf `{0,2}`: Konjunktion.** -/
theorem W_min_02 : ActsAsMin W 0 2 := by decide

/-- **`W` ist lokal klassisch** (Muster min/max/min), aus den drei Muster-Sätzen. -/
theorem W_locally_classical : LocallyClassical W :=
  ⟨Or.inl W_min_01, Or.inr W_max_12, Or.inl W_min_02⟩

/-- **Die Uneinheitlichkeit ist echt** — der Wechsel des Strukturprinzips am Term: auf
`{1,2}` ist `W` die Disjunktion und *nicht* die Konjunktion, auf `{0,2}` die Konjunktion
und *nicht* die Disjunktion. Die lokalen Wahlen sind wirklich verschieden, nicht bloß
mehrdeutig benannt. -/
theorem W_uneven :
    ActsAsMax W 1 2 ∧ ¬ ActsAsMin W 1 2 ∧ ActsAsMin W 0 2 ∧ ¬ ActsAsMax W 0 2 := by decide

/-! ## Teil 3 — die Begleit-Relation `ρ` und ihre Klon-Invarianz

Nach der `tolB`/`Tol`-Schablone Bool-getragen, damit `Decidable` ohne Instanz-Bastelei
greift. Die Klon-Ebene (`rho_is_invariant`) ist dieselbe Verschaltung wie
`tolerance_is_invariant`: `ρ` als Substruktur des Produkts (`rhoSub`, über dem vorhandenen
`prodStruc`), `Term.realize_mem` hält die Paar-Realisierung darin, `fstHom`/`sndHom`
zerlegen sie — keine eigene Term-Induktion. -/

/-- Die Begleit-Relation als Bool-Träger: `(y = 0 ∧ x ≠ 2) ∨ (y = 2 ∧ x ≠ 0)`. -/
def rhoB (x y : Fin 3) : Bool :=
  (y == 0 && !(x == 2)) || (y == 2 && !(x == 0))

/-- `ρ(x, y)` — „`y` ist ein Extrem und `x` liegt in der gemischten Kontextur von `y`". -/
def Rho (x y : Fin 3) : Prop := rhoB x y = true

/-- `Rho` ist entscheidbar (defeq zur Bool-Gleichheit); trägt alle `by decide`-Sätze. -/
instance instDecidableRho (x y : Fin 3) : Decidable (Rho x y) :=
  inferInstanceAs (Decidable (rhoB x y = true))

/-- **Die Lesart von `ρ`, bewiesen statt behauptet:** `ρ(x, y)` gilt genau dann, wenn `y`
ein Extrem ist und `x` in der gemischten Kontextur von `y` liegt — für `y = 0` heißt das
`x ∈ {0,1}`, für `y = 2` heißt das `x ∈ {1,2}`. -/
theorem rho_companion : ∀ x y : Fin 3,
    Rho x y ↔ ((y = 0 ∧ (x = 0 ∨ x = 1)) ∨ (y = 2 ∧ (x = 1 ∨ x = 2))) := by decide

/-- **`ρ` ist echt (Nichttrivialitäts-Beleg):** weder leer (`ρ 1 0`) noch die Allrelation
(`¬ ρ 0 2`). Die Entsprechung zu `tol_proper` und nicht optional: ohne diesen Beleg wäre
jede Erhaltungs-Aussage über `ρ` wertlos. -/
theorem rho_proper : Rho 1 0 ∧ ¬ Rho 0 2 := by decide

/-- **`min` (`∧`) erhält `ρ`.** -/
theorem min_preserves_rho :
    ∀ a b c d : Fin 3, Rho a c → Rho b d → Rho (min a b) (min c d) := by decide

/-- **`max` (`∨`) erhält `ρ`.** -/
theorem max_preserves_rho :
    ∀ a b c d : Fin 3, Rho a c → Rho b d → Rho (max a b) (max c d) := by decide

/-- **`negFin` (`¬`) erhält `ρ`.** -/
theorem negFin_preserves_rho :
    ∀ a c : Fin 3, Rho a c → Rho (negFin a) (negFin c) := by decide

/-- Die Begleit-Relation `ρ` als Substruktur des Produkts `Fin 3 × Fin 3` (Träger
`{p | Rho p.1 p.2}`), nach der `tolSub`-Schablone. Die `fun_mem`-Verpflichtung ist wörtlich
`min`/`max`/`negFin_preserves_rho`. -/
def rhoSub : L.Substructure (Fin 3 × Fin 3) where
  carrier := {p | Rho p.1 p.2}
  fun_mem := by
    intro n f
    match n, f with
    | 1, .neg =>
        intro x hx
        exact negFin_preserves_rho (x 0).1 (x 0).2 (hx 0)
    | 2, .and =>
        intro x hx
        exact min_preserves_rho (x 0).1 (x 1).1 (x 0).2 (x 1).2 (hx 0) (hx 1)
    | 2, .or =>
        intro x hx
        exact max_preserves_rho (x 0).1 (x 1).1 (x 0).2 (x 1).2 (hx 0) (hx 1)

/-- **Jeder Term erhält `ρ` (Klon-Ebene).** Stimmen zwei Belegungen `v`, `w` argumentweise
in `ρ` überein, so auch die Realisierungen jedes Terms. Dieselbe Verschaltung wie
`tolerance_is_invariant`: `Term.realize_mem` hält das Paar in `rhoSub`,
`HomClass.realize_term` zerlegt über `fstHom`/`sndHom` — keine eigene Induktion. -/
theorem rho_is_invariant (t : L.Term (Fin 2)) (v w : Fin 2 → Fin 3)
    (h : ∀ i, Rho (v i) (w i)) : Rho (t.realize v) (t.realize w) := by
  have hmem : t.realize (fun i => (v i, w i)) ∈ rhoSub :=
    Term.realize_mem t (fun i => (v i, w i)) (fun i =>
      show (v i, w i) ∈ ({p | Rho p.1 p.2} : Set (Fin 3 × Fin 3)) from h i)
  have hmem' : Rho (t.realize (fun i => (v i, w i))).1
      (t.realize (fun i => (v i, w i))).2 := hmem
  have hv : t.realize v = (t.realize (fun i => (v i, w i))).1 :=
    HomClass.realize_term fstHom (t := t) (v := fun i => (v i, w i))
  have hw : t.realize w = (t.realize (fun i => (v i, w i))).2 :=
    HomClass.realize_term sndHom (t := t) (v := fun i => (v i, w i))
  rw [hv, hw]; exact hmem'

/-! ## Teil 4 — die Schranke -/

/-- **Die Bruchstelle, benannt:** die Argument-Paare `(1,0)` und `(2,2)` sind `ρ`-verbunden,
die Ergebnis-Paarung `(W 1 2, W 0 2) = (2, 0)` ist es nicht. Der Bruch sitzt exakt an der
uneinheitlichen Wahl: `W 1 2 = 2` ist die `max`-Wahl auf `{1,2}`, `W 0 2 = 0` die
`min`-Wahl auf `{0,2}` — zwei klassische Wahlen, die keine einheitliche Term-Operation
zugleich treffen kann. -/
theorem rho_breaks_at_uneven_site :
    Rho 1 0 ∧ Rho 2 2 ∧ ¬ Rho (W 1 2) (W 0 2) := by decide

/-- **Die zweite Klon-Schranke (der tragende Satz).** Es gibt keinen Term
`t : L.Term (Fin 2)`, dessen Realisierung der Zeuge `W` ist — `W` liegt nicht im von
`{∧, ∨, ¬}` erzeugten Klon, obwohl `W` alle drei Elementarkontexturen erhält und auf jeder
klassisch wirkt.

Beweis: angenommen `⟨t, ht⟩`. Die Belegungen `v = ![1, 2]` und `w = ![0, 2]` sind
argumentweise `ρ`-verbunden (`ρ 1 0`, `ρ 2 2`), also hält `rho_is_invariant` die
Realisierungen in `ρ`. Nach `ht` sind die Realisierungen `W 1 2 = 2` und `W 0 2 = 0`,
aber `¬ ρ 2 0`. Widerspruch — genau an der Uneinheitlichkeits-Stelle. -/
theorem W_not_in_clone :
    ¬ ∃ t : L.Term (Fin 2), ∀ v : Fin 2 → Fin 3, t.realize v = W (v 0) (v 1) := by
  rintro ⟨t, ht⟩
  have h : Rho (t.realize ![1, 2]) (t.realize ![0, 2]) := by
    apply rho_is_invariant
    intro i
    revert i
    decide
  rw [ht (![1, 2]), ht (![0, 2])] at h
  exact absurd h (by decide)

/-- **Der Satz der Sonde 15 (die Existenz-Fassung).** Es existiert eine binäre Operation
auf `Fin 3`, die jede Elementarkontextur erhält, auf jeder klassisch wirkt — und nicht im
Klon von `{min, max, neg}` liegt. Der Zeuge ist `W`; der Grund ist nicht Transzendenz
(Kontexturtreue schließt sie aus), sondern die Uneinheitlichkeit der lokalen Wahl. -/
theorem nonuniform_witness_exists :
    ∃ f : Fin 3 → Fin 3 → Fin 3, ContextureFaithful f ∧ LocallyClassical f ∧
      ¬ ∃ t : L.Term (Fin 2), ∀ v : Fin 2 → Fin 3, t.realize v = f (v 0) (v 1) :=
  ⟨W, W_contexture_faithful, W_locally_classical, W_not_in_clone⟩

/-! ## Teil 5 — die Gegenrichtung: vier Wahlmuster sind erzeugbar

Damit `nonuniform_witness_exists` nicht nach „alles ist nicht-erzeugbar" aussieht: vier der
Wahlmuster sind im Klon realisiert, mit expliziten Termen vorgezeigt. Die Muster-Notation
ist (Wahl auf `{0,1}` / auf `{1,2}` / auf `{0,2}`). Die Terme für max/min/min und
max/min/max sind echte Kompositionen (mit `¬` im Innern) — die Gegenrichtung ist nicht auf
die trivialen Projektions-Fälle `∧`, `∨` beschränkt. -/

/-- Erste Variable als Term. -/
def varX : L.Term (Fin 2) := Term.var 0

/-- Zweite Variable als Term. -/
def varY : L.Term (Fin 2) := Term.var 1

/-- Term-Konjunktion (Symbol `∧` angewandt). -/
def tand (s t : L.Term (Fin 2)) : L.Term (Fin 2) :=
  Term.func (l := 2) (BinaryFun.and : L.Functions 2) ![s, t]

/-- Term-Disjunktion (Symbol `∨` angewandt). -/
def tor (s t : L.Term (Fin 2)) : L.Term (Fin 2) :=
  Term.func (l := 2) (BinaryFun.or : L.Functions 2) ![s, t]

/-- Term-Negation (Symbol `¬` angewandt). -/
def tneg (s : L.Term (Fin 2)) : L.Term (Fin 2) :=
  Term.func (l := 1) (UnaryFun.neg : L.Functions 1) ![s]

/-- **Muster min/min/min ist erzeugbar:** der Term `x ∧ y`. -/
theorem pattern_min_min_min_in_clone :
    ∃ t : L.Term (Fin 2),
      ActsAsMin (fun a b => t.realize ![a, b]) 0 1 ∧
      ActsAsMin (fun a b => t.realize ![a, b]) 1 2 ∧
      ActsAsMin (fun a b => t.realize ![a, b]) 0 2 :=
  ⟨tand varX varY, by decide⟩

/-- **Muster max/max/max ist erzeugbar:** der Term `x ∨ y`. -/
theorem pattern_max_max_max_in_clone :
    ∃ t : L.Term (Fin 2),
      ActsAsMax (fun a b => t.realize ![a, b]) 0 1 ∧
      ActsAsMax (fun a b => t.realize ![a, b]) 1 2 ∧
      ActsAsMax (fun a b => t.realize ![a, b]) 0 2 :=
  ⟨tor varX varY, by decide⟩

/-- **Muster max/min/min ist erzeugbar:** der Term
`(x ∧ y) ∨ (¬x ∧ (¬y ∧ (x ∨ y)))` — Disjunktion auf `{0,1}`, Konjunktion auf `{1,2}` und
`{0,2}`. Anders als beim Zeugen `W` (min/max/min) ist dieses Wahlmuster durch eine
einheitliche Term-Komposition realisierbar. -/
theorem pattern_max_min_min_in_clone :
    ∃ t : L.Term (Fin 2),
      ActsAsMax (fun a b => t.realize ![a, b]) 0 1 ∧
      ActsAsMin (fun a b => t.realize ![a, b]) 1 2 ∧
      ActsAsMin (fun a b => t.realize ![a, b]) 0 2 :=
  ⟨tor (tand varX varY) (tand (tneg varX) (tand (tneg varY) (tor varX varY))), by decide⟩

/-- **Muster max/min/max ist erzeugbar:** der Term `(x ∧ y) ∨ ((x ∨ y) ∧ ¬(x ∧ y))`. -/
theorem pattern_max_min_max_in_clone :
    ∃ t : L.Term (Fin 2),
      ActsAsMax (fun a b => t.realize ![a, b]) 0 1 ∧
      ActsAsMin (fun a b => t.realize ![a, b]) 1 2 ∧
      ActsAsMax (fun a b => t.realize ![a, b]) 0 2 :=
  ⟨tor (tand varX varY) (tand (tor varX varY) (tneg (tand varX varY))), by decide⟩

/-! **Statement-Pins.** Voller Wortlaut links, Satz rechts — jede Drift des *Statements*
bricht den Build. Namenlose `example`s, keine Axiom-Wache. -/

-- STATEMENT-PIN
example : ContextureFaithful W := W_contexture_faithful
-- STATEMENT-PIN
example :
    ActsAsMax W 1 2 ∧ ¬ ActsAsMin W 1 2 ∧ ActsAsMin W 0 2 ∧ ¬ ActsAsMax W 0 2 := W_uneven
-- STATEMENT-PIN
example : Rho 1 0 ∧ Rho 2 2 ∧ ¬ Rho (W 1 2) (W 0 2) := rho_breaks_at_uneven_site
-- STATEMENT-PIN
example (t : L.Term (Fin 2)) (v w : Fin 2 → Fin 3) (h : ∀ i, Rho (v i) (w i)) :
    Rho (t.realize v) (t.realize w) := rho_is_invariant t v w h
-- STATEMENT-PIN
example :
    ¬ ∃ t : L.Term (Fin 2), ∀ v : Fin 2 → Fin 3, t.realize v = W (v 0) (v 1) :=
  W_not_in_clone
-- STATEMENT-PIN
example :
    ∃ f : Fin 3 → Fin 3 → Fin 3, ContextureFaithful f ∧ LocallyClassical f ∧
      ¬ ∃ t : L.Term (Fin 2), ∀ v : Fin 2 → Fin 3, t.realize v = f (v 0) (v 1) :=
  nonuniform_witness_exists

/-! ## Teil 6 — E1: die drei übrigen Zeugen

Nach derselben Schablone wie `W`: jede Definition ist die Abweichung von `min` bzw. `max`
auf den benannten Kontexturen. `W2` erhält den zweiten direkten `ρ`-Beweis; `W3` und `W4`
erhalten ihre Schranke in Teil 7 per `conj`-Transport. -/

/-- Der zweite Zeuge `W2` (Muster min/min/max): Konjunktion überall, nur auf der
Booleschen Kontextur `{0,2}` die Disjunktion. Tafel: `0 0 2 | 0 1 1 | 2 1 2`. -/
def W2 (a b : Fin 3) : Fin 3 :=
  if (a = 0 ∧ b = 2) ∨ (a = 2 ∧ b = 0) then max a b else min a b

/-- Der dritte Zeuge `W3` (Muster min/max/max): Disjunktion überall, nur auf der
gemischten Kontextur `{0,1}` die Konjunktion. Tafel: `0 0 2 | 0 1 2 | 2 2 2`. -/
def W3 (a b : Fin 3) : Fin 3 :=
  if (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) then min a b else max a b

/-- Der vierte Zeuge `W4` (Muster max/max/min): Disjunktion überall, nur auf der
Booleschen Kontextur `{0,2}` die Konjunktion. Tafel: `0 1 0 | 1 1 2 | 0 2 2`. -/
def W4 (a b : Fin 3) : Fin 3 :=
  if (a = 0 ∧ b = 2) ∨ (a = 2 ∧ b = 0) then min a b else max a b

/-- **`W2` trägt das Muster min/min/max.** -/
theorem W2_pattern : ActsAsMin W2 0 1 ∧ ActsAsMin W2 1 2 ∧ ActsAsMax W2 0 2 := by decide

/-- **`W3` trägt das Muster min/max/max.** -/
theorem W3_pattern : ActsAsMin W3 0 1 ∧ ActsAsMax W3 1 2 ∧ ActsAsMax W3 0 2 := by decide

/-- **`W4` trägt das Muster max/max/min.** -/
theorem W4_pattern : ActsAsMax W4 0 1 ∧ ActsAsMax W4 1 2 ∧ ActsAsMin W4 0 2 := by decide

/-- **Die Bruchstelle von `W2` an `ρ`:** `(0,0)` und `(1,2)` sind `ρ`-verbunden, die
Ergebnisse `(W2 0 1, W2 0 2) = (0, 2)` nicht — die min-Wahl auf `{0,1}` gegen die
max-Wahl auf `{0,2}`. Wieder sitzt der Bruch exakt an der uneinheitlichen Wahl. -/
theorem rho_breaks_at_uneven_site_W2 :
    Rho 0 0 ∧ Rho 1 2 ∧ ¬ Rho (W2 0 1) (W2 0 2) := by decide

/-- **`W2` liegt nicht im Klon** — zweiter direkter `ρ`-Beweis, Kopie der `W`-Route mit
den Belegungen `![0, 1]` und `![0, 2]`. -/
theorem W2_not_in_clone :
    ¬ ∃ t : L.Term (Fin 2), ∀ v : Fin 2 → Fin 3, t.realize v = W2 (v 0) (v 1) := by
  rintro ⟨t, ht⟩
  have h : Rho (t.realize ![0, 1]) (t.realize ![0, 2]) := by
    apply rho_is_invariant
    intro i
    revert i
    decide
  rw [ht (![0, 1]), ht (![0, 2])] at h
  exact absurd h (by decide)

/-! ## Teil 7 — E1: die `neg`-Konjugation und der Transport der Schranke

Die Konjugation `conj f = ¬ ∘ f ∘ (¬ × ¬)` ist die Symmetrie der Kontexturstruktur:
`negFin` vertauscht die gemischten Kontexturen `{0,1}` und `{1,2}` und fixiert die
Boolesche `{0,2}`. Der Klon ist unter `conj` abgeschlossen (`clone_closed_under_conj`,
per Term-Konstruktion `¬ t[¬x, ¬y]` über `Term.subst` — der eine nicht-kopierte Beweis
dieses Nachzugs), also transportiert sich Nicht-Erzeugbarkeit entlang `conj`
(`not_in_clone_conj`): `W3 = conj W` und `W4 = conj W2` erben ihre Schranke. Die
4/4-Teilung ist damit als **symmetrisch** belegt — der Strukturbefund der Sonde 15
(Zeugen gehen auf Zeugen) wird konsumiert, nicht nur gemessen. -/

/-- Die `neg`-Konjugation: `conj f = negFin ∘ f ∘ (negFin × negFin)`. -/
def conj (f : Fin 3 → Fin 3 → Fin 3) : Fin 3 → Fin 3 → Fin 3 :=
  fun a b => negFin (f (negFin a) (negFin b))

/-- `negFin` ist involutiv. -/
lemma negFin_negFin : ∀ x : Fin 3, negFin (negFin x) = x := by decide

/-- **`conj` ist involutiv** — die Konjugation ist eine Symmetrie, keine Richtung. -/
theorem conj_involutive : ∀ f : Fin 3 → Fin 3 → Fin 3, conj (conj f) = f := by
  intro f
  funext a b
  simp [conj, negFin_negFin]

/-- **`conj W = W3`:** die Konjugation trägt den Zeugen min/max/min auf min/max/max
(die gemischten Kontexturen tauschen, die Wahl dualisiert, `{0,2}` dualisiert in sich). -/
theorem conj_W_eq : conj W = W3 := by
  funext a b
  revert a b
  decide

/-- **`conj W2 = W4`:** min/min/max geht auf max/max/min. -/
theorem conj_W2_eq : conj W2 = W4 := by
  funext a b
  revert a b
  decide

/-- **Der Klon ist unter `conj` abgeschlossen.** Realisiert ein Term `t` die Operation
`f`, so realisiert der Term `¬ (t.subst (¬ var))` — außen negiert, alle Variablen negiert —
die Konjugierte `conj f`. Der eine nicht-kopierte Beweis des E1-Nachzugs: Konsum von
`Term.realize_subst` (Mathlib), keine eigene Induktion. -/
theorem clone_closed_under_conj (f : Fin 3 → Fin 3 → Fin 3)
    (h : ∃ t : L.Term (Fin 2), ∀ v : Fin 2 → Fin 3, t.realize v = f (v 0) (v 1)) :
    ∃ t : L.Term (Fin 2), ∀ v : Fin 2 → Fin 3, t.realize v = conj f (v 0) (v 1) := by
  obtain ⟨t, ht⟩ := h
  refine ⟨tneg (t.subst fun i => tneg (Term.var i)), fun v => ?_⟩
  calc (tneg (t.subst fun i => tneg (Term.var i))).realize v
      = negFin ((t.subst fun i => tneg (Term.var i)).realize v) := by
        simp [tneg, Term.realize]
    _ = negFin (t.realize fun i => negFin (v i)) := by
        rw [Term.realize_subst]
        congr 1
    _ = negFin (f (negFin (v 0)) (negFin (v 1))) := by
        rw [ht (fun i => negFin (v i))]
    _ = conj f (v 0) (v 1) := rfl

/-- **Nicht-Erzeugbarkeit transportiert entlang `conj`.** Wäre `conj f` erzeugbar, so
nach `clone_closed_under_conj` auch `conj (conj f) = f` — Kontraposition mit Involution. -/
theorem not_in_clone_conj (f : Fin 3 → Fin 3 → Fin 3)
    (h : ¬ ∃ t : L.Term (Fin 2), ∀ v : Fin 2 → Fin 3, t.realize v = f (v 0) (v 1)) :
    ¬ ∃ t : L.Term (Fin 2), ∀ v : Fin 2 → Fin 3, t.realize v = conj f (v 0) (v 1) := by
  intro hc
  exact h (by simpa [conj_involutive] using clone_closed_under_conj (conj f) hc)

/-- **`W3` liegt nicht im Klon** — per Transport (`conj W = W3`), keine Beweiskopie. -/
theorem W3_not_in_clone :
    ¬ ∃ t : L.Term (Fin 2), ∀ v : Fin 2 → Fin 3, t.realize v = W3 (v 0) (v 1) := by
  rw [← conj_W_eq]
  exact not_in_clone_conj W W_not_in_clone

/-- **`W4` liegt nicht im Klon** — per Transport (`conj W2 = W4`). -/
theorem W4_not_in_clone :
    ¬ ∃ t : L.Term (Fin 2), ∀ v : Fin 2 → Fin 3, t.realize v = W4 (v 0) (v 1) := by
  rw [← conj_W2_eq]
  exact not_in_clone_conj W2 W2_not_in_clone

/-! ## Teil 8 — E1: der Struktursatz und der Hauptsatz der Klassifikation

Der Struktursatz der Sonde 16 (§2) für `m = 3`: eine lokal-klassische Operation ist genau
ein Wahlvektor — `ofChoices c01 c12 c02` mit je einem Bit pro Elementarkontextur
(`true` = Disjunktion, `false` = Konjunktion). Zusammen mit der Injektivität liegt damit
die Zählung **genau `2^3 = 8`** im Korpus, als Bijektions-Paar statt als Kardinalzahl.
Darauf der Hauptsatz: erzeugbar sind genau die vier Vektoren
`(f,f,f), (t,f,f), (t,f,t), (t,t,t)` — die Rev2-Zielaussage „von den acht Wahlmustern
sind genau vier im Klon erzeugbar und genau vier nicht" als ein Satz. -/

/-- Der Wahlvektor als Operation: auf `{0,1}` nach `c01`, auf `{1,2}` nach `c12`, auf
`{0,2}` nach `c02` (`true` = `max`, `false` = `min`); die Diagonale ist unter beiden
Wahlen dieselbe. Die Fall-Reihenfolge ist unerheblich, da jeder Punkt `(a,b)` mit
`a ≠ b` in genau einer Kontextur liegt. -/
def ofChoices (c01 c12 c02 : Bool) (a b : Fin 3) : Fin 3 :=
  if (a = 0 ∨ a = 1) ∧ (b = 0 ∨ b = 1) then cond c01 (max a b) (min a b)
  else if (a = 1 ∨ a = 2) ∧ (b = 1 ∨ b = 2) then cond c12 (max a b) (min a b)
  else cond c02 (max a b) (min a b)

/-- **Jeder Wahlvektor ist lokal klassisch** (die eine Richtung des Struktursatzes). -/
theorem ofChoices_locally_classical :
    ∀ c01 c12 c02 : Bool, LocallyClassical (ofChoices c01 c12 c02) := by decide

/-- **Jede lokal-klassische Operation ist ein Wahlvektor** (die andere Richtung, die
Rekonstruktion): aus den drei lokalen Wahlen wird der Vektor abgelesen, die Gleichheit
punktweise über die drei `ActsAs`-Hypothesen geschlossen. -/
theorem locally_classical_reconstruct (f : Fin 3 → Fin 3 → Fin 3)
    (h : LocallyClassical f) : ∃ c01 c12 c02 : Bool, f = ofChoices c01 c12 c02 := by
  obtain ⟨h1, h2, h3⟩ := h
  have H1 : ∃ c : Bool, ∀ a b : Fin 3, (a = 0 ∨ a = 1) → (b = 0 ∨ b = 1) →
      f a b = cond c (max a b) (min a b) :=
    h1.elim (fun hm => ⟨false, hm⟩) (fun hM => ⟨true, hM⟩)
  have H2 : ∃ c : Bool, ∀ a b : Fin 3, (a = 1 ∨ a = 2) → (b = 1 ∨ b = 2) →
      f a b = cond c (max a b) (min a b) :=
    h2.elim (fun hm => ⟨false, hm⟩) (fun hM => ⟨true, hM⟩)
  have H3 : ∃ c : Bool, ∀ a b : Fin 3, (a = 0 ∨ a = 2) → (b = 0 ∨ b = 2) →
      f a b = cond c (max a b) (min a b) :=
    h3.elim (fun hm => ⟨false, hm⟩) (fun hM => ⟨true, hM⟩)
  obtain ⟨c1, H1⟩ := H1
  obtain ⟨c2, H2⟩ := H2
  obtain ⟨c3, H3⟩ := H3
  refine ⟨c1, c2, c3, ?_⟩
  -- Abdeckung: jeder Punkt liegt in einer der drei Kontexturen (Classical-frei, kein
  -- `fin_cases` — das zöge über die Fintype-Maschinerie `Classical.choice`).
  have hcov : ∀ a b : Fin 3,
      ((a = 0 ∨ a = 1) ∧ (b = 0 ∨ b = 1)) ∨ ((a = 1 ∨ a = 2) ∧ (b = 1 ∨ b = 2)) ∨
        ((a = 0 ∨ a = 2) ∧ (b = 0 ∨ b = 2)) := by decide
  funext a b
  rcases hcov a b with ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩
  · rw [H1 a b ha hb]
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
      cases c1 <;> cases c2 <;> cases c3 <;> decide
  · rw [H2 a b ha hb]
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
      cases c1 <;> cases c2 <;> cases c3 <;> decide
  · rw [H3 a b ha hb]
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
      cases c1 <;> cases c2 <;> cases c3 <;> decide

/-- **Der Struktursatz (m = 3).** Lokal klassisch ⟺ Wahlvektor. Mit
`ofChoices_injective` zusammen: es gibt *genau* `2^3` lokal-klassische Operationen —
die Zählung der Sonde 15/16 im Korpus. -/
theorem locally_classical_iff (f : Fin 3 → Fin 3 → Fin 3) :
    LocallyClassical f ↔ ∃ c01 c12 c02 : Bool, f = ofChoices c01 c12 c02 := by
  constructor
  · exact locally_classical_reconstruct f
  · rintro ⟨c1, c2, c3, rfl⟩
    exact ofChoices_locally_classical c1 c2 c3

/-- **Die Wahlvektoren sind paarweise verschieden** (Injektivität; die zweite Hälfte der
Zählung). Über drei Auswertungspunkte — je einer pro Kontextur — statt über
Funktionsraum-`decide` (das zöge `Classical.choice`). -/
theorem ofChoices_injective :
    ∀ c1 c2 c3 d1 d2 d3 : Bool, ofChoices c1 c2 c3 = ofChoices d1 d2 d3 →
      c1 = d1 ∧ c2 = d2 ∧ c3 = d3 := by
  intro c1 c2 c3 d1 d2 d3 h
  have h1 := congrFun (congrFun h 0) 1
  have h2 := congrFun (congrFun h 1) 2
  have h3 := congrFun (congrFun h 0) 2
  revert h1 h2 h3
  cases c1 <;> cases c2 <;> cases c3 <;> cases d1 <;> cases d2 <;> cases d3 <;> decide

/-- **Lokale Klassizität erzwingt Kontexturtreue** — die zweite Vorbedingung der Sonde
ist aus der ersten ableitbar (`min`/`max` eines Paars bleiben im Paar); die Klasse ist
also durch lokale Klassizität allein bestimmt. -/
theorem locally_classical_faithful (f : Fin 3 → Fin 3 → Fin 3)
    (h : LocallyClassical f) : ContextureFaithful f := by
  obtain ⟨c1, c2, c3, rfl⟩ := locally_classical_reconstruct f h
  revert c1 c2 c3
  decide

/-- Der Zeuge `W` als Wahlvektor: `(false, true, false)`. -/
lemma W_eq_ofChoices : W = ofChoices false true false := by
  funext a b; revert a b; decide

/-- `W2` als Wahlvektor: `(false, false, true)`. -/
lemma W2_eq_ofChoices : W2 = ofChoices false false true := by
  funext a b; revert a b; decide

/-- `W3` als Wahlvektor: `(false, true, true)`. -/
lemma W3_eq_ofChoices : W3 = ofChoices false true true := by
  funext a b; revert a b; decide

/-- `W4` als Wahlvektor: `(true, true, false)`. -/
lemma W4_eq_ofChoices : W4 = ofChoices true true false := by
  funext a b; revert a b; decide

/-- Eta-Gesetz für Zweier-Belegungen: `v = ![v 0, v 1]` — per `Fin.cases`, nicht per
`fin_cases`/`decide` über dem Funktionsraum (das zöge `Classical.choice`). -/
lemma vec_eta (v : Fin 2 → Fin 3) : v = ![v 0, v 1] := by
  funext i
  exact Fin.cases rfl (fun j => Fin.cases rfl (fun k => k.elim0) j) i

/-- Brücke von der punktweisen zur Belegungs-Form: genügt die Realisierung an allen
Paar-Belegungen `![a, b]`, so an jeder Belegung. Hält die `in_clone`-Beweise beim
punktweisen `decide` (81 Fälle) statt beim Funktionsraum-`decide`. -/
lemma realize_eq_of_pointwise (t : L.Term (Fin 2)) (g : Fin 3 → Fin 3 → Fin 3)
    (h : ∀ a b : Fin 3, t.realize ![a, b] = g a b) (v : Fin 2 → Fin 3) :
    t.realize v = g (v 0) (v 1) := by
  conv_lhs => rw [vec_eta v]
  exact h (v 0) (v 1)

/-- **Wahlvektor `(f,f,f)` (= `min`) ist erzeugbar:** der Term `x ∧ y`. -/
theorem ofChoices_mmm_in_clone :
    ∃ t : L.Term (Fin 2), ∀ v : Fin 2 → Fin 3,
      t.realize v = ofChoices false false false (v 0) (v 1) :=
  ⟨tand varX varY, realize_eq_of_pointwise _ _ (by decide)⟩

/-- **Wahlvektor `(t,f,f)` (Muster max/min/min) ist erzeugbar:** derselbe Term wie in
`pattern_max_min_min_in_clone`, jetzt als Tafel-Gleichheit gegen den Wahlvektor. -/
theorem ofChoices_Mmm_in_clone :
    ∃ t : L.Term (Fin 2), ∀ v : Fin 2 → Fin 3,
      t.realize v = ofChoices true false false (v 0) (v 1) :=
  ⟨tor (tand varX varY) (tand (tneg varX) (tand (tneg varY) (tor varX varY))),
    realize_eq_of_pointwise _ _ (by decide)⟩

/-- **Wahlvektor `(t,f,t)` (Muster max/min/max) ist erzeugbar.** -/
theorem ofChoices_MmM_in_clone :
    ∃ t : L.Term (Fin 2), ∀ v : Fin 2 → Fin 3,
      t.realize v = ofChoices true false true (v 0) (v 1) :=
  ⟨tor (tand varX varY) (tand (tor varX varY) (tneg (tand varX varY))),
    realize_eq_of_pointwise _ _ (by decide)⟩

/-- **Wahlvektor `(t,t,t)` (= `max`) ist erzeugbar:** der Term `x ∨ y`. -/
theorem ofChoices_max_in_clone :
    ∃ t : L.Term (Fin 2), ∀ v : Fin 2 → Fin 3,
      t.realize v = ofChoices true true true (v 0) (v 1) :=
  ⟨tor varX varY, realize_eq_of_pointwise _ _ (by decide)⟩

/-- **Der Hauptsatz der Klassifikation (Rev2-Einheit E1).** Ein Wahlvektor ist genau dann
erzeugbar, wenn er einer der vier Vektoren `(f,f,f)`, `(t,f,f)`, `(t,f,t)`, `(t,t,t)`
ist — von den acht Wahlmustern sind **genau vier** im Klon von `{∧, ∨, ¬}` erzeugbar und
**genau vier** nicht. Die Rückrichtung sind die vier expliziten Terme; die Hinrichtung
sind die vier Zeugen-Schranken (zwei direkt über `ρ`, zwei per `conj`-Transport). -/
theorem four_of_eight_generatable :
    ∀ c1 c2 c3 : Bool,
      (∃ t : L.Term (Fin 2), ∀ v : Fin 2 → Fin 3,
          t.realize v = ofChoices c1 c2 c3 (v 0) (v 1))
        ↔ ((c1, c2, c3) = (false, false, false) ∨ (c1, c2, c3) = (true, false, false)
            ∨ (c1, c2, c3) = (true, false, true) ∨ (c1, c2, c3) = (true, true, true)) := by
  intro c1 c2 c3
  cases c1 <;> cases c2 <;> cases c3
  · exact iff_of_true ofChoices_mmm_in_clone (by decide)
  · exact iff_of_false (by rw [← W2_eq_ofChoices]; exact W2_not_in_clone) (by decide)
  · exact iff_of_false (by rw [← W_eq_ofChoices]; exact W_not_in_clone) (by decide)
  · exact iff_of_false (by rw [← W3_eq_ofChoices]; exact W3_not_in_clone) (by decide)
  · exact iff_of_true ofChoices_Mmm_in_clone (by decide)
  · exact iff_of_true ofChoices_MmM_in_clone (by decide)
  · exact iff_of_false (by rw [← W4_eq_ofChoices]; exact W4_not_in_clone) (by decide)
  · exact iff_of_true ofChoices_max_in_clone (by decide)

/-- **Die Ops-Fassung der Klassifikation.** Jede lokal-klassische Operation ist entweder
erzeugbar oder einer der vier Zeugen — die Dichotomie ohne Wahlvektor-Codierung. -/
theorem locally_classical_dichotomy (f : Fin 3 → Fin 3 → Fin 3)
    (h : LocallyClassical f) :
    (∃ t : L.Term (Fin 2), ∀ v : Fin 2 → Fin 3, t.realize v = f (v 0) (v 1))
      ∨ (f = W ∨ f = W2 ∨ f = W3 ∨ f = W4) := by
  obtain ⟨c1, c2, c3, rfl⟩ := locally_classical_reconstruct f h
  cases c1 <;> cases c2 <;> cases c3
  · exact Or.inl ofChoices_mmm_in_clone
  · exact Or.inr (Or.inr (Or.inl W2_eq_ofChoices.symm))
  · exact Or.inr (Or.inl W_eq_ofChoices.symm)
  · exact Or.inr (Or.inr (Or.inr (Or.inl W3_eq_ofChoices.symm)))
  · exact Or.inl ofChoices_Mmm_in_clone
  · exact Or.inl ofChoices_MmM_in_clone
  · exact Or.inr (Or.inr (Or.inr (Or.inr W4_eq_ofChoices.symm)))
  · exact Or.inl ofChoices_max_in_clone

/-! **Statement-Pins (E1).** Voller Wortlaut links, Satz rechts — wie oben. -/

-- STATEMENT-PIN
example (f : Fin 3 → Fin 3 → Fin 3)
    (h : ∃ t : L.Term (Fin 2), ∀ v : Fin 2 → Fin 3, t.realize v = f (v 0) (v 1)) :
    ∃ t : L.Term (Fin 2), ∀ v : Fin 2 → Fin 3, t.realize v = conj f (v 0) (v 1) :=
  clone_closed_under_conj f h
-- STATEMENT-PIN
example (f : Fin 3 → Fin 3 → Fin 3) :
    LocallyClassical f ↔ ∃ c01 c12 c02 : Bool, f = ofChoices c01 c12 c02 :=
  locally_classical_iff f
-- STATEMENT-PIN
example :
    ∀ c1 c2 c3 : Bool,
      (∃ t : L.Term (Fin 2), ∀ v : Fin 2 → Fin 3,
          t.realize v = ofChoices c1 c2 c3 (v 0) (v 1))
        ↔ ((c1, c2, c3) = (false, false, false) ∨ (c1, c2, c3) = (true, false, false)
            ∨ (c1, c2, c3) = (true, false, true) ∨ (c1, c2, c3) = (true, true, true)) :=
  four_of_eight_generatable
-- STATEMENT-PIN
example (f : Fin 3 → Fin 3 → Fin 3) (h : LocallyClassical f) :
    (∃ t : L.Term (Fin 2), ∀ v : Fin 2 → Fin 3, t.realize v = f (v 0) (v 1))
      ∨ (f = W ∨ f = W2 ∨ f = W3 ∨ f = W4) :=
  locally_classical_dichotomy f h

/-! ## Teil 9 — die Axiom-Wachen (Ist-gebunden)

Ist-Ausgabe des grünen Builds (v4.30.0-rc2), pro Satz als Regressions-Wache eingefroren
(Datei-Vollständigkeits-Regel: alle Sätze der Datei). Ab hier bricht jede Axiom-Drift den
Build. Kein Satz zieht `Classical.choice` oder `sorryAx`. -/

/-- info: 'Reformulation.Proemial.NonUniformCloneBound.W_contexture_faithful' depends on axioms: [propext] -/
#guard_msgs in #print axioms W_contexture_faithful

/-- info: 'Reformulation.Proemial.NonUniformCloneBound.W_min_01' depends on axioms: [propext] -/
#guard_msgs in #print axioms W_min_01

/-- info: 'Reformulation.Proemial.NonUniformCloneBound.W_max_12' depends on axioms: [propext] -/
#guard_msgs in #print axioms W_max_12

/-- info: 'Reformulation.Proemial.NonUniformCloneBound.W_min_02' depends on axioms: [propext] -/
#guard_msgs in #print axioms W_min_02

/-- info: 'Reformulation.Proemial.NonUniformCloneBound.W_locally_classical' depends on axioms: [propext] -/
#guard_msgs in #print axioms W_locally_classical

/-- info: 'Reformulation.Proemial.NonUniformCloneBound.W_uneven' depends on axioms: [propext] -/
#guard_msgs in #print axioms W_uneven

/-- info: 'Reformulation.Proemial.NonUniformCloneBound.rho_companion' depends on axioms: [propext] -/
#guard_msgs in #print axioms rho_companion

/-- info: 'Reformulation.Proemial.NonUniformCloneBound.rho_proper' depends on axioms: [propext] -/
#guard_msgs in #print axioms rho_proper

/-- info: 'Reformulation.Proemial.NonUniformCloneBound.min_preserves_rho' depends on axioms: [propext] -/
#guard_msgs in #print axioms min_preserves_rho

/-- info: 'Reformulation.Proemial.NonUniformCloneBound.max_preserves_rho' depends on axioms: [propext] -/
#guard_msgs in #print axioms max_preserves_rho

/-- info: 'Reformulation.Proemial.NonUniformCloneBound.negFin_preserves_rho' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms negFin_preserves_rho

/-- info: 'Reformulation.Proemial.NonUniformCloneBound.rho_is_invariant' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms rho_is_invariant

/-- info: 'Reformulation.Proemial.NonUniformCloneBound.rho_breaks_at_uneven_site' depends on axioms: [propext] -/
#guard_msgs in #print axioms rho_breaks_at_uneven_site

/-- info: 'Reformulation.Proemial.NonUniformCloneBound.W_not_in_clone' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms W_not_in_clone

/-- info: 'Reformulation.Proemial.NonUniformCloneBound.nonuniform_witness_exists' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms nonuniform_witness_exists

/-- info: 'Reformulation.Proemial.NonUniformCloneBound.pattern_min_min_min_in_clone' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms pattern_min_min_min_in_clone

/-- info: 'Reformulation.Proemial.NonUniformCloneBound.pattern_max_max_max_in_clone' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms pattern_max_max_max_in_clone

/-- info: 'Reformulation.Proemial.NonUniformCloneBound.pattern_max_min_min_in_clone' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms pattern_max_min_min_in_clone

/-- info: 'Reformulation.Proemial.NonUniformCloneBound.pattern_max_min_max_in_clone' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms pattern_max_min_max_in_clone

/-! **Wachen des E1-Nachzugs (Teile 6–8).** Ist-Ausgabe des grünen Builds, verbatim.
Auch hier zieht kein Satz `Classical.choice` oder `sorryAx` — die Fintype-Pi-Fallen
(`fin_cases`, Funktionsraum-`decide`) sind in den Beweisen bewusst umgangen
(Abdeckungs-Route, `congrFun`-Punkte, `vec_eta`/`realize_eq_of_pointwise`). -/

/-- info: 'Reformulation.Proemial.NonUniformCloneBound.W2_pattern' depends on axioms: [propext] -/
#guard_msgs in #print axioms W2_pattern

/-- info: 'Reformulation.Proemial.NonUniformCloneBound.W3_pattern' depends on axioms: [propext] -/
#guard_msgs in #print axioms W3_pattern

/-- info: 'Reformulation.Proemial.NonUniformCloneBound.W4_pattern' depends on axioms: [propext] -/
#guard_msgs in #print axioms W4_pattern

/-- info: 'Reformulation.Proemial.NonUniformCloneBound.rho_breaks_at_uneven_site_W2' depends on axioms: [propext] -/
#guard_msgs in #print axioms rho_breaks_at_uneven_site_W2

/-- info: 'Reformulation.Proemial.NonUniformCloneBound.W2_not_in_clone' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms W2_not_in_clone

/-- info: 'Reformulation.Proemial.NonUniformCloneBound.conj_involutive' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms conj_involutive

/-- info: 'Reformulation.Proemial.NonUniformCloneBound.conj_W_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms conj_W_eq

/-- info: 'Reformulation.Proemial.NonUniformCloneBound.conj_W2_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms conj_W2_eq

/-- info: 'Reformulation.Proemial.NonUniformCloneBound.clone_closed_under_conj' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms clone_closed_under_conj

/-- info: 'Reformulation.Proemial.NonUniformCloneBound.not_in_clone_conj' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms not_in_clone_conj

/-- info: 'Reformulation.Proemial.NonUniformCloneBound.W3_not_in_clone' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms W3_not_in_clone

/-- info: 'Reformulation.Proemial.NonUniformCloneBound.W4_not_in_clone' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms W4_not_in_clone

/-- info: 'Reformulation.Proemial.NonUniformCloneBound.ofChoices_locally_classical' depends on axioms: [propext] -/
#guard_msgs in #print axioms ofChoices_locally_classical

/-- info: 'Reformulation.Proemial.NonUniformCloneBound.locally_classical_reconstruct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms locally_classical_reconstruct

/-- info: 'Reformulation.Proemial.NonUniformCloneBound.locally_classical_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms locally_classical_iff

/-- info: 'Reformulation.Proemial.NonUniformCloneBound.ofChoices_injective' depends on axioms: [propext] -/
#guard_msgs in #print axioms ofChoices_injective

/-- info: 'Reformulation.Proemial.NonUniformCloneBound.locally_classical_faithful' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms locally_classical_faithful

/-- info: 'Reformulation.Proemial.NonUniformCloneBound.realize_eq_of_pointwise' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms realize_eq_of_pointwise

/-- info: 'Reformulation.Proemial.NonUniformCloneBound.ofChoices_mmm_in_clone' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ofChoices_mmm_in_clone

/-- info: 'Reformulation.Proemial.NonUniformCloneBound.ofChoices_Mmm_in_clone' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ofChoices_Mmm_in_clone

/-- info: 'Reformulation.Proemial.NonUniformCloneBound.ofChoices_MmM_in_clone' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ofChoices_MmM_in_clone

/-- info: 'Reformulation.Proemial.NonUniformCloneBound.ofChoices_max_in_clone' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ofChoices_max_in_clone

/-- info: 'Reformulation.Proemial.NonUniformCloneBound.four_of_eight_generatable' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms four_of_eight_generatable

/-- info: 'Reformulation.Proemial.NonUniformCloneBound.locally_classical_dichotomy' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms locally_classical_dichotomy

end Reformulation.Proemial.NonUniformCloneBound
