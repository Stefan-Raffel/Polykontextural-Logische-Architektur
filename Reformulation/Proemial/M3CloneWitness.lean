import Reformulation.Proemial.NonUniformCloneBound

/-!
# Proemial.M3CloneWitness — die M3-Grenze als Satz

Diese Datei überführt die letzte handgerechnete tragende Aussage der Architektur in einen
Satz: auf dem kleinsten flachen Verband `M3` existiert ein expliziter Term über der Basis
`{∧, ∨, ¬}`, der auf jedem **vergleichbaren** Paar klassisch wirkt und global weder
Infimum noch Supremum ist (`m3_mixed_term_exists`). Damit steht die Grenze der
E3-Charakterisierung (linear gestufte Träger) auf demselben Grund wie die
Charakterisierung selbst.

Es ist die **leichte Hälfte des Differentials**: eine Existenz mit explizitem Zeugen. Die
schwere Hälfte (E3 für alle m ≥ 4) steht seit `GeneralCloneBound`. Eine
Charakterisierungs-Schranke wird durch einen Zeugen begrenzt; mehr behauptet der Satz
nicht.

**Ertrag** (`CLAUDE.md` §4): ein Satz mit eigenem Gehalt, keine Instanz eines
Bestandssatzes.

## Der Gegenstand

`M3` mit fünf Elementen: `bot`, drei paarweise unvergleichbare Atome `a1`, `a2`, `a3`,
`top`. Die Ordnung ist `le a b :⟺ a = b ∨ a = bot ∨ b = top`; `meet` und `join` sind
Tafeln (bei gleichen Argumenten identisch; `bot`/`top` absorbieren; zwei verschiedene
Atome: `meet = bot`, `join = top`); `negM3` vertauscht `bot` und `top` und hält die Atome
fest. Vergleichbar sind 7 der 10 Paare; unvergleichbar sind genau die drei Atompaare.

**Der Träger ist ein eigener Typ, nicht `Fin 5`.** `GeneralCloneBound.strucM` ist eine
globale `L.Structure (Fin m)`-Instanz für **alle** m, also auch für `Fin 5`, dort mit
`∧ = min` über der linearen Ordnung. Eine zweite `L.Structure (Fin 5)`-Instanz mit den
M3-Tafeln erzeugte in jeder Datei, die beide importiert — das Aggregat tut es —, eine
stille Instanz-Ambiguität; welche Instanz `Term.realize` wählt, entschiede die
Instanz-Priorität und nicht der Bau. Ein `abbrev` auf `Fin 5` genügte nicht: reducible,
die Instanzsuche sähe hindurch. Der induktive Typ schließt den Diamanten aus, und die
lineare Ordnung von `Fin 5` kann nicht einsickern.

Folgerichtig **keine Mathlib-`Lattice`/`Order`-Instanz**. Die Verbandsgesetze
(Kommutativität, Assoziativität, Absorption) und die Involutions-Eigenschaften stehen als
benannte `decide`-Lemmata (Teil 2); sie tragen die Rede „M3 ist ein Verband mit
ordnungsumkehrender Involution" ohne Instanz-Risiko. Der Satz konsumiert ohnehin keine
Mathlib-Verbandslemmata.

## Der Zeuge

`tM3 = (x ∧ y) ∨ ((x ∨ y) ∧ (¬x ∧ ¬y))` über derselben Sprache `L` wie D/E1/E2/E3 —
derselbe Termkalkül, anderer Träger. Seine Tafel (Zeile = erstes Argument, Spalte =
zweites; Reihenfolge `bot, a1, a2, a3, top`) ist Definitionsfolge und `decide`-nachprüfbar:

```text
        bot  a1   a2   a3   top
  bot | bot  a1   a2   a3   bot
  a1  | a1   a1   bot  bot  a1
  a2  | a2   bot  a2   bot  a2
  a3  | a3   bot  bot  a3   a3
  top | bot  a1   a2   a3   top
```

`tM3` wirkt als **join** auf `{bot,a1}`, `{bot,a2}`, `{bot,a3}` und als **meet** auf
`{bot,top}`, `{a1,top}`, `{a2,top}`, `{a3,top}`. Widerlegungspunkte: gegen `meet` steht
`fM3 bot a1 = a1 ≠ bot`, gegen `join` steht `fM3 bot top = bot ≠ top`. Die
Nicht-Uniformität sitzt zwischen den **vergleichbaren** Paaren `{bot,a1}` und `{bot,top}`;
kein unvergleichbares Paar wird für den Bruch gebraucht.

## Warum nur vergleichbare Paare

`LocallyClassicalCmp` quantifiziert über vergleichbare Paare, und das ist Begriff und
nicht Bequemlichkeit. Die Rechtfertigung steht als **Dichotomie** (Teil 3), nicht als
Einzelbeobachtung: auf einem vergleichbaren Paar bleiben Infimum und Supremum in der
Zweiermenge (`cmp_pair_closed`), auf einem unvergleichbaren führen beide heraus
(`incomparable_pair_not_closed`, `∀`-Fassung; `meet_leaves_incomparable` als benannter
Einzelfall). Eine Zweiermenge ist genau im ersten Fall eine Elementarkontextur im Sinne
von `Definitionen.md` §2 (ein in sich geschlossener zweiwertiger Zusammenhang). Die
Begründung stand bisher als Prosa im Doc-String von `StageAggregation`; hier ist sie
Satz.

Dass „vergleichbar" dabei der Ordnungsbegriff **dieses** Verbandes ist und nicht eine
zweite, zufällig passende Relation, tragen `le_iff_meet` und `le_iff_join` (Teil 2):
`le` ist als Disjunktion definiert, `meet` und `join` als Tafeln — die Brücke zwischen
beiden ist Satz, nicht Augenschein.

## Wortlaut-Grenzen (verbindlich)

1. **Deutungs-Marke.** Bewiesen sind Existenz und Mischung auf diesem konkreten `M3`.
   „Die E3-Charakterisierung fällt auf nicht-linearen Verbänden" ist **Lesart** des
   Satzes und keine formale Negation von E3: E3 ist auf `Fin m` mit linearer Ordnung
   formuliert; eine Verbands-Fassung von E3 gibt es im Korpus nicht und sie wird hier
   nicht behauptet.
2. **Die Basis ist gewählt, nicht gefunden.** Die ordnungsumkehrende Involution ist auf
   `M3` nicht eindeutig bestimmt — die drei Atome sind beliebig permutierbar. Gewählt ist
   die atomfeste Form. Rubrik „canonical is the procedure, chosen is the basis".
3. **Zahlen bleiben draußen** (`CLAUDE.md` §6). Weder die Klongröße noch die Zeugenzahl
   noch die Termtiefe der Sondierung erscheinen im Korpus; sie sind außerhalb gerechnet
   und haben hier keine Beweiskraft. Die Tafel oben ist keine Außenzählung, sondern
   `decide`-nachprüfbare Definitionsfolge.
4. **Keine Charakterisierung behauptet.** Welcher Teil der lokal-klassischen Operationen
   auf `M3` erzeugbar ist, bleibt offen und außerhalb dieser Datei.
5. **Die Robustheits-Pflicht `CLAUDE.md` §9 greift hier nicht.** Sie gilt für
   Nicht-Erzeugbarkeits-Schranken, deren Geltung an einer Invariante hängt; dieser Satz
   ist die positive Hälfte (ein Term wird vorgezeigt, keine Schranke gezogen). Es ist
   darum keine Invariante zu prüfen und keine zu erfinden.

**Ablage:** setzungsfrei, sorry-frei, konsumiert nur Aggregat-Inhalt — Aggregat
(`CLAUDE.md` §10).
-/

open FirstOrder Language

namespace Reformulation.Proemial.M3CloneWitness

open Reformulation.Proemial.TransjunctionCloneBound
open Reformulation.Proemial.NonUniformCloneBound

/-! ## Teil 1 — der Träger, die Tafeln und die Struktur

Ein frischer induktiver Fünf-Elemente-Typ (Begründung im Dateikopf). `DecidableEq` per
`deriving`; die `Prop`-Definitionen erhalten ihre `Decidable`-Instanzen per
`inferInstanceAs` nach dem `NonUniformCloneBound`-Muster (Fallstrick 2: bei `def P : Prop`
findet die Instanzensuche sonst nichts). Keine Funktionsraum-Quantifikation
(Fallstrick 3).

**`Fintype` von Hand, nicht per `deriving`.** `deriving Fintype` übersetzt auf diesem
Träger anstandslos, trägt aber `Classical.choice` in jeden `decide`-Satz der Datei, der
über `∀ x : M3` quantifiziert. **Gemessen ist die Differenz zweier Fassungen** — dieselbe
Datei, nur die `Fintype`-Instanz getauscht: dreizehn Sätze mit
`[propext, Classical.choice, Quot.sound]` gegen dieselben dreizehn mit
`[propext, Quot.sound]`. Punktweise Sätze bleiben unberührt.

**Nicht gemessen ist der Mechanismus.** Dass die Aufzählungs-Maschinerie hinter
`deriving` das Axiom trägt, ist die naheliegende Erklärung und bleibt **Vermutung**;
geprüft wurde der Unterschied der Profile, nicht der Weg des Axioms in den Term. Der
Eintrag steht als Fallstrick 10 in `CLAUDE.md` §8, dort mit derselben Trennung. -/

/-- Der kleinste flache Verband `M3`: `bot`, drei paarweise unvergleichbare Atome, `top`.
Eigener Typ statt `Fin 5`, damit keine zweite `L.Structure (Fin 5)`-Instanz neben
`GeneralCloneBound.strucM` entsteht. -/
inductive M3
  | bot | a1 | a2 | a3 | top
  deriving DecidableEq

/-- `Fintype M3` von Hand über die Fünf-Elemente-Liste; trägt jedes `decide` über
`∀ x : M3`. Die `deriving`-Fassung zöge `Classical.choice` (Doc-String oben). -/
instance instFintypeM3 : Fintype M3 where
  elems := ⟨[M3.bot, M3.a1, M3.a2, M3.a3, M3.top], by decide⟩
  complete := by intro x; cases x <;> decide

/-- Das Infimum auf `M3`: `bot` absorbiert, `top` ist neutral, zwei verschiedene Atome
treffen sich in `bot`. -/
def meet : M3 → M3 → M3
  | .bot, _ => .bot
  | _, .bot => .bot
  | .top, y => y
  | x, .top => x
  | .a1, .a1 => .a1
  | .a2, .a2 => .a2
  | .a3, .a3 => .a3
  | _, _ => .bot

/-- Das Supremum auf `M3`: `top` absorbiert, `bot` ist neutral, zwei verschiedene Atome
vereinigen sich in `top`. -/
def join : M3 → M3 → M3
  | .top, _ => .top
  | _, .top => .top
  | .bot, y => y
  | x, .bot => x
  | .a1, .a1 => .a1
  | .a2, .a2 => .a2
  | .a3, .a3 => .a3
  | _, _ => .top

/-- Die ordnungsumkehrende Involution: `bot` und `top` tauschen, die Atome bleiben fest.
Gewählt, nicht gefunden (Wortlaut-Grenze 2 im Dateikopf). -/
def negM3 : M3 → M3
  | .bot => .top
  | .a1 => .a1
  | .a2 => .a2
  | .a3 => .a3
  | .top => .bot

/-- Die Ordnung: `a ≤ b` genau dann, wenn `a = b` oder `a` das Nullelement oder `b` das
Einselement ist. -/
def le (x y : M3) : Prop := x = y ∨ x = M3.bot ∨ y = M3.top

instance instDecidableLe (x y : M3) : Decidable (le x y) :=
  inferInstanceAs (Decidable (x = y ∨ x = M3.bot ∨ y = M3.top))

/-- Vergleichbarkeit: `x` und `y` stehen in der einen oder der anderen Richtung. -/
def Cmp (x y : M3) : Prop := le x y ∨ le y x

instance instDecidableCmp (x y : M3) : Decidable (Cmp x y) :=
  inferInstanceAs (Decidable (le x y ∨ le y x))

/-- Die Interpretation auf `M3`: `∧ = meet`, `∨ = join`, `¬ = negM3` — nach der
`struc`-Schablone aus `TransjunctionCloneBound`, auf dem eigenen Träger. -/
instance strucM3 : L.Structure M3 where
  funMap := fun {n} =>
    match n with
    | 1 => fun _ x => negM3 (x 0)
    | 2 => fun f x => match f with
        | .and => meet (x 0) (x 1)
        | .or => join (x 0) (x 1)
    | 0 => fun f _ => nomatch f
    | (_ + 3) => fun f _ => nomatch f
  RelMap := fun r _ => nomatch r

@[simp] lemma funMap_neg (x : Fin 1 → M3) :
    @Structure.funMap L M3 _ 1 UnaryFun.neg x = negM3 (x 0) := rfl

@[simp] lemma funMap_and (x : Fin 2 → M3) :
    @Structure.funMap L M3 _ 2 BinaryFun.and x = meet (x 0) (x 1) := rfl

@[simp] lemma funMap_or (x : Fin 2 → M3) :
    @Structure.funMap L M3 _ 2 BinaryFun.or x = join (x 0) (x 1) := rfl

/-! ## Teil 2 — S1: der Rahmen (`M3` ist der behauptete Gegenstand)

Die Verbandsgesetze und die Involutions-Eigenschaften als benannte Lemmata statt als
Mathlib-Instanz. Sie tragen die Rede vom Verband mit ordnungsumkehrender Involution und
belegen, dass der Träger nicht linear ist. -/

/-- **Kommutativität des Infimums.** -/
theorem meet_comm : ∀ x y : M3, meet x y = meet y x := by decide

/-- **Kommutativität des Supremums.** -/
theorem join_comm : ∀ x y : M3, join x y = join y x := by decide

/-- **Assoziativität des Infimums.** -/
theorem meet_assoc : ∀ x y z : M3, meet (meet x y) z = meet x (meet y z) := by decide

/-- **Assoziativität des Supremums.** -/
theorem join_assoc : ∀ x y z : M3, join (join x y) z = join x (join y z) := by decide

/-- **Absorption, erste Richtung.** -/
theorem meet_absorb : ∀ x y : M3, meet x (join x y) = x := by decide

/-- **Absorption, zweite Richtung.** Mit den vier Sätzen davor: `M3` ist ein Verband. -/
theorem join_absorb : ∀ x y : M3, join x (meet x y) = x := by decide

/-- **`negM3` ist involutiv.** -/
theorem negM3_involutive : ∀ x : M3, negM3 (negM3 x) = x := by decide

/-- **`negM3` ist ordnungsumkehrend**, als Äquivalenz. Mit `negM3_involutive` zusammen
trägt das die Rede von der ordnungsumkehrenden Involution.

Die Hinrichtung allein genügte sachlich: die Rückrichtung folgt aus ihr, angewandt auf
`negM3 x` und `negM3 y`, plus `negM3_involutive`. Gebaut ist trotzdem die Äquivalenz,
weil sie die spezifizierte Fassung ist — ein Statement, das schwächer ist als das
verlangte, ist eine Abweichung, auch wo es die stärkere Fassung mitbringt. -/
theorem negM3_antitone : ∀ x y : M3, le x y ↔ le (negM3 y) (negM3 x) := by decide

/-- **Der Träger ist nicht linear** (Nichttrivialität): das Atompaar `a1`, `a2` ist
unvergleichbar. Ohne diesen Beleg wäre die Einschränkung auf vergleichbare Paare leer
gesprochen und der Satz eine Aussage über eine Kette. -/
theorem atoms_incomparable : ¬ Cmp M3.a1 M3.a2 := by decide

/-- **Die Ordnung ist die Ordnung dieses Verbandes, erste Hälfte.** `le` und `meet` sind
getrennt definiert — `le` als Disjunktion, `meet` als Tafel. Ohne diesen Satz wären es
zwei Gegenstände, die zufällig zueinander passen, und `Cmp` wäre nicht als der
Ordnungsbegriff *dieses* Verbandes ausgewiesen. -/
theorem le_iff_meet : ∀ x y : M3, le x y ↔ meet x y = x := by decide

/-- **Die Ordnung ist die Ordnung dieses Verbandes, zweite Hälfte.** Dieselbe Bindung
über das Supremum. -/
theorem le_iff_join : ∀ x y : M3, le x y ↔ join x y = y := by decide

/-! ## Teil 3 — S2: die Begriffsgrenze, als Dichotomie

Die Grenze ist keine Einzelbeobachtung, sondern ein Schnitt durch alle Paare, und sie
wird hier in beiden Hälften geführt:

* auf einem **vergleichbaren** Paar bleiben `meet` und `join` **in** der Zweiermenge
  (`cmp_pair_closed`) — die Menge ist dann eine Elementarkontextur im Sinne von
  `Definitionen.md` §2 (ein in sich geschlossener zweiwertiger Zusammenhang);
* auf einem **unvergleichbaren** Paar führen beide **heraus**
  (`incomparable_pair_not_closed`) — die Menge ist dann keine.

Erst die positive Hälfte trägt die Einschränkung von `LocallyClassicalCmp` auf
vergleichbare Paare: ohne sie stünde im Korpus nur, dass ein Paar ausfällt, nicht dass
die übrigen tragen. Sie ist zugleich die Stelle, an der die Analogie zu E3 hängt — dort
quantifiziert `LocallyClassical` über *alle* Paare, weil auf `Fin m` alle vergleichbar
sind. Die Begründung stand bisher als Prosa im Doc-String von `StageAggregation`; hier
ist sie Satz. -/

/-- **S2, positive Hälfte — vergleichbare Paare sind abgeschlossen.** Auf einem
vergleichbaren Paar `{x, y}` liegen Infimum und Supremum wieder in `{x, y}`. Das ist
der Satz, der die Einschränkung von `LocallyClassicalCmp` trägt: die sieben
vergleichbaren Paare sind Elementarkontexturen. -/
theorem cmp_pair_closed : ∀ x y : M3, Cmp x y →
    (meet x y = x ∨ meet x y = y) ∧ (join x y = x ∨ join x y = y) := by decide

/-- **S2, negative Hälfte — unvergleichbare Paare sind es nicht.** Auf jedem
unvergleichbaren Paar führen Infimum *und* Supremum aus der Zweiermenge heraus. Die
`∀`-Fassung; der benannte Einzelfall steht in `meet_leaves_incomparable`. -/
theorem incomparable_pair_not_closed : ∀ x y : M3, ¬ Cmp x y →
    (meet x y ≠ x ∧ meet x y ≠ y) ∧ (join x y ≠ x ∧ join x y ≠ y) := by decide

/-- **S2 — der benannte Einzelfall.** Das Atompaar `{a1, a2}` ist unvergleichbar, und
`meet` führt aus ihm heraus: `meet a1 a2` ist weder `a1` noch `a2` (es ist `bot`). Die
Zweiermenge ist unter `meet` nicht abgeschlossen und damit keine Elementarkontextur.
Instanz von `incomparable_pair_not_closed`, hier eigens benannt, weil der Statement-Pin
und die Nennorte auf ihn zeigen. -/
theorem meet_leaves_incomparable :
    ¬ Cmp M3.a1 M3.a2 ∧ meet M3.a1 M3.a2 ≠ M3.a1 ∧ meet M3.a1 M3.a2 ≠ M3.a2 := by decide

/-! ## Teil 4 — die lokalen Prädikate und der Zeuge

`ActsAsMeet` / `ActsAsJoin` nach der `ActsAsMin`/`ActsAsMax`-Schablone aus
`NonUniformCloneBound`, mit `meet`/`join` statt `min`/`max`. `LocallyClassicalCmp`
quantifiziert nur über vergleichbare Paare (Teil 3). -/

/-- `f` wirkt auf `{x, y}` als Konjunktion: dort ist `f = meet`. -/
def ActsAsMeet (f : M3 → M3 → M3) (x y : M3) : Prop :=
  ∀ a b : M3, (a = x ∨ a = y) → (b = x ∨ b = y) → f a b = meet a b

instance instDecidableActsAsMeet (f : M3 → M3 → M3) (x y : M3) :
    Decidable (ActsAsMeet f x y) :=
  inferInstanceAs (Decidable (∀ a b : M3,
    (a = x ∨ a = y) → (b = x ∨ b = y) → f a b = meet a b))

/-- `f` wirkt auf `{x, y}` als Disjunktion: dort ist `f = join`. -/
def ActsAsJoin (f : M3 → M3 → M3) (x y : M3) : Prop :=
  ∀ a b : M3, (a = x ∨ a = y) → (b = x ∨ b = y) → f a b = join a b

instance instDecidableActsAsJoin (f : M3 → M3 → M3) (x y : M3) :
    Decidable (ActsAsJoin f x y) :=
  inferInstanceAs (Decidable (∀ a b : M3,
    (a = x ∨ a = y) → (b = x ∨ b = y) → f a b = join a b))

/-- Lokale Klassizität auf `M3`: auf **jedem vergleichbaren** Paar `x ≠ y` wirkt `f` wie
`meet` oder wie `join`. Die Einschränkung auf vergleichbare Paare ist Begriff, nicht
Bequemlichkeit — `meet_leaves_incomparable`. -/
def LocallyClassicalCmp (f : M3 → M3 → M3) : Prop :=
  ∀ x y : M3, x ≠ y → Cmp x y → ActsAsMeet f x y ∨ ActsAsJoin f x y

instance instDecidableLocallyClassicalCmp (f : M3 → M3 → M3) :
    Decidable (LocallyClassicalCmp f) :=
  inferInstanceAs (Decidable (∀ x y : M3, x ≠ y → Cmp x y →
    ActsAsMeet f x y ∨ ActsAsJoin f x y))

/-- Der Zeugen-Term `(x ∧ y) ∨ ((x ∨ y) ∧ (¬x ∧ ¬y))`, gebaut aus den
strukturunabhängigen Term-Konstruktoren von `NonUniformCloneBound`. Dieselbe Sprache `L`
wie in D/E1/E2/E3 — derselbe Termkalkül, anderer Träger. -/
def tM3 : L.Term (Fin 2) :=
  tor (tand varX varY) (tand (tor varX varY) (tand (tneg varX) (tneg varY)))

/-- Die Realisierung des Zeugen auf `M3`. Tafel im Dateikopf. -/
def fM3 (a b : M3) : M3 := tM3.realize ![a, b]

/-! ## Teil 5 — S3 bis S6: der Zeuge, die Mischung und der Zielsatz -/

/-- **S3 — der Zeuge wirkt lokal klassisch.** Auf jedem vergleichbaren Paar ist `fM3`
entweder das Infimum oder das Supremum. -/
theorem tM3_locally_classical : LocallyClassicalCmp fM3 := by decide

/-- **S4 — die Mischung ist echt** (das Analogon zu `NonUniformCloneBound.W_uneven`): auf
`{bot, a1}` ist `fM3` das Supremum und **nicht** das Infimum, auf `{bot, top}` das
Infimum und **nicht** das Supremum. Beide Paare sind vergleichbar und enthalten `bot`;
für den Bruch wird kein unvergleichbares Paar gebraucht. -/
theorem tM3_mixed :
    ActsAsJoin fM3 M3.bot M3.a1 ∧ ¬ ActsAsMeet fM3 M3.bot M3.a1 ∧
      ActsAsMeet fM3 M3.bot M3.top ∧ ¬ ActsAsJoin fM3 M3.bot M3.top := by decide

/-- **S5 — der Widerlegungspunkt gegen das Infimum:** `fM3 bot a1 = a1`, aber
`meet bot a1 = bot`. -/
theorem tM3_ne_meet : fM3 M3.bot M3.a1 ≠ meet M3.bot M3.a1 := by decide

/-- **S5 — der Widerlegungspunkt gegen das Supremum:** `fM3 bot top = bot`, aber
`join bot top = top`. -/
theorem tM3_ne_join : fM3 M3.bot M3.top ≠ join M3.bot M3.top := by decide

/-- **S6 — der Zielsatz (die M3-Grenze als Satz).** Es existiert ein Term über der Basis
`{∧, ∨, ¬}`, dessen Realisierung auf `M3` auf jedem vergleichbaren Paar klassisch wirkt
und global weder das Infimum noch das Supremum ist. Zeuge ist `tM3`; die
Funktions-Ungleichungen folgen punktweise aus `tM3_ne_meet` und `tM3_ne_join`
(`congrFun`, kein `funext`-Umweg).

Lesart (Deutung, kein Satzgehalt): die E3-Charakterisierung ist an lineare Stufung
gebunden. Formal negiert wird E3 damit nicht — E3 ist auf `Fin m` formuliert, eine
Verbands-Fassung gibt es im Korpus nicht. -/
theorem m3_mixed_term_exists :
    ∃ t : L.Term (Fin 2),
      LocallyClassicalCmp (fun a b => t.realize ![a, b]) ∧
        (fun a b : M3 => t.realize ![a, b]) ≠ meet ∧
        (fun a b : M3 => t.realize ![a, b]) ≠ join := by
  refine ⟨tM3, tM3_locally_classical, ?_, ?_⟩
  · intro h
    exact tM3_ne_meet (congrFun (congrFun h M3.bot) M3.a1)
  · intro h
    exact tM3_ne_join (congrFun (congrFun h M3.bot) M3.top)

/-! **Statement-Pins.** Voller Wortlaut links, Satz rechts — jede Drift des *Statements*
bricht den Build. Namenlose `example`s, keine Axiom-Wache. -/

-- STATEMENT-PIN
example : ∀ x y : M3, Cmp x y →
    (meet x y = x ∨ meet x y = y) ∧ (join x y = x ∨ join x y = y) :=
  cmp_pair_closed
-- STATEMENT-PIN
example :
    ¬ Cmp M3.a1 M3.a2 ∧ meet M3.a1 M3.a2 ≠ M3.a1 ∧ meet M3.a1 M3.a2 ≠ M3.a2 :=
  meet_leaves_incomparable
-- STATEMENT-PIN
example : LocallyClassicalCmp fM3 := tM3_locally_classical
-- STATEMENT-PIN
example :
    ∃ t : L.Term (Fin 2),
      LocallyClassicalCmp (fun a b => t.realize ![a, b]) ∧
        (fun a b : M3 => t.realize ![a, b]) ≠ meet ∧
        (fun a b : M3 => t.realize ![a, b]) ≠ join :=
  m3_mixed_term_exists

/-! ## Teil 6 — die Axiom-Wachen (Ist-gebunden)

Ist-Ausgabe des grünen Builds (v4.30.0-rc2), pro Satz als Regressions-Wache eingefroren
(Datei-Vollständigkeits-Regel: alle Sätze der Datei). Ab hier bricht jede Axiom-Drift den
Build. **Kein Satz zieht `Classical.choice` oder `sorryAx`** — der Weg dahin steht in
Teil 1 (Handinstanz statt `deriving Fintype`), gemessen und nicht geschätzt. -/

/-- info: 'Reformulation.Proemial.M3CloneWitness.meet_comm' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms meet_comm

/-- info: 'Reformulation.Proemial.M3CloneWitness.join_comm' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms join_comm

/-- info: 'Reformulation.Proemial.M3CloneWitness.meet_assoc' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms meet_assoc

/-- info: 'Reformulation.Proemial.M3CloneWitness.join_assoc' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms join_assoc

/-- info: 'Reformulation.Proemial.M3CloneWitness.meet_absorb' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms meet_absorb

/-- info: 'Reformulation.Proemial.M3CloneWitness.join_absorb' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms join_absorb

/-- info: 'Reformulation.Proemial.M3CloneWitness.negM3_involutive' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms negM3_involutive

/-- info: 'Reformulation.Proemial.M3CloneWitness.negM3_antitone' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms negM3_antitone

/-- info: 'Reformulation.Proemial.M3CloneWitness.le_iff_meet' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms le_iff_meet

/-- info: 'Reformulation.Proemial.M3CloneWitness.le_iff_join' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms le_iff_join

/-- info: 'Reformulation.Proemial.M3CloneWitness.atoms_incomparable' does not depend on any axioms -/
#guard_msgs in #print axioms atoms_incomparable

/-- info: 'Reformulation.Proemial.M3CloneWitness.cmp_pair_closed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms cmp_pair_closed

/-- info: 'Reformulation.Proemial.M3CloneWitness.incomparable_pair_not_closed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms incomparable_pair_not_closed

/-- info: 'Reformulation.Proemial.M3CloneWitness.meet_leaves_incomparable' depends on axioms: [propext] -/
#guard_msgs in #print axioms meet_leaves_incomparable

/-- info: 'Reformulation.Proemial.M3CloneWitness.tM3_locally_classical' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms tM3_locally_classical

/-- info: 'Reformulation.Proemial.M3CloneWitness.tM3_mixed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms tM3_mixed

/-- info: 'Reformulation.Proemial.M3CloneWitness.tM3_ne_meet' depends on axioms: [propext] -/
#guard_msgs in #print axioms tM3_ne_meet

/-- info: 'Reformulation.Proemial.M3CloneWitness.tM3_ne_join' depends on axioms: [propext] -/
#guard_msgs in #print axioms tM3_ne_join

/-- info: 'Reformulation.Proemial.M3CloneWitness.m3_mixed_term_exists' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms m3_mixed_term_exists

end Reformulation.Proemial.M3CloneWitness
