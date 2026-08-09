import Reformulation.Kenogram.PlaceSwap

/-!
# Kenogram.IdentifiedConcat — Verkettung zweier Reihen unter einer Identifikation

**Ertrag.** Eine Operation und vier Sätze über sie. Die Verkettung nimmt zwei
Reihen **und eine Identifikation** — eine injektive Umbenennung der Symbole der
hinteren Reihe — und liefert eine Reihe in Normalform.

* **Z1** (`concatWith_isRGS_length`) — das Ergebnis ist wohlgeformt, und seine
  Länge ist die Summe der Längen. Ohne Voraussetzung an `a` und `b`.
* **Z2** (`concatWith_dropLast`) — der Abstieg auf der verketteten Reihe wirkt
  auf dem hinteren Teil, solange dieser nicht leer ist.
* **Z3** (`concatWith_pair_not_injective`) — aus der verketteten Reihe ist die
  **Zerlegung** nicht zurückgewinnbar; dazu `concatWith_ambiguous_nonempty`, das
  denselben Befund an vier **nichtleeren** wohlgeformten Reihen zeigt.
* Dazu zwei Sätze, die die Bauform der Operation festhalten:
  `concatWith_take_left` (die vordere Reihe steht unverändert im Ergebnis, in
  Normalform) und `concatWith_pattern_right` (das Gleichheitsmuster der hinteren
  Reihe überlebt die Identifikation, Stelle für Stelle).

## Die Grenzformel

**Bewiesen ist eine Konstruktion über Reihen und ihre Eigenschaften; über
Relata, Stufenwechsel oder proemiale Bewegung sagt kein Satz dieses Moduls
etwas.**

Z2 ist eine Gleichung zwischen zwei Listenoperationen, Z3 die Nichtinjektivität
einer Abbildung. Keiner der beiden redet von einer Bewegung, von einem Vergessen
oder davon, dass Relata zusammengingen.

## Die Herkunft der Operation, als Zuschreibung mit Fundstelle

Die Operation stammt aus Mahler, *Morphogrammatik*, Kap. 3.3.5.2 (die
kenogrammatische Verkettung mit Def. 3.17/3.18) und Kap. 3.3.5.3 (die
**indizierte** Verkettung, die sie eindeutig macht). Dort ist der Index eine
Liste von Tripeln über Gleichheits- und Verschiedenheitsbeziehungen, die einer
**Konsistenzbedingung** genügen muss.

**Hier steht die funktionale Fassung**: die Identifikation ist eine Abbildung
und kein Tripel-Register. Der Grund ist die Beweislast — bei einer Abbildung
ist die Transitivität, die Mahler als Bedingung stellen muss, keine Bedingung,
sondern eine Eigenschaft der Gleichheit von Bildern; ein inkonsistenter Index
ist gar nicht erst formulierbar.

**Was hier ausdrücklich nicht behauptet wird**, zweifach: dass die funktionale
Fassung mit Mahlers Fassung **äquivalent** sei — das ist ein Argument der
Lektüre-Notiz und in diesem Modul nicht bewiesen —, und dass Mahler eine
Leistung für die proemiale Frage gezeigt oder beansprucht hätte. Er hat die
Operation; über ihren Dienst an jener Frage sagt sein Kapitel nichts.

## Warum die Identifikation eine **Einbettung** ist, und nicht irgendeine Abbildung

Gemessen, nicht gewählt. Mit einer beliebigen Abbildung `g : ℕ → ℕ` zerfällt das
Gleichheitsmuster der hinteren Reihe: über allen Reihen der Länge höchstens drei
und 125 Kandidaten für `g` gezählt, verletzen **165** Fälle die Erhaltung des
Musters, unter injektivem `g` **null**. Die Verkettung, die Mahler beschreibt,
lässt `a` unverändert und das **Muster** von `b` konstant; variabel ist allein,
womit die Symbole von `b` belegt werden. Eine Abbildung, die zwei Symbole von
`b` zusammenwirft, ist darum keine Identifikation im Sinn der Operation,
sondern eine andere Operation.

Der Typ `ℕ ↪ ℕ` trägt diese Bedingung, statt sie als Nebenbedingung an die Sätze
zu hängen. **Was er nicht leistet:** dass jede auf den Symbolen von `b`
injektive Belegung sich zu einer Einbettung von `ℕ` fortsetzt, ist hier **nicht
bewiesen** — elementar, aber ungemessen.

## Was Z3 nicht sagt, und was nicht gemessen ist

Z3 steht in der **schwächeren** Fassung: die **Zerlegung** ist nicht
zurückgewinnbar. Über die Identifikation sagt er nichts, und das hat einen
gemessenen Grund: über allen Paaren von Reihen der Länge höchstens drei und
allen Paaren aus 125 Kandidaten für `g` gibt es **280488** Paare, die dasselbe
Ergebnis liefern und die Symbole von `b` verschieden belegen — und **null**
davon sind mehr als eine Umbenennung der neu eingeführten Symbole.

**Ob die Identifikation echte Freiheit trägt, ist damit nicht entschieden,
sondern in diesem Bereich nicht gefunden.** Ausserhalb des gezählten Bereichs
— längere Reihen, grössere Wertevorräte — ist es **ungemessen**. Der Korpus
führt hier keine Aussage, weil er keine hat.

**Und eine zweite Reichweitengrenze, damit die zwei Sätze nicht
zusammengelesen werden:** Z3 gilt für **jede** Identifikation, sein Zeuge
benutzt aber die leere Reihe; der nichtleere Zeuge daneben ist für die
**Identität** gebaut. *Für jede Identifikation ein nichtleerer Zeuge* ist
**nicht gemessen** und steht hier nicht.

## Deutungsgrenzen

**Eine Kopplung ist kein Grund.** Diese Sätze konstituieren **keine**
Proemialrelation. Z2 koppelt zwei Operationen über Listen; daraus folgt nichts
über einen Grund, eine Richtung oder ein Voraus.

Kein Deklarationsname dieses Moduls trägt ein Deutungswort.

## Der Ort, und ein Fund am Rand

`Reformulation/Kenogram/`, auf der Listen-Linie (`PlaceSwap`, `Descent`,
`JointClosure`) und nicht auf der Subtyp-Linie `RGS n`. Der Grund ist die
Bauforderung, dass die Wohlgeformtheit **erzeugt** und nicht vorausgesetzt wird:
über `RGS n` wäre sie eine Voraussetzung an die Argumente und Z1 kein Satz,
sondern eine Typangabe. Dazu trägt die Listen-Linie die Bausteine — `relabel_take`
und `relabel_dropLast` stehen in `PlaceSwap` und sind choice-frei.

**Der Fund:** die allgemeine Aussage, dass die Kanonisierung eine injektive
Umbenennung nicht sieht, steht als `Proemial.RelabelInvariance.relabel_map_of_injective`
im Bestand — und ist von hier aus **nicht konsumierbar**, weil der
Kenogram-Zweig `Proemial` nie importiert. `concatWith_pattern_right` ist darum
keine Dublette: er sagt etwas anderes, nämlich dass das Muster von `b` **an
seinen Stellen im Ergebnis** überlebt, mit dem Versatz um `a.length`. Dass die
allgemeine Fassung auf der falschen Seite der Importrichtung liegt, ist ein
Posten für einen eigenen Zug und keiner für diesen.

## Profil

`Classical.choice` tragen **zwei** Sätze — `concatWith_isRGS_length` über
`relabel_isRGS` und `concatWith_pattern_right` über `relabel_getElem?_eq_iff`;
beide Bausteine tragen ihn (gemessen, Wachen in `Basic.lean`), er ist **geerbt**
und nicht hier erzeugt. Z2 und `concatWith_take_left` laufen über
`relabel_dropLast` und `relabel_take` und sind choice-frei; Z3 ist es ebenfalls,
und `concatWith_ambiguous_nonempty` ist **axiomfrei**.

## Aggregat-Reife

Konsumiert `Kenogram.PlaceSwap` — Aggregat — sowie Mathlib. Keine Sonde, keine
Setzung.

Kein `sorry`, kein `axiom`, kein `: True`-Feld.
-/

namespace Reformulation.Kenogram

/-! ## Teil 1 — die Operation -/

/-- **Die Verkettung unter einer Identifikation.** `g` sagt, welches Symbol von
`b` mit welchem von `a` zusammenfällt und welches neu ist; `a` geht unverändert
ein, und die Wohlgeformtheit des Ergebnisses wird durch die Kanonisierung
**erzeugt** und nicht von den Argumenten verlangt.

Die Injektivität von `g` ist im Typ und keine Nebenbedingung — siehe den
Dateikopf, wo sie gemessen begründet ist. -/
def concatWith (g : ℕ ↪ ℕ) (a b : List ℕ) : List ℕ := relabel (a ++ b.map g)

/-! ## Teil 2 — Z1 und die zwei Sätze zur Bauform -/

/-- **Z1.** Das Ergebnis ist eine wohlgeformte Reihe, und seine Länge ist die
Summe der Längen. **Ohne Voraussetzung an `a` und `b`** — das ist die Satzform
davon, dass die Kanonisierung die Wohlgeformtheit erzeugt. -/
theorem concatWith_isRGS_length (g : ℕ ↪ ℕ) (a b : List ℕ) :
    IsRGS (concatWith g a b) ∧
      (concatWith g a b).length = a.length + b.length := by
  refine ⟨relabel_isRGS _, ?_⟩
  rw [concatWith, relabel_length, List.length_append, List.length_map]

/-- **Die vordere Reihe steht unverändert im Ergebnis** — genauer: ihre
Normalform steht dort, und für eine wohlgeformte Reihe ist das sie selbst. Der
Satz steht hier, weil diese Eigenschaft der Signatur **nicht** anzusehen ist:
sie hängt an der Präfix-Verträglichkeit der Kanonisierung. -/
theorem concatWith_take_left (g : ℕ ↪ ℕ) (a b : List ℕ) :
    (concatWith g a b).take a.length = relabel a := by
  rw [concatWith, ← relabel_take, List.take_left]

/-- **Das Gleichheitsmuster der hinteren Reihe überlebt die Identifikation.**
Zwei Stellen von `b` stimmen im Ergebnis genau dann überein, wenn sie es in `b`
tun — an ihren Plätzen im Ergebnis, also um `a.length` versetzt. Auch dieser
Satz steht hier, weil die Eigenschaft der Signatur nicht anzusehen ist; sie
hängt an der Injektivität von `g`. -/
theorem concatWith_pattern_right (g : ℕ ↪ ℕ) (a b : List ℕ) (i j : ℕ) :
    ((concatWith g a b)[a.length + i]? = (concatWith g a b)[a.length + j]?)
      ↔ (b[i]? = b[j]?) := by
  rw [concatWith, relabel_getElem?_eq_iff,
    List.getElem?_append_right (by omega), List.getElem?_append_right (by omega)]
  simp only [Nat.add_sub_cancel_left, List.getElem?_map]
  exact ⟨fun h => Option.map_injective g.injective h, fun h => by rw [h]⟩

/-! ## Teil 3 — Z2, die Kopplung mit dem Abstieg -/

/-- **Z2.** Der Abstieg auf der verketteten Reihe wirkt auf dem hinteren Teil.

**Die Voraussetzung ist tragend und gemessen, nicht vorsichtshalber gesetzt:**
über allen Reihen der Länge höchstens vier und 125 Kandidaten für `g` fällt die
Gleichung für `b = []` in **2875** Fällen — nämlich in allen, in denen `a`
nicht leer ist. Dort streicht der Abstieg links, wo die Gleichung ihn rechts
nicht findet. Mit der Voraussetzung: **null** Gegenbeispiele. -/
theorem concatWith_dropLast (g : ℕ ↪ ℕ) (a : List ℕ) {b : List ℕ} (hb : b ≠ []) :
    (concatWith g a b).dropLast = concatWith g a b.dropLast := by
  rw [concatWith, concatWith, ← relabel_dropLast]
  congr 1
  rw [List.dropLast_append_of_ne_nil (by simpa using hb)]
  simp [List.dropLast_eq_take, List.length_map, List.map_take]

/-! ## Teil 4 — Z3, was nicht zurückgewinnbar ist -/

/-- **Z3.** Aus der verketteten Reihe ist die **Zerlegung** nicht
zurückgewinnbar: die Abbildung, die einem Paar seine Verkettung zuordnet, ist
für **keine** Identifikation injektiv.

Der Zeuge des Beweises benutzt die leere Reihe; die nichtentartete Gestalt
desselben Befunds steht daneben in `concatWith_ambiguous_nonempty`. -/
theorem concatWith_pair_not_injective (g : ℕ ↪ ℕ) :
    ¬ Function.Injective (fun p : List ℕ × List ℕ => concatWith g p.1 p.2) := by
  intro h
  have hpair : (([], [0]) : List ℕ × List ℕ) = ([0], []) := by
    apply h
    show concatWith g [] [0] = concatWith g [0] []
    simp [concatWith, relabel]
  exact absurd (congrArg Prod.fst hpair) (by decide)

/-- **Z3, nichtentartet.** Derselbe Befund an vier **nichtleeren** und
**wohlgeformten** Reihen: `[0]` mit `[0,0]` und `[0,0]` mit `[0]` liefern
dieselbe Reihe. Der Satz steht daneben, weil der Zeuge von Z3 die leere Reihe
benutzt und die Nichtinjektivität sonst als Randfall gelesen werden könnte.

**Er gilt für die Identität und nicht für jede Identifikation** — die
allgemeine Fassung ist ungemessen, siehe Kopf. -/
theorem concatWith_ambiguous_nonempty :
    ∃ a₁ b₁ a₂ b₂ : List ℕ,
      (a₁, b₁) ≠ (a₂, b₂) ∧ a₁ ≠ [] ∧ b₁ ≠ [] ∧ a₂ ≠ [] ∧ b₂ ≠ [] ∧
      IsRGS a₁ ∧ IsRGS b₁ ∧ IsRGS a₂ ∧ IsRGS b₂ ∧
      concatWith (Function.Embedding.refl ℕ) a₁ b₁
        = concatWith (Function.Embedding.refl ℕ) a₂ b₂ :=
  ⟨[0], [0, 0], [0, 0], [0], by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, rfl⟩

/-! ## Teil 5 — Statement-Pins

Voller Wortlaut links, Satz rechts — jede Drift des *Statements* bricht den Bau. -/

-- STATEMENT-PIN
example (g : ℕ ↪ ℕ) (a b : List ℕ) :
    IsRGS (relabel (a ++ b.map g)) ∧
      (relabel (a ++ b.map g)).length = a.length + b.length :=
  concatWith_isRGS_length g a b

-- STATEMENT-PIN
example (g : ℕ ↪ ℕ) (a b : List ℕ) (hb : b ≠ []) :
    (concatWith g a b).dropLast = concatWith g a b.dropLast :=
  concatWith_dropLast g a hb

-- STATEMENT-PIN
example (g : ℕ ↪ ℕ) :
    ¬ Function.Injective (fun p : List ℕ × List ℕ => concatWith g p.1 p.2) :=
  concatWith_pair_not_injective g

-- STATEMENT-PIN
example (g : ℕ ↪ ℕ) (a b : List ℕ) (i j : ℕ) :
    ((concatWith g a b)[a.length + i]? = (concatWith g a b)[a.length + j]?)
      ↔ (b[i]? = b[j]?) :=
  concatWith_pattern_right g a b i j

/-! ## Teil 6 — die Axiom-Wachen (Ist-gebunden)

Ist-Ausgabe des grünen Builds. `Classical.choice` ist geerbt, siehe Kopf. -/

/-- info: 'Reformulation.Kenogram.concatWith_isRGS_length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms concatWith_isRGS_length

/-- info: 'Reformulation.Kenogram.concatWith_take_left' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms concatWith_take_left

/-- info: 'Reformulation.Kenogram.concatWith_pattern_right' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms concatWith_pattern_right

/-- info: 'Reformulation.Kenogram.concatWith_dropLast' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms concatWith_dropLast

/-- info: 'Reformulation.Kenogram.concatWith_pair_not_injective' depends on axioms: [propext] -/
#guard_msgs in #print axioms concatWith_pair_not_injective

/-- info: 'Reformulation.Kenogram.concatWith_ambiguous_nonempty' does not depend on any axioms -/
#guard_msgs in #print axioms concatWith_ambiguous_nonempty

end Reformulation.Kenogram
