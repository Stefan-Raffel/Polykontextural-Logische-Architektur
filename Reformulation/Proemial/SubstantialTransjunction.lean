import Reformulation.Proemial.RealizedTransjunction

/-!
# Reformulation.Proemial.SubstantialTransjunction — die bindende Transjunktion (Pfad A)

Zwölfte Niederlegungs-Schicht. Sie legt **Pfad A** nieder: die bindende
Transjunktion über einem *substantiellen* `K`, deren Überschreitung
*binär-interaktiv* ist (das Rejektions-Ziel hängt an BEIDEN Argumenten) und die
darum beweisbar außerhalb der um *unäre* Überschreitungen erweiterten
`internalS`-Familie sitzt. Sie überführt die explorative Sondierung
(`SubstantiellesKSondierung.lean`, nicht im Aggregat) in eine echte, ins
Aggregat aufgenommene Schicht — die Definitionen und Sätze sind dort bereits
axiom-sauber bewiesen (je nur `propext`, kein `sorryAx`); diese Schicht
überführt das Erprobte und fügt die Beglaubigungs-Substanz hinzu. Sie erfindet
in Teil 1 bis 3 nichts Neues.

## Die Stelligkeits-Pointe (der Hauptfund der Sequenz)

Der Binde-Ort ist die **Stelligkeit der Überschreitung** (des `inr`-Ziels),
nicht die Substanz von `K` an sich und nicht die Stelligkeit der Operation (die
ist immer 2-stellig in den Argumenten). Eine Überschreitung, deren Ziel an der
*Interaktion* beider Argumente hängt (binär), bindet; die *unäre*,
strukturerhaltende Überschreitung (`g a`, erstes Argument allein) bindet nicht —
sie ist gerade die funktorielle (`F.obj : S → K`). **Funktorialität ist
Unarität, Binde-Kraft verlangt Binarität; sie schließen sich aus.** Das
verklammert den C-Befund der ersten Sondierung (die Operation ist KEIN Funktor)
mit dem jetzigen: zwei Sondierungen, eine Erkenntnis.

## Die binär-trans-kontexturale Form (Grenze 4, Hermeneutes)

Bindend ist NICHT die Binarität als solche: die Multiplikation ist binär und
keine Transjunktion (sie bleibt intra-kontextural). Bindend ist die
interaktions-bestimmte Überschreitung *in die zweite Kontextur* — der `inr`-Wert,
dessen Ziel an beiden Argumenten hängt. Die Pointe trifft die günthersche
Akkretion (das Neue) nur, sofern die Binarität die System-Umwelt-Interaktion
abbildet, nicht eine bloße Zweistelligkeit.

## Werkphasen-Verankerung (Hermeneutes)

Die binäre Form ist günthersch dreifach verankert: die Transjunktion (Cybernetic
Ontology, 1962, vier Eingangs-Konstellationen); die Akkretion gegen die Iteration
(LZEE 1967; Identität Gegenidentität Negativsprache 1979); die Verbundkontextur
(Die historische Kategorie des Neuen, 1970, mit `m(m−1)/2` Vermittlungen).

## Akkretion gegen Iteration (Horistês), präzise

Unär entspricht der Iteration (kein Neues, das Ziel wiederholt die Quelle);
binär-interaktiv entspricht der Akkretion (setzt Neues, das Ziel ist aus der
Interaktion). Günther sagt „setzt Neues", NICHT „binär" — die Stelligkeits-Pointe
trifft die Akkretion nur unter der genannten Maßgabe (Binarität bildet die
Interaktion ab), nicht automatisch.

## Die Symmetrisierung (Janus)

Sie beißt (der Skeptiker wird von der Mathematik in die Metaphysik getrieben: bei
`K = Unit` ist die Rejektion kanonisch erfassbar, bei substantiellem `K` nicht),
sie zwingt nicht (dritte Sonde: die ≤unäre Lesart von „kanonisch" ist
intra-kontextural nicht erzwingbar). Die binäre Gegen-Lesart trivialisiert sich
selbst (`binary_captures_all`); das ZEIGT die Grenze, ZWINGT aber nicht. Die
Schicht legt die Symmetrisierung nieder, nicht den Zwang.

## `K = ℕ → Bool` (Hermeneutes)

Strukturell günther-treu: zwei kardinal eigenständige Bereiche mit eigenen Werten
(`S = ℕ` abzählbar, `K = ℕ → Bool` überabzählbar — keine kanonische Iso, Speculums
Zweitkopie-Falle vermieden). Es ist die günthersche *Struktur* einer Umwelt in
technischer Form, KEINE symbolische Wertbelegung im traditionellen Sinn; die
technische Form ist als solche markiert.

## „ruht auf"-Audit

Teil 1 bis 3 konsumieren: die Sum-Maschinerie (`Sum.inl`/`Sum.inr`/`cond`,
No-Confusion via `simp`); `Function.Injective`; `decide` für die
charakteristischen Funktionen. Teil 4 konsumiert zusätzlich
`CategoryTheory.Discrete` + `Discrete.functor` (Kategorien-Hüllen) und
`LiftedTransjunctiveC` (elfte Schicht); `Sum.map` für die Discrete-Hebung.

## Sorry-Bilanz

* Teil 1 (`InExtendedUnary`, `unit_captures_all`): 0 — aus der Sondierung,
  axiom-sauber.
* Teil 2 (`exTransjectA`, `exTransjectA_outside`, `rejection_targets_injective`):
  0 — instanzgebunden, kein Form α.
* Teil 3 (`exTransjectB_inside`, `binary_captures_all`): 0 — Kontrast und
  Grenz-Markierung.
* Teil 4 (`exLiftedA`, Einbettung in die Naht): 0 — die Category-Einbettung
  trägt; `exTransjectA` sitzt als `transject`-Feld über substantiellem `K`.
* Gesamt: 0 Sorries.

## Was die Schicht NICHT tut

Sie zwingt den Skeptiker nicht (Symmetrisierung, nicht Zwang); sie behauptet
nicht, Binarität als solche binde (Grenze 4); sie löst die Diskontexturalität
nicht vollständig in Positivität auf — der gesetzte Rest ist von „bindet die
Konstruktion?" auf die Stelligkeits-Lesart der Kanonizität geschrumpft, eine
eingegrenzte Naht, nicht verschwunden; sie ersetzt die elfte Schicht nicht, sie
füllt deren Naht (substantielles `K` statt binde-leerem `K = Unit`).
-/

namespace Reformulation.Proemial.SubstantialTransjunction

open CategoryTheory
open Reformulation.Proemial.RealizedTransjunction

-- ============================================================
-- Teil 1 — Die Stelligkeits-Charakterisierung (das Kriterium, Grenze 1)
-- ============================================================

/-- DIE UNÄRE erweiterte Familie (das Stelligkeits-Kriterium): `t` ist „S-intern
    plus kanonische Überschreitung", wenn die Rejektion (der `inr`-Wert) von einer
    Abbildung `g : S → K` des ERSTEN Arguments allein bestimmt ist. Die kanonische
    Überschreitung überschreitet zu einem Ziel, das an der Quell-Stelle hängt
    (wo es im Träger steht), nicht an der Interaktion beider Argumente.

    Grenze 1: diese Familie muss (a) und (b) ZUGLEICH tragen — bei `K = Unit`
    total (`unit_captures_all`), bei substantiellem `K` echte Teilmenge
    (`exTransjectA_outside`). -/
def InExtendedUnary {S K : Type*} (t : S → S → (S ⊕ K)) : Prop :=
  ∃ (op : S → S → S) (sel : S → S → Bool) (g : S → K),
    ∀ a b, t a b = cond (sel a b) (Sum.inl (op a b)) (Sum.inr (g a))

/-- (a) DIE UNIT-SEITE (Janus' Befund formal eingelöst, Grenze 1): bei
    `K = Unit` liegt JEDES `t : S → S → (S ⊕ Unit)` in der unären erweiterten
    Familie. Das einzige `g : S → Unit` ist konstant `()`; der `inr`-Zweig ist auf
    `inr ()` fixiert und trifft jeden vorkommenden Rejektionswert (es gibt nur
    einen). Darum bindet `K = Unit` NICHT — kein `transject` kann außerhalb
    sitzen. -/
theorem unit_captures_all {S : Type*} [Inhabited S]
    (t : S → S → (S ⊕ Unit)) : InExtendedUnary t := by
  refine ⟨fun a b => (t a b).elim id (fun _ => default),
          fun a b => (t a b).isLeft,
          fun _ => (), ?_⟩
  intro a b
  cases h : t a b with
  | inl s => simp [h]
  | inr u => simp [h]

-- ============================================================
-- Teil 2 — Die bindende Instanz über substantiellem K (Grenzen 2+3+4)
-- ============================================================

/-- Die BINDENDE Operation über substantiellem `K`: `S = ℕ` (unendlich, Grenze 3),
    `K = ℕ → Bool` (überabzählbar, kardinal eigenständig von `ℕ`, Grenze 3 — keine
    kanonische Iso). Bei `a = b` bleibt sie S-intern (`inl`); bei `a ≠ b` rejiziert
    sie zur charakteristischen Funktion von `{b}` — das Rejektions-Ziel KODIERT das
    *zweite* Argument (Grenze 4: binär-interaktiv, das Ziel hängt an der
    Interaktion, nicht an der Quelle allein). -/
def exTransjectA : ℕ → ℕ → (ℕ ⊕ (ℕ → Bool)) :=
  fun a b => if a = b then Sum.inl a else Sum.inr (fun n => decide (n = b))

/-- (ii) NICHT-TABELLIERBARKEIT (unendliches `S`, Grenze 3): die Rejektions-Ziele
    von `exTransjectA` sind paarweise verschieden — unendlich viele verschiedene
    Werte. Bei endlichem `S` wäre `transject` durch `|S|²` Werte tabellierbar;
    hier ist es das nicht. -/
theorem rejection_targets_injective :
    Function.Injective (fun b : ℕ => (fun n => decide (n = b))) := by
  intro b1 b2 hb
  have := congrFun hb b1
  simpa using this

/-- (iii)+(b) DER PFAD-A-KERN (Grenze 2: instanzgebunden, KEIN Form α):
    `exTransjectA` sitzt AUSSERHALB der unären erweiterten Familie. Der Beweis
    nutzt zwei endliche Zeugen `(0,1)` und `(0,2)` (gleiches erstes Argument `0`,
    beide rejizieren, aber zu VERSCHIEDENEN Zielen) — kein globales `¬∃` über alle
    Kardinalitäten oder Darstellungen. Ein unäres `g 0` müsste beide Ziele zugleich
    sein; Auswertung an `n = 1` widerlegt das.

    Hier beißt die Substanz von `K` (Grenze 3): bei `K = Unit` kollabierten die
    zwei Ziele auf `()`, der Widerspruch verschwände — genau das ist (a). -/
theorem exTransjectA_outside : ¬ InExtendedUnary exTransjectA := by
  rintro ⟨op, sel, g, h⟩
  have h1 := h 0 1
  have h2 := h 0 2
  have e1 : exTransjectA 0 1 = Sum.inr (fun n => decide (n = 1)) := rfl
  have e2 : exTransjectA 0 2 = Sum.inr (fun n => decide (n = 2)) := rfl
  rw [e1] at h1
  rw [e2] at h2
  have hg1 : g 0 = (fun n => decide (n = 1)) := by
    cases hs : sel 0 1 with
    | true => rw [hs, cond_true] at h1; exact absurd h1 (by simp)
    | false => rw [hs, cond_false] at h1; simpa using h1.symm
  have hg2 : g 0 = (fun n => decide (n = 2)) := by
    cases hs : sel 0 2 with
    | true => rw [hs, cond_true] at h2; exact absurd h2 (by simp)
    | false => rw [hs, cond_false] at h2; simpa using h2.symm
  rw [hg1] at hg2
  have := congrFun hg2 1
  simp at this

-- ============================================================
-- Teil 3 — Kontrast (unär bindet nicht) und Grenz-Markierung (binär trivialisiert)
-- ============================================================

/-- KONTRAST (der Funktor-Befund eingelöst): eine strukturerhaltende /
    funktor-artige Überschreitung läuft über `g a` — das Rejektions-Ziel hängt an
    der QUELLE allein, genau wie der `.obj`-Wechsel `S → K` der ersten Sondierung
    (`switchOfTransition`). -/
def exTransjectB (g : ℕ → (ℕ → Bool)) : ℕ → ℕ → (ℕ ⊕ (ℕ → Bool)) :=
  fun a b => if a = b then Sum.inl a else Sum.inr (g a)

/-- DER KONTRAST-BEFUND: die unäre / strukturerhaltende Überschreitung bindet
    NICHT — sie liegt INNERHALB der erweiterten Familie. Strukturerhaltung zieht
    `transject` gerade in die Familie. (Funktorialität ist Unarität; die bindende
    Operation muss interaktions-bestimmt sein, darum ist sie kein Funktor — der
    C-Befund der ersten Sondierung.) -/
theorem exTransjectB_inside (g : ℕ → (ℕ → Bool)) :
    InExtendedUnary (exTransjectB g) := by
  refine ⟨fun a _ => a, fun a b => decide (a = b), g, ?_⟩
  intro a b
  by_cases hab : a = b
  · simp [exTransjectB, hab]
  · simp [exTransjectB, hab]

/-- Die BINÄRE erweiterte Familie — die VERBOTENE „trivial-alles"-Fassung, hier
    NUR als Grenz-Markierung (nicht als Teil der bindenden Substanz): das
    Rejektions-Ziel `g a b` darf an beiden Argumenten hängen. -/
def InExtendedBinary {S K : Type*} (t : S → S → (S ⊕ K)) : Prop :=
  ∃ (op : S → S → S) (sel : S → S → Bool) (g : S → S → K),
    ∀ a b, t a b = cond (sel a b) (Sum.inl (op a b)) (Sum.inr (g a b))

/-- DIE GRENZ-MARKIERUNG (die Unär-Schranke ist nicht willkürlich): lässt man
    BINÄRE Überschreitungen zu, so liegt JEDES `t` in der Familie — (iii) ist dann
    unmöglich. Das ist die vom Prompt verbotene Trivialisierung; sie ist hier
    bewiesen, um zu zeigen, WORAN der Pfad-A-Erfolg hängt: einzig an der gesetzten
    Unär-Schranke. `no_generic_switch` erzwingt diese Schranke NICHT.

    Stelligkeits-Tabelle: nullär (fester Punkt) trägt (a)+(b)+(iii); unär (`g a`,
    Kandidat A/B) trägt (a)+(b)+(iii); binär (`g a b`) trivialisiert — nur die
    binäre Aufblähung zerstört (b). Jede (a)+(b)-Definition schneidet unter
    binär. -/
theorem binary_captures_all {S K : Type*} [Inhabited S] [Inhabited K]
    (t : S → S → (S ⊕ K)) : InExtendedBinary t := by
  refine ⟨fun a b => (t a b).elim id (fun _ => default),
          fun a b => (t a b).isLeft,
          fun a b => (t a b).elim (fun _ => default) id, ?_⟩
  intro a b
  cases h : t a b with
  | inl s => simp [h]
  | inr k => simp [h]

-- ============================================================
-- Teil 4 — Die Einbettung in die Naht (Vollendung der elften Schicht)
-- ============================================================

/-- Die Discrete-Hebung einer Operation: trägt `t` von den nackten Typen auf die
    Kategorien-Hüllen `Discrete ℕ` / `Discrete (ℕ → Bool)` (via `Sum.map` der
    `Discrete.mk`-Hüllen). So sitzt `exTransjectA` LITERAL als `transject`-Feld
    der Naht. -/
def liftToDiscrete (t : ℕ → ℕ → (ℕ ⊕ (ℕ → Bool))) :
    Discrete ℕ → Discrete ℕ → (Discrete ℕ ⊕ Discrete (ℕ → Bool)) :=
  fun a b => (t a.as b.as).map Discrete.mk Discrete.mk

/-- DIE VOLLENDUNG DER ELFTEN SCHICHT: die Realisierungs-Naht
    `LiftedTransjunctiveC` über SUBSTANTIELLEM `K` — `S = Discrete ℕ`,
    `K = Discrete (ℕ → Bool)` (zwei kardinal eigenständige Träger, anders als der
    elfte-Schicht-Zeuge `Discrete Bool` / `Discrete Unit` mit binde-leerem
    `K = Unit`). Das `transject`-Feld IST die gehobene `exTransjectA`; die
    Übergangs-Hebung schickt `n` auf die charakteristische Funktion von `{n}`
    (nicht-trivial). Die Naht, in der elften Schicht binde-leer gefüllt, trägt
    jetzt die bindende Operation über substantiellem `K`. -/
def exLiftedA : LiftedTransjunctiveC (Discrete ℕ) (Discrete (ℕ → Bool)) where
  transition := Discrete.functor (fun n => ⟨fun m => decide (m = n)⟩)
  transject  := liftToDiscrete exTransjectA
  rejects    := ⟨⟨0⟩, ⟨1⟩, ⟨fun n => decide (n = 1)⟩, rfl⟩

/-- Der Anschluss explizit: das `transject`-Feld der Naht ist punktweise die
    gehobene `exTransjectA` (Teil 2). Die Binde-Substanz (`exTransjectA_outside`)
    lebt auf der un-gehobenen Form; die Einbettung trägt sie in die Naht. -/
theorem exLiftedA_transject_eq (a b : ℕ) :
    exLiftedA.transject ⟨a⟩ ⟨b⟩ = (exTransjectA a b).map Discrete.mk Discrete.mk :=
  rfl

/-- NICHT-DEGENERATIONS-ZEUGE: die Übergangs-Hebung ist nicht-trivial — sie
    schickt verschiedene Objekte auf verschiedene charakteristische Funktionen
    (`0 ↦ {0}`, `1 ↦ {1}`), kein konstanter und kein Identitäts-Funktor. -/
theorem exLiftedA_transition_nontrivial :
    exLiftedA.transition.obj ⟨0⟩ ≠ exLiftedA.transition.obj ⟨1⟩ := by
  intro h
  have h' : (fun m => decide (m = 0)) = (fun m => decide (m = 1)) :=
    congrArg Discrete.as h
  have := congrFun h' 0
  simp at this

-- ============================================================
-- Axiom-Sauberkeit der Kerne (kein `sorryAx`)
-- ============================================================

-- Ist-Ausgabe des grünen Builds (v4.30.0-rc2), pro Satz als Regressions-Wache
-- eingefroren (Zug „Wachen-Vollzug", Datei-Vollständigkeit); ab hier bricht jede
-- Axiom-Drift den Build.
/-- info: 'Reformulation.Proemial.SubstantialTransjunction.unit_captures_all' depends on axioms: [propext] -/
#guard_msgs in #print axioms unit_captures_all

/-- info: 'Reformulation.Proemial.SubstantialTransjunction.exTransjectA_outside' depends on axioms: [propext] -/
#guard_msgs in #print axioms exTransjectA_outside

/-- info: 'Reformulation.Proemial.SubstantialTransjunction.rejection_targets_injective' depends on axioms: [propext] -/
#guard_msgs in #print axioms rejection_targets_injective

/-- info: 'Reformulation.Proemial.SubstantialTransjunction.exTransjectB_inside' depends on axioms: [propext] -/
#guard_msgs in #print axioms exTransjectB_inside

/-- info: 'Reformulation.Proemial.SubstantialTransjunction.binary_captures_all' depends on axioms: [propext] -/
#guard_msgs in #print axioms binary_captures_all

/-- info: 'Reformulation.Proemial.SubstantialTransjunction.exLiftedA_transject_eq' depends on axioms: [propext] -/
#guard_msgs in #print axioms exLiftedA_transject_eq

/-- info: 'Reformulation.Proemial.SubstantialTransjunction.exLiftedA_transition_nontrivial' depends on axioms: [propext] -/
#guard_msgs in #print axioms exLiftedA_transition_nontrivial

end Reformulation.Proemial.SubstantialTransjunction
