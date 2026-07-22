import Reformulation.Proemial.IrreversibleAdvance

/-!
# Reformulation.Proemial.ComplementaryMediation — die komplementäre Vermittlung (vierundzwanzigste Schicht)

Die **Schluss-Stelle der Natur**: das vierte Intervall, die Komplementarität als
„Vermittlung", bekommt seine Fassung als **Koexistenz** — ein Träger, in dem
beide Zeit-Formen echt zusammen bestehen: ein wiederkehrender Punkt UND ein nie
zurückkehrender. Die Dritt-Klassen-Sätze trennen die Stelle von **beiden**
Nachbarn (damit sind die drei Natur-Klassen paarweise getrennt), und der Zeuge
ist die **Summe der Nachbar-Zeugen selbst**: `Sum.map swap Nat.succ` — links
kreist die 20., rechts steigt die 23. Das Intervall-Ende ist Konsum des eigenen
Zitat-Ankers (`nature_closes_at_14`): die Natur schließt 14-wertig.

**Ein Import** (`IrreversibleAdvance`, transitiv die gesamte Kette und das
Substrat); die Kette wird 16→19→20→22→23→24. Term-identisch konsumiert werden
`NoReturn`/`succ_noreturn` (23.), `Reversible`/`reversible_pointwise_periodic`/
`swap_reversible` (22.), `swap` (20.), `intervalStart`/`intervalEnd`/
`nature_closes_at_14` (21.). Nichts wird dupliziert; **kein Mathlib-Import über
die transitive Hülle hinaus**.

## (1) Quellen

Der Anker im Wortlaut: „Strukturen …, die Zweiwertigkeit und Dreiwertigkeit
miteinander vermitteln" (Lille Z. 506–508, **Volltext-verifiziert**). Die
Zeit-Dreiheit reversibel / irreversibel / Komplementarität: Z. 484–508.
„Organik": Z. 512–513. Der Ort (Intervall IV als Abschnitt des 14-wertigen
Systems): Z. 517–519. Härte-Ökonomie: einmal geeicht (Beiträge III, S. 160,
druck-verifiziert), verlängerbar.

## (2) HEGEL-RELATIVITÄTS-MARKE

Die Zuordnung „Organik = Intervall IV" ist **Lesart der Hegel-Stufe**, nicht Satz
dieser Schicht: Günther meldet „ernsthafte Zweifel" (Z. 921–922) an und nennt die
Zuordnung „nur relativ" (Z. 936–938); gesichert ist allein die Gliederung „je
drei Intervalle".

## (3) Substrat-Erbe

Der Ort (`interval_IV_start`, `interval_IV_end`) kommt aus dem Rückgrat (21.) —
**das Rückgrat zählt, diese Schicht deutet**. Die Orts-Sätze sind Substrat-Abruf,
ihre Arithmetik ist dort term-fest.

## (4) VERMITTLUNGS-MARKE

Günthers „vermitteln" betrifft **wörtlich die Werte-Struktur** (Zweiwertigkeit
und Dreiwertigkeit) — das ist Werte-Semantik und liegt **außerhalb dieses Baus**.
Die **Koexistenz-Lesart** von „vermitteln" ist **Deutung**, kein Satz: term-fest
wird das Zusammenbestehen zweier Iterations-Verhalten in einem Träger, nicht eine
Vermittlung von Wertigkeiten. Und ausdrücklich: **der Quanten-Sinn der
Komplementarität (Weizsäcker, Scheibe; Lille Fn. 9 und Fn. 10) wird nicht
formalisiert und nicht beansprucht.**

## (5) Term-fest werden hiermit

`reversible_noreturn_empty`, `mediates_not_reversible`, `mediates_not_noreturn`,
`mediator_mediates`, `interval_IV_start`, `interval_IV_end`, Kür
`swap_not_mediates`, `succ_not_mediates`.

**KONSUM-EHRLICHKEIT:** eigener Beweis-Gehalt liegt in der Schnitt-Leere, den
zwei Dritt-Klassen-Sätzen und den beiden Iterations-Helfern; **der Zeugen-Bau und
das Orts-Ende sind Konsum**. Der Zeuge ist wörtlich die Summe der
Nachbar-Zeugen — kein neuer Zeuge wird erfunden; das Intervall-Ende ist der
Anker-Satz der 21. selbst. Das ist die **Bauform-These der Mittelstellen** in
ihrer dritten Einlösung: Merkmal + Ort + Anschlüsse, **kein neuer Apparat**.

## (6) Deutungs-Marken

`Mediates` als Lesart der Komplementarität ist **Deutung**; die Zuordnung der
Formalisierung zur Stelle 4 ist **strukturanalytisch**; „zweiwertig" und
„dreiwertig" sind Themen-Rede bzw. Werte-Rede der Quelle, hier keine
Werte-Semantik; der **Summen-Träger** `Fin 2 ⊕ ℕ` ist **Modellwahl** (die
Koexistenz ist an ihm gezeigt, nicht auf ihn festgelegt); **Designation ≠
Denotation** gilt fort.

## (7) Abgrenzung

Kein Vorgriff auf die Hebdomas — eigenes Paket. Keine Werte-Semantik und keine
Zeit-Semantik. Die U5-Figuren und die Vollkommene-Zahlen-Beobachtung (von
Foerster, Z. 660–692) bleiben benannte Posten. Die Nonempty-Bedingung der
Schnitt-Leere ist **Voraussetzungs-Ehrlichkeit, keine Setzung**: auf leerem
Träger sind beide Prädikate leer wahr, und der Schnitt ist bewohnt.

## (8) Sorry-Bilanz und Axiom-Ist

**0 Sorries.** Axiom-Ist (erster grüner Build, v4.30.0-rc2), je Satz
`#guard_msgs`-verwacht am Datei-Ende — **mit Abgleich gegen die Profil-Rechnung**
(Vererbungs-Satz und Taktik × Träger):

* **axiom-frei:** `reversible_noreturn_empty`, `mediates_not_reversible`,
  `mediates_not_noreturn`, `interval_IV_start`, `interval_IV_end`.
* **`[propext]`:** `swap_not_mediates` (`decide`-Hülle über `Fin 2`, geerbt aus
  `swap_reversible` der 22.).
* **`[propext, Quot.sound]`:** `mediator_mediates`, `succ_not_mediates`
  (mitreisende `omega`-Hülle über `succ_noreturn` der 23.).

**Kein `Classical`** — auch der Nonempty-Satz nicht.

**Abgleich gegen die Profil-Rechnung (M6(8)) — zwei Treffer, eine
Unterbietung:**

* **Getroffen, und der wichtigere der beiden:** `interval_IV_end` ist
  **axiom-frei**, wie gerechnet — der Konsum eines axiom-freien Ankers bleibt
  axiom-frei. Eine Abweichung hier wäre ein Befund erster Ordnung gewesen; sie
  tritt nicht ein.
* **Getroffen:** `mediator_mediates` und `succ_not_mediates` tragen
  `[propext, Quot.sound]` — genau die `omega`-Hülle, die der Vererbungs-Satz für
  alles vorhersagt, was `succ_noreturn` konsumiert.
* **Unterboten (Verschärfung, kein Blocker):** M2/M3 waren „frei bis `[propext]`
  (Erbe aus 22. und 23.)" gerechnet, liegen aber **axiom-frei**. Grund: die
  Erwartung hatte die Quellen zu grob veranschlagt — konsumiert wird allein
  `reversible_pointwise_periodic` (22.), und die ist selbst axiom-frei; die
  `Fin 2`-`decide`-Hüllen der 22. sitzen in deren *Zeugen*, die hier nicht
  einlaufen. Damit ist die Unterbietung keine Verfehlung des Vererbungs-Satzes,
  sondern seine **Bestätigung gegen eine zu lasche Anwendung**: er sagt das
  Profil der *tatsächlich* konsumierten Quelle voraus, nicht das der
  Herkunfts-Schicht im Ganzen. Die Rechnung wird künftig an den Quell-Sätzen
  angesetzt, nicht an den Quell-Schichten.

Das Vorhersage-Instrument der 23. hält damit an seiner ersten Anwendung: sechs
von acht Profilen sind vorab ausgerechnet und getroffen; die zwei Abweichungen
gehen beide nach oben und erklären sich aus derselben Regel.
-/

namespace Reformulation.Proemial.ComplementaryMediation

open Reformulation.Proemial.IrreversibleAdvance
open Reformulation.Proemial.ReversibleExchange
open Reformulation.Proemial.IntervalBackbone
open Reformulation.Proemial.RecurringGround
open Reformulation.Proemial.ExhaustionTransition
open Reformulation.Proemial.IrreversibleAscent

-- ============================================================
-- Teil 1 — Das Merkmal (M1)
-- ============================================================

/-- Die Vermittlung als Koexistenz: ein Träger, in dem beide Zeit-Formen echt
    zusammen bestehen — ein wiederkehrender Punkt UND ein nie zurückkehrender.
    Die Zuordnung zur „Komplementarität" des vierten Intervalls (Stelle 4) ist
    strukturanalytisch; Koexistenz als Lesart von „vermitteln" ist Deutung. -/
def Mediates {α : Type*} (f : α → α) : Prop :=
  (∃ x, ∃ n, 0 < n ∧ f^[n] x = x) ∧ (∃ y, ∀ n, 0 < n → f^[n] y ≠ y)

-- ============================================================
-- Teil 2 — Schnitt-Leere und Dritt-Klassen-Sätze (M2/M3)
-- ============================================================

/-- SCHNITT-LEERE: auf bewohntem Träger ist kein f zugleich reversibel und
    rückkehrfrei — die Trennung der 23., zur Disjunktheit verschärft (über die
    Brücke der 22.: reversibel → jeder Punkt kehrt bei einer positiven Stufe
    zurück). -/
theorem reversible_noreturn_empty {α : Type*} [Nonempty α] {f : α → α} :
    ¬ (Reversible f ∧ NoReturn f) := by
  rintro ⟨hr, hnr⟩
  obtain ⟨x⟩ := ‹Nonempty α›
  obtain ⟨n, hn, hfx⟩ := reversible_pointwise_periodic hr x
  exact hnr x n hn hfx

/-- Wer vermittelt, ist nicht reversibel: die fliehende Komponente widerspricht
    der Rückkehr aller Punkte. -/
theorem mediates_not_reversible {α : Type*} {f : α → α}
    (h : Mediates f) : ¬ Reversible f := by
  rintro hr
  obtain ⟨y, hy⟩ := h.2
  obtain ⟨n, hn, hfy⟩ := reversible_pointwise_periodic hr y
  exact hy n hn hfy

/-- Wer vermittelt, ist nicht rückkehrfrei: die wiederkehrende Komponente
    widerspricht der Flucht aller Punkte. St.4 liegt term-fest außerhalb BEIDER
    Nachbar-Klassen — die drei Natur-Stellen sind paarweise getrennt. -/
theorem mediates_not_noreturn {α : Type*} {f : α → α}
    (h : Mediates f) : ¬ NoReturn f := by
  rintro hnr
  obtain ⟨x, n, hn, hfx⟩ := h.1
  exact hnr x n hn hfx

-- ============================================================
-- Teil 3 — Der Summen-Zeuge (M4)
-- ============================================================

/-- DER ZEUGE AUS DER SUMME DER NACHBARN: links kreist der `swap` (20.), rechts
    steigt der `Nat.succ` (23.) — die Vermittlung besteht aus den Vermittelten;
    kein neuer Zeuge wird erfunden. Summen-Träger: Modellwahl. -/
def mediator : Fin 2 ⊕ ℕ → Fin 2 ⊕ ℕ := Sum.map swap Nat.succ

/-- Iterations-Helfer, linke Seite (Teil 0 (1): Mathlib führt kein
    `Sum.map`-Iterations-Lemma, also eigene Induktion — punktweise genügt). -/
private theorem mediator_iterate_inl (a : Fin 2) (n : ℕ) :
    mediator^[n] (Sum.inl a) = Sum.inl (swap^[n] a) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply']; rfl

/-- Iterations-Helfer, rechte Seite. -/
private theorem mediator_iterate_inr (b : ℕ) (n : ℕ) :
    mediator^[n] (Sum.inr b) = Sum.inr (Nat.succ^[n] b) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply']; rfl

/-- Der `mediator` vermittelt: `inl 0` kehrt wieder (Periode 2 des swap — Abruf
    von `swap_reversible` (22.), da `f^[2] x` defeq zu `f (f x)` ist), `inr 0`
    flieht (Rückkehrfreiheit des succ — Abruf von `succ_noreturn` (23.)). Beide
    Hälften sind Konsum; eigener Gehalt liegt allein in den Helfern. -/
theorem mediator_mediates : Mediates mediator := by
  constructor
  · exact ⟨Sum.inl 0, 2, Nat.zero_lt_two, by
      rw [mediator_iterate_inl]
      exact congrArg Sum.inl (swap_reversible 0)⟩
  · exact ⟨Sum.inr 0, fun n hn h => by
      rw [mediator_iterate_inr] at h
      exact succ_noreturn 0 n hn (Sum.inr.inj h)⟩

-- ============================================================
-- Teil 4 — Orts-Sätze (M5)
-- ============================================================

/-- Der Ort aus dem Rückgrat (21.; Lille Z. 517–519): Intervall IV beginnt
    bei 10 … -/
theorem interval_IV_start : intervalStart 4 = 10 := by decide

/-- … und die Natur schließt 14-wertig — KONSUM des Zitat-Ankers der 21.: die
    Schluss-Stelle ruft ihren eigenen Anker ab, statt ihn nachzurechnen. -/
theorem interval_IV_end : intervalEnd 4 = 14 := nature_closes_at_14

-- ============================================================
-- Teil 5 — Kür (K1; die Zeugen-Reinheit)
-- ============================================================

/-- KÜR — Zeugen-Reinheit I: `swap` vermittelt nicht (alles kreist; die
    Flucht-Komponente scheitert an der Periode 2). -/
theorem swap_not_mediates : ¬ Mediates swap := by
  rintro ⟨_, y, hy⟩
  exact hy 2 Nat.zero_lt_two (swap_reversible y)

/-- KÜR — Zeugen-Reinheit II: `Nat.succ` vermittelt nicht (alles steigt; die
    Wiederkehr-Komponente scheitert an `succ_noreturn`). Damit hat jede der drei
    Natur-Klassen einen Zeugen in genau ihrer Klasse. -/
theorem succ_not_mediates : ¬ Mediates Nat.succ := by
  rintro ⟨⟨x, n, hn, hfx⟩, _⟩
  exact succ_noreturn x n hn hfx

end Reformulation.Proemial.ComplementaryMediation

-- ============================================================
-- Teil 6 — Die `#guard_msgs`-Wachen (M7; Ist-gebunden)
-- ============================================================

-- Ist-Ausgabe des ersten grünen Builds (v4.30.0-rc2), pro Satz als Wache.
open Reformulation.Proemial.ComplementaryMediation in
section

/-- info: 'Reformulation.Proemial.ComplementaryMediation.reversible_noreturn_empty' does not depend on any axioms -/
#guard_msgs in #print axioms reversible_noreturn_empty

/-- info: 'Reformulation.Proemial.ComplementaryMediation.mediates_not_reversible' does not depend on any axioms -/
#guard_msgs in #print axioms mediates_not_reversible

/-- info: 'Reformulation.Proemial.ComplementaryMediation.mediates_not_noreturn' does not depend on any axioms -/
#guard_msgs in #print axioms mediates_not_noreturn

/-- info: 'Reformulation.Proemial.ComplementaryMediation.mediator_mediates' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms mediator_mediates

/-- info: 'Reformulation.Proemial.ComplementaryMediation.interval_IV_start' does not depend on any axioms -/
#guard_msgs in #print axioms interval_IV_start

/-- info: 'Reformulation.Proemial.ComplementaryMediation.interval_IV_end' does not depend on any axioms -/
#guard_msgs in #print axioms interval_IV_end

/-- info: 'Reformulation.Proemial.ComplementaryMediation.swap_not_mediates' depends on axioms: [propext] -/
#guard_msgs in #print axioms swap_not_mediates

/-- info: 'Reformulation.Proemial.ComplementaryMediation.succ_not_mediates' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms succ_not_mediates

end
