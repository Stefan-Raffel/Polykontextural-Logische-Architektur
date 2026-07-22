import Reformulation.Proemial.ReversibleExchange

/-!
# Reformulation.Proemial.IrreversibleAdvance — der irreversible Fortgang (dreiundzwanzigste Schicht)

Die **zweite Mittelstelle** der achtfachen Thematik: das dritte Intervall, die
irreversible Zeit, bekommt seine Fassung als **Rückkehrfreiheit** — kein Zustand
kehrt je zurück. Das Aufstiegs-Differential der 16. wird dabei **nicht
nachgebaut, sondern als Stellen-Fassung konsumiert** (das Rang-Lemma als geerbte
Prüfbarkeit); die beiden Natur-Nachbarn St.2/St.3 werden term-getrennt; die
„kommt nirgends an"-Sätze zeigen, dass die rein irreversible Welt weder Grund
noch Erschöpfungs-Ziel kennt. Der positive Zeuge ist `Nat.succ` — die Stufung
selbst.

**Ein Import** (`ReversibleExchange`, transitiv `IntervalBackbone`,
`RecurringGround`, `ExhaustionTransition`, `IrreversibleAscent`); die Kette wird
16→19→20→22→23. Term-identisch konsumiert werden `Reversible` und
`reversible_pointwise_periodic` (22.), `intervalStart`/`intervalEnd` (21.),
`FixpointFree`/`no_ground_in_fixpointfree`/`Ground`/`swap` (20.),
`Exhausts`/`collapse` (19.), `PointwisePeriodic`/`no_return_of_strict_rank`/
`succ_iterate'` (16.). Nichts wird dupliziert; **kein Mathlib-Import über die
transitive Hülle hinaus**.

## (1) Quellen

Der Anker im Wortlaut: „müssen wir mindestens zum dritten Intervall übergehen …
zum ersten Mal eine dreiwertige Thematik … die vollkommene Symmetrie von
Position und Negation … aufgehoben" (Lille Z. 493–496, **Volltext-verifiziert**).
Die Zeit-Dreiheit reversibel / irreversibel / Komplementarität als Rolle der drei
Mittelstellen: Z. 484–486. „Physik": Z. 512–513. Der Ort (Intervall III als
Abschnitt des 14-wertigen Systems): Z. 517–519. Härte-Ökonomie: einmal geeicht
(Beiträge III, S. 160, druck-verifiziert), verlängerbar.

## (2) HEGEL-RELATIVITÄTS-MARKE

Die Zuordnung „Physik = Intervall III" ist **Lesart der Hegel-Stufe**, nicht Satz
dieser Schicht: Günther meldet „ernsthafte Zweifel" (Z. 921–922) an und nennt die
Zuordnung „nur relativ" (Z. 936–938); gesichert ist allein die Gliederung „je
drei Intervalle".

## (3) Substrat-Erbe

Der Ort (`interval_III_start`, `interval_III_end`) kommt aus dem Rückgrat (21.) —
**das Rückgrat zählt, diese Schicht deutet**. Die Orts-Sätze sind Substrat-Abruf,
ihre Arithmetik ist dort term-fest.

## (4) SYMMETRIE-BRUCH-MARKE

Günthers Bruch betrifft **wörtlich Position/Negation der Werte-Struktur** — das
ist Werte-Semantik und liegt **außerhalb dieses Baus**. Die Verbindung des
Quell-Bruchs zur hier term-gebauten St.2/St.3-Trennung (`noreturn_not_periodic`,
`noreturn_not_reversible`) ist **Deutung**, kein Satz. Term-fest wird die
Trennung der Iterations-Klassen, nicht der Bruch einer Werte-Symmetrie.

## (5) Term-fest werden hiermit

`noreturn_fixpointfree`, `noreturn_not_periodic`, `noreturn_not_reversible`,
`noreturn_no_ground`, `noreturn_no_exhaustion`, `noreturn_of_strict_rank`,
`succ_noreturn`, `swap_not_noreturn`, `collapse_not_noreturn`,
`interval_III_start`, `interval_III_end`, Kür `succ_noreturn_via_rank`.

**KONSUM-EHRLICHKEIT:** eigener Beweis-Gehalt liegt im succ-Zeugen und den zwei
Nonempty-Trennungen; alles Übrige ist Kontraposition (`noreturn_fixpointfree` ist
der n=1-Fall) oder benannter Konsum. **Das Aufstiegs-Differential bleibt Eigentum
der 16.** — `noreturn_of_strict_rank` ist seine Stellen-Fassung per Konsum, kein
Duplikat. Das ist die **Bauform-These der Mittelstellen**: Merkmal + Ort +
Anschlüsse, **kein neuer Apparat**. Die Stelle *liegt außerhalb* der armen Klasse
der Periodik — das ist ihr Befund, kein Differential-Ersatz.

## (6) Deutungs-Marken

`NoReturn` als Lesart der irreversiblen Zeit ist **Deutung**; die Zuordnung der
Formalisierung zur Stelle 3 ist **strukturanalytisch**; „dreiwertig" ist
Themen-Rede (die Zahl der Themen des dritten Intervalls), keine Werte-Semantik;
„kommt nirgends an" ist markierte Struktur-Aussage über die Sätze
`noreturn_no_ground`/`noreturn_no_exhaustion`, **kein Zitat**; die Träger `Fin 2`
und `ℕ` der Zeugen sind **Modellwahl**; **Designation ≠ Denotation** gilt fort.

## (7) Abgrenzung

Kein Vorgriff auf St.4 (Komplementarität) — eigenes Paket. Keine Werte-Semantik,
keine Zeit-Metaphysik. Die U5-Figuren bleiben benannte Posten. Die
Nonempty-Bedingung der zwei Trennungs-Sätze ist **Voraussetzungs-Ehrlichkeit,
keine Setzung**: auf leerem Träger sind beide Prädikate leer wahr.

## (8) Sorry-Bilanz und Axiom-Ist

**0 Sorries.** Axiom-Ist (erster grüner Build, v4.30.0-rc2), je Satz
`#guard_msgs`-verwacht am Datei-Ende:

* **axiom-frei:** `noreturn_fixpointfree`, `noreturn_not_periodic`,
  `noreturn_not_reversible`, `noreturn_no_ground`, `noreturn_no_exhaustion`,
  `interval_III_start`, `interval_III_end`.
* **`[propext]`:** `swap_not_noreturn`, `collapse_not_noreturn`
  (`decide`-Hülle über `Fin 2`).
* **`[propext, Quot.sound]`:** `noreturn_of_strict_rank`, `succ_noreturn`,
  `succ_noreturn_via_rank` (`omega`-Hülle über ℕ).

**Kein `Classical`** — insbesondere tragen die beiden Nonempty-Sätze es nicht:
`obtain ⟨x⟩ := ‹Nonempty α›` auf einem Prop-Ziel ist `Nonempty.elim` und bleibt
axiom-frei (Routen-Bestätigung, verwacht statt behauptet).

**Abweichung (gewöhnliche Notiz, kein Blocker):** die Erwartung „Kontraposition
und Konsum frei bis `[propext]`" trifft für `noreturn_of_strict_rank` **nicht** —
der Satz trägt `[propext, Quot.sound]`. Grund: die `omega`-Hülle des konsumierten
`no_return_of_strict_rank` (16., über `rank_add_le_iterate`) **reist mit dem
Konsum mit**. Konsum erbt das Profil des Konsumierten; er kann es nicht
unterbieten. Die fünf übrigen Kontrapositions- und Konsum-Sätze unterschreiten
die Erwartung dagegen (axiom-frei), weil ihre Quellen (`no_ground_in_fixpointfree`,
20.) selbst axiom-frei sind.

**ZWEI-ROUTEN-MESSUNG (der gezielte vierte Hüllen-Datenpunkt):** `succ_noreturn`
(direkte Route: `succ_iterate'`-Konsum + `omega`) und `succ_noreturn_via_rank`
(Konsum-Route: Rang = `id` über das Rang-Lemma) tragen **dasselbe Profil**
`[propext, Quot.sound]`. Der kontrollierte Vergleich ergibt also **keinen
Unterschied** — beide Wege laufen durch dieselbe `omega`-Hülle, die direkte über
`succ_iterate'`, die Konsum-Route über `rank_add_le_iterate` im Rang-Lemma. Das
Ergebnis ist ein Befund über die Hülle, nicht über die Routen: an einer
ℕ-Iterations-Aussage kauft der Konsum kein schärferes Profil.

## (9) Rang-Anspruch (Superlativ-Regel, Ist-geprüft)

„**Erster ℕ-Zeuge einer Stelle**" ist geprüft an den vier Stellen-Schichten:
19. (`collapse : Fin 2 → Fin 2`), 20. (`collapse`, `swap : Fin 2 → Fin 2`),
21. (**keine Zeugen** — Substrat, per eigener Substrat-Marke), 22. (`swap`,
`collapse`, beide `Fin 2`). `Nat.succ` ist damit der erste ℕ-Zeuge **einer
Stelle**. Ausdrücklich **nicht** behauptet ist ein erster ℕ-Zeuge überhaupt: die
16. führt `Nat.succ` bereits als Zeugen ihres Differentials — sie ist keine
Stellen-Schicht, und diese Schicht konsumiert genau von dort. Weitere
Rang-Ansprüche werden nicht erhoben.
-/

namespace Reformulation.Proemial.IrreversibleAdvance

open Reformulation.Proemial.ReversibleExchange
open Reformulation.Proemial.IntervalBackbone
open Reformulation.Proemial.RecurringGround
open Reformulation.Proemial.ExhaustionTransition
open Reformulation.Proemial.IrreversibleAscent

-- ============================================================
-- Teil 1 — Das Merkmal (M1)
-- ============================================================

/-- Die Rückkehrfreiheit: kein Zustand kehrt je zurück — echt stärker als
    `FixpointFree` (dessen n=1-Fall). Die Zuordnung zum „irreversiblen" dritten
    Intervall (Stelle 3) ist strukturanalytisch; `NoReturn` als Lesart der
    irreversiblen Zeit ist Deutung. -/
def NoReturn {α : Type*} (f : α → α) : Prop := ∀ x n, 0 < n → f^[n] x ≠ x

-- ============================================================
-- Teil 2 — Die Trennungs-Familie (M2)
-- ============================================================

/-- n=1-Fall: Rückkehrfreiheit erzwingt Fixpunktfreiheit (`f^[1] x` ist defeq
    zu `f x`). Kontraposition der Definitionen — Konsum-Ehrlichkeit, Rubrik (5). -/
theorem noreturn_fixpointfree {α : Type*} {f : α → α}
    (h : NoReturn f) : FixpointFree f :=
  fun x hx => h x 1 Nat.one_pos hx

/-- NATUR-NACHBAR-TRENNUNG I: die rückkehrfreie Welt ist nicht punktweise
    periodisch — St.3 liegt außerhalb der armen Klasse, in der St.2 zuhause ist.
    Die Nonempty-Bedingung ist Voraussetzungs-Ehrlichkeit: auf leerem Träger sind
    beide Prädikate leer wahr. Ohne `Classical` (Rubrik (8)). -/
theorem noreturn_not_periodic {α : Type*} [Nonempty α] {f : α → α}
    (h : NoReturn f) : ¬ PointwisePeriodic f := by
  intro hp
  obtain ⟨x⟩ := ‹Nonempty α›
  obtain ⟨n, hn, hfx⟩ := hp x
  exact h x n hn hfx

/-- NATUR-NACHBAR-TRENNUNG II (direkt): rückkehrfreie Zeit ist nicht reversibel —
    über die Brücke der 22. Die Verbindung zu Günthers Symmetrie-Bruch ist
    Deutung, nicht dieser Satz (SYMMETRIE-BRUCH-MARKE, Rubrik (4)). -/
theorem noreturn_not_reversible {α : Type*} [Nonempty α] {f : α → α}
    (h : NoReturn f) : ¬ Reversible f :=
  fun hr => noreturn_not_periodic h (reversible_pointwise_periodic hr)

/-- „KOMMT NIRGENDS AN" I: in der rückkehrfreien Welt gibt es keinen Grund —
    Konsum von `no_ground_in_fixpointfree` (20.) über den n=1-Fall. -/
theorem noreturn_no_ground {α : Type*} {f : α → α}
    (h : NoReturn f) : ∀ a, ¬ Ground f a :=
  no_ground_in_fixpointfree (noreturn_fixpointfree h)

/-- „KOMMT NIRGENDS AN" II: kein Erschöpfungs-Übergang — das Ziel der achten
    Stelle existiert hier nicht. Über die Grund-Komponente von `Exhausts`
    (`.1`; term-identisches Muster zu `exhausts_ground`, 20.). -/
theorem noreturn_no_exhaustion {α : Type*} {f : α → α}
    (h : NoReturn f) : ∀ x b, ¬ Exhausts f x b :=
  fun _ b he => noreturn_no_ground h b he.1

-- ============================================================
-- Teil 3 — Stellen-Fassung des Rang-Lemmas (M3; Konsum, kein Duplikat)
-- ============================================================

/-- Das Rang-Lemma als geerbte Prüfbarkeit: strikt steigender Rang erzwingt
    Rückkehrfreiheit — die hinreichende Bedingung, als Stellen-Satz benannt.
    Reiner Konsum von `no_return_of_strict_rank` (16.), dessen Konklusions-Form
    `(x : α) (k : ℕ) (hk : 0 < k) : f^[k] x ≠ x` genau `NoReturn f` ist; `f` ist
    dort explizit. Das Differential bleibt Eigentum der 16. -/
theorem noreturn_of_strict_rank {α : Type*} {f : α → α}
    (rank : α → ℕ) (hrank : ∀ x, rank x < rank (f x)) : NoReturn f :=
  no_return_of_strict_rank f rank hrank

-- ============================================================
-- Teil 4 — Zeugen und Orts-Sätze (M4/M5)
-- ============================================================

/-- Der erste ℕ-Zeuge einer Stelle (Rang-Anspruch Ist-geprüft, Rubrik (9)): die
    Stufung selbst ist rückkehrfrei. Direkte Route: `succ_iterate'` (16.,
    `Nat.succ^[k] n = n + k`) plus `omega` — Mathlib führt kein
    `Nat.succ_iterate`, die 16. hat den Namen bereits, also Konsum statt
    Neubeweis und kein neuer Import. -/
theorem succ_noreturn : NoReturn Nat.succ := by
  intro x n hn
  rw [succ_iterate']
  omega

/-- Geteilter Gegen-Zeuge: `swap` (20.) kehrt zurück (Periode 2) … -/
theorem swap_not_noreturn : ¬ NoReturn swap :=
  fun h => h 0 2 (by decide) (by decide)

/-- … und `collapse` (19.) steht (Grund bei 1) — beide Zeugen der
    Nachbar-Stellen liegen außerhalb der Stelle 3. -/
theorem collapse_not_noreturn : ¬ NoReturn collapse :=
  fun h => h 1 1 (by decide) (by decide)

/-- Der Ort aus dem Rückgrat (21.; Lille Z. 517–519): Intervall III beginnt
    bei 6 … -/
theorem interval_III_start : intervalStart 3 = 6 := by decide

/-- … und endet bei 9 — Substrat-Abruf. -/
theorem interval_III_end : intervalEnd 3 = 9 := by decide

-- ============================================================
-- Teil 5 — Kür (K1; die Zwei-Routen-Messung)
-- ============================================================

/-- KÜR (der gezielte vierte Hüllen-Datenpunkt): derselbe Satz auf der
    Konsum-Route — Rang = `id` über das Rang-Lemma. Kein Routen-Entscheid: beide
    Sätze werden geliefert, der Vergleich ist der Zweck. Ergebnis der Messung
    (Rubrik (8)): **beide Routen tragen dasselbe Profil** `[propext, Quot.sound]`
    — an einer ℕ-Iterations-Aussage kauft der Konsum kein schärferes Profil. -/
theorem succ_noreturn_via_rank : NoReturn Nat.succ :=
  noreturn_of_strict_rank id (fun x => Nat.lt_succ_self x)

end Reformulation.Proemial.IrreversibleAdvance

-- ============================================================
-- Teil 6 — Die `#guard_msgs`-Wachen (M7; Ist-gebunden)
-- ============================================================

-- Ist-Ausgabe des ersten grünen Builds (v4.30.0-rc2), pro Satz als Wache.
open Reformulation.Proemial.IrreversibleAdvance in
section

/-- info: 'Reformulation.Proemial.IrreversibleAdvance.noreturn_fixpointfree' does not depend on any axioms -/
#guard_msgs in #print axioms noreturn_fixpointfree

/-- info: 'Reformulation.Proemial.IrreversibleAdvance.noreturn_not_periodic' does not depend on any axioms -/
#guard_msgs in #print axioms noreturn_not_periodic

/-- info: 'Reformulation.Proemial.IrreversibleAdvance.noreturn_not_reversible' does not depend on any axioms -/
#guard_msgs in #print axioms noreturn_not_reversible

/-- info: 'Reformulation.Proemial.IrreversibleAdvance.noreturn_no_ground' does not depend on any axioms -/
#guard_msgs in #print axioms noreturn_no_ground

/-- info: 'Reformulation.Proemial.IrreversibleAdvance.noreturn_no_exhaustion' does not depend on any axioms -/
#guard_msgs in #print axioms noreturn_no_exhaustion

/-- info: 'Reformulation.Proemial.IrreversibleAdvance.noreturn_of_strict_rank' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms noreturn_of_strict_rank

/-- info: 'Reformulation.Proemial.IrreversibleAdvance.succ_noreturn' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms succ_noreturn

/-- info: 'Reformulation.Proemial.IrreversibleAdvance.swap_not_noreturn' depends on axioms: [propext] -/
#guard_msgs in #print axioms swap_not_noreturn

/-- info: 'Reformulation.Proemial.IrreversibleAdvance.collapse_not_noreturn' depends on axioms: [propext] -/
#guard_msgs in #print axioms collapse_not_noreturn

/-- info: 'Reformulation.Proemial.IrreversibleAdvance.interval_III_start' does not depend on any axioms -/
#guard_msgs in #print axioms interval_III_start

/-- info: 'Reformulation.Proemial.IrreversibleAdvance.interval_III_end' does not depend on any axioms -/
#guard_msgs in #print axioms interval_III_end

/-- info: 'Reformulation.Proemial.IrreversibleAdvance.succ_noreturn_via_rank' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms succ_noreturn_via_rank

end
