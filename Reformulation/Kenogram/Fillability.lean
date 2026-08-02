import Reformulation.Kenogram.Basic

/-!
# Kenogram.Fillability — zweiwertige Besetzbarkeit und ihre Zählung

**Ertrag.** Günthers Satz aus `Definitionen.md` §16 — die klassische Logik mit ihren
sechzehn binären Wahrheitsfunktionen ruht auf nur acht der fünfzehn vierstelligen
Morphogramme, und sie ist darum morphogrammatisch unvollständig — wird hier zu Sätzen:
einer Charakterisierung, zwei Zählungen, einem Zeugen und einer strikten Ungleichung.

## Was bewiesen ist

* `marksLeOne_iff_fillable` — **die Brücke, der tragende Satz der Datei**: ein RGS hat
  höchste Marke `≤ 1` **genau dann**, wenn er die Normalform einer zweiwertigen
  Wertfolge `Fin n → Bool` ist. Erst dieser Satz macht `MarksLeOne` zum richtigen
  Prädikat statt zu einem Proxy: „höchste Marke ≤ 1" *ist* „von einer zweiwertigen
  Wertfolge erfüllt". Allgemeines `n`, kein `decide`-Weg (`canonicalize` ist
  `noncomputable`).
* `card_rgs_four` — fünfzehn vierstellige Morphogramme.
* `card_rgs_four_fillable` — acht davon sind zweiwertig besetzbar.
* `exists_nonfillable` — ein Zeuge, der es nicht ist: `[0,1,2,0]`, die Normalform der
  Wertfolge `(1,2,3,1)` aus §16, also das Muster `[a,b,c,a]`.
* `fillable_card_lt_card` — die strikte Ungleichung, die formale Lesung von
  „unvollständig".

## Warum die Zahlen hier Sätze sind und keine Außenzahlen

`CLAUDE.md` §6 hält außerhalb gerechnete Zahlen draußen und lässt sie nur in
Bijektions- oder Iff-Form herein. Die Regel trifft **importierte** Zahlen. Eine per
`decide` aus der Definition **bewiesene** `Fintype.card`-Gleichung ist keine
Außenzählung, sondern ein Satz: Lean rechnet Günthers Tafelzahl aus dem Generator
`rgsList` aus, dessen Korrektheit `mem_rgsList_iff` trägt. Das ist stehender Bestand —
`Basic.lean` Phase 4 führt die Marken 1, 2, 5, 15, 52 in genau dieser Form, und
`NonUniformCloneBound` führt die Zählung `2³ = 8` in der Bijektionsform. Beide Wege sind
zulässig; diese Datei nutzt für `n = 4` die `decide`-Form und für die Besetzbarkeit die
Iff-Form.

**Draußen bleiben** die allgemeine Bell-Folge, die allgemeine `2^(n−1)`-Formel,
`B(6) = 203` und alle Faserzahlen.

**Zur Doppelung mit Phase 4.** `card_rgs_four` sagt dasselbe wie das anonyme `example`
in `Basic.lean`. Das ist keine zweite Quelle im Drift-Sinn: beide sind entscheidbare,
maschinengeprüfte Aussagen über dieselbe Definition — jede Änderung an `RGS` bricht
beide zugleich, auseinanderlaufen können sie nicht. Was hinzukommt, ist der **benannte,
zitierbare Träger**: ein anonymes `example` ist Berechnungs-Reihe und kein
konsumierbarer Satz. `Basic.lean` bleibt unangetastet.

## Deutungs-Marken (verbindlich)

1. **„Vierstelliges Morphogramm = RGS der Länge 4"** konsumiert die stehende
   Operationalisierung (Ledger L16-1, `relabel`); `Definitionen.md` §16 definiert die
   Morphogramm-Bildung wörtlich als dieses relabel-Verfahren.
2. **Die Zeilenordnung ist gewählt, nicht gefunden.** Die Lesung von `Fin n → Bool` als
   Wertfolge und — für `n = 4` — als Wahrheitstafel einer binären Funktion setzt eine
   Ordnung der vier Belegungszeilen voraus; `Bool × Bool ≃ Fin 4` ist eine Wahl. Die
   Zählungen sind davon unberührt, denn `canonicalize` und `MarksLeOne` hängen nur am
   Gleichheitsmuster. Die Invarianz unter Umordnung wird **nicht** bewiesen und nicht
   behauptet. Rubrik „canonical is the procedure, chosen is the basis".
3. **Die Identifikation der acht mit den acht „klassisch" markierten Zeilen von Günthers
   Tafel VIII ist quellengestützte Deutung, kein Satz.** Bewiesen ist die Zählung der
   zweiwertig besetzbaren Klasse, nicht die zeilenweise Übereinstimmung mit einer
   historischen Tafel.
4. **„Morphogrammatische Unvollständigkeit"** ist die Lesung von `exists_nonfillable`
   und `fillable_card_lt_card`, nicht ihr Wortlaut. Kein Satz dieser Datei trägt den
   Namen — der Titel liefe dem Satz voraus.

## Was offen bleibt

Die Datei **schließt die Ledger-Zeile L16-6 nicht, sie verengt sie**. Getragen sind
danach die Zähl- und die Besetzbarkeitsseite. Offen bleiben die semantischen
Wertbesetzungs-Fälle 1–3 aus `Definitionen.md` §16, die zeilenweise Identifikation mit
Günthers Tafel und alles jenseits von `n = 4`.

**Die Robustheits-Pflicht `CLAUDE.md` §9 greift nicht:** sie gilt für
Nicht-Erzeugbarkeits-Schranken, deren Geltung an einer Invariante hängt. Hier stehen
Zählungen und eine positive Existenz; es ist keine Invariante zu prüfen.

## Zum Axiom-Profil

Der Kenogram-Zweig trägt `Classical.choice` über `instFintypeRGS` und dessen
Mathlib-Kette (B1-Choice-Analyse im Doc von `Basic.lean`). Die Sätze dieser Datei erben
ihn; das ist **kein** Fall von Fallstrick 10 (`CLAUDE.md` §8): der Anteil kommt nicht
aus einer bequemen `deriving`-Klausel, sondern aus der Generator-Korrektheit
(`mem_rgsList_iff`). Ein choice-freier Nachbau der `Fintype`-Instanz wäre Nachbau von
Bestandsbeweisen und ist Nicht-Ziel. Eine Wache ist Driftschutz, keine Ertragsmarke.

**Ablage:** setzungsfrei, sorry-frei, konsumiert nur Aggregat-Inhalt — Aggregat.
-/

namespace Reformulation.Kenogram.Fillability

open Reformulation.Kenogram

/-! ## Teil 1 — das Prädikat und die konsumierte Normalform-Gleichung -/

/-- **Zweiwertige Besetzbarkeit, syntaktisch:** kein Eintrag des RGS überschreitet die
Marke `1`. Für `n = 4` sind das genau die Morphogramme, die eine binäre Wahrheitstafel
tragen können — bewiesen in `marksLeOne_iff_fillable`. -/
def MarksLeOne {n : ℕ} (r : RGS n) : Prop := ∀ v ∈ r.1, v ≤ 1

/-- `MarksLeOne` ist entscheidbar; die `Prop`-Definition ist für die Instanzensuche
opak (Fallstrick 2), darum `inferInstanceAs`. Trägt jedes `decide` unten. -/
instance instDecidableMarksLeOne {n : ℕ} (r : RGS n) : Decidable (MarksLeOne r) :=
  inferInstanceAs (Decidable (∀ v ∈ r.1, v ≤ 1))

/-- **Ein RGS ist die Normalform seiner eigenen Wertfunktion.** Konsum, kein Nachbau:
die Rechnung steckt heute inline in `rgs_equiv_partition.left_inv` und ist hier
herausgezogen, weil `marksLeOne_iff_fillable` sie in beiden Richtungen braucht.
`Basic.lean` bleibt unangetastet. -/
theorem canonicalize_rgsFun {n : ℕ} (r : RGS n) : canonicalize (rgsFun r) = r := by
  apply Subtype.ext
  have hof : List.ofFn (rgsFun r) = r.1 := by
    apply List.ext_getElem?
    intro k
    by_cases hk : k < n
    · rw [List.getElem?_ofFn, dif_pos hk, List.getElem?_eq_getElem (by rw [r.2.1]; exact hk)]
      rfl
    · rw [List.getElem?_ofFn, dif_neg hk, List.getElem?_eq_none_iff.mpr (by rw [r.2.1]; omega)]
  show relabel (List.ofFn (rgsFun r)) = r.1
  rw [hof]; exact relabel_eq_self_of_isRGS r.2.2

/-- Auf Marken `≤ 1` unterscheidet der Test „ist die Marke `1`?" genau die Marken.
Das Arbeitsstück der Hinrichtung von `marksLeOne_iff_fillable`; die Fallunterscheidung
läuft über `dite` statt über eine `omega`-Disjunktion (Fallstrick 7). -/
lemma decide_eq_iff_of_le_one {a b : ℕ} (ha : a ≤ 1) (hb : b ≤ 1) :
    (decide (a = 1) = decide (b = 1)) ↔ a = b := by
  have ha' : a = 0 ∨ a = 1 := if hz : a = 0 then Or.inl hz else Or.inr (by omega)
  have hb' : b = 0 ∨ b = 1 := if hz : b = 0 then Or.inl hz else Or.inr (by omega)
  rcases ha' with rfl | rfl <;> rcases hb' with rfl | rfl <;> decide

/-! ## Teil 2 — die Brücke

Der tragende Satz: das syntaktische Kriterium `MarksLeOne` und die semantische
Besetzbarkeit durch eine zweiwertige Wertfolge fallen zusammen.

*Hinrichtung:* aus den Marken wird die Wertfolge gebaut — `f i := (Marke i = 1)`. Auf
Marken `≤ 1` ist das injektiv genug, um das Gleichheitsmuster zu erhalten, und
`canonicalize_eq_iff` überträgt es auf die Normalformen.

*Rückrichtung:* wäre eine Marke `≥ 2`, so lägen drei paarweise verschiedene Marken vor
— `0` am Kopf (`isRGS_head`), eine `1` im Präfix (Dichtheit, `rgs_take_mem`, aus der
RGS-Schranke `isRGS_getElem_le`) und die Marke selbst. Über das Muster wären dann drei
`Bool`-Werte paarweise verschieden, und davon gibt es nur zwei. -/

/-- **Z1 — die Brücke (der tragende Satz).** Ein RGS hat höchste Marke `≤ 1` genau
dann, wenn er die Normalform einer zweiwertigen Wertfolge ist. -/
theorem marksLeOne_iff_fillable {n : ℕ} (r : RGS n) :
    MarksLeOne r ↔ ∃ f : Fin n → Bool, canonicalize f = r := by
  constructor
  · intro h
    refine ⟨fun i => decide (rgsFun r i = 1), ?_⟩
    have hmem : ∀ i : Fin n, rgsFun r i ≤ 1 := by
      intro i
      exact h _ (List.getElem_mem _)
    have hpat : ∀ i j : Fin n,
        (decide (rgsFun r i = 1) = decide (rgsFun r j = 1)) ↔ rgsFun r i = rgsFun r j :=
      fun i j => decide_eq_iff_of_le_one (hmem i) (hmem j)
    calc canonicalize (fun i => decide (rgsFun r i = 1))
        = canonicalize (rgsFun r) := (canonicalize_eq_iff _ _).mpr hpat
      _ = r := canonicalize_rgsFun r
  · rintro ⟨f, hf⟩ v hv
    by_contra hgt
    have h2 : 2 ≤ v := by omega
    -- die Stelle der grossen Marke
    obtain ⟨p, hp, hpv⟩ := List.mem_iff_getElem.mp hv
    have hppos : 0 < p := by
      rcases Nat.eq_zero_or_pos p with hp0 | hpos
      · exfalso
        subst hp0
        rw [isRGS_head r.2.2 hp] at hpv
        omega
      · exact hpos
    -- eine `1` im Praefix: aus der RGS-Schranke und der Dichtheit
    have hle := isRGS_getElem_le r.2.2 hp hppos
    have hmax : 1 ≤ (r.1.take p).foldr max 0 := by omega
    have hone := rgs_take_mem r.2.2 p (le_of_lt hp) hppos 1 hmax
    obtain ⟨q, hq, hqv⟩ := List.mem_iff_getElem.mp hone
    rw [List.length_take] at hq
    have hqp : q < p := by omega
    rw [List.getElem_take] at hqv
    -- drei Stellen mit drei verschiedenen Marken
    have hlen : r.1.length = n := r.2.1
    have hpn : p < n := by omega
    have hqn : q < n := by omega
    have h0n : 0 < n := by omega
    set i0 : Fin n := ⟨0, h0n⟩ with hi0def
    set iq : Fin n := ⟨q, hqn⟩ with hiqdef
    set ip : Fin n := ⟨p, hpn⟩ with hipdef
    have v0 : rgsFun r i0 = 0 := isRGS_head r.2.2 (by omega)
    have vq : rgsFun r iq = 1 := hqv
    have vp : rgsFun r ip = v := hpv
    -- das Muster ueberträgt sich auf `f`
    have hcan : canonicalize f = canonicalize (rgsFun r) := by
      rw [hf, canonicalize_rgsFun]
    have hker := (canonicalize_eq_iff f (rgsFun r)).mp hcan
    have e01 : f i0 ≠ f iq := by
      intro hE
      have := (hker i0 iq).mp hE
      rw [v0, vq] at this
      exact absurd this (by decide)
    have e12 : f iq ≠ f ip := by
      intro hE
      have := (hker iq ip).mp hE
      rw [vq, vp] at this
      omega
    have e02 : f i0 ≠ f ip := by
      intro hE
      have := (hker i0 ip).mp hE
      rw [v0, vp] at this
      omega
    revert e01 e12 e02
    generalize f i0 = b0
    generalize f iq = b1
    generalize f ip = b2
    revert b0 b1 b2
    decide

/-! ## Teil 3 — die Zählungen, der Zeuge und die Ungleichung

`decide` über den bewiesenen Generator, nach dem Muster der Phase-4-Reihe in
`Basic.lean`. Die `maxRecDepth`-Setzungen sind gemessen, nicht geschätzt. -/

set_option maxRecDepth 4000 in
/-- **Z2 — die Fünfzehn, benannt.** `B(4) = 15`: es gibt fünfzehn vierstellige
Morphogramme (Günther, Tafel VIII). Dieselbe Aussage wie das anonyme `example` der
Phase 4 in `Basic.lean`, hier als zitierbarer Träger. -/
theorem card_rgs_four : Fintype.card (RGS 4) = 15 := by decide

set_option maxRecDepth 4000 in
/-- **Z3 — die Acht.** Genau acht der fünfzehn vierstelligen Morphogramme sind
zweiwertig besetzbar. Mit `marksLeOne_iff_fillable` ist das die Zählung der
Morphogramme, die eine binäre Wahrheitstafel tragen. -/
theorem card_rgs_four_fillable :
    Fintype.card {r : RGS 4 // MarksLeOne r} = 8 := by decide

/-- **Z4 — der Zeuge, der nicht besetzbar ist.** `[0,1,2,0]` ist ein vierstelliges
Morphogramm mit Marke `2` — die Normalform der Wertfolge `(1,2,3,1)` aus
`Definitionen.md` §16, also das Muster `[a,b,c,a]`. Mit `marksLeOne_iff_fillable`:
keine zweiwertige Wertfolge erzeugt es. Der Zeuge steht im Beweis, nicht nur die
Existenz. -/
theorem exists_nonfillable : ∃ r : RGS 4, ¬ MarksLeOne r :=
  ⟨⟨[0, 1, 2, 0], by decide⟩, by decide⟩

set_option maxRecDepth 4000 in
/-- **Z5 — die strikte Ungleichung.** Echt weniger vierstellige Morphogramme sind
zweiwertig besetzbar als es überhaupt gibt. Das ist die formale Lesung von
„morphogrammatisch unvollständig" — die Lesung, nicht der Wortlaut. -/
theorem fillable_card_lt_card :
    Fintype.card {r : RGS 4 // MarksLeOne r} < Fintype.card (RGS 4) := by decide

/-! **Statement-Pins.** Voller Wortlaut links, Satz rechts — jede Drift des *Statements*
bricht den Build. Namenlose `example`s, keine Axiom-Wache. -/

-- STATEMENT-PIN
example {n : ℕ} (r : RGS n) : MarksLeOne r ↔ ∃ f : Fin n → Bool, canonicalize f = r :=
  marksLeOne_iff_fillable r
-- STATEMENT-PIN
example : Fintype.card {r : RGS 4 // MarksLeOne r} = 8 := card_rgs_four_fillable
-- STATEMENT-PIN
example : Fintype.card {r : RGS 4 // MarksLeOne r} < Fintype.card (RGS 4) :=
  fillable_card_lt_card

/-! ## Teil 4 — die Axiom-Wachen (Ist-gebunden)

Ist-Ausgabe des grünen Builds (v4.30.0-rc2), pro Satz eingefroren
(Datei-Vollständigkeits-Regel, hier einschließlich des Hilfslemmas). Der
`Classical.choice`-Anteil ist der geerbte des Kenogram-Zweigs (Dateikopf, Abschnitt
„Zum Axiom-Profil"), kein neuer. `exists_nonfillable` unterbietet ihn: der Zeuge ist
konkret und braucht die `Fintype`-Instanz nicht. -/

/-- info: 'Reformulation.Kenogram.Fillability.decide_eq_iff_of_le_one' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms decide_eq_iff_of_le_one

/-- info: 'Reformulation.Kenogram.Fillability.canonicalize_rgsFun' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms canonicalize_rgsFun

/-- info: 'Reformulation.Kenogram.Fillability.marksLeOne_iff_fillable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms marksLeOne_iff_fillable

/-- info: 'Reformulation.Kenogram.Fillability.card_rgs_four' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms card_rgs_four

/-- info: 'Reformulation.Kenogram.Fillability.card_rgs_four_fillable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms card_rgs_four_fillable

/-- info: 'Reformulation.Kenogram.Fillability.exists_nonfillable' does not depend on any axioms -/
#guard_msgs in #print axioms exists_nonfillable

/-- info: 'Reformulation.Kenogram.Fillability.fillable_card_lt_card' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms fillable_card_lt_card

end Reformulation.Kenogram.Fillability
