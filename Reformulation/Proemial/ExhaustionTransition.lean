import Reformulation.Proemial.IrreversibleAscent
import Reformulation.Proemial.IntervalBackbone

/-!
# Reformulation.Proemial.ExhaustionTransition — der Erschöpfungs-Übergang (neunzehnte Schicht)

Die achte Stelle der achtfachen Form in Zeugen-Fassung: der Erschöpfungs-Übergang
(die „Erschöpfung der nicht-designativen Reflexion", Lille S. 19; der Tod
als Rückgabe der Reflexivität, 1957) — die Erschöpfung als
vierteiliges Merkmal, ihre Unmöglichkeit im Maßstab-Grenzfall (derselbe wie bei
der sechzehnten Schicht, per Import term-identisch), der Phasenwechsel als
Wohlfundiertheits-Theorem, das Spiegel-Stück zum Rang-Lemma.

Erste Schicht-zu-Schicht-Abhängigkeit unter den Niederlegungs-Schichten: die arme
Klasse `PointwisePeriodic` wird per Import **term-identisch** wiederverwendet, nicht
dupliziert — der Import ist die Architektur-Aussage, dass Aufstieg (16.) und
Erschöpfung (19.) am *selben* Maßstab-Grenzfall gemessen werden.

## (1) Quellen

Günther, Lille (Strukturelle Minimalbedingungen…), S. 19 („die achte Thematik, die aus
der Erschöpfung der nicht-designativen Reflexion … hervorgeht"; Ankerform Seite und
Wortlaut seit Sammel-Vollzug 6); Beiträge III —
S. 160 (druck-verifiziert; Doppel-Abgleich 13. Juli: Vorprüfung + volles Hermeneutes-Siegel) — der Wiedereintritt des
Designativen; kategoriale Inhomogenität 7→8 (Phasenwechsel statt Stufung).
**Aufstufung (Autopsie 13. Juli):** Die *achtfache Thematik* samt
1+3+3+1-Gliederung, die gnostische Thanatos-Idee, die *Erschöpfung der
nicht-designativen Reflexion* und die *hinzugefügte Ur-Designation (Einwertigkeit)*
sind **Günther-wörtlich** — die Ableitung ist keine Projekt-Rekonstruktion, ihr Kern
ist die Stelle. **Etiketten-Marken:** Die Etiketten *Wiedereintritt des Designativen*
(Günthers Verb: „hinzugefügt"), *der Grund ist nicht das erste Sein* (Wortlaut: „in
ihren Grund, d.h. in das Sein zurück" — die Nicht-Identitäts-Lesart ist Projekt-Deutung
der Quell-Spannung) und *Phasenwechsel statt Stufung* (Günther: „mit dem nächsten
Intervall") sind **Projekt-Formulierungen**, keine Zitate. *Ideen zu einer Metaphysik
des Todes* (1957, Autopsie): „gibt das, was seine Reflexivität zur Seele machte, an das
impersonale Sein zurück"; „Folglich ist auf dem Boden der klassischen Logik keine
Metaphysik des Todes möglich" — **behauptete negative Richtung, behauptet ≠ bewiesen**:
der Satz dieser Schicht ist die bewiesene Iterations-Fassung, nicht die Einlösung jener
Stelle. Werkmeister-Lesart Position/Designation ↔ Funktion/Totalität: Deutung.

## (2) Stellen-Marke

Die 1+3+3+1-Gliederung selbst ist Günther-wörtlich (Autopsie 13. Juli, Rubrik (1));
strukturanalytisch bleibt allein die Zuordnung „diese Formalisierung ist Stelle 8".
„Erschöpfung/Bestand/Grund" sind Namen — term-fest sind Fixpunkt-Erreichung,
Nicht-Wiederkehr, Absorption (Benennung ist kein Satz).

## (3) Term-fest werden hiermit

`exhausts_ne`, `no_exhaustion_in_periodic`, `collapse_exhausts`,
`fixpoint_reached_of_strict_descent`, Kür `exhausted_stays`. Seit dem 23. September dazu
`dstep`, `dstep_decomp`, `dstep_no_fixpoint` und `decomp_never_exhausts` (Teil 5b).

## (3a) Die zweite Gestalt — und dass sie diese nicht ist

Der Bestand trägt Günthers „Erschöpfung" seit dem 23. September zweimal: hier als
`Exhausts` — eine Iteration erreicht einen **absorbierenden** Bestand und kehrt nicht
wieder — und in `IntervalBackbone` als `Exhausted` — der Überschuss einer Wertzahl hat ihre
Themenzahl erreicht, und danach **beginnt** ein neues Intervall (`exhausted_seam`).

**Das Verhältnis ist ein Satz:** `decomp_never_exhausts` — der Gang von `decomp`, als
Selbstabbildung `dstep` auf `ℕ × ℕ` gelesen (`dstep_decomp`), fällt **nie** unter
`Exhausts`, weil sein Schritt keinen Fixpunkt hat (`dstep_no_fixpoint`) und `Exhausts`
einen verlangt. **Die zwei Gestalten schliessen einander aus:** wo `Exhausted` greift, geht
es weiter; wo `Exhausts` greift, geht es nicht weiter. Keine Dublette.
*Marke:* **UMBENENNUNG** (über die Definition) — der Beweisterm ist `dstep_no_fixpoint`,
angewandt auf `.1` von `Exhausts`; die Folgerung sitzt in `dstep_no_fixpoint`. Der
Ausschluss ist damit, wie die Klammer `RecurringGround.exhausts_ground`, **definitorisch**:
beide lesen `.1` derselben Definition.

*Lesart, nicht Satz* (Mathematiker, 23.9.): die zwei Gestalten sind die zwei Seiten der
Quell-Spannung, die `exhausts_ne` zitiert — die Subjektivität geht „in ihren Grund, d.h. in
das Sein zurück" (ein Ende: `Exhausts`), und das Erreichte beginnt als erste Ontologie des
Nächsten (ein Anfang: `Exhausted`). Formal gemessen ist nur der Ausschluss; die Zuordnung
zu Günthers zwei Seiten stützt sich auf die schon zitierten Zeilen, nicht auf eine neue
Quellenlektüre.

**Ort, gemessen:** keiner der zwei Moduln importierte den anderen. Der Satz steht hier, weil
hier die Prosa steht, die er ablöst, und `IntervalBackbone` projekt-import-frei bleiben soll
(sein Kopf sagt es); die neue Importzeile zieht ein Modul und einen Mathlib-Baustein nach.

## (4) Bauform und Stufen-Disziplin

Die arme Klasse ist per Import **term-identisch** die der sechzehnten Schicht —
Aufstieg und Erschöpfung messen am selben Maßstab-Grenzfall; im symmetrischen Fall
wird nichts geboren und stirbt nichts (aion-Lesart, Deutung); der negative Satz
`no_exhaustion_in_periodic` ist der dünnste des Pakets — strengste Wort-Kontrolle;
das Erschöpfungs-Lemma `fixpoint_reached_of_strict_descent` ist das Spiegel-Stück zum
Rang-Lemma `no_return_of_strict_rank` (16.): steigender Rang → nie Bestand;
fallender Rang → Bestand erreicht (die zwei Zeit-Richtungen der Achse in einer
Sprache). Der Zeuge `collapse` ist die Instanz `rank := fun y => if y = 1 then 0
else 1`.

## (5) Abgrenzung und Wache

**Designation ≠ Denotation** — Günthers Designation (Einwertigkeit, Seins-These) ist
nicht die Denotation der achtzehnten Schicht (`realize`-Semantik); kein gemeinsamer
Gehalt, Verwechslungs-Wache. Stelle 1 und Mittelstellen: eigene Pakete (V1-Gate);
SO2-Wiedervorlage nach diesem Paket.

## (6) Sorry-Bilanz und Axiom-Ist

0 Sorries. Axiom-Ist (je Kern-Satz `#guard_msgs`-verwacht, Datei-Ende):
`exhausts_ne` `[Quot.sound]`; `no_exhaustion_in_periodic` axiom-frei (hängt an
keinem Axiom); `collapse_exhausts` `[propext, Quot.sound]`; `exhausted_stays`
`[propext, Quot.sound]`. **Abweichung (gewöhnliche Notiz, kein Blocker):**
`fixpoint_reached_of_strict_descent` zieht zusätzlich `Classical.choice` — der
Fallunterscheidung `by_cases f x = x` über einem beliebigen Träger `α` ohne
`DecidableEq` inhärent (die Fixpunkt-Alternative ist klassisch). Der erwartete
Spec-Bereich `propext`/`Quot.sound` ist damit für die drei anderen Kern-Sätze
erreicht bzw. unterschritten (`no_exhaustion_in_periodic` axiom-frei — eine
Verschärfung), nur beim Descent-Lemma überschritten. Teil 5b: `dstep_decomp` axiom-frei,
`dstep_no_fixpoint` und `decomp_never_exhausts` `[propext, Quot.sound]` — der Fixpunkt-Beweis
schliesst mit `dsimp only; omega`, weil ein offenes `simp at this` an derselben Stelle
`Classical.choice` zieht (Fallstrick 21, gemessen vom Mathematiker am 23.9.).
-/

namespace Reformulation.Proemial.ExhaustionTransition

open Reformulation.Proemial.IrreversibleAscent

-- ============================================================
-- Teil 1 — Merkmal und Grund-Lemma (M1/M2)
-- ============================================================

/-- Die Erschöpfung: f verlässt x irreversibel (nie Wiederkehr) und erreicht
    den Bestand b (absorbierend). Dass der Grund nicht der Anfang ist (x ≠ b),
    ist FOLGE (`exhausts_ne`), keine Zutat der Definition. -/
def Exhausts {α : Type*} (f : α → α) (x b : α) : Prop :=
  f b = b ∧ (∃ n, f^[n] x = b) ∧ (∀ k > 0, f^[k] x ≠ x)

/-- Die strukturelle Nicht-Identität: der erreichte Bestand ist nie der verlassene
    Anfang (x ≠ b folgt aus der Erschöpfung). Projekt-Deutung der achten Stelle —
    KEIN Günther-Zitat: der Lille-Wortlaut sagt „Die Subjektivität geht, wie Hegel
    sagen würde, in ihren Grund, d.h. in das Sein zurück" (S. 19) und
    zugleich, dass das Erreichte „die erste Ontologie des objektiven Geistes" ist —
    das Lemma formalisiert die zweite Seite dieser Quell-Spannung (das Erreichte
    ist Neues, nicht das erste Intervall), nicht einen Satz Günthers. -/
theorem exhausts_ne {α : Type*} {f : α → α} {x b : α}
    (h : Exhausts f x b) : x ≠ b := by
  rintro rfl
  exact h.2.2 1 Nat.one_pos (by simpa using h.1)

-- ============================================================
-- Teil 2 — Negative Hälfte (M3)
-- ============================================================

/-- NEGATIVE HÄLFTE: im Maßstab-Grenzfall (punktweise Periodik — dieselbe arme
    Klasse wie die der sechzehnten Schicht, per Import term-identisch) gibt es
    keine Erschöpfung: jeder Punkt kehrt wieder, nichts wird endgültig
    verlassen. Der dünnste negative Satz des Pakets — die Doc-Rubrik (4) trägt
    die Stufen-Disziplin ausdrücklich. -/
theorem no_exhaustion_in_periodic {α : Type*} {f : α → α}
    (hf : PointwisePeriodic f) : ∀ x b, ¬ Exhausts f x b := by
  intro x b h
  obtain ⟨n, hn, hx⟩ := hf x
  exact h.2.2 n hn hx

-- ============================================================
-- Teil 3 — Positive Hälfte: der Zeuge (M4)
-- ============================================================

/-- Der minimale Erschöpfungs-Fall: alles kollabiert auf 1. -/
def collapse : Fin 2 → Fin 2 := fun _ => 1

theorem collapse_iterate_pos (k : ℕ) (hk : 0 < k) (y : Fin 2) :
    collapse^[k] y = 1 := by
  cases k with
  | zero => omega
  | succ k => rw [Function.iterate_succ_apply']; rfl

/-- POSITIVE HÄLFTE: der Zeuge — 0 wird verlassen und nie wieder erreicht,
    1 ist absorbierender Bestand. -/
theorem collapse_exhausts : Exhausts collapse 0 1 := by
  refine ⟨rfl, ⟨1, ?_⟩, ?_⟩
  · simp [collapse]
  · intro k hk h
    rw [collapse_iterate_pos k hk] at h
    exact absurd h (by decide)

-- ============================================================
-- Teil 4 — Das Erschöpfungs-Lemma (M5)
-- ============================================================

/-- ERSCHÖPFUNGS-LEMMA (der Phasenwechsel als Theorem): trägt eine Iteration
    einen strikt fallenden ℕ-Rang außerhalb der Fixpunkte, erreicht jede
    Trajektorie in endlich vielen Schritten einen Fixpunkt. Spiegel-Stück zu
    `no_return_of_strict_rank` (16. Schicht): steigender Rang → nie Bestand;
    fallender Rang → Bestand erreicht. Der Zeuge oben ist die Instanz
    `rank := fun y => if y = 1 then 0 else 1`. -/
theorem fixpoint_reached_of_strict_descent {α : Type*} (f : α → α) (rank : α → ℕ)
    (hr : ∀ x, f x ≠ x → rank (f x) < rank x) :
    ∀ x, ∃ n, f (f^[n] x) = f^[n] x := by
  have H : ∀ r : ℕ, ∀ x, rank x = r → ∃ n, f (f^[n] x) = f^[n] x := by
    intro r
    induction r using Nat.strong_induction_on with
    | _ r ih =>
      intro x hx
      by_cases hfx : f x = x
      · exact ⟨0, hfx⟩
      · obtain ⟨n, hn⟩ := ih (rank (f x)) (hx ▸ hr x hfx) (f x) rfl
        exact ⟨n + 1, by rwa [Function.iterate_succ_apply]⟩
  intro x
  exact H (rank x) x rfl

-- ============================================================
-- Teil 5 — Kür: die Permanenz des Bestands (K1)
-- ============================================================

/-- KÜR — der Bestand bleibt: ab dem Erreichen ist jeder spätere Stand b. -/
theorem exhausted_stays {α : Type*} {f : α → α} {x b : α} {n : ℕ}
    (hfix : f b = b) (hreach : f^[n] x = b) : ∀ m, n ≤ m → f^[m] x = b := by
  intro m hm
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
  clear hm
  rw [Nat.add_comm, Function.iterate_add_apply, hreach]
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', ih, hfix]

-- ============================================================
-- Teil 5b — Die zweite Gestalt: der Gang von `decomp` erschöpft sich nie
-- ============================================================

/-- Der Schritt von `IntervalBackbone.decomp`, als Selbstabbildung auf `ℕ × ℕ`: der
Überschuss wächst, bis er die Themenzahl erreicht; dann beginnt das nächste Intervall. -/
def dstep (p : ℕ × ℕ) : ℕ × ℕ := if p.2 < p.1 then (p.1, p.2 + 1) else (p.1 + 1, 0)

/-- `dstep` ist genau der Schritt von `decomp`. -/
theorem dstep_decomp (m : ℕ) :
    dstep (IntervalBackbone.decomp m) = IntervalBackbone.decomp (m + 1) := by
  rw [IntervalBackbone.decomp_succ]; rfl

/-- `dstep` hat keinen Fixpunkt: an jeder Stelle geht es weiter. -/
theorem dstep_no_fixpoint (p : ℕ × ℕ) : dstep p ≠ p := by
  unfold dstep; split
  · intro h; have := congrArg Prod.snd h; exact absurd this (by dsimp only; omega)
  · intro h; have := congrArg Prod.fst h; exact absurd this (by dsimp only; omega)

/-- **Der Gang von `decomp` fällt nie unter `Exhausts`.** Die zwei Gestalten von Günthers
„Erschöpfung" im Bestand schliessen einander aus. -/
theorem decomp_never_exhausts (x b : ℕ × ℕ) : ¬ Exhausts dstep x b :=
  fun h => dstep_no_fixpoint b h.1

end Reformulation.Proemial.ExhaustionTransition

-- ============================================================
-- Teil 6 — Die `#guard_msgs`-Wachen (M7; Ist-gebunden)
-- ============================================================

-- Ist-Ausgabe des ersten grünen Builds (v4.30.0-rc2), pro Kern-Satz als Wache.
open Reformulation.Proemial.ExhaustionTransition in
section

/-- info: 'Reformulation.Proemial.ExhaustionTransition.exhausts_ne' depends on axioms: [Quot.sound] -/
#guard_msgs in #print axioms exhausts_ne

/-- info: 'Reformulation.Proemial.ExhaustionTransition.no_exhaustion_in_periodic' does not depend on any axioms -/
#guard_msgs in #print axioms no_exhaustion_in_periodic

/-- info: 'Reformulation.Proemial.ExhaustionTransition.collapse_exhausts' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms collapse_exhausts

/-- info: 'Reformulation.Proemial.ExhaustionTransition.fixpoint_reached_of_strict_descent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms fixpoint_reached_of_strict_descent

/-- info: 'Reformulation.Proemial.ExhaustionTransition.exhausted_stays' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms exhausted_stays

/-- info: 'Reformulation.Proemial.ExhaustionTransition.dstep_decomp' does not depend on any axioms -/
#guard_msgs in #print axioms dstep_decomp

/-- info: 'Reformulation.Proemial.ExhaustionTransition.dstep_no_fixpoint' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms dstep_no_fixpoint

/-- info: 'Reformulation.Proemial.ExhaustionTransition.decomp_never_exhausts' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms decomp_never_exhausts

end
