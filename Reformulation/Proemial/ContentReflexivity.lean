import Reformulation.Proemial.ComplementaryMediation

/-!
# Reformulation.Proemial.ContentReflexivity — die Reflexivität der Inhalte (fünfundzwanzigste Schicht)

Die **erste Geist-Stelle**: das fünfte Intervall, die „Reflexivität der
Bewusstseinsinhalte", bekommt ihre Fassung als **Hebung** — `reflect f :=
Set.image f` lässt denselben Prozess auf seinen Inhalten laufen; Mengen von
Zuständen werden selbst Zustände. Die Hebung **erbt** den Umtausch (reversible
Inhalte reversibler Prozesse) und **bricht** die Irreversibilität: der leere
Inhalt ist Fixpunkt jeder Reflexion, also ist keine reflektierte Welt
rückkehrfrei — die Stufung selbst, unten rückkehrfrei,
wird an ihren Inhalten rückkehr-fähig.

**Ein Import** (`ComplementaryMediation`, transitiv die gesamte Kette und das
Substrat); die Kette wird 16→19→20→22→23→24→25. Term-identisch konsumiert
werden `Reversible` (22.), `NoReturn` und `noreturn_no_ground` (23.), `Ground`
(20.), `intervalStart`/`intervalEnd` (21.). Nichts wird dupliziert; **kein
Mathlib-Import über die transitive Hülle hinaus** (die Mengen-Lemmata
`Set.image_image`, `Set.image_comp`, `Set.image_id`, `Set.eq_empty_iff_forall_notMem`
liegen sämtlich in der Hülle — Teil-0-Befund).

## (1) Quellen

Der Anker: Intervall V ist „der **Reflexivität der Bewusstseinsinhalte**"
gewidmet (Lille Z. 605–607, bestätigt Z. 804; **Volltext-verifiziert**; die
Zeilen-Marken stehen unter der A2-Lokator-Klausel). Härte-Ökonomie: einmal
geeicht (Beiträge III, S. 160), verlängerbar.

## (2) MARKEN-TRIAS (Pflicht, W1-F3 — erstmals im Vollzug)

**Lokale Hegel-Relativitäts-Fassung:** die Intervall-Zuordnung der Stufen ist
„eine vorläufige" (Lille Z. 811–816, direkt neben den Stufen-Bestimmungen) —
Lesart der Hegel-Stufe, nicht Satz dieser Schicht.
**Substrat-Erbe:** der Ort (`interval_V_start`, `interval_V_end`) kommt aus dem
Rückgrat (21.) — das Rückgrat zählt die Orte, diese Schicht deutet; die
Orts-Sätze sind Substrat-Abruf.
**Monas-Struktur-Marke:** die Ein-Positiv-Struktur (ein positiver Wert, alle
anderen seine Reflexionen, Lille Z. 1015–1017) ist Günthers Wort; jede
Werte-Formalisierung bleibt außerhalb dieses Baus.

## (3) VERZICHTS-MARKE (W1-F1)

Der Hegel-Hintergrund (Enzyklopädie, Paragraph 387 folgend) ist **benannt, nicht
beigezogen** — Lesart, kein Günther-Beleg; die Beiziehung bliebe siegel-pflichtig
am Druck.

## (4) GRENZE

**Bewusstsein wird nicht formalisiert** — keine Bewusstseins-Semantik; term-fest
wird eine Struktur-Hebung. Reflexivität als Hebung ist **Deutung**; „der leere
Inhalt steht still" ist **markierte Struktur-Aussage** (Projekt-Rede, kein
Zitat).

## (5) Term-fest werden hiermit

`reflect_iterate`, `reflect_reversible`, `reflect_ground_empty`,
`reflect_not_noreturn`, `reflect_succ_not_noreturn`, `interval_V_start`,
`interval_V_end`, Kür `reflect_monotone`.

**KONSUM-EHRLICHKEIT (Bauform-These):** eigener Beweis-Gehalt liegt im
Iterations-Gesetz, im Erbe-Satz und im Grund-Satz; der Bruch-Satz ist Konsum der
23. (über `noreturn_no_ground`), der Zeugen-Satz reine Delegation an den
Bruch-Satz (Profil = Vorgänger). **KONSTRUKTIONS-MERKMAL (R1-Ist-geprüft):** das
Merkmal `reflect : Set α → Set α` ist eine **Konstruktion**, keine Eigenschaft —
und **die erste unter den fünf gebauten Stellen-Schichten** [19./20./22./23./24.]
mit einem Konstruktions- statt Eigenschafts-Merkmal (`Exhausts`, `Ground`,
`Reversible`, `NoReturn`, `Mediates` sind sämtlich `: Prop`; nachgezählt am
Bestand, die Bereichs-Qualifikation ist unverlierbar). Weitere Rang-Ansprüche
werden nicht erhoben.

## (6) Deutungs-Marken

Der Set-Träger ist **Modellwahl** (die Hebung ist an ihm gezeigt, nicht auf ihn
festgelegt); **Designation ist nicht Denotation** gilt fort.

## (7) Abgrenzung

Kein Vorgriff auf St.6 oder St.7 — eigene Pakete. Keine Werte- und keine
Bewusstseins-Semantik; die benannten Posten der Vorschichten (U5-Figuren,
Monas-Werte-Struktur) bleiben unberührt. Die Lage-Sätze der Stufe sind
Hebungs-Sätze, kein neues Differential (Verortungs-Reihe).

## (8) Sorry-Bilanz und Axiom-Ist — mit Rechnungs-Abgleich

**0 Sorries.** Axiom-Ist (erster grüner Build, v4.30.0-rc2), je Satz
`#guard_msgs`-verwacht am Datei-Ende (acht Wachen):

* **`[propext, Quot.sound]`:** `reflect_iterate`, `reflect_reversible`,
  `reflect_ground_empty`, `reflect_not_noreturn`, `reflect_succ_not_noreturn`
  (Mengen-Extensionalität; die `Set`-Hüllen reisen mit).
* **axiom-frei:** `interval_V_start`, `interval_V_end` (Substrat-`decide`),
  `reflect_monotone` (Eigenbeweis, siehe unten).

**Abgleich gegen die Profil-Rechnung (M6(8), R2 = Erwartung):**

* **Getroffen:** M5 frei (wie gerechnet); M2/M3/M4a/M4b/M4c im propext-Bereich —
  die Rechnung hatte `[propext]` veranschlagt, das Ist ist `[propext, Quot.sound]`
  (die `Quot.sound`-Zugabe derselben Mengen-Hülle, dasselbe Muster wie im
  Rückgrat 21.); M4c = Profil von M4b (Delegation), getroffen.
* **ROUTEN-BEFUND (Teil 0, kein Hüllen-Schicksal), zweifach aufgelöst:** die
  **naiven** Routen zögen `Classical.choice` herein — `Set.image_empty` **und**
  `Set.image_mono` tragen in diesem Mathlib `[propext, Classical.choice,
  Quot.sound]` (gemessen). Die Spec verlangt **kein `Classical`**. Beide Stellen
  sind classical-frei umgangen: `reflect_ground_empty` geht über
  `Set.eq_empty_iff_forall_notMem` (statt `simp`/`Set.image_empty`) und liegt bei
  `[propext, Quot.sound]`; die Kür `reflect_monotone` geht den **Eigenbeweis**
  (`rintro ⟨x, hx, rfl⟩`) statt `Set.image_mono` und ist damit **axiom-frei**.
* **Kür-Messung (Routen-Bau-Regel):** Kandidat A (`Set.image_mono`) trägt
  `Classical.choice`, Kandidat B (Eigenbeweis) ist axiom-frei — **kein
  Gleichstand**, die ärmere Route B gewinnt und wird geliefert (die Spec-Vorgabe
  „bei Gleichstand A" greift nicht, weil A strikt reicher ist).

**Kein `Classical`** — an keiner der acht Stellen.
-/

namespace Reformulation.Proemial.ContentReflexivity

open Reformulation.Proemial.ComplementaryMediation
open Reformulation.Proemial.IrreversibleAdvance
open Reformulation.Proemial.ReversibleExchange
open Reformulation.Proemial.IntervalBackbone
open Reformulation.Proemial.RecurringGround

-- ============================================================
-- Teil 1 — Das Merkmal (M1): eine Konstruktion, keine Eigenschaft
-- ============================================================

/-- Die Reflexion: derselbe Prozess, auf seine Inhalte gewendet — Mengen von
    Zuständen werden selbst Zustände. Die Zuordnung zur „Reflexivität der
    Bewusstseinsinhalte" des fünften Intervalls (Stelle 5) ist
    strukturanalytisch; Hebung als Lesart von „Reflexivität" ist Deutung;
    Bewusstsein wird nicht formalisiert. -/
def reflect {α : Type*} (f : α → α) : Set α → Set α := Set.image f

-- ============================================================
-- Teil 2 — Iterations-Gesetz und Erbe (M2/M3)
-- ============================================================

/-- Die gehobene Iteration ist die Iteration der Bilder (öffentlicher Satz —
    das Gesetz ist selbst Posten). -/
theorem reflect_iterate {α : Type*} (f : α → α) (n : ℕ) (S : Set α) :
    (reflect f)^[n] S = f^[n] '' S := by
  induction n with
  | zero => simp [reflect]
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih]
      show f '' (f^[n] '' S) = f^[n + 1] '' S
      rw [← Set.image_comp, ← Function.iterate_succ']

/-- Die Inhalte eines reversiblen Prozesses sind reversibel — der Umtausch hebt
    sich mit. Route (Teil 0 (4)): `Set.image_image`, punktweise `h`, dann
    `Set.image_id`. -/
theorem reflect_reversible {α : Type*} {f : α → α}
    (h : Reversible f) : Reversible (reflect f) := by
  intro S
  show f '' (f '' S) = S
  rw [Set.image_image, show (fun x => f (f x)) = id from funext h, Set.image_id]

-- ============================================================
-- Teil 3 — Der Kern-Satz (M4): der leere Inhalt steht still
-- ============================================================

/-- „DER LEERE INHALT STEHT STILL": ∅ ist Fixpunkt jeder Reflexion (markierte
    Struktur-Aussage, Projekt-Rede — kein Zitat). Classical-frei über
    `Set.eq_empty_iff_forall_notMem` — nicht über `Set.image_empty`, das in
    diesem Mathlib `Classical.choice` trägt (Routen-Befund, Modul-Doc (8)). -/
theorem reflect_ground_empty {α : Type*} (f : α → α) :
    Ground (reflect f) (∅ : Set α) := by
  show reflect f ∅ = ∅
  rw [Set.eq_empty_iff_forall_notMem]
  rintro y ⟨x, hx, -⟩
  exact hx

/-- BRUCH DER IRREVERSIBILITÄT AN DEN INHALTEN: die reflektierte Welt ist
    niemals rückkehrfrei — was als Prozess nirgends ankommt, hat als
    Inhalts-Prozess stets einen Grund (Konsum von `noreturn_no_ground`, 23.). -/
theorem reflect_not_noreturn {α : Type*} (f : α → α) :
    ¬ NoReturn (reflect f) :=
  fun h => noreturn_no_ground h ∅ (reflect_ground_empty f)

/-- Der Zeugen-Satz: die Stufung selbst wird an ihren Inhalten rückkehr-fähig
    (reine Delegation — Profil = Vorgänger). -/
theorem reflect_succ_not_noreturn : ¬ NoReturn (reflect Nat.succ) :=
  reflect_not_noreturn Nat.succ

-- ============================================================
-- Teil 4 — Orts-Sätze (M5): Substrat-Abruf
-- ============================================================

/-- Der Ort aus dem Rückgrat (21.): Intervall V beginnt bei 15 … -/
theorem interval_V_start : intervalStart 5 = 15 := by decide

/-- … und endet bei 20 — Substrat-Abruf. -/
theorem interval_V_end : intervalEnd 5 = 20 := by decide

-- ============================================================
-- Teil 5 — Kür (K1): die Ordnung der gehobenen Welt
-- ============================================================

/-- KÜR: die Reflexion achtet die Inhalts-Ordnung — die gehobene Welt ist
    geordnet, wo die untere nur läuft. Route nach Profil-Messung (Modul-Doc (8)):
    Kandidat A (`Set.image_mono`) trägt `Classical.choice`, Kandidat B
    (Eigenbeweis via `rintro ⟨x, hx, rfl⟩`) ist axiom-frei — kein Gleichstand,
    die ärmere Route B wird geliefert. -/
theorem reflect_monotone {α : Type*} (f : α → α) {S T : Set α}
    (h : S ⊆ T) : reflect f S ⊆ reflect f T := by
  rintro y ⟨x, hx, rfl⟩
  exact ⟨x, h hx, rfl⟩

end Reformulation.Proemial.ContentReflexivity

-- ============================================================
-- Teil 6 — Die `#guard_msgs`-Wachen (M7; Ist-gebunden)
-- ============================================================

-- Ist-Ausgabe des ersten grünen Builds (v4.30.0-rc2), pro Satz als Wache.
open Reformulation.Proemial.ContentReflexivity in
section

/-- info: 'Reformulation.Proemial.ContentReflexivity.reflect_iterate' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms reflect_iterate

/-- info: 'Reformulation.Proemial.ContentReflexivity.reflect_reversible' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms reflect_reversible

/-- info: 'Reformulation.Proemial.ContentReflexivity.reflect_ground_empty' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms reflect_ground_empty

/-- info: 'Reformulation.Proemial.ContentReflexivity.reflect_not_noreturn' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms reflect_not_noreturn

/-- info: 'Reformulation.Proemial.ContentReflexivity.reflect_succ_not_noreturn' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms reflect_succ_not_noreturn

/-- info: 'Reformulation.Proemial.ContentReflexivity.interval_V_start' does not depend on any axioms -/
#guard_msgs in #print axioms interval_V_start

/-- info: 'Reformulation.Proemial.ContentReflexivity.interval_V_end' does not depend on any axioms -/
#guard_msgs in #print axioms interval_V_end

/-- info: 'Reformulation.Proemial.ContentReflexivity.reflect_monotone' does not depend on any axioms -/
#guard_msgs in #print axioms reflect_monotone

end
