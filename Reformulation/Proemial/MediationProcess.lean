import Reformulation.Proemial.ContentReflexivity

/-!
# Reformulation.Proemial.MediationProcess — der Vermittlungsprozess (sechsundzwanzigste Schicht)

Die **zweite Geist-Stelle**: das sechste Intervall, „der Subjektivität als
Vermittlungsprozess gewidmet", hat per Bauform-Entscheid **kein eigenes
Merkmal** — sie verortet `Mediates` (24.) auf dem Träger der `reflect`-Hebung
(25.). Der Kern-Satz: **jeder rückkehrfreie Prozess vermittelt an seinen
Inhalten** — der leere Inhalt kehrt wieder (25.), der Einer-Inhalt flieht
(Bahn-Gesetz plus Rückkehrfreiheit); was die Natur-Stufe 4 als vorgefundene
Koexistenz kennt, erzeugt die Geist-Stufe 6 aus der Reflexion. Das Duett mit der
24. am selben Zeugen: dieselbe Stufung, die unten nicht vermittelt
(`succ_not_mediates`), vermittelt an ihren Inhalten; die Kür setzt den Kontrast —
die Reflexion des Reversiblen vermittelt nicht.

**Ein Import** (`ContentReflexivity`, transitiv die gesamte Kette und das
Substrat); die Kette wird 16→19→20→22→23→24→25→26. Term-identisch konsumiert
werden `reflect`, `reflect_iterate`, `reflect_ground_empty`, `reflect_reversible`
(25.), `Mediates`, `mediates_not_reversible` (24.), `NoReturn`, `succ_noreturn`
(23.), `Reversible` (22.), `Ground` (20.), `intervalStart`/`intervalEnd` (21.).
Nichts wird dupliziert; **kein Mathlib-Import über die transitive Hülle hinaus**.

## (1) Quellen

Der Anker: Intervall VI ist „der **Subjektivität als Vermittlungsprozess**
gewidmet" (Lille Z. 805–806; **Volltext-verifiziert**; die Zeilen-Marken stehen
unter der A2-Lokator-Klausel). Härte-Ökonomie: einmal geeicht (Beiträge III,
S. 160), verlängerbar.

## (2) MARKEN-TRIAS (Pflicht, W1-F3)

**Lokale Hegel-Relativitäts-Fassung:** die Intervall-Zuordnung der Stufen ist
„eine vorläufige" (Lille Z. 811–816) — Lesart der Hegel-Stufe, nicht Satz dieser
Schicht.
**Substrat-Erbe:** der Ort (`interval_VI_start`, `interval_VI_end`) kommt aus dem
Rückgrat (21.) — das Rückgrat zählt die Orte, diese Schicht deutet.
**Monas-Struktur-Marke:** die Ein-Positiv-Struktur (ein positiver Wert, alle
anderen seine Reflexionen, Lille Z. 1015–1017) ist Günthers Wort; jede
Werte-Formalisierung bleibt außerhalb dieses Baus.

## (3) VERZICHTS-MARKE (W1-F1)

Der Hegel-Hintergrund ist **benannt, nicht beigezogen** — Lesart, kein
Günther-Beleg; die Beiziehung bliebe siegel-pflichtig am Druck.

## (4) GRENZE

**Subjektivität wird nicht formalisiert** — keine Subjektivitäts- und keine
Bewusstseins-Semantik; term-fest werden Prozess-Sätze über der Hebung.
Vermittlungsprozess als gehobene Koexistenz ist **Deutung**; „die Vermittlung
entsteht in der Reflexion" ist **markierte Struktur-Aussage** (Projekt-Rede,
kein Zitat).

## (5) Term-fest werden hiermit

`reflect_singleton`, `reflect_mediates_of_noreturn`,
`reflect_noreturn_not_reversible`, `reflect_succ_mediates`, `interval_VI_start`,
`interval_VI_end`, Kür `reflect_reversible_not_mediates`.

**BAUFORM-ENTSCHEID:** die Stufe hat **kein eigenes Merkmal** — sie verortet
`Mediates` (24.) auf dem `reflect`-Träger (25.); das Merkmal ist ganz Anschluss.
Das ist die Bauform-These an ihrer reinsten Stelle, **kein Definitions-Defizit**.
R1-Ist-geprüft: unter den **sechs gebauten Stellen-Schichten** [19./20./22./23./
24./25.] führt jede eine eigene Merkmals-Konstante ein (`Exhausts`, `Ground`,
`Reversible`, `NoReturn`, `Mediates`, `reflect`); diese Schicht führt **keine** —
die erste ohne eigenes Merkmal in diesem Bereich (die Bereichs-Qualifikation ist
unverlierbar). Weitere Rang-Ansprüche werden nicht erhoben.
**KONSUM-EHRLICHKEIT:** eigener Beweis-Gehalt liegt im Bahn-Gesetz und im
Kern-Satz; die Konsum-Folge, der Zeugen-Satz und die Kür sind Konsum bzw.
Anwendung.

## (6) Deutungs-Marken

Der Set-Träger ist **Modellwahl**; **Designation ist nicht Denotation** gilt fort.

## (7) Abgrenzung

Kein Vorgriff auf St.7 — eigenes Paket. Keine Werte-, Bewusstseins- und keine
Subjektivitäts-Semantik; die benannten Posten der Vorschichten bleiben unberührt.
Die Nonempty-Bedingung des Kern-Satzes ist **Voraussetzungs-Ehrlichkeit, keine
Setzung**: auf leerem Träger fehlt der fliehende Einer-Inhalt. Die Lage-Sätze der
Stufe sind Anschluss-Sätze, kein neues Differential oder Merkmal.

## (8) Sorry-Bilanz und Axiom-Ist — mit Vormessungs-Tabelle und Rechnungs-Abgleich

**0 Sorries.** Axiom-Ist (erster grüner Build, v4.30.0-rc2), je Satz
`#guard_msgs`-verwacht am Datei-Ende (sieben Wachen):

* **`[propext, Quot.sound]`:** `reflect_singleton`, `reflect_mediates_of_noreturn`,
  `reflect_noreturn_not_reversible`, `reflect_succ_mediates`,
  `reflect_reversible_not_mediates` (Mengen-Extensionalität; die `omega`-Hülle
  von `succ_noreturn` reist in `reflect_succ_mediates` auf demselben Niveau mit).
* **axiom-frei:** `interval_VI_start`, `interval_VI_end` (Substrat-`decide`).

**Quell-Satz-Vormessung (Teil 0 (1), vor Routen-Wahl):**

* `Set.image_singleton` — `[propext, Classical.choice, Quot.sound]` (**Classical-
  Träger**).
* `Set.singleton_injective` — `[propext, Quot.sound]` (rein, benutzt).
* `Set.singleton_eq_singleton_iff` — `[propext, Quot.sound]` (rein, Alternative).

**Routen-Befund (Teil 0), classical-frei aufgelöst:** die naive Route für das
Bahn-Gesetz (`rw [reflect_iterate, Set.image_singleton]`) zöge `Classical.choice`
herein (`Set.image_singleton` trägt es in diesem Mathlib, wie zuvor
`Set.image_empty`/`Set.image_mono` in der 25.). `reflect_singleton` geht darum
den **Eigenbeweis** (`Set.ext` + `Set.mem_singleton_iff` + `rintro`) und liegt
classical-frei bei `[propext, Quot.sound]`; die Singleton-Extraktion im Kern-Satz
nutzt das reine `Set.singleton_injective`.

**Abgleich gegen die Profil-Rechnung (M7(8), R2 = Erwartung):** getroffen an
allen sieben — M2/M3 Set-ext-Bereich `[propext, Quot.sound]`, M5 mit
mitreisender `omega`-Hülle auf gleichem Niveau, M4 und Kür geerbt, M6 frei; **kein
`Classical`**, obwohl die naive Bahn-Gesetz-Route es hereingezogen hätte (siehe
Routen-Befund). Die `(reflect f)^[1] ∅ = ∅`-Wiederkehr-Hälfte trägt
`reflect_ground_empty` per Defeq (`Function.iterate_one` nicht nötig); die
Nonempty-Route bleibt classical-frei (`obtain ⟨x⟩ := ‹Nonempty α›` auf Prop-Ziel,
Muster der 23.).
-/

namespace Reformulation.Proemial.MediationProcess

open Reformulation.Proemial.ContentReflexivity
open Reformulation.Proemial.ComplementaryMediation
open Reformulation.Proemial.IrreversibleAdvance
open Reformulation.Proemial.ReversibleExchange
open Reformulation.Proemial.IntervalBackbone
open Reformulation.Proemial.RecurringGround

-- ============================================================
-- Teil 1 — Kein eigenes Merkmal (M1; Bauform-Entscheid, Doc-Posten)
-- ============================================================
-- Diese Schicht definiert KEINE neue Merkmals-Konstante. Sie verortet `Mediates`
-- (24.) auf dem `reflect`-Träger (25.). Der Entscheid steht in Doc-Rubrik (5).

-- ============================================================
-- Teil 2 — Das Bahn-Gesetz (M2)
-- ============================================================

/-- Die Einer-Inhalte laufen die Bahn des Punktes (öffentlicher Satz — das
    Gesetz ist Posten; Konsum des Iterations-Gesetzes der 25.). Route
    (Teil 0 (1)/(4)): `reflect_iterate`, dann classical-freier Eigenbeweis für
    `f^[n] '' {x} = {f^[n] x}` — nicht `Set.image_singleton`, das in diesem
    Mathlib `Classical.choice` trägt (Routen-Befund, Modul-Doc (8)). -/
theorem reflect_singleton {α : Type*} (f : α → α) (n : ℕ) (x : α) :
    (reflect f)^[n] {x} = {f^[n] x} := by
  rw [reflect_iterate]
  apply Set.ext
  intro y
  constructor
  · rintro ⟨a, ha, rfl⟩
    rw [Set.mem_singleton_iff] at ha
    subst ha
    rfl
  · intro hy
    rw [Set.mem_singleton_iff] at hy
    exact ⟨x, rfl, hy.symm⟩

-- ============================================================
-- Teil 3 — Der Kern-Satz (M3)
-- ============================================================

/-- „DIE VERMITTLUNG ENTSTEHT IN DER REFLEXION": jeder rückkehrfreie Prozess
    vermittelt an seinen Inhalten — der leere Inhalt kehrt wieder (25.), der
    Einer-Inhalt flieht (Bahn-Gesetz plus Rückkehrfreiheit). Was die Natur-Stufe
    4 als vorgefundene Koexistenz kennt, erzeugt die Geist-Stufe 6 aus der
    Reflexion (markierte Struktur-Aussage). Nonempty ehrlich, classical-frei. -/
theorem reflect_mediates_of_noreturn {α : Type*} [Nonempty α] {f : α → α}
    (h : NoReturn f) : Mediates (reflect f) := by
  constructor
  · -- Wiederkehr: ∅ bei Stufe 1 ((reflect f)^[1] ∅ = ∅ per Defeq aus 25.)
    exact ⟨∅, 1, Nat.one_pos, reflect_ground_empty f⟩
  · -- Flucht: der Einer-Inhalt eines Punktes
    obtain ⟨x⟩ := ‹Nonempty α›
    refine ⟨{x}, fun n hn hEq => ?_⟩
    rw [reflect_singleton] at hEq
    exact h x n hn (Set.singleton_injective hEq)

-- ============================================================
-- Teil 4 — Konsum-Folge und Zeugen-Satz (M4/M5)
-- ============================================================

/-- Echter Dritter, zweite Hälfte: die gehobene Welt des Rückkehrfreien ist
    nicht reversibel — die erste Hälfte („nicht rückkehrfrei") ist
    `reflect_not_noreturn` (25.). An beiden Sätzen ist sie keiner der Nachbarn. -/
theorem reflect_noreturn_not_reversible {α : Type*} [Nonempty α] {f : α → α}
    (h : NoReturn f) : ¬ Reversible (reflect f) :=
  fun hr => mediates_not_reversible (reflect_mediates_of_noreturn h) hr

/-- DAS DUETT MIT DER 24.: dieselbe Stufung, die unten nicht vermittelt
    (`succ_not_mediates`, 24.), vermittelt an ihren Inhalten — der
    Vermittlungsprozess an dem Zeugen, der unten nicht vermittelt (reine Anwendung
    des Kern-Satzes auf `succ_noreturn`, 23.). -/
theorem reflect_succ_mediates : Mediates (reflect Nat.succ) :=
  reflect_mediates_of_noreturn succ_noreturn

-- ============================================================
-- Teil 5 — Orts-Sätze (M6)
-- ============================================================

/-- Der Ort aus dem Rückgrat (21.): Intervall VI beginnt bei 21 … -/
theorem interval_VI_start : intervalStart 6 = 21 := by decide

/-- … und endet bei 27 — Substrat-Abruf. -/
theorem interval_VI_end : intervalEnd 6 = 27 := by decide

-- ============================================================
-- Teil 6 — Kür (K1): der Kontrast als Satz
-- ============================================================

/-- KÜR — DER KONTRAST ALS SATZ: die Reflexion des Reversiblen vermittelt NICHT
    (reiner Doppel-Konsum: `reflect_reversible` der 25. plus
    `mediates_not_reversible` der 24.) — die Vermittlung entsteht in der
    Reflexion genau des Irreversiblen, nicht des Reversiblen. -/
theorem reflect_reversible_not_mediates {α : Type*} {f : α → α}
    (h : Reversible f) : ¬ Mediates (reflect f) :=
  fun hm => mediates_not_reversible hm (reflect_reversible h)

end Reformulation.Proemial.MediationProcess

-- ============================================================
-- Teil 7 — Die `#guard_msgs`-Wachen (M8; Ist-gebunden)
-- ============================================================

-- Ist-Ausgabe des ersten grünen Builds (v4.30.0-rc2), pro Satz als Wache.
open Reformulation.Proemial.MediationProcess in
section

/-- info: 'Reformulation.Proemial.MediationProcess.reflect_singleton' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms reflect_singleton

/-- info: 'Reformulation.Proemial.MediationProcess.reflect_mediates_of_noreturn' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms reflect_mediates_of_noreturn

/-- info: 'Reformulation.Proemial.MediationProcess.reflect_noreturn_not_reversible' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms reflect_noreturn_not_reversible

/-- info: 'Reformulation.Proemial.MediationProcess.reflect_succ_mediates' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms reflect_succ_mediates

/-- info: 'Reformulation.Proemial.MediationProcess.interval_VI_start' does not depend on any axioms -/
#guard_msgs in #print axioms interval_VI_start

/-- info: 'Reformulation.Proemial.MediationProcess.interval_VI_end' does not depend on any axioms -/
#guard_msgs in #print axioms interval_VI_end

/-- info: 'Reformulation.Proemial.MediationProcess.reflect_reversible_not_mediates' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms reflect_reversible_not_mediates

end
