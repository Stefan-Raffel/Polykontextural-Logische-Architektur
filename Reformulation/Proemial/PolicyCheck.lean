import Reformulation.Proemial.GeneralCloneBound

/-!
# Proemial.PolicyCheck — die zweite Anwendung: Werkzeug-Freigabepolitik (E3-Instanz)

**Benennung, kein Ertrag.** Diese Datei liefert **keinen neuen Satz**. Beide
Schranken-Sätze sind **Instanzen von E3** — `freigabe_nicht_erzeugbar` die
`mp`-Richtung von `GeneralCloneBound.locally_classical_in_clone_iff` bei m = 4,
`freigabe_nicht_erzeugbar_konstanten` die Konstanten-Fassung
`GeneralCloneBound.constant_clone_min_or_max`. Neu sind allein die **Daten** (die
Politik `freigabe`, zwei Widerlegungspunkte) und die **Lesart**, und die ist
Deutung, kein Satzgehalt (CLAUDE.md §4).

## Die Lesart: vier Freigabestufen

```text
0 blocked < 1 needs_review < 2 approved < 3 privileged
```

**Die Namen sind Lesart; term-fest ist `Fin 4`.** Es gibt keine benannten
Stufen-Abkürzungen: was gebaut ist, sind vier linear geordnete Werte, alles
Weitere steht in diesem Doc-String.

Die Politik ist permissiv (`max`) **nur zwischen den beiden niedrigsten Stufen**,
sonst konservativ (`min`): was `blocked` und `needs_review` zusammenführt, fällt
nicht still auf `blocked`, sondern steigt zur Prüfung (`needs_review`) — eine
Politik, die nie schweigend blockiert; alles, was `approved` oder `privileged`
berührt, aggregiert konservativ. Ein Term über `L` ist die Verschaltung lokaler,
kontextur-blinder Prüfer (intra-kontexturell, `Definitionen.md` §9), gleich in
welcher Tiefe.

## Abgrenzung zu `StageAggregation`: andere Mischstelle

`StageAggregation.agg` mischt **oben** (permissiv zwischen den beiden höchsten
Stufen), `freigabe` mischt **unten**. Beide sind punktweise verschieden, und zwar
an genau den vier Stellen `(0,1)`, `(1,0)`, `(2,3)`, `(3,2)`. Zweck dieser Datei
ist der **zweite Konsument desselben generischen Satzes** — der Beleg, dass die
Schranke nicht an der Mischstelle von `StageAggregation` hängt —, ausdrücklich
**keine zweite Quelle** für eine Tatsache, die schon eine hat: kein Satz-Statement
dieses Moduls wiederholt eine Aussage des Bestands.

## Anwendungsschwelle vier Stufen

Bei m = 3 wäre der Satz falsch — das Argument liegt in E1
(`NonUniformCloneBound`) und im Doc-String von `StageAggregation`; hier steht der
Verweis, nicht seine Wiederholung.

## Robustheit (CLAUDE.md §9)

Die Invariante des konsumierten Satzes ist `R 4`, und sie ist **reflexiv**
(`GeneralCloneBound.R_diag`); darum überlebt die Schranke die Erweiterung der
Signatur um **alle vier Konstanten**. Das ist das Ergebnis der
Reflexivitätsprüfung für dieses Modul; eine eigene Invariante wird nicht gebaut,
sondern die des konsumierten Satzes ausgewiesen. In der Anwendungslesart ist das
die tragende Hälfte: ein konstanter Prüfer („liefere immer `approved`") ist der
natürlichste Baustein überhaupt, den eine Freigabepolitik hat.

## Wortlaut-Grenzen

1. Diese Datei gibt
   **keine Sicherheits-, Rechts-, Wahrheits- oder Retrievalgarantie**.
   Bewiesen ist, was aus lokalen, kontextur-blinden Prüfern nicht
   zusammensetzbar ist — nicht, dass ein System mit einer solchen Politik
   sicher, korrekt oder rechtmäßig handelt.
2. **Keine Behauptung über AI-Systeme.** Der Satz handelt von Operationen auf
   endlichen Stufenmengen. Dass Werkzeug-Freigaben so gebaut sind, ist eine
   Anwendungsannahme, keine Folgerung.
3. Die Schranke trägt nur auf **linear gestuften** Trägern: auf nicht-linearen
   Verbänden fällt die Charakterisierung bereits am kleinsten flachen Verband
   `M3` (Grenzabschnitt im Doc-String von `StageAggregation`; die Zahlen der
   Sonde bleiben außerhalb des Korpus, CLAUDE.md §6).
4. Marke 3 unverändert: der Dateiname sagt, was gebaut ist, nicht was gedeutet
   wird.

**Namens-Abwägung (Marke 3).** `PolicyCheck` benennt nicht den Satz — der bleibt
E3 und liegt in `GeneralCloneBound` —, sondern den gebauten Gegenstand: eine
Freigabepolitik samt ihrer Prüfung auf lokale Klassizität und
Nicht-Erzeugbarkeit; der Name nennt den Anwendungsgegenstand, nicht einen
bewiesenen Vermittlungs- oder Sicherheitsgehalt. Rückfallname wäre
`ToolAuthorization`.

Fallstrick 2 (CLAUDE.md §8): `LocallyClassical`, `ActsAsMin` und `ActsAsMax` sind
`def`s, `decide` sieht nicht hindurch — `unfold` davor.

0 Sorries; kein Satz zieht `Classical.choice`.
-/

open FirstOrder Language
open Reformulation.Proemial.TransjunctionCloneBound (L)
open Reformulation.Proemial.GeneralCloneBound

namespace Reformulation.Proemial.PolicyCheck

/-! ## Teil 1 — die Politik -/

/-- Die Freigabepolitik: konservativ (Minimum) überall — außer zwischen den beiden
niedrigsten Stufen, wo permissiv (Maximum) aggregiert wird. Genau diese Mischung
macht sie zum Zeugen: auf jeder Elementarkontextur klassisch, im ganzen weder
`min` noch `max`. Mischstelle **unten**, im Kontrast zu `StageAggregation.agg`. -/
def freigabe (a b : Fin 4) : Fin 4 :=
  if (a = 0 && b = 1) || (a = 1 && b = 0) then max a b else min a b

/-! ## Teil 2 — die Voraussetzung und die beiden Anwendungssätze -/

/-- **`freigabe` ist lokal klassisch:** auf jeder Elementarkontextur `{x, y}` wirkt
sie wie `min` oder wie `max` — wie `max` auf `{0, 1}`, wie `min` auf den fünf
übrigen. Fallstrick 2: `unfold` vor `decide`. -/
theorem freigabe_lokal : LocallyClassical freigabe := by
  unfold LocallyClassical ActsAsMin ActsAsMax; decide

/-- **Der Anwendungssatz: `freigabe` ist nicht erzeugbar.** Keine Verschaltung
lokaler, kontextur-blinder Prüfer liefert die Politik — gleich in welcher Tiefe.
Eine **Instanz von E3**, kein neuer Satz: die `mp`-Richtung von
`locally_classical_in_clone_iff` plus zwei Widerlegungspunkte, `(0,1)` gegen `min`
und `(2,3)` gegen `max`. -/
theorem freigabe_nicht_erzeugbar :
    ¬ ∃ t : L.Term (Fin 2), ∀ v, t.realize v = freigabe (v 0) (v 1) := by
  intro h
  rcases (locally_classical_in_clone_iff (m := 4) (by omega) freigabe
      freigabe_lokal).mp h with h1 | h1
  · have hp := congrFun (congrFun h1 0) 1; revert hp; decide
  · have hp := congrFun (congrFun h1 2) 3; revert hp; decide

/-- **Robustheit nach CLAUDE.md §9:** auch mit beliebigen konstanten Prüfern als
Bausteinen bleibt `freigabe` unkomponierbar. Träger ist die Reflexivität von `R 4`
(`R_diag`), über die E3 die Konstanten-Fassung `constant_clone_min_or_max`
bereitstellt. -/
theorem freigabe_nicht_erzeugbar_konstanten :
    ¬ ∃ t : (Lc 4).Term (Fin 2), ∀ v, t.realize v = freigabe (v 0) (v 1) := by
  intro h
  rcases constant_clone_min_or_max (m := 4) (by omega) freigabe freigabe_lokal h with h1 | h1
  · have hp := congrFun (congrFun h1 0) 1; revert hp; decide
  · have hp := congrFun (congrFun h1 2) 3; revert hp; decide

/-! ## Teil 3 — Statement-Pins

Voller Wortlaut links, Satz rechts — jede Drift des *Statements* bricht den Build.
Namenlose `example`s, keine Axiom-Wache; Datei-Vollständigkeit: alle drei Sätze. -/

-- STATEMENT-PIN
example : ∀ x y : Fin 4, x ≠ y →
    (∀ a b : Fin 4, (a = x ∨ a = y) → (b = x ∨ b = y) → freigabe a b = min a b) ∨
    (∀ a b : Fin 4, (a = x ∨ a = y) → (b = x ∨ b = y) → freigabe a b = max a b) :=
  freigabe_lokal

-- STATEMENT-PIN
example : ¬ ∃ t : L.Term (Fin 2), ∀ v : Fin 2 → Fin 4,
    t.realize v = freigabe (v 0) (v 1) :=
  freigabe_nicht_erzeugbar

-- STATEMENT-PIN
example : ¬ ∃ t : (Lc 4).Term (Fin 2), ∀ v : Fin 2 → Fin 4,
    t.realize v = freigabe (v 0) (v 1) :=
  freigabe_nicht_erzeugbar_konstanten

/-! ## Teil 4 — die Axiom-Wachen (Ist-gebunden)

Ist-Ausgabe des grünen Builds (v4.30.0-rc2), pro Satz als Regressions-Wache
eingefroren (Datei-Vollständigkeits-Regel: alle drei Sätze der Datei). **Kein Satz
zieht `Classical.choice` oder `sorryAx`.** -/

/-- info: 'Reformulation.Proemial.PolicyCheck.freigabe_lokal' depends on axioms: [propext] -/
#guard_msgs in #print axioms freigabe_lokal

/-- info: 'Reformulation.Proemial.PolicyCheck.freigabe_nicht_erzeugbar' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms freigabe_nicht_erzeugbar

/-- info: 'Reformulation.Proemial.PolicyCheck.freigabe_nicht_erzeugbar_konstanten' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms freigabe_nicht_erzeugbar_konstanten

end Reformulation.Proemial.PolicyCheck
