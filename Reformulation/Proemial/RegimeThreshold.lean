import Reformulation.Proemial.GeneralCloneBound

/-!
# Proemial.RegimeThreshold — der Schwellensatz: das diskonturale Regime kippt bei m = 4

**Ertrag.** Dieser Satz bindet die **Wert-Aufstiegs-Achse** an die
**Verlust-Achse** an genau dem einen Ort, an dem sie sich im Korpus wirklich
treffen (Sondierungs-Befund `Wertbasierter_Traeger_Sondierung_Befund.md`): dem
Übergang von drei zu vier Werten. Er ist die sachlich richtigere Antwort auf die
„Kontexturgrenze"-Spalte der KA-Matrix als der Längen-Turm — nicht per Setzung
„Stufe = Kontextur", sondern auf dem wertbasierten Kontextur-Begriff der D/E-Reihe.

## Was er sagt

Eine **gemischte** lokal-klassische Operation — eine, die auf einer
Elementarkontextur wie `max`, auf einer anderen wie `min` wirkt — ist

- bei `m = 3` **erzeugbar** (liegt im Klon von `{∧, ∨, ¬}`): der Zeuge ist das
  Muster max/min/min (`NonUniformCloneBound.pattern_max_min_min_in_clone`, E1);
- bei `m = 4` **nicht erzeugbar**: jede erzeugbare lokal-klassische Operation ist
  global `min` oder global `max` (`GeneralCloneBound.locally_classical_in_clone_iff`,
  E3) — für eine gemischte bleibt kein Term.

Der Wert-Schritt `3 → 4` ist damit der Punkt, an dem nicht-uniforme lokale Wahl
von „komponierbar" zu „unkomponierbar" kippt. Das ist keine arithmetische
Zählung, sondern eine **qualitative Änderung des logischen Universums** an einer
bestimmten Wertzahl — das endliche Gegenstück zu Günthers Regimewechsel.

## Warum das mehr trägt als der Längen-Turm

Beim Längen-Turm (`TowerAsymmetryProbe`) lagen die drei Merkmale auf getrennten
Achsen (Richtung/Substruktur am Aufstieg `n → n+1`, Verlust bei festem Objekt),
und die Kontextur-Deutung war eine freie Setzung (`contextureCrossing : True`).
Hier fallen Aufstieg (`m → m+1`) und Verlust (Nicht-Erzeugbarkeit) in **einem**
Vorgang zusammen, und „Kontextur = Wert-Zweiermenge" ist der *etablierte* Begriff
der Schranken-Reihe, keine neue Wette. Der Schwellensatz ist eine **Bindung
derselben Achse**, keine Verkonjunktion zweier.

## Die verbleibende Grenze (E4-Begutachtung)

Der Satz trägt auf linearem `Fin m`. Die starke Charakterisierung fällt **nicht**
auf Kontexturverbände: auf `M3` gibt es lokal-klassische Terme, die weder `meet`
noch `join` sind — **bewiesen** in `Proemial.M3CloneWitness`
(`m3_mixed_term_exists`); die Klon-Zählungen der Sondierung bleiben außerhalb des
Korpus (CLAUDE.md §6). Die Schwelle ist ein Satz über Wertzahlen, kein Satz über
beliebige Verbund-Gitter.

## Aggregat-Reife

Konsumiert **nur** Aggregat-Inhalt (`GeneralCloneBound` ⊇ `NonUniformCloneBound`);
keine Standalone-Sonde, keine Setzung. Damit — anders als Turm und Transition —
ohne Kern/Rand-Bruch aggregatfähig; der Anschluss bleibt eine eigene Entscheidung.

Kein `sorry`, kein `axiom`, kein `: True`-Feld.
-/

open FirstOrder Language
open Reformulation.Proemial.TransjunctionCloneBound (L)

namespace Reformulation.Proemial.RegimeThreshold

open Reformulation.Proemial.NonUniformCloneBound
  (ActsAsMax ActsAsMin pattern_max_min_min_in_clone)
open Reformulation.Proemial.GeneralCloneBound
  (LocallyClassical locally_classical_in_clone_iff)

/-- **Der Schwellensatz.** Das diskonturale Regime kippt beim Wert-Schritt
`3 → 4`: eine gemischte lokal-klassische Operation ist bei `m = 3` erzeugbar,
bei `m = 4` nicht.

Erste Konjunkte (`m = 3`, E1): der Zeuge `pattern_max_min_min_in_clone` — ein
Term wirkt als `max` auf `{0,1}`, als `min` auf `{1,2}` und `{0,2}`, ist also
gemischt und im Klon.

Zweite Konjunkte (`m = 4`, E3): jede erzeugbare lokal-klassische Operation ist
global `min` oder global `max` — für eine gemischte bleibt kein Term. Reiner
Konsum der `mp`-Richtung von `locally_classical_in_clone_iff` bei `m = 4`. -/
theorem regime_threshold_at_four :
    (∃ t : L.Term (Fin 2),
        ActsAsMax (fun a b => t.realize ![a, b]) 0 1
      ∧ ActsAsMin (fun a b => t.realize ![a, b]) 1 2
      ∧ ActsAsMin (fun a b => t.realize ![a, b]) 0 2)
    ∧
    (∀ f : Fin 4 → Fin 4 → Fin 4, LocallyClassical f →
        (∃ t : L.Term (Fin 2), ∀ v : Fin 2 → Fin 4, t.realize v = f (v 0) (v 1)) →
        f = (fun a b => min a b) ∨ f = (fun a b => max a b)) :=
  ⟨pattern_max_min_min_in_clone,
   fun f h hc => (locally_classical_in_clone_iff (by omega) f h).mp hc⟩

-- ============================================================
-- Wachen — Axiom-Profile
-- ============================================================

/-! **Wachen.** Ist-Ausgabe des grünen Builds (v4.30.0-rc2). Der Schwellensatz
erbt über seine Hülle die Profile der konsumierten E1- und E3-Sätze. -/

/-- info: 'Reformulation.Proemial.RegimeThreshold.regime_threshold_at_four' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms regime_threshold_at_four

end Reformulation.Proemial.RegimeThreshold
