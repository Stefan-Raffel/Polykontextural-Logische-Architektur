import Reformulation.Proemial.GeneralCloneBound

/-!
# Proemial.RAGAuthority — die dritte Anwendung: Quellenautorität (E3-Instanz)

**Benennung, kein Ertrag.** Diese Datei liefert **keinen neuen Satz**. Beide
Schranken-Sätze sind **Instanzen von E3** — `autoritaet_nicht_erzeugbar` die
`mp`-Richtung von `GeneralCloneBound.locally_classical_in_clone_iff` bei m = 4,
`autoritaet_nicht_erzeugbar_konstanten` die Konstanten-Fassung
`GeneralCloneBound.constant_clone_min_or_max`. Neu sind allein die **Daten** (die
Politik `autoritaet`, zwei Widerlegungspunkte) und die **Lesart**, und die ist
Deutung, kein Satzgehalt (CLAUDE.md §4).

## Die Lesart: vier Autoritätsstufen

```text
0 Notiz < 1 Teamdokument < 2 Policy < 3 Gesetz
```

**Die Namen sind Lesart; term-fest ist `Fin 4`.** Es gibt keine benannten
Stufen-Abkürzungen. Die Skala stammt aus `PKL-Anwendungsfaelle.md` §2.

Die Politik nimmt die **schwächere** Quelle (`min`): eine Aussage, die sich auf
Quellen verschiedener Autorität stützt, trägt das Niveau der schwächsten — eine
Notiz zieht alles auf Notiz-Niveau, und nichts unterhalb des Gesetzes wird durch
Kombination zum Gesetz. Die eine Ausnahme ist der interne
Governance-Korridor: wo Teamdokument und Policy kollidieren, gilt der **Vorrang
der Policy** (`max` auf `{1,2}`). Genau diese eine bereichsabhängige Ausnahme
macht die Politik zum Zeugen: lokal überall klassisch, global weder `min` noch
`max`. Ein Term über `L` ist die Verschaltung lokaler, kontextur-blinder Prüfer
(intra-kontexturell, `Definitionen.md` §9), gleich in welcher Tiefe.

## Der dritte Zeuge: die Mischstelle wandert, die Schranke bleibt

Drei Zeugen an drei Mischstellen — `PolicyCheck.freigabe` **unten** (`{0,1}`),
`autoritaet` in der **Mitte** (`{1,2}`), `StageAggregation.agg` **oben**
(`{2,3}`). Die Schranke hängt an der **Mischung**, nicht am Ort der Mischstelle.
`autoritaet` ist punktweise verschieden von `agg` an genau `(1,2)`, `(2,1)`,
`(2,3)`, `(3,2)` und von `freigabe` an genau `(0,1)`, `(1,0)`, `(1,2)`, `(2,1)`;
das ist Definitionsbefund und **kein Satz** — kein Vergleichssatz im Korpus, weil
keine Zeile des Bestands einen verlangt, und kein Satz-Statement dieses Moduls
wiederholt eine Aussage des Bestands.

## Anwendungsschwelle vier Stufen

Bei m = 3 wäre der Satz falsch — das Argument liegt in E1
(`NonUniformCloneBound`) und E3 (`GeneralCloneBound`); hier steht der Verweis,
nicht seine Wiederholung.

## Robustheit (CLAUDE.md §9)

Die Invariante des konsumierten Satzes ist `R 4`, und sie ist **reflexiv**
(`GeneralCloneBound.R_diag`); darum überlebt die Schranke die Erweiterung der
Signatur um **alle vier Konstanten**. Das ist das Ergebnis der
Reflexivitätsprüfung für dieses Modul; eine eigene Invariante wird nicht gebaut,
sondern die des konsumierten Satzes ausgewiesen. Ein konstanter Prüfer („diese
Quelle gilt immer als `Policy`") ist in dieser Lesart der natürlichste Baustein
überhaupt.

## Wortlaut-Grenzen

1. Diese Datei gibt
   **keine Sicherheits-, Rechts-, Wahrheits- oder Retrievalgarantie**.
   Bewiesen ist, was aus lokalen, kontextur-blinden Prüfern nicht
   zusammensetzbar ist.
2. **Autorität ist nicht Evidenz.** Der Satz sagt nichts über die *Wahrheit* von
   Quellinhalten; er handelt von der Stufung, nicht vom Inhalt.
3. **Keine Behauptung über RAG-Systeme.** Der Satz handelt von Operationen auf
   endlichen Stufenmengen. Dass Retrieval-Systeme so gebaut sind, ist eine
   Anwendungsannahme, keine Folgerung.
4. Die Schranke trägt nur auf **linear gestuften** Trägern: gleichrangige Quellen
   ohne Stufenachse werden nicht getragen, und auf nicht-linearen Verbänden fällt
   die Charakterisierung bereits am kleinsten flachen Verband `M3`
   (Grenzabschnitt im Doc-String von `StageAggregation`; die Zahlen der Sonde
   bleiben außerhalb des Korpus, CLAUDE.md §6).
5. Marke 3 unverändert: der Dateiname sagt, was gebaut ist, nicht was gedeutet
   wird.

**Namens-Abwägung (Marke 3).** `RAGAuthority` benennt nicht den Satz — der bleibt
E3 und liegt in `GeneralCloneBound` —, sondern den Anwendungsgegenstand, die
Autoritätsstufung von Retrieval-Quellen; nicht behauptet ist ein bewiesener
Retrieval- oder Wahrheitsgehalt. Rückfallname wäre `SourceAuthority`.

Fallstrick 2 (CLAUDE.md §8): `LocallyClassical`, `ActsAsMin` und `ActsAsMax` sind
`def`s, `decide` sieht nicht hindurch — `unfold` davor.

0 Sorries; kein Satz zieht `Classical.choice`.
-/

open FirstOrder Language
open Reformulation.Proemial.TransjunctionCloneBound (L)
open Reformulation.Proemial.GeneralCloneBound

namespace Reformulation.Proemial.RAGAuthority

/-! ## Teil 1 — die Politik -/

/-- Die Autoritätspolitik: konservativ (Minimum) überall — außer zwischen
Teamdokument und Policy, wo permissiv (Maximum) aggregiert wird (Vorrang der
Policy im internen Governance-Korridor). Mischstelle **Mitte**, im Kontrast zu
`PolicyCheck.freigabe` (unten) und `StageAggregation.agg` (oben). -/
def autoritaet (a b : Fin 4) : Fin 4 :=
  if (a = 1 && b = 2) || (a = 2 && b = 1) then max a b else min a b

/-! ## Teil 2 — die Voraussetzung und die beiden Anwendungssätze -/

/-- **`autoritaet` ist lokal klassisch:** auf jeder Elementarkontextur `{x, y}`
wirkt sie wie `min` oder wie `max` — wie `max` auf `{1, 2}`, wie `min` auf den
fünf übrigen. Fallstrick 2: `unfold` vor `decide`. -/
theorem autoritaet_lokal : LocallyClassical autoritaet := by
  unfold LocallyClassical ActsAsMin ActsAsMax; decide

/-- **Der Anwendungssatz: `autoritaet` ist nicht erzeugbar.** Keine Verschaltung
lokaler, kontextur-blinder Prüfer liefert die Politik — gleich in welcher Tiefe.
Eine **Instanz von E3**, kein neuer Satz: die `mp`-Richtung von
`locally_classical_in_clone_iff` plus zwei Widerlegungspunkte, `(1,2)` gegen
`min` und `(0,1)` gegen `max`. -/
theorem autoritaet_nicht_erzeugbar :
    ¬ ∃ t : L.Term (Fin 2), ∀ v, t.realize v = autoritaet (v 0) (v 1) := by
  intro h
  rcases (locally_classical_in_clone_iff (m := 4) (by omega) autoritaet
      autoritaet_lokal).mp h with h1 | h1
  · have hp := congrFun (congrFun h1 1) 2; revert hp; decide
  · have hp := congrFun (congrFun h1 0) 1; revert hp; decide

/-- **Robustheit nach CLAUDE.md §9:** auch mit beliebigen konstanten Prüfern als
Bausteinen bleibt `autoritaet` unkomponierbar. Träger ist die Reflexivität von
`R 4` (`R_diag`), über die E3 die Konstanten-Fassung `constant_clone_min_or_max`
bereitstellt. -/
theorem autoritaet_nicht_erzeugbar_konstanten :
    ¬ ∃ t : (Lc 4).Term (Fin 2), ∀ v, t.realize v = autoritaet (v 0) (v 1) := by
  intro h
  rcases constant_clone_min_or_max (m := 4) (by omega) autoritaet autoritaet_lokal h
    with h1 | h1
  · have hp := congrFun (congrFun h1 1) 2; revert hp; decide
  · have hp := congrFun (congrFun h1 0) 1; revert hp; decide

/-! ## Teil 3 — Statement-Pins

Voller Wortlaut links, Satz rechts — jede Drift des *Statements* bricht den Build.
Namenlose `example`s, keine Axiom-Wache; Datei-Vollständigkeit: alle drei Sätze. -/

-- STATEMENT-PIN
example : ∀ x y : Fin 4, x ≠ y →
    (∀ a b : Fin 4, (a = x ∨ a = y) → (b = x ∨ b = y) →
      autoritaet a b = min a b) ∨
    (∀ a b : Fin 4, (a = x ∨ a = y) → (b = x ∨ b = y) →
      autoritaet a b = max a b) :=
  autoritaet_lokal

-- STATEMENT-PIN
example : ¬ ∃ t : L.Term (Fin 2), ∀ v : Fin 2 → Fin 4,
    t.realize v = autoritaet (v 0) (v 1) :=
  autoritaet_nicht_erzeugbar

-- STATEMENT-PIN
example : ¬ ∃ t : (Lc 4).Term (Fin 2), ∀ v : Fin 2 → Fin 4,
    t.realize v = autoritaet (v 0) (v 1) :=
  autoritaet_nicht_erzeugbar_konstanten

/-! ## Teil 4 — die Axiom-Wachen (Ist-gebunden)

Ist-Ausgabe des grünen Builds (v4.30.0-rc2), pro Satz als Regressions-Wache
eingefroren (Datei-Vollständigkeits-Regel: alle drei Sätze der Datei). **Kein Satz
zieht `Classical.choice` oder `sorryAx`.** -/

/-- info: 'Reformulation.Proemial.RAGAuthority.autoritaet_lokal' depends on axioms: [propext] -/
#guard_msgs in #print axioms autoritaet_lokal

/-- info: 'Reformulation.Proemial.RAGAuthority.autoritaet_nicht_erzeugbar' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms autoritaet_nicht_erzeugbar

/-- info: 'Reformulation.Proemial.RAGAuthority.autoritaet_nicht_erzeugbar_konstanten' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms autoritaet_nicht_erzeugbar_konstanten

end Reformulation.Proemial.RAGAuthority
