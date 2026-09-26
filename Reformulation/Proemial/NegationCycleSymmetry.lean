import Reformulation.Proemial.NegationCycleSearch

/-!
# Proemial.NegationCycleSymmetry — Günthers Familienrede auf Sätzen

**Stufen, je Satz am Beweis bestimmt** (26.9.2026; die modulweite Marke „FOLGERUNG" traf
keinen der drei Sätze):
- `no_888_all` — ZUSAMMENSTELLUNG — `exactly_fortyfour` und `alleKreise_no_888`, dazu die
  Umkehrung.
- `mirror_gerichtet` — EICHUNG — die 88 gerichteten Kreise.
- `mirror_all` — ZUSAMMENSTELLUNG — `full_iff_mem`, `alleB_perm_gerichtet` und
  `mirror_gerichtet`.

Gebaut auf Anordnung des Architekten vom 25. September 2026 nach
`KorpusRev2/Spec_Zug1_NegationCycleSymmetry.md` (Fassung 2, Mathematiker), Teil A; die
Sätze stammen aus `KorpusRev2/Mut_Bauoptionen_Rueckschau_Impl.md` (M2, M3). Das Modul
liegt hinter `NegationCycleSearch`, weil zwei seiner Sätze `exactly_fortyfour` und
`full_iff_mem` verbrauchen. `NegationCycle` kann `NegationCycleSearch` nicht importieren.

* **K1 — `no_888_all`, Günthers „niemals" für jeden vierwertigen Vollkreis.** IGN S. 43:
  „Dabei ergibt sich, dass alle drei Operatoren sich niemals gleich oft wiederholen dürfen,
  um den erwünschten Kreis zu bilden." Günther sagt es ohne Beweis. Hier ist es ein Satz,
  vom selben Typ wie `triadic_unique`: der Beweis einer Quellenaussage. Er folgt aus
  `exactly_fortyfour` (jeder Vollkreis ist einer der 44 oder die Umkehrung eines davon) und
  `alleKreise_no_888`. Vor Stufe 2b war das nur durch Aufzählung zu haben.
* **K2 — `mirror_all`, die Spiegelung `N₁ ↔ N₃`.** Sie führt jeden Vollkreis in einen
  Vollkreis über, **bei vier Werten**, weil der Beweis über die entschiedene Tafel läuft
  (`mirror_gerichtet` ist die Eichung über die 88 gerichteten Kreise). Für mehr Werte ist
  der Satz **ungemessen**; die allgemeine Fassung über die Konjugation mit der Wertumkehr ist
  nicht gebaut.
* **K3 — die Familienrede.** Mit `reverse_full` (Drehsinn, für jedes `m`) und `mirror_all`
  (Spiegelung, vier Werte) steht Günthers Familienrede auf Sätzen. IGN S. 43: „Wir haben
  dabei die Umkehrung der ersten Verteilung der Operatoren 10-9-5, also 5-9-10 zur gleichen
  Familie gerechnet." „Familie" ist Günthers Wort, darum steht es im Kopf und in keinem
  Bezeichner. Die Familien selbst, nach der Häufigkeit der Operatoren, sind in
  `NegationCycleThreeCycle` vollständig gezählt (`verteilungen_vollstaendig_all`); die
  Spiegelung hier ist der Grund, warum 10-9-5 und 5-9-10 eine Familie sind.
* **K4 — nicht:** Tafel XX, kein §20-Anspruch, keine Ledger-Zeile.

## Axiomprofil

Gemessen nach grünem Bau und am Dateiende gewacht: `no_888_all` und `mirror_all` tragen
`[propext, Quot.sound]`, `mirror_gerichtet` trägt `[propext]`. **Kein `Classical.choice`.**
-/

namespace Reformulation.Proemial.NegationCycleSymmetry

open Reformulation.Proemial.NegationCycle Reformulation.Proemial.NegationCycleTable
  Reformulation.Proemial.NegationCycleSearch

/-- **Kein vierwertiger Vollkreis verteilt die Operatoren 8-8-8** — Günthers „niemals"
(IGN S. 43), für jeden Vollkreis. -/
theorem no_888_all (seq : List (Fin 3)) (h : IsFullCycle seq) :
    ¬(seq.count 0 = 8 ∧ seq.count 1 = 8 ∧ seq.count 2 = 8) := by
  rcases (exactly_fortyfour seq).mp h with h1 | h1
  · exact alleKreise_no_888 seq h1
  · have := alleKreise_no_888 _ h1
    simpa only [List.count_reverse] using this

/-- Eichung: die Spiegelung `N₁ ↔ N₃` führt die 88 gerichteten Kreise in sich über. -/
theorem mirror_gerichtet : ∀ s ∈ gerichtet, s.map Fin.rev ∈ gerichtet := by decide

/-- **Die Spiegelung `N₁ ↔ N₃` führt jeden vierwertigen Vollkreis in einen Vollkreis
über.** -/
theorem mirror_all (seq : List (Fin 3)) (h : IsFullCycle seq) :
    IsFullCycle (seq.map Fin.rev) := by
  have hm : seq ∈ gerichtet :=
    (List.Perm.mem_iff alleB_perm_gerichtet).mpr ((full_iff_mem seq).mp h)
  exact (full_iff_mem _).mpr (alleB_perm_gerichtet.mem_iff.mp (mirror_gerichtet seq hm))

-- ============================================================
-- Wachen
-- ============================================================

/-- info: 'Reformulation.Proemial.NegationCycleSymmetry.no_888_all' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms no_888_all

/-- info: 'Reformulation.Proemial.NegationCycleSymmetry.mirror_gerichtet' depends on axioms: [propext] -/
#guard_msgs in #print axioms mirror_gerichtet

/-- info: 'Reformulation.Proemial.NegationCycleSymmetry.mirror_all' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms mirror_all

end Reformulation.Proemial.NegationCycleSymmetry
