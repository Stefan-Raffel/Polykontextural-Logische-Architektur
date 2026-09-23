import Reformulation.Proemial.NegationCycle

/-!
# Proemial.NegationCycleSJT — die Steinhaus–Johnson–Trotter-Konstruktion der Vollkreise (Teil A)

**FOLGERUNG und EICHUNG.** Gebaut auf Anordnung des Architekten vom 25. September 2026 nach
`KorpusRev2/Spec_SJT_Zug.md` (Mathematiker), Teil A. Sondiert in
`KorpusRev2/Sondierung_SJT_Listenfassung_Impl.md`, begutachtet in
`KorpusRev2/Begutachtung_Spec_SJT_Zug_Impl.md`. Teil B, der Beweis für jede Wertzahl, ist
ein eigener Posten und hier **nicht gebaut**.

**Die Konstruktion** (`blocks`, `sjtNat`, `sjt`): Der neue Wert fegt abwechselnd nach links
(Indizes `k−2 … 0`) und nach rechts (`0 … k−2`). Zwischen zwei Fegegängen steht ein Schritt
des kleineren Kreises, um eins verschoben, wenn der neue Wert links steht. „Steinhaus–
Johnson–Trotter" ist der Name der Konstruktion in der Mathematik, kein Günther-Wort.

* **K1 — Günthers Voraussetzung.** Günther setzt einen Vollkreis für jede Wertzahl voraus:
  Er spricht vom „Wörterbuch einer fünfwertigen Negativsprache", dessen Termini „schon in
  die Milliarden" gehen (1980 S. 21). Die Wörter dieses Wörterbuchs sind die vollständigen
  Hamiltonkreise (1980 S. 20). Dieses Modul baut die Konstruktion, die solche Kreise liefert,
  und beweist sie als Vollkreis für zwei, drei und vier Werte (`sjt1_full`, `sjt2_full`,
  `sjt3_full`). Für jede Wertzahl ist das Teil B, nicht gebaut.
* **K2 — bei einem Wert gibt es keinen Vollkreis** (`no_full_at_one_value`). Das einzige Wort
  ist das leere, es hat keine Stationen, und die eine Anordnung müsste Station sein. Ein Satz
  über jede Wertzahl beginnt darum bei zwei Werten.
* **K3 — die Listen-Fassung aus einem Vollkreis** (`reach_of_full`, für jedes `m`). Gibt es
  einen Vollkreis, so ist jede Anordnung Endpunkt eines Negatorworts, konstruktiv: Das Wort
  ist das Anfangsstück des Kreises bis zu ihrer Station (`mem_stations_endpoint`). Für jede
  Wertzahl wird die Listen-Fassung erst mit Teil B.
* **K4 — Günthers Kreise als Eichung.** Bei drei Werten ist `sjt` Günthers Folge (5)
  (`sjt2_eq`, IGN S. 18). Bei vier Werten ist die SJT-Folge Negator für Negator der
  gespiegelte **emendierte** zweite Kreis (`sjt3_mirror_kreis2`). Das ist ein Zeuge der
  Emendation von ausserhalb des Textes: Eine Konstruktion, die von Günther nichts weiss,
  setzt dasselbe `·1·3` an dieselbe Stelle wie `kreis2_emendation` und `janus1974`. Es ist
  einer von drei Kreisen (der erste und der dritte gehören anderen Familien an); ob Günther
  so gebildet hat, ist eine Quellenfrage.
* **K5 — Stellensicht und Wertsicht.** Die Negatoren wirken auf Werte; die Stationen sind
  darum die Inversen der Stationen, die dasselbe Indexwort als Stellentausch erzeugt. Weil
  jeder Negator seine eigene Umkehrung ist, ist ein Wort im einen Sinn genau dann ein
  Vollkreis, wenn es einer im anderen ist. Die Sätze hier sprechen direkt über `IsFullCycle`.

**Nicht:** Hegels „Kreis von Kreisen", Tafel XX, kein §20-Anspruch, keine Ledger-Zeile.

## Axiomprofil

Gemessen nach grünem Bau und am Dateiende gewacht: alle Sätze tragen `[propext]`, **kein
`Classical.choice`**. Kein `set_option maxRecDepth` nötig.
-/

namespace Reformulation.Proemial.NegationCycleSJT

open Reformulation.Proemial.NegationCycle

/-- Die Blöcke: der neue Wert fegt abwechselnd nach links und nach rechts, dazwischen ein
Schritt des kleineren Kreises (um eins verschoben, wenn der neue Wert links steht). -/
def blocks (k : ℕ) : Bool → List ℕ → List ℕ
  | _, [] => []
  | true, s :: ss => (List.range (k - 1)).reverse ++ [s + 1] ++ blocks k false ss
  | false, s :: ss => List.range (k - 1) ++ [s] ++ blocks k true ss

/-- Steinhaus–Johnson–Trotter als Indexwort über `ℕ`, für `n` Werte. -/
def sjtNat : ℕ → List ℕ
  | 0 => []
  | 1 => []
  | 2 => [0, 0]
  | n + 3 => blocks (n + 3) true (sjtNat (n + 2))

/-- Ein Indexwort über `ℕ` als Negatorwort. -/
def toFin (m : ℕ) (l : List ℕ) : List (Fin m) :=
  l.filterMap (fun k => if h : k < m then some ⟨k, h⟩ else none)

/-- Die SJT-Folge als Negatorwort über `m + 1` Werten. -/
def sjt (m : ℕ) : List (Fin m) := toFin m (sjtNat (m + 1))

/-- Jede Station ist Endpunkt eines Anfangsstücks. -/
theorem mem_stations_endpoint {m : ℕ} (w : List (Fin m)) (x l : List (Fin (m + 1)))
    (h : l ∈ stations w x) : ∃ k, endpoint (w.take k) x = l := by
  induction w generalizing x with
  | nil => simp [stations] at h
  | cons i is ih =>
    simp only [stations, List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨0, rfl⟩
    · obtain ⟨k, hk⟩ := ih _ h
      exact ⟨k + 1, by simpa [endpoint] using hk⟩

/-- **Die Listen-Fassung aus einem Vollkreis**: gibt es einen Vollkreis, so ist jede
Anordnung Endpunkt eines Negatorworts — für jedes `m`. -/
theorem reach_of_full {m : ℕ} {w : List (Fin m)} (hw : IsFullCycle w)
    (a : List (Fin (m + 1))) (ha : a ∈ (origin m).permutations') :
    ∃ v : List (Fin m), endpoint v (origin m) = a := by
  obtain ⟨k, hk⟩ := mem_stations_endpoint w _ a (hw.all_arrangements a ha)
  exact ⟨_, hk⟩

/-- **Bei einem Wert gibt es keinen Vollkreis.** -/
theorem no_full_at_one_value : ¬ ∃ w : List (Fin 0), IsFullCycle w := by
  rintro ⟨w, hw⟩
  cases w with
  | nil => exact absurd hw (by decide)
  | cons i _ => exact i.elim0

/-- Eichung: zwei Werte. -/
theorem sjt1_full : IsFullCycle (sjt 1) := by decide

/-- Eichung: bei drei Werten ist `sjt` Günthers Folge (5), `N2·1·2·1·2·1` (IGN S. 18). -/
theorem sjt2_eq : sjt 2 = tafelVI5 := by decide

/-- Eichung: drei Werte. -/
theorem sjt2_full : IsFullCycle (sjt 2) := by decide

/-- Eichung: vier Werte. -/
theorem sjt3_full : IsFullCycle (sjt 3) := by decide

/-- **Bei vier Werten ist die SJT-Folge der gespiegelte emendierte zweite Kreis Günthers**,
Negator für Negator. -/
theorem sjt3_mirror_kreis2 : sjt 3 = kreis2.map Fin.rev := by decide

-- ============================================================
-- Wachen
-- ============================================================

/-- info: 'Reformulation.Proemial.NegationCycleSJT.mem_stations_endpoint' depends on axioms: [propext] -/
#guard_msgs in #print axioms mem_stations_endpoint

/-- info: 'Reformulation.Proemial.NegationCycleSJT.reach_of_full' depends on axioms: [propext] -/
#guard_msgs in #print axioms reach_of_full

/-- info: 'Reformulation.Proemial.NegationCycleSJT.no_full_at_one_value' depends on axioms: [propext] -/
#guard_msgs in #print axioms no_full_at_one_value

/-- info: 'Reformulation.Proemial.NegationCycleSJT.sjt1_full' depends on axioms: [propext] -/
#guard_msgs in #print axioms sjt1_full

/-- info: 'Reformulation.Proemial.NegationCycleSJT.sjt2_eq' depends on axioms: [propext] -/
#guard_msgs in #print axioms sjt2_eq

/-- info: 'Reformulation.Proemial.NegationCycleSJT.sjt2_full' depends on axioms: [propext] -/
#guard_msgs in #print axioms sjt2_full

/-- info: 'Reformulation.Proemial.NegationCycleSJT.sjt3_full' depends on axioms: [propext] -/
#guard_msgs in #print axioms sjt3_full

/-- info: 'Reformulation.Proemial.NegationCycleSJT.sjt3_mirror_kreis2' depends on axioms: [propext] -/
#guard_msgs in #print axioms sjt3_mirror_kreis2

end Reformulation.Proemial.NegationCycleSJT
