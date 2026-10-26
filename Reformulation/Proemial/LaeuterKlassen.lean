import Reformulation.Proemial.AkkretivitaetsBruecke   -- rotate_full; über GegenidentitaetProbe: umkehr, dreh, umkehr_full, guentherFamilie1

/-!
# Proemial.LaeuterKlassen — die 88 gerichteten Vollkreise auf vier Werten unter Drehung und Umkehr:  vier Klassen

STANDALONE, NICHT im Aggregat;  Target `Probes`.  AxiomGate unberührt.  Sonde nach `KorpusRev2/Prompt_Instanz_J12_Laeuterklassen_Eichung.md`
(Mathematiker, 26.10.2026 18:34;  Architekt 18:34 „J12: ja").  Herkunft:  `KorpusRev2/Meldung_Rev11_Plan3_Eichanker_Glocken_Impl.md` §2 G4
und Fund (gerechnet, `T_Vorprobe_Skripte/Plan3_Glocken.py`);  Anspruchsliste Rev11 J12, J4.  Diese Sonde macht die Rechnung zum Satz.
Konsumiert `GegenidentitaetProbe` (`umkehr`, `dreh`, `umkehr_umkehr`, `umkehr_full`, `guentherFamilie1`), `AkkretivitaetsBruecke`
(`rotate_full`), `NegationCycleTable` (`gerichtet`, `gerichtet_full`), `NegationCycleThreeCycle` (`vert`, `mem_gerichtet`), `NegationCycle`
(`IsFullCycle`, `kreis1`, `kreis2`, `kreis3`);  ändert nichts davon.

## Zählung

Wörter über `Fin 3` = Folgen der Negatoren N₁, N₂, N₃ auf vier Werten (Index 0, 1, 2).  `umkehr w := w.map Fin.rev` (N₁ ↔ N₃, N₂ fest;
die Werte von der anderen Seite gezählt), `dreh w := w.reverse` (rückwärts gelesen), `w.rotate k` (die Folge ab der k-ten Station gelesen:
eine andere Startreihe).  `vert w` = (Zahl der N₁, der N₂, der N₃).

## WAS

```text
laeuterKlasse w   :=  die Wörter  w.rotate k  und  umkehr (w.rotate k),  k < w.length   (mit Wiederholungen;  jede Wertzahl)

SATZ (jede Wertzahl)
  mem_laeuterKlasse         u ∈ laeuterKlasse w  ⟺  ∃ k < w.length,  u = w.rotate k  ∨  u = umkehr (w.rotate k)
  umkehr_rotate             umkehr (w.rotate k) = (umkehr w).rotate k  — Umkehr und Drehung vertauschen
  laeuterKlasse_trans       u ∈ laeuterKlasse z  →  v ∈ laeuterKlasse u  →  v ∈ laeuterKlasse z
  laeuterKlasse_symm        u ∈ laeuterKlasse z  →  z ∈ laeuterKlasse u
  laeuterKlasse_gleich      u ∈ laeuterKlasse z  →  dieselbe Klasse (Inklusion in beide Richtungen):  die Klassen SIND Bahnen
  laeuterKlasse_full   LK1  Ist w ein Vollkreis, so jedes Glied seiner Klasse (über rotate_full, umkehr_full)

LK1   klasse_in_gerichtet        FOLGERUNG   für w ∈ gerichtet liegt jedes Glied von laeuterKlasse w in gerichtet
LK2   vier_klassen               EICHUNG     vertreter = [kreis1, z24, kreis2, kreis3] liegen in gerichtet;  ihre Klassen haben
                                             48, 24, 8, 8 verschiedene Glieder;  jedes w ∈ gerichtet liegt in GENAU EINER von ihnen
      jede_klasse_eine_der_vier  FOLGERUNG   die Klasse jedes w ∈ gerichtet IST (als Menge) die Klasse eines der vier Vertreter
LK3   dreh_in_klasse             EICHUNG     dreh w ∈ laeuterKlasse w für jedes w ∈ gerichtet:  „rückwärts" gibt keine neue Klasse
LK4   familie1_klasse            EICHUNG     guentherFamilie1 w (10-9-5 oder 5-9-10)  ⟺  w ∈ laeuterKlasse kreis1, auf gerichtet
LK5   familie969_klasse          EICHUNG     vert w = (9, 6, 9)  ⟺  w ∈ laeuterKlasse kreis2, auf gerichtet
LK6   familie6126_zwei_klassen   EICHUNG     vert w = (6, 12, 6)  ⟺  w ∈ laeuterKlasse z24 ∨ w ∈ laeuterKlasse kreis3, auf gerichtet;
                                             z24 liegt nicht in der Klasse von kreis3 (zwei Klassen, keine einzelne)
```

Die vier Klassen zusammen:  48 + 24 + 8 + 8 = 88 (`gerichtet_length`).  **Günthers drei gedruckte Kreise** (`kreis1`, `kreis2` emendiert,
`kreis3`;  IGN S. 44 f.) **liegen in drei verschiedenen Klassen** — FOLGERUNG aus LK2, sie sind drei der vier Vertreter.  Die 24er-Klasse
enthält keinen von ihnen;  ihr Vertreter `z24` ist das fünfte Wort von `gerichtet`.

**Bauweise.**  `laeuterKlasse` ist eine Liste, keine `Finset` (Fallstrick 24);  die Eichungen per `decide +kernel` wie `familien_zahlen`.
Die Bahn-Sätze von Hand über `List.rotate_rotate`, `List.rotate_mod`, `List.rotate_length`, `List.map_rotate`;  `omega` nur auf atomaren
Zielen (Fallstrick 7).  Profile:  siehe die Wachen;  kein `Classical.choice`, kein `native_decide`, kein `sorry`, kein True-Feld.

## Grenze

Nur vier Werte (m = 3 Negatoren) für LK1–LK6 als Eichung;  über andere Wertzahlen sagen die Eichungen nichts (die Bahn-Sätze gelten für
jede).  Die Klassen sind **Wortklassen**.  Dass Platz- und Wert-Lesung dieselben Klassen geben (die Läuter tauschen Plätze, Günthers
Negatoren Werte;  die Stationen sind zueinander invers, die Vollkreise dieselben Wörter):  **GERECHNET**, nicht Satz
(`KorpusRev2/Meldung_Rev11_Plan3_Eichanker_Glocken_Impl.md` G2, G4).  Mit `dreh` dazu bleibt es bei vier Klassen (LK3);  ohne `umkehr`
wären es fünf (gerechnet, ebd.).

## QUELLE

Günthers Familien 10-9-5 / 5-9-10, 9-6-9, 6-12-6:  IGN S. 43, Tafel (18), am Bild (Hermeneutes);  `guentherFamilie1` und `vert` aus dem
Bestand (`GegenidentitaetProbe`, `NegationCycleThreeCycle`).

## ZUORDNUNG — ungeprüft im Sinn des Hauses

Dass diese vier Klassen die Klassen der Läuter sind (Holroyds Liste der 29 „essentially different" extents auf vier Glocken — von
10 792 extents, bis auf Kent/Oxford-Varianten —, Smiths „single-change" extents, Fund vom 21.10. in
`KorpusRev2/Fund_Wechsellaeuten_Plain_Changes_Vollkreis.md`):  Abschrift über WebFetch, **nicht am Bild**.  Die Gruppe ist bei Holroyd
(dort:  „Drehung, Umkehr, Spiegelbild", nach dem Fund);  hier Drehung und `umkehr` (LK3:  `dreh` gibt nichts dazu).  Welches der drei
Wörter des Funds welcher Operation des Bestands entspricht, ist nicht geprüft.

## NICHT

„Günther hat die Klassen der Läuter gekannt";  „counter-identity";  „die Familie IST die Läuterklasse" ohne „auf den Wörtern, unter Drehung
und Umkehr";  „bei m Werten" (geeicht ist m = 3);  die 6-12-6-Familie als eine Klasse (LK6).
-/

namespace Reformulation.Proemial.LaeuterKlassen

open Reformulation.Proemial.NegationCycle
open Reformulation.Proemial.GegenidentitaetProbe
open Reformulation.Proemial.AkkretivitaetsBruecke (rotate_full)
open Reformulation.Proemial.NegationCycleTable (gerichtet gerichtet_full)
open Reformulation.Proemial.NegationCycleThreeCycle (vert mem_gerichtet)

/-- **Die Klasse eines Wortes unter Drehung und Umkehr:**  jede Drehung des Wortes und ihre Umkehr (mit Wiederholungen) -/
def laeuterKlasse {m : ℕ} (w : List (Fin m)) : List (List (Fin m)) :=
  (List.range w.length).flatMap fun k => [w.rotate k, umkehr (w.rotate k)]

theorem mem_laeuterKlasse {m : ℕ} {w u : List (Fin m)} :
    u ∈ laeuterKlasse w ↔ ∃ k, k < w.length ∧ (u = w.rotate k ∨ u = umkehr (w.rotate k)) := by
  unfold laeuterKlasse
  rw [List.mem_flatMap]
  constructor
  · rintro ⟨k, hk, hu⟩
    refine ⟨k, List.mem_range.mp hk, ?_⟩
    rcases List.mem_cons.mp hu with h | h
    · exact Or.inl h
    · exact Or.inr (List.mem_singleton.mp h)
  · rintro ⟨k, hk, h | h⟩
    · exact ⟨k, List.mem_range.mpr hk, List.mem_cons.mpr (Or.inl h)⟩
    · exact ⟨k, List.mem_range.mpr hk, List.mem_cons.mpr (Or.inr (List.mem_singleton.mpr h))⟩

/-- **Umkehr und Drehung vertauschen.** -/
theorem umkehr_rotate {m : ℕ} (w : List (Fin m)) (k : ℕ) : umkehr (w.rotate k) = (umkehr w).rotate k := by
  unfold umkehr
  exact List.map_rotate _ _ _

/-- **Die Klasse ist abgeschlossen:**  was in der Klasse eines Gliedes liegt, liegt in der Klasse. -/
theorem laeuterKlasse_trans {m : ℕ} {z u v : List (Fin m)} (hu : u ∈ laeuterKlasse z)
    (hv : v ∈ laeuterKlasse u) : v ∈ laeuterKlasse z := by
  obtain ⟨k, hk, hk'⟩ := mem_laeuterKlasse.mp hu
  obtain ⟨j, -, hj'⟩ := mem_laeuterKlasse.mp hv
  have hpos : 0 < z.length := by omega
  refine mem_laeuterKlasse.mpr ⟨(k + j) % z.length, Nat.mod_lt _ hpos, ?_⟩
  rw [List.rotate_mod]
  rcases hk' with rfl | rfl <;> rcases hj' with rfl | rfl
  · exact Or.inl (List.rotate_rotate _ _ _)
  · exact Or.inr (by rw [List.rotate_rotate])
  · exact Or.inr ((umkehr_rotate (z.rotate k) j).symm.trans (by rw [List.rotate_rotate]))
  · exact Or.inl (by rw [← umkehr_rotate, umkehr_umkehr, List.rotate_rotate])

/-- **Die Klasse ist symmetrisch:**  liegt u in der Klasse von z, so z in der von u. -/
theorem laeuterKlasse_symm {m : ℕ} {z u : List (Fin m)} (hu : u ∈ laeuterKlasse z) :
    z ∈ laeuterKlasse u := by
  obtain ⟨k, hk, hk'⟩ := mem_laeuterKlasse.mp hu
  have hlen : u.length = z.length := by
    rcases hk' with rfl | rfl
    · exact List.length_rotate _ _
    · exact (List.length_map ..).trans (List.length_rotate _ _)
  have hpos : 0 < u.length := by omega
  have hkn : k + (z.length - k) = z.length := by omega
  refine mem_laeuterKlasse.mpr ⟨(z.length - k) % u.length, Nat.mod_lt _ hpos, ?_⟩
  rw [List.rotate_mod]
  rcases hk' with rfl | rfl
  · exact Or.inl (by rw [List.rotate_rotate, hkn, List.rotate_length])
  · exact Or.inr (by rw [← umkehr_rotate, umkehr_umkehr, List.rotate_rotate, hkn, List.rotate_length])

/-- **Die Klassen sind Bahnen:**  liegt u in der Klasse von z, so haben u und z dieselbe Klasse (Inklusion in beide Richtungen). -/
theorem laeuterKlasse_gleich {m : ℕ} {z u : List (Fin m)} (hu : u ∈ laeuterKlasse z) :
    laeuterKlasse u ⊆ laeuterKlasse z ∧ laeuterKlasse z ⊆ laeuterKlasse u :=
  ⟨fun _ hv => laeuterKlasse_trans hu hv, fun _ hv => laeuterKlasse_trans (laeuterKlasse_symm hu) hv⟩

/-- (LK1, allgemein) **Drehung und Umkehr erhalten Vollkreise:**  jedes Glied der Klasse eines Vollkreises ist ein Vollkreis. -/
theorem laeuterKlasse_full {m : ℕ} {w u : List (Fin m)} (h : IsFullCycle w) (hu : u ∈ laeuterKlasse w) :
    IsFullCycle u := by
  obtain ⟨k, -, rfl | rfl⟩ := mem_laeuterKlasse.mp hu
  · exact rotate_full h k
  · exact umkehr_full (rotate_full h k)

/-- (LK1) **Die Klassen bleiben in den 88.** -/
theorem klasse_in_gerichtet : ∀ w ∈ gerichtet, ∀ u ∈ laeuterKlasse w, u ∈ gerichtet :=
  fun w hw u hu => mem_gerichtet u (laeuterKlasse_full (gerichtet_full w hw) hu)

/-- Vertreter der 24er-Klasse:  das fünfte Wort von `gerichtet` (Verteilung 6-12-6;  keiner von Günthers gedruckten Kreisen). -/
def z24 : List (Fin 3) := [0, 1, 0, 1, 2, 1, 0, 1, 2, 1, 2, 1, 0, 1, 0, 1, 2, 1, 0, 1, 2, 1, 2, 1]

/-- Die vier Vertreter:  Günthers drei gedruckte Kreise (IGN S. 44 f., `kreis2` emendiert) und `z24`. -/
def vertreter : List (List (Fin 3)) := [kreis1, z24, kreis2, kreis3]

/-- (LK2) **Vier Klassen, 48 / 24 / 8 / 8:**  die Vertreter liegen in `gerichtet`, ihre Klassen haben 48, 24, 8 und 8 verschiedene
    Glieder, und jeder der 88 gerichteten Vollkreise liegt in genau einer von ihnen. -/
theorem vier_klassen :
    (∀ z ∈ vertreter, z ∈ gerichtet) ∧
    vertreter.map (fun z => (laeuterKlasse z).dedup.length) = [48, 24, 8, 8] ∧
    ∀ w ∈ gerichtet, (vertreter.filter fun z => decide (w ∈ laeuterKlasse z)).length = 1 := by
  decide +kernel

theorem gerichtet_in_vertreter : ∀ w ∈ gerichtet, ∃ z ∈ vertreter, w ∈ laeuterKlasse z := by
  decide +kernel

/-- (LK2, Bahnfassung) **Die Klasse jedes gerichteten Vollkreises ist die Klasse eines der vier Vertreter** (als Menge). -/
theorem jede_klasse_eine_der_vier : ∀ w ∈ gerichtet, ∃ z ∈ vertreter,
    laeuterKlasse w ⊆ laeuterKlasse z ∧ laeuterKlasse z ⊆ laeuterKlasse w := by
  intro w hw
  obtain ⟨z, hz, hwz⟩ := gerichtet_in_vertreter w hw
  exact ⟨z, hz, laeuterKlasse_gleich hwz⟩

/-- (LK3) **„Rückwärts" gibt keine neue Klasse:**  der Drehsinn jedes gerichteten Vollkreises liegt in seiner Klasse. -/
theorem dreh_in_klasse : ∀ w ∈ gerichtet, dreh w ∈ laeuterKlasse w := by
  decide +kernel

/-- (LK4) **Günthers erste Familie (10-9-5 / 5-9-10) ist genau die Klasse von `kreis1`**, auf den 88. -/
theorem familie1_klasse : ∀ w ∈ gerichtet, guentherFamilie1 w = true ↔ w ∈ laeuterKlasse kreis1 := by
  decide +kernel

/-- (LK5) **Die Familie 9-6-9 ist genau die Klasse von `kreis2`**, auf den 88. -/
theorem familie969_klasse : ∀ w ∈ gerichtet, vert w = (9, 6, 9) ↔ w ∈ laeuterKlasse kreis2 := by
  decide +kernel

/-- (LK6) **Die Familie 6-12-6 ist die Vereinigung zweier Klassen** (der von `z24` und der von `kreis3`), auf den 88;  `z24` liegt
    nicht in der Klasse von `kreis3`. -/
theorem familie6126_zwei_klassen :
    (∀ w ∈ gerichtet, vert w = (6, 12, 6) ↔ (w ∈ laeuterKlasse z24 ∨ w ∈ laeuterKlasse kreis3)) ∧
    z24 ∉ laeuterKlasse kreis3 := by
  decide +kernel

end Reformulation.Proemial.LaeuterKlassen

/-! ## Axiom-Wachen (gemessen, verbatim) -/

/-- info: 'Reformulation.Proemial.LaeuterKlassen.mem_laeuterKlasse' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.LaeuterKlassen.mem_laeuterKlasse

/-- info: 'Reformulation.Proemial.LaeuterKlassen.umkehr_rotate' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.LaeuterKlassen.umkehr_rotate

/-- info: 'Reformulation.Proemial.LaeuterKlassen.laeuterKlasse_trans' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.LaeuterKlassen.laeuterKlasse_trans

/-- info: 'Reformulation.Proemial.LaeuterKlassen.laeuterKlasse_symm' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.LaeuterKlassen.laeuterKlasse_symm

/-- info: 'Reformulation.Proemial.LaeuterKlassen.laeuterKlasse_gleich' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.LaeuterKlassen.laeuterKlasse_gleich

/-- info: 'Reformulation.Proemial.LaeuterKlassen.laeuterKlasse_full' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.LaeuterKlassen.laeuterKlasse_full

/-- info: 'Reformulation.Proemial.LaeuterKlassen.klasse_in_gerichtet' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.LaeuterKlassen.klasse_in_gerichtet

/-- info: 'Reformulation.Proemial.LaeuterKlassen.vier_klassen' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Proemial.LaeuterKlassen.vier_klassen

/-- info: 'Reformulation.Proemial.LaeuterKlassen.gerichtet_in_vertreter' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Proemial.LaeuterKlassen.gerichtet_in_vertreter

/-- info: 'Reformulation.Proemial.LaeuterKlassen.jede_klasse_eine_der_vier' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.LaeuterKlassen.jede_klasse_eine_der_vier

/-- info: 'Reformulation.Proemial.LaeuterKlassen.dreh_in_klasse' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Proemial.LaeuterKlassen.dreh_in_klasse

/-- info: 'Reformulation.Proemial.LaeuterKlassen.familie1_klasse' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Proemial.LaeuterKlassen.familie1_klasse

/-- info: 'Reformulation.Proemial.LaeuterKlassen.familie969_klasse' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Proemial.LaeuterKlassen.familie969_klasse

/-- info: 'Reformulation.Proemial.LaeuterKlassen.familie6126_zwei_klassen' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Proemial.LaeuterKlassen.familie6126_zwei_klassen
