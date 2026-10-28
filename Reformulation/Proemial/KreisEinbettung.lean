import Reformulation.Proemial.AkkretivitaetsBruecke   -- phi, phi_sjt;  über NegationCycleSJT:  sjt, sjt3_full

/-!
# Proemial.KreisEinbettung — die Einbettung eines Negationskreises in einen Wert mehr:  der Kreis bleibt, die Vollständigkeit nicht

STANDALONE, NICHT im Aggregat;  Target `Probes`.  AxiomGate unberührt.  Sonde nach `KorpusRev2/Prompt_Instanz_Sonde_KR_Konstitutiv_Regulativ.md`
(Mathematiker, 28.10.2026 17:38;  Architekt 17:35).  Herkunft:  `KorpusRev2/Notiz_Konstitutiv_Regulativ_formal_Impl.md` §3–§5.  Konsumiert
`NegationCycle` (`IsKreis`, `IsFullCycle`, `sw`, `sw_val`, `negate`, `stations`, `endpoint`, `origin`), `NegationCycleSJT` (`sjt`,
`sjt3_full`), `AkkretivitaetsBruecke` (`phi`, `phi_sjt`);  ändert nichts davon.

**Name (Regel 9):**  `einbett` ist im Bestand besetzt (`Pfalzgraf/FaserungT.lean`:  Einbettung von Formeln) — darum `einbettWort`.
**Abgrenzung:**  Das ist NICHT die Wert-Einbettung von Kapitel 6 (`SPar.castSucc_negFin_ne`);  hier werden die
NEGATORINDIZES eingebettet (`Fin.castSucc`), der neue, größte Wert kommt hinzu und wird nie bewegt.

## WAS

```text
einbettWort w := w.map Fin.castSucc          hebe l := l.map Fin.castSucc ++ [Fin.last (m + 1)]   (eine Anordnung, um den neuen Wert verlängert)

KR1   kreis_einbett            SATZ, jede Wertzahl   IsKreis w → IsKreis (einbettWort w):  der Kreis bleibt ein Kreis
KR2   einbett_nie_voll         SATZ, jede Wertzahl   ¬ IsFullCycle (einbettWort w) — für JEDES Wort, nicht nur für Vollkreise:  die
                                                     Anordnung mit dem neuen Wert vorn wird nie erreicht.  Choice-frei über diese eine
                                                     Anordnung, nicht über full_length (das Classical.choice trägt)
      voll_einbett_nicht_voll  SATZ                  die Form des Auftrags:  IsFullCycle w → ¬ IsFullCycle (einbettWort w)
KR2′  voll_einbett_kreis       FOLGERUNG             IsFullCycle w → 3 ≤ w.length → Kreis und nicht Vollkreis.  Die Längenvoraussetzung ist
                                                     NÖTIG:  bei zwei Werten ist der Vollkreis [0, 0] (Hin und Zurück), und IsKreis schließt
                                                     ihn aus (nontriv);  ab drei Werten gilt sie (Länge (m+1)!, full_length — mit Choice,
                                                     darum hier als Voraussetzung)
KR3   partiell_vier            EICHUNG               [0, 2, 0, 2] (N₁, N₃ im Wechsel) ist auf vier Werten ein Kreis, kein Vollkreis
KR4   zwei_schritte            EICHUNG               an sjt 2:  die Einbettung ist Kreis, nicht Vollkreis;  Φ hebt zum Vollkreis sjt 3
KR5   einbett_laenge           SATZ                  die Einbettung ändert die Länge nicht
```

In Worten:  **Bettet man einen Kreis in einen Wert mehr ein, bleibt er ein Kreis;  ein Vollkreis hört dabei auf, ein Vollkreis zu sein.
Φ stellt die Vollständigkeit auf der nächsten Stufe neu her (`phi_full`, AkkretivitaetsBruecke).**

Hilfssätze:  `sw_castSucc`, `sw_last`, `negate_hebe`, `stations_hebe` (die Stationen der Einbettung sind die gehobenen Stationen),
`endpoint_hebe`, `origin_hebe`, `map_castSucc_inj`, `hebe_inj`, `nodup_map_hebe`, `kreis_of_voll`.

**Profile:**  alle 17 Sätze ohne `Classical.choice` — `[propext]`, `[propext, Quot.sound]` oder axiomfrei (Wachen unten).  Kein
`native_decide`, kein `sorry`, kein True-Feld.

## QUELLE

IGN S. 57 (Rev10 C.8, am Bild, zwei Hände):  die Hamiltonschen Vollkreise „regulativ" von vier Werten an;  „logisch konstitutiv – mithin
technisch wiederholbar – nur partielle Zyklen";  im Triadischen der Unterschied „noch nicht" (Bestand:  `kreis_iff_voll`).
IGN S. 56 (TEXTSCHICHT, Bild ausstehend):  „regulative Prinzipien";  „Grade der Konstruierbarkeit".

## LESART — der Instanz, als solche

„konstitutiv = beim Hinzunehmen eines Wertes erhalten;  regulativ = an die Totalität einer Stufe gebunden" (Notiz der Instanz §3).  Die
Sonde gibt ein Modell, in dem diese Lesart aufgeht (KR1, KR2);  sie beweist Günthers Kette „konstitutiv ⇒ wiederholbar" NICHT.

## GRENZE

Die Einbettung lässt den neuen Wert am Ende und bewegt ihn nie — EINE Einbettung unter mehreren.  Für Rev11 nur der SATZ, nicht die Lesart.

## NICHT

„konstitutiv heißt formal …" als Günthers Definition;  der Kant-Bezug (KrV ungeprüft);  Pseudokreise = partielle Zyklen (NegationCycle
K-R7);  „Φ ist die Wiederholbarkeit" (Anspruchsliste H, J7);  die Einbettung als „die reichere Struktur" (Günther nennt keine).
-/

namespace Reformulation.Proemial.KreisEinbettung

open Reformulation.Proemial.NegationCycle
open Reformulation.Proemial.NegationCycleSJT (sjt sjt3_full)
open Reformulation.Proemial.AkkretivitaetsBruecke (phi phi_sjt)

/-- **Die Einbettung eines Worts:**  dieselben Negatoren, ein Wert mehr;  der neue Wert (der größte) wird nie bewegt. -/
def einbettWort {m : ℕ} (w : List (Fin m)) : List (Fin (m + 1)) := w.map Fin.castSucc

/-- Eine Anordnung, um den neuen Wert am Ende verlängert. -/
def hebe {m : ℕ} (l : List (Fin (m + 1))) : List (Fin (m + 2)) := l.map Fin.castSucc ++ [Fin.last (m + 1)]

theorem sw_castSucc {m : ℕ} (i : Fin m) (v : Fin (m + 1)) : sw i.castSucc v.castSucc = (sw i v).castSucc := by
  apply Fin.ext
  rw [sw_val, Fin.val_castSucc, Fin.val_castSucc, Fin.val_castSucc, sw_val]

theorem sw_last {m : ℕ} (i : Fin m) : sw i.castSucc (Fin.last (m + 1)) = Fin.last (m + 1) := by
  apply Fin.ext
  have hi := i.isLt
  rw [sw_val, Fin.val_castSucc, Fin.val_last, if_neg (by omega), if_neg (by omega)]

theorem negate_hebe {m : ℕ} (i : Fin m) (l : List (Fin (m + 1))) : negate i.castSucc (hebe l) = hebe (negate i l) := by
  unfold negate hebe
  rw [List.map_append, List.map_map, List.map_map, List.map_cons, List.map_nil, sw_last]
  congr 1
  exact List.map_congr_left (fun v _ => sw_castSucc i v)

theorem stations_hebe {m : ℕ} : ∀ (w : List (Fin m)) (l : List (Fin (m + 1))),
    stations (einbettWort w) (hebe l) = (stations w l).map hebe
  | [], _ => rfl
  | i :: is, l => by
    show hebe l :: stations (einbettWort is) (negate i.castSucc (hebe l)) = hebe l :: (stations is (negate i l)).map hebe
    rw [negate_hebe, stations_hebe is]

theorem endpoint_hebe {m : ℕ} : ∀ (w : List (Fin m)) (l : List (Fin (m + 1))),
    endpoint (einbettWort w) (hebe l) = hebe (endpoint w l)
  | [], _ => rfl
  | i :: is, l => by
    show endpoint (einbettWort is) (negate i.castSucc (hebe l)) = hebe (endpoint is (negate i l))
    rw [negate_hebe, endpoint_hebe is]

theorem origin_hebe (m : ℕ) : origin (m + 1) = hebe (origin m) := by
  unfold origin hebe
  exact List.finRange_succ_last

theorem map_castSucc_inj {m : ℕ} : ∀ {l₁ l₂ : List (Fin (m + 1))}, l₁.map Fin.castSucc = l₂.map Fin.castSucc → l₁ = l₂
  | [], [], _ => rfl
  | [], _ :: _, h => absurd h (List.cons_ne_nil _ _).symm
  | _ :: _, [], h => absurd h (List.cons_ne_nil _ _)
  | a :: as, b :: bs, h => by
    rw [List.map_cons, List.map_cons] at h
    obtain ⟨h1, h2⟩ := List.cons.inj h
    rw [Fin.castSucc_inj.mp h1, map_castSucc_inj h2]

theorem hebe_inj {m : ℕ} {l₁ l₂ : List (Fin (m + 1))} (h : hebe l₁ = hebe l₂) : l₁ = l₂ :=
  map_castSucc_inj (List.append_cancel_right h)

theorem nodup_map_hebe {m : ℕ} : ∀ {L : List (List (Fin (m + 1)))}, L.Nodup → (L.map hebe).Nodup
  | [], _ => List.nodup_nil
  | l :: ls, h => by
    rw [List.map_cons]
    have h' := List.nodup_cons.mp h
    refine List.nodup_cons.mpr ⟨fun hm => ?_, nodup_map_hebe h'.2⟩
    obtain ⟨t, ht, e⟩ := List.mem_map.mp hm
    exact h'.1 (hebe_inj e ▸ ht)

/-- (KR1) **Ein Kreis bleibt ein Kreis, wenn man ihn in einen Wert mehr einbettet** — für jede Wertzahl. -/
theorem kreis_einbett {m : ℕ} {w : List (Fin m)} (h : IsKreis w) : IsKreis (einbettWort w) where
  closes := by rw [origin_hebe, endpoint_hebe, h.closes]
  nodup := by rw [origin_hebe, stations_hebe]; exact nodup_map_hebe h.nodup
  nontriv := by unfold einbettWort; rw [List.length_map]; exact h.nontriv

/-- (KR2) **Die Einbettung ist nie ein Vollkreis** — für jedes Wort und jede Wertzahl:  die Anordnung, die den neuen Wert vorn hat, wird
    nie erreicht, weil der neue Wert nie bewegt wird. -/
theorem einbett_nie_voll {m : ℕ} (w : List (Fin m)) : ¬ IsFullCycle (einbettWort w) := by
  intro h
  have hl : origin m = (List.finRange m).map Fin.castSucc ++ [Fin.last m] := List.finRange_succ_last
  let c : List (Fin (m + 2)) := Fin.last (m + 1) :: (origin m).map Fin.castSucc
  have hc : c ∈ (origin (m + 1)).permutations' := by
    rw [List.mem_permutations', origin_hebe]
    exact (List.perm_append_singleton _ _).symm
  have hs := h.all_arrangements c hc
  rw [origin_hebe, stations_hebe] at hs
  obtain ⟨t, _, e⟩ := List.mem_map.mp hs
  have e1 : (hebe t).getLast? = some (Fin.last (m + 1)) := List.getLast?_concat
  have e2 : c.getLast? = some (Fin.castSucc (Fin.last m)) := by
    show (Fin.last (m + 1) :: (origin m).map Fin.castSucc).getLast? = _
    rw [hl, List.map_append, List.map_cons, List.map_nil, ← List.cons_append, List.getLast?_concat]
  rw [e, e2] at e1
  have := congrArg Fin.val (Option.some.inj e1)
  rw [Fin.val_castSucc, Fin.val_last, Fin.val_last] at this
  omega

/-- (KR2, in der Form des Auftrags) **Ein Vollkreis hört bei der Einbettung auf, ein Vollkreis zu sein.** -/
theorem voll_einbett_nicht_voll {m : ℕ} {w : List (Fin m)} (_ : IsFullCycle w) : ¬ IsFullCycle (einbettWort w) :=
  einbett_nie_voll w

/-- Ein Vollkreis mit mindestens drei Negatoren ist ein Kreis.  (Bei zwei Werten ist der Vollkreis `[0, 0]` — Hin und Zurück — und
    darum KEIN Kreis:  `IsKreis` schließt das blosse Hin und Zurück aus.) -/
theorem kreis_of_voll {m : ℕ} {w : List (Fin m)} (h : IsFullCycle w) (hl : 3 ≤ w.length) : IsKreis w :=
  ⟨h.closes, h.nodup, hl⟩

/-- (KR2′) **Die Einbettung eines Vollkreises ist ein Kreis** (bei mindestens drei Negatoren) — aber kein Vollkreis (KR2). -/
theorem voll_einbett_kreis {m : ℕ} {w : List (Fin m)} (h : IsFullCycle w) (hl : 3 ≤ w.length) :
    IsKreis (einbettWort w) ∧ ¬ IsFullCycle (einbettWort w) :=
  ⟨kreis_einbett (kreis_of_voll h hl), einbett_nie_voll w⟩

/-- (KR5) **Die Einbettung ändert die Länge nicht.** -/
theorem einbett_laenge {m : ℕ} (w : List (Fin m)) : (einbettWort w).length = w.length := List.length_map ..

/-- (KR3) **Ein partieller Kreis auf vier Werten:**  N₁ und N₃ im Wechsel. -/
theorem partiell_vier : IsKreis ([0, 2, 0, 2] : List (Fin 3)) ∧ ¬ IsFullCycle ([0, 2, 0, 2] : List (Fin 3)) := by
  decide

/-- (KR4) **Die zwei Schritte an demselben Wort:**  die Einbettung des dreiwertigen Vollkreises `sjt 2` ist ein Kreis, aber kein
    Vollkreis;  Φ hebt ihn zum Vollkreis `sjt 3`. -/
theorem zwei_schritte :
    IsKreis (einbettWort (sjt 2)) ∧ ¬ IsFullCycle (einbettWort (sjt 2)) ∧ phi true (sjt 2) = sjt 3 ∧ IsFullCycle (phi true (sjt 2)) := by
  refine ⟨by decide, einbett_nie_voll _, phi_sjt 1, ?_⟩
  rw [phi_sjt 1]
  exact sjt3_full

end Reformulation.Proemial.KreisEinbettung

/-! ## Axiom-Wachen (gemessen, verbatim) -/

/-- info: 'Reformulation.Proemial.KreisEinbettung.sw_castSucc' does not depend on any axioms -/
#guard_msgs in #print axioms Reformulation.Proemial.KreisEinbettung.sw_castSucc

/-- info: 'Reformulation.Proemial.KreisEinbettung.sw_last' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.KreisEinbettung.sw_last

/-- info: 'Reformulation.Proemial.KreisEinbettung.negate_hebe' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.KreisEinbettung.negate_hebe

/-- info: 'Reformulation.Proemial.KreisEinbettung.stations_hebe' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.KreisEinbettung.stations_hebe

/-- info: 'Reformulation.Proemial.KreisEinbettung.endpoint_hebe' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.KreisEinbettung.endpoint_hebe

/-- info: 'Reformulation.Proemial.KreisEinbettung.origin_hebe' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.KreisEinbettung.origin_hebe

/-- info: 'Reformulation.Proemial.KreisEinbettung.map_castSucc_inj' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Proemial.KreisEinbettung.map_castSucc_inj

/-- info: 'Reformulation.Proemial.KreisEinbettung.hebe_inj' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.KreisEinbettung.hebe_inj

/-- info: 'Reformulation.Proemial.KreisEinbettung.nodup_map_hebe' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.KreisEinbettung.nodup_map_hebe

/-- info: 'Reformulation.Proemial.KreisEinbettung.kreis_einbett' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.KreisEinbettung.kreis_einbett

/-- info: 'Reformulation.Proemial.KreisEinbettung.einbett_nie_voll' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.KreisEinbettung.einbett_nie_voll

/-- info: 'Reformulation.Proemial.KreisEinbettung.voll_einbett_nicht_voll' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.KreisEinbettung.voll_einbett_nicht_voll

/-- info: 'Reformulation.Proemial.KreisEinbettung.kreis_of_voll' does not depend on any axioms -/
#guard_msgs in #print axioms Reformulation.Proemial.KreisEinbettung.kreis_of_voll

/-- info: 'Reformulation.Proemial.KreisEinbettung.voll_einbett_kreis' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.KreisEinbettung.voll_einbett_kreis

/-- info: 'Reformulation.Proemial.KreisEinbettung.einbett_laenge' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Proemial.KreisEinbettung.einbett_laenge

/-- info: 'Reformulation.Proemial.KreisEinbettung.partiell_vier' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Proemial.KreisEinbettung.partiell_vier

/-- info: 'Reformulation.Proemial.KreisEinbettung.zwei_schritte' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.KreisEinbettung.zwei_schritte
