import Reformulation.Proemial.GegenidentitaetProbe   -- umkehr, dreh, umkehr_eq_dreh_three; über ThreeCycle: valMap, sjt
import Mathlib.Data.List.Rotate                      -- List.rotate (Eichung E2)

/-!
# Proemial.SpurProbe — die Spur eines Werts unter Umkehr und Drehsinn

STANDALONE, NICHT im Aggregat; Target `Probes`. AxiomGate unberührt. Kleiner Zug „Spur" nach
`KorpusRev2/Prompt_Spur_Zug_track_umkehr_dreh.md` (Mathematiker, 21. Oktober 2026), auf Grundlage
von `KorpusRev2/Vorfrage_Designation_Gegenidentitaet_Speculum.md` §3 (G0–G2) und
`KorpusRev2/Replik_Mathematiker_Speculum_Designation.md` §2. Konsumiert `NegationCycle` (`track`,
`sw_rev_conj`, `tafelVI4`), `NegationCycleCatalog` (`valMap`, `endpoint_eq_map`) und
`GegenidentitaetProbe` (`umkehr`, `dreh`); ändert nichts davon.

## Was die Spur ist

`track w v` (NegationCycle, der Weg **eines** Werts durch die Stationen; `track_mediates`, L11-6)
ist die Folge der Werte, die `v` unter dem Wort `w` nacheinander annimmt. Die drei Sätze dieses
Moduls sagen, was Umkehr und Drehsinn mit ihr tun — für jede Wertzahl:

* (S1) `track_umkehr`: die Umkehr schickt die Spur von `v` auf die Spur von `rev v`,
  `track (umkehr w) (rev v) = (track w v).map rev`, für **jedes Wort**.
* (S2) `track_valMap`, `track_closes`: die Spur endet bei `valMap w v`; ein schließendes Wort
  führt jeden Wert zu sich zurück (Vollkreis nicht nötig).
* (S3) `track_reverse`, `track_dreh`: das rückwärts gelesene Wort läuft die Spur rückwärts,
  `track w.reverse (valMap w v) = (track w v).reverse` für jedes Wort; für ein schließendes
  Wort also `track (dreh w) v = (track w v).reverse`, derselbe Wert.

Speculum hatte G0 und G2 nur bei drei und vier Werten gerechnet; hier gelten sie für jedes `m`.

## Der Satz, der trägt

**Ein ausgezeichneter Randwert nimmt der Vierergruppe die Umkehr und lässt den Drehsinn.** Am
Paar (Wort, Wert): der Drehsinn lässt den Wert stehen (`spur_dreh_fest`), die Umkehr schickt `d`
auf `rev d` (`spur_umkehr_wandert`). Für `d ≠ rev d` bleibt also vom Paar nur der Drehsinn
übrig; für den mittleren Wert `d = rev d` (nur bei ungerader Wertzahl) bleibt alles. Die
Fixgruppe ist kein Lean-Begriff dieses Moduls, sie steht nur hier. In der Triade, wo
Umkehr und Drehsinn auf jedem Vollkreis dasselbe Wort liefern (`umkehr_eq_dreh_three`), trennt
das mitgeführte Datum sie wieder (`triade_spur_trennt`).

ZUORDNUNG (Speculum, 21. Oktober 2026): die Spur als das Datum neben dem Wort, an dem man
abliest, was ein ausgezeichneter Wert der Vierergruppe nimmt. Ausdrücklich **keine**
Gleichsetzung mit Lilles achtem Thema: die Operationen der Gegenidentität sind Involutionen und
können sich nicht erschöpfen (`no_exhaustion_in_periodic`); das sind zwei Figuren. Auf den
Negationskreisen zeichnet Günther eine **Station** aus — die als positiv gesetzte Wertfolge (IGN
S. 19: „das als positiv gesetzte p, also die Sequenz 1⋅2⋅3"; S. 52) —, keinen Wert; ein Wert, der
auf dem Kreis ausgezeichnet bleibt, ist bei ihm nicht belegt (Hermeneutes, 21. Oktober 2026: IGN,
*Als Wille*, Lille durchgesehen). Die Spur-Lesart ist eine Zuordnung des Hauses. Und die Auszeichnung ist
bei Günther eine Setzung, mit mehr Werten zurücknehmbar — IGN S. 3: „Es »gibt« also keinen ersten
Wert, der per se der erste und damit positiv wäre."

## Zwei Wege, die Triade zu trennen

Eine Auszeichnung trennt die Triade (`triade_spur_trennt`). Das ist der Weg, den Günther 1963 ging
— BdM 1963, S. 176 (*Das Bewusstsein der Maschinen*, 2. Aufl., PDF-S. 174): „Trotzdem kommt auch
in Tafel (VII) die reflexive Überordnung des „Ich" über das „Du" zum Ausdruck! Dies geschieht aber
nicht vermittels der Stellenwerte, die die einzelnen zweiwertigen Systeme relativ zueinander
besitzen, sondern durch die Reflexionsziffer, die dem „Ich"-System zugehört." — und 1977 verwarf:
IuG S. XXVIII (Vorwort zur zweiten Auflage): „Eine Umtauschrelation aber ist kein
Ordnungsverhältnis in dem das eine Glied je dem anderen übergeordnet werden kann." 1979 sucht er
die Unterscheidung von Ich und Du in mehr Werten: IGN S. 20, nach dem Satz „dann bleibt Ich und Du
in der Subjektivität nicht unterscheidbar": „Sie entsteht aus dem Fortschreiten zu höheren
Wertstufen und damit auch zu Kreisen mit wachsenden Zahlen von Negationsorten in zyklischer
Anordnung." Diesen Weg tragen `GegenidentitaetProbe` und `SpiegelfesteAnordnungen`:
`umkehr_eq_dreh_three` (drei Werte: eine Gegenoperation) gegen `umkehr_ne_dreh_all` (ab vier Werten
trennen sich Umkehr und Drehsinn ohne Auszeichnung).

*Marken:* die drei Zitate BESTÄTIGUNG — am Bild (Hermeneutes, 21. Oktober 2026) und hier an der
Textschicht gegengelesen, mit den Seitenzahlen des Drucks (BdM Fuß 176, IuG Fuß XXVIII, IGN Fuß
20). Die Zuordnung der zwei Wege zu den Sätzen ist ZUORDNUNG, eine Zusammenschau: kein Beleg, dass
Günther die Vierergruppe meinte.

## Quellen

G. Günther, „Als Wille verhält der Geist sich praktisch", im Text *Als Wille* (wie Rev10),
`KorpusRev1/gg_als_wille.pdf` (vordenker, Februar 2004); Textschicht am 21. Oktober geprüft.
Seiten = PDF-Seiten der Datei, wie in Rev10 (dort „S. 4"); Druck: Hegel-Jahrbuch 1977/78,
S. 55–59.

Der Satz von den zwei Willkürwahlen steht seit Rev9 im Haus (`docs/rev9/de.html`) und ist in
Rev10 Teil A gedruckt (Kapitel 3, Abschnitt „Der Bewegungsvorrat", „Als Wille, S. 4 der benutzten
Datei"; Entwurf `KorpusRev2/Entwurf_2026-10-09_Rev10_TeilA_Gestalt_de.md`); neu ist hier sein
Beweis — der Anfangspunkt als `rotate_full`, die Drehrichtung als `dreh` (Custos, 21. Oktober 2026).

* PDF 4: „Da in einer heterarchischen Kreisordnung jeder Anfang eine Willkürwahl darstellt (und,
  ist einmal ein Anfangspunkt gewählt, es keinen originären Grund gibt, zu entscheiden, ob der
  Kreis links- oder rechtsläufig durchlaufen werden soll), stoßen wir hier auf das logische Motiv
  der Kontingenz." Günthers zwei Willkürwahlen sind die zwei Freiheiten des Bestandes: der
  Anfangspunkt (`AkkretivitaetsBruecke.rotate_full`; Eichung E2 hier) und die Drehrichtung
  (`dreh`) — BESTÄTIGUNG der zwei Freiheiten; dass sie „Kontingenz" heißen, ZUORDNUNG.
* PDF 4: „Verzichten wir auf eine Rangordnung, dann schließen sich die Werte zu einem Kreis, indem
  die Letzten die Ersten und die Ersten die Letzten sein können." „Die Letzten die Ersten" ist die
  Umkehr; eine Rangordnung nimmt sie — ZUORDNUNG mit Rückhalt im Wort, zum Satz oben.

Wechselläuten (`KorpusRev2/Fund_Wechsellaeuten_Plain_Changes_Vollkreis.md`): „plain changes" auf
`n` Glocken ist der SJT-Kreis `sjt (n − 1)`. Auf vier Glocken ist dessen Umkehr eine Drehung
(Läuter sagen „double"), ab fünf nicht mehr; der Drehsinn ist auch auf fünf eine Drehung — Eichung
E2, keine Läuter-Zitate. Die „blue line" eines Läuters entspricht der Spur `track` (ZUORDNUNG).
Läuter tauschen Plätze, Günthers Negatoren Werte; die Reihe des Läuters ist die inverse
Permutation der Station.

## Stufen (CLAUDE.md §4)

| Satz | Stufe |
|---|---|
| `track_umkehr` (S1) | FOLGERUNG (Induktion über `sw_rev_conj`) |
| `track_valMap` (S2) | HEBUNG (`NegationCycle.track_last` mit `valMap` statt `foldl`) |
| `track_closes` (S2) | ZUSAMMENSTELLUNG (`track_valMap`, `endpoint_eq_map`, `map_eq_iff`) |
| `track_reverse` (S3) | FOLGERUNG |
| `track_dreh` (S3) | ZUSAMMENSTELLUNG (`track_reverse`, `valMap_of_closes`) |
| `spur_dreh_fest`, `spur_umkehr_wandert` (F1) | INSTANZIIERUNG (`track_dreh` am Vollkreis; `track_umkehr` an `rev d`) |
| `triade_spur_trennt` (E1), `sjt_vier_drehungen`, `sjt_fuenf_dreh` (E2) | EICHUNG |

Hilfssätze: `track_head`, `valMap_of_closes`, `valMap_append`, `valMap_reverse`,
`track_append`.

Kein `sorry`, kein `native_decide`, kein `: True`-Feld, kein `axiom`.
-/

namespace Reformulation.Proemial.SpurProbe

open Reformulation.Proemial.NegationCycle
open Reformulation.Proemial.GegenidentitaetProbe
open Reformulation.Proemial.NegationCycleCatalog (valMap endpoint_eq_map map_eq_iff origin_perm)
open Reformulation.Proemial.NegationCycleSJT (sjt)

-- ============================================================
-- §I — Die Umkehr schickt die Spur von v auf die Spur von rev v (S1)
-- ============================================================

/-- (S1) **Die Spur unter der Umkehr:** `track (umkehr w) (rev v) = (track w v).map rev`, für jedes
Wort und jede Wertzahl (über `sw_rev_conj`). -/
theorem track_umkehr {m : ℕ} : ∀ (w : List (Fin m)) (v : Fin (m + 1)),
    track (umkehr w) (Fin.rev v) = (track w v).map Fin.rev
  | [], _ => rfl
  | i :: is, v => by
    have hc : Fin.rev (sw i v) = sw (Fin.rev i) (Fin.rev v) := by
      have := sw_rev_conj i (Fin.rev v)
      rwa [Fin.rev_rev] at this
    show Fin.rev v :: track (umkehr is) (sw (Fin.rev i) (Fin.rev v)) =
      Fin.rev v :: (track is (sw i v)).map Fin.rev
    rw [← hc, track_umkehr is (sw i v)]

-- ============================================================
-- §II — Die Spur endet am Bild; ein schließendes Wort führt jeden Wert zurück (S2)
-- ============================================================

/-- Die Spur beginnt bei ihrem Wert. -/
theorem track_head {m : ℕ} : ∀ (w : List (Fin m)) (v : Fin (m + 1)),
    ∃ t, track w v = v :: t
  | [], _ => ⟨[], rfl⟩
  | i :: is, v => ⟨track is (sw i v), rfl⟩

/-- (S2) **Die Spur endet bei `valMap w v`.** -/
theorem track_valMap {m : ℕ} : ∀ (w : List (Fin m)) (v : Fin (m + 1)),
    (track w v).getLast? = some (valMap w v)
  | [], _ => rfl
  | i :: is, v => by
    obtain ⟨t, ht⟩ := track_head is (sw i v)
    show (v :: track is (sw i v)).getLast? = some (valMap is (sw i v))
    rw [← track_valMap is (sw i v), ht, List.getLast?_cons_cons]

/-- Ein schließendes Wort lässt jeden Wert fest: `valMap w = id`. -/
theorem valMap_of_closes {m : ℕ} {w : List (Fin m)} (hc : endpoint w (origin m) = origin m)
    (v : Fin (m + 1)) : valMap w v = v := by
  rw [endpoint_eq_map] at hc
  have hc' : (origin m).map (valMap w) = (origin m).map id := by rw [List.map_id]; exact hc
  exact (map_eq_iff origin_perm _ _).mp hc' v

/-- (S2) **Die Spur eines schließenden Worts kehrt zu ihrem Wert zurück** — jedes `m`, jedes
schließende Wort (Vollkreis nicht nötig). -/
theorem track_closes {m : ℕ} {w : List (Fin m)} (hc : endpoint w (origin m) = origin m)
    (v : Fin (m + 1)) : (track w v).getLast? = some v := by
  rw [track_valMap, valMap_of_closes hc]

-- ============================================================
-- §III — Der Drehsinn läuft dieselbe Spur rückwärts (S3)
-- ============================================================

theorem valMap_append {m : ℕ} : ∀ (a b : List (Fin m)) (v : Fin (m + 1)),
    valMap (a ++ b) v = valMap b (valMap a v)
  | [], _, _ => rfl
  | i :: is, b, v => valMap_append is b (sw i v)

/-- Das rückwärts gelesene Wort macht die Wertabbildung rückgängig. -/
theorem valMap_reverse {m : ℕ} : ∀ (w : List (Fin m)) (v : Fin (m + 1)),
    valMap w.reverse (valMap w v) = v
  | [], _ => rfl
  | i :: is, v => by
    rw [List.reverse_cons, valMap_append]
    show valMap [i] (valMap is.reverse (valMap is (sw i v))) = v
    rw [valMap_reverse is (sw i v)]
    exact sw_sw i v

/-- Die Spur einer Verkettung. -/
theorem track_append {m : ℕ} : ∀ (a b : List (Fin m)) (v : Fin (m + 1)),
    track (a ++ b) v = (track a v).dropLast ++ track b (valMap a v)
  | [], _, _ => rfl
  | i :: is, b, v => by
    obtain ⟨t, ht⟩ := track_head is (sw i v)
    show v :: track (is ++ b) (sw i v) = (v :: track is (sw i v)).dropLast ++ track b (valMap is (sw i v))
    rw [track_append is b (sw i v), ht]
    rfl

/-- (S3, allgemein) **Das rückwärts gelesene Wort läuft die Spur rückwärts:**
`track w.reverse (valMap w v) = (track w v).reverse`, für jedes Wort. -/
theorem track_reverse {m : ℕ} : ∀ (w : List (Fin m)) (v : Fin (m + 1)),
    track w.reverse (valMap w v) = (track w v).reverse
  | [], _ => rfl
  | i :: is, v => by
    obtain ⟨t, ht⟩ := track_head is (sw i v)
    have ih := track_reverse is (sw i v)
    rw [ht, List.reverse_cons] at ih
    rw [List.reverse_cons]
    show track (is.reverse ++ [i]) (valMap is (sw i v)) = (v :: track is (sw i v)).reverse
    rw [track_append, ih, valMap_reverse, ht, List.reverse_cons, List.reverse_cons,
      List.dropLast_concat]
    show t.reverse ++ [sw i v, sw i (sw i v)] = t.reverse ++ [sw i v] ++ [v]
    rw [sw_sw, List.append_assoc]
    rfl

/-- (S3) **Der Drehsinn eines schließenden Worts läuft dieselbe Spur rückwärts**, für jeden Wert. -/
theorem track_dreh {m : ℕ} {w : List (Fin m)} (hc : endpoint w (origin m) = origin m)
    (v : Fin (m + 1)) : track (dreh w) v = (track w v).reverse := by
  have := track_reverse w v
  rw [valMap_of_closes hc] at this
  exact this

-- ============================================================
-- §IV — Ein ausgezeichneter Wert: der Drehsinn bleibt, die Umkehr wandert (F1)
-- ============================================================

/-- (F1) **Der Drehsinn lässt den Wert `d` stehen:** auf einem Vollkreis ist die Spur von `d` unter
dem Drehsinn die Spur von `d`, rückwärts. -/
theorem spur_dreh_fest {m : ℕ} {w : List (Fin m)} (h : IsFullCycle w) (d : Fin (m + 1)) :
    track (dreh w) d = (track w d).reverse :=
  track_dreh h.closes d

/-- (F1) **Die Umkehr schickt `d` auf `rev d`:** die Spur von `d` unter der Umkehr ist die
umgekehrte Spur von `rev d`. -/
theorem spur_umkehr_wandert {m : ℕ} (w : List (Fin m)) (d : Fin (m + 1)) :
    track (umkehr w) d = (track w (Fin.rev d)).map Fin.rev := by
  have := track_umkehr w (Fin.rev d)
  rwa [Fin.rev_rev] at this

-- ============================================================
-- §V — Eichungen
-- ============================================================

/-- (E1) **In der Triade trennt ein ausgezeichneter Wert wieder, was die Triade zusammenlegt:** auf
Günthers Folge (4) ist die Umkehr der Drehsinn — aber die Umkehr schickt das Paar (Wort, 0) auf
(Wort, `rev 0`), der Drehsinn auf (Wort, 0), und die Spuren der mitgeführten Werte sind
verschieden. Die Ungleichung gilt schon, weil die beiden Spuren mit verschiedenen Werten beginnen
(`track_head`, `rev 0 ≠ 0`); sie eicht die Paar-Lesart an Günthers Folge (4), mehr nicht. Der
Inhalt steht in `spur_umkehr_wandert` / `spur_dreh_fest`. Weg von 1963 (siehe Kopf). -/
theorem triade_spur_trennt :
    umkehr tafelVI4 = dreh tafelVI4 ∧
      track (umkehr tafelVI4) (Fin.rev 0) ≠ track (dreh tafelVI4) 0 := by
  decide

/-- (E2) Vier Werte: der Drehsinn des SJT-Kreises ist dessen Drehung um 7, die Umkehr dessen
Drehung um 4. -/
theorem sjt_vier_drehungen : dreh (sjt 3) = (sjt 3).rotate 7 ∧ umkehr (sjt 3) = (sjt 3).rotate 4 := by
  decide +kernel

/-- (E2) Fünf Werte: der Drehsinn des SJT-Kreises ist dessen Drehung um 39. -/
theorem sjt_fuenf_dreh : dreh (sjt 4) = (sjt 4).rotate 39 := by
  decide +kernel

-- ============================================================
-- Wachen — Axiom-Profile
-- ============================================================

/-! **Wachen.** Ist-Ausgabe des grünen Builds (v4.30.0-rc2), alle 15 Deklarationen. Kein
`Classical.choice`. -/

/-- info: 'Reformulation.Proemial.SpurProbe.track_umkehr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms track_umkehr

/-- info: 'Reformulation.Proemial.SpurProbe.track_head' does not depend on any axioms -/
#guard_msgs in #print axioms track_head

/-- info: 'Reformulation.Proemial.SpurProbe.track_valMap' depends on axioms: [propext] -/
#guard_msgs in #print axioms track_valMap

/-- info: 'Reformulation.Proemial.SpurProbe.valMap_of_closes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms valMap_of_closes

/-- info: 'Reformulation.Proemial.SpurProbe.track_closes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms track_closes

/-- info: 'Reformulation.Proemial.SpurProbe.valMap_append' does not depend on any axioms -/
#guard_msgs in #print axioms valMap_append

/-- info: 'Reformulation.Proemial.SpurProbe.valMap_reverse' depends on axioms: [propext] -/
#guard_msgs in #print axioms valMap_reverse

/-- info: 'Reformulation.Proemial.SpurProbe.track_append' does not depend on any axioms -/
#guard_msgs in #print axioms track_append

/-- info: 'Reformulation.Proemial.SpurProbe.track_reverse' depends on axioms: [propext] -/
#guard_msgs in #print axioms track_reverse

/-- info: 'Reformulation.Proemial.SpurProbe.track_dreh' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms track_dreh

/-- info: 'Reformulation.Proemial.SpurProbe.spur_dreh_fest' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms spur_dreh_fest

/-- info: 'Reformulation.Proemial.SpurProbe.spur_umkehr_wandert' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms spur_umkehr_wandert

/-- info: 'Reformulation.Proemial.SpurProbe.triade_spur_trennt' depends on axioms: [propext] -/
#guard_msgs in #print axioms triade_spur_trennt

/-- info: 'Reformulation.Proemial.SpurProbe.sjt_vier_drehungen' does not depend on any axioms -/
#guard_msgs in #print axioms sjt_vier_drehungen

/-- info: 'Reformulation.Proemial.SpurProbe.sjt_fuenf_dreh' does not depend on any axioms -/
#guard_msgs in #print axioms sjt_fuenf_dreh
end Reformulation.Proemial.SpurProbe
