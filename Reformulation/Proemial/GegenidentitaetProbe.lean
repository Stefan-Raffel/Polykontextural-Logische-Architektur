import Reformulation.Proemial.NegationCycleThreeCycle   -- vert, mem_gerichtet; über Search/Table: gerichtet

/-!
# Proemial.GegenidentitaetProbe — Spiegel und Drehsinn: in der Triade eins, ab vier Werten überall zwei

STANDALONE, NICHT im Aggregat; Target `Probes`. AxiomGate unberührt. Sonde nach
`KorpusRev2/Sondierung_Gegenidentitaet_Spiegel_Drehsinn_Prompt.md` (Mathematiker, 20. Oktober
2026, auf Anordnung des Architekten). Konsumiert `NegationCycle` (`IsFullCycle`, `stations`,
`endpoint`, `origin`, `reverse_full`, `sw_rev_conj`, `endpoint_map_rev`,
`endpoint_reverse_values`, `origin_map_rev`, `triadic_unique'`), `NegationCycleTable`
(`gerichtet`) und `NegationCycleThreeCycle` (`vert`, `mem_gerichtet`); ändert keines davon.

## Die Quelle

IGN = G. Günther, „Identität, Gegenidentität und Negativsprache" (1979; vordenker-Edition März
2000), Textschicht `KorpusRev1/gunther_identitaet.pdf`, am 20. Oktober gegen die Zitate des
Prompts gehalten.

* S. 9: „dann entwickelt sich aus der primordialen Identität eine »Gegenidentität«. Und da die
  akkretive Kraft des Negierens unerschöpflich erscheint, erneuert sich die Gegenidentität immer
  wieder in Strukturformen höherer und höherer Akkretvität." (*Akkretvität* so in der Edition.)
* S. 16: mit der Triade „treten jetzt Gegenidentitäten gegenüber, und zwar ist es gleich im
  ersten System einer solcherart geschwächten Identität nicht nur ein Gegenbild des in sich
  ruhenden Einen, sondern zwei".
* S. 19 f.: die Folgen (4) und (5) unterscheiden sich dadurch, „dass wir den Kreis einmal im
  Uhrzeigersinn und einmal in der Gegenrichtung durchlaufen haben"; „dass diese Vertauschbarkeit
  von N 1 und N 2 nur innerhalb der heterarchischen Ordnung zulässig ist".
* S. 20: „Da die beiden zur Diskussion stehenden Negationsfolgen im Symmetrieverhältnis stehen,
  bilden Identität und Gegenidentität ein Umtauschverhältnis, in dem jede die Stelle der anderen
  einnehmen kann, ohne dass sich dabei ontisch etwas ändert. Sieht man in der Triade die höchste
  Strukturform des Denkens (wie Ch.S. Peirce das tut), dann bleibt Ich und Du in der
  Subjektivität nicht unterscheidbar." Und: mit dem „Fortschreiten zu höheren Wertstufen" werde
  „eine neue Frage akut".
* S. 43, Tafel (18): drei Familien, „10 oder 5 / 9 oder 9 / 5 oder 10", „9 / 6 / 9",
  „6 / 12 / 6" (spaltenweise gedruckt); „Wir haben dabei die Umkehrung der ersten Verteilung der
  Operatoren 10-9-5, also 5-9-10 zur gleichen Familie gerechnet."
* S. 57: „dass Ich und Du nur in einer Gegenidentität als konstruierbar verstanden werden
  können".

## Zwei Lesarten, die in der Triade zusammenfallen

Günthers Text legt bei drei Werten zwei Operationen auf einem Negationswort nahe, ohne sie zu
trennen: den **Drehsinn** `dreh` (dasselbe Wort rückwärts, S. 19: „in der Gegenrichtung") und
den **Spiegel** `spiegel` (die Umkehr der Werte, die `N_{i+1}` in `N_{m−i}` überführt,
`sw_rev_conj`; S. 19 f.: „Vertauschbarkeit von N 1 und N 2"). Der Bestand liest dieselbe Stelle
S. 19 f. schon einmal als Drehrichtung (`DirectionChoice`, Kopf (1)) — bei drei Werten ist das
kein Widerspruch, denn dort ist beides dasselbe:

* (GI2) `spiegel_eq_dreh_three` — für **jeden** dreiwertigen Vollkreis ist der Spiegel der
  Drehsinn. Bisher stand das als Gleichung der Tafelfolgen (`tafelVI5_eq_mirror`,
  `tafelVI5_eq_reverse`) und als Prosa in deren Dokstring.
* (GI3) `spiegel_ne_dreh_four`, `spiegel_ne_self_four`, `dreh_ne_self_four` — bei **vier**
  Werten fallen sie für keinen der Vollkreise zusammen; keiner ist spiegel- oder drehfest.
  `bahn_vier`: jeder Kreis hat drei verschiedene Partner. Günthers „neue Frage" (S. 20) als
  Satz: ab vier Werten bilden Spiegel und Drehsinn kein Umtauschverhältnis mehr, sondern mit
  ihrer Verkettung eine Vierheit.
* (GI1) `spiegel_full` — der Spiegel erhält den Vollkreis **für jede Wertzahl**. Für vier Werte
  stand das als `NegationCycleSymmetry.mirror_all`, über die entschiedene Tafel; dessen Kopf
  nennt die allgemeine Fassung „nicht gebaut". Für den Drehsinn steht es im Bestand
  (`reverse_full`).
* (GI4) `vert_spiegel`, `vert_dreh` — der Spiegel kehrt die Verteilung der Operatoren um,
  `(a, b, c) ↦ (c, b, a)`; der Drehsinn lässt sie stehen. Günthers „Umkehrung der ersten
  Verteilung" (S. 43) ist darum die des Spiegels, nicht die des Drehsinns.
  `NegationCycleSymmetry` (Kopf K3) sagte das als Prosa; hier ist es ein Satz.

## Stufen und Marken, je Satz am Beweis bestimmt (CLAUDE.md §4)

| Satz | Stufe | Quellenmarke |
|---|---|---|
| `spiegel_spiegel` | UMBENENNUNG (Beweisterm `map_rev_map_rev`) | — |
| `dreh_dreh`, `spiegel_dreh_comm` | UMBENENNUNG (`List.reverse_reverse`, `List.map_reverse`) | — |
| `spiegel_full` | FOLGERUNG (allgemeine Fassung von `mirror_all`) | — |
| `spiegel_eq_dreh_three` | ZUSAMMENSTELLUNG (`triadic_unique'` und zwei Rechnungen) | BESTÄTIGUNG (S. 20) |
| `spiegel_ne_dreh_four`, `…_self_four` (zwei) | ZUSAMMENSTELLUNG (`mem_gerichtet` und die Eichung), wie `no_888_all` | keine — Günther kündigt an, er behauptet nicht |
| `bahn_vier` | ZUSAMMENSTELLUNG (GI0, GI3, `reverse_full`) | — |
| `vert_spiegel` | FOLGERUNG (über `count_map_rev`) | BESTÄTIGUNG der Gruppierung (S. 43) |
| `vert_dreh` | ZUSAMMENSTELLUNG (`List.count_reverse`) | — |
| `gerichtet_getrennt`, `bahnen_zweiundzwanzig`, `familien_zahlen` | EICHUNG über die 88 | — |

Hilfssätze, gewacht wie alle Deklarationen: `map_rev_map_rev`, `negate_map_rev`,
`stations_map_rev`, `stations_reverse_values` (die zwei Gegenstücke zu `endpoint_map_rev` und
`endpoint_reverse_values` für `stations`), `stationSpiegel*`, `stations_spiegel`,
`count_map_rev`.

**Was die 22 nicht ist (§12 Regel 11).** Dass die 88 gerichteten Kreise in 22 Bahnen zerfallen,
erzwingt `bahn_vier`: jede Bahn hat vier Elemente, und `gerichtet` ist unter Spiegel und
Drehsinn abgeschlossen (`mirror_gerichtet`, `reverse_full`), also 88 = 22 · 4. Die Eichung
prüft die Rechnung, sie ist kein zusätzliches Indiz.

## ZUORDNUNG (nur hier, in keinem Satz)

Dass `spiegel` Günthers Gegenidentität **ist** und `dreh` sein Drehsinn, sagt kein Satz; ebenso
wenig, dass die Vierheit der Bahn Ich, Du und Objekt trägt. C&V S. 23 (gedruckte Seite, am
PDF geprüft): „the switch in the proemial relationship always involves not two relata but
four!" — die Nähe zur Vierheit von `bahn_vier` ist eine Zuordnung, kein Beleg. Bewiesen ist die
Arithmetik, an der Günther die Gegenidentität festmacht (S. 18–20), nicht die Gegenidentität als
Theorie der Subjektivität. Nichts hier ist die zweite Negation (L07-4 offen).

**Was die Sonde nicht baut.** Keinen Satz für mehr als vier Werte („nie Spiegel = Drehsinn"
für jedes m ≥ 3): gemessen ist nur m = 3; die Vermutung steht im Befund. Keine Deutung der 22
Bahnen. Keine Änderung an `DirectionChoice` oder `NegationCycleSymmetry`.

Kein `sorry`, kein `native_decide`, kein `: True`-Feld, kein `axiom`.
-/

namespace Reformulation.Proemial.GegenidentitaetProbe

open Reformulation.Proemial.NegationCycle
open Reformulation.Proemial.NegationCycleTable (gerichtet)
open Reformulation.Proemial.NegationCycleThreeCycle (vert mem_gerichtet)

-- ============================================================
-- §I — Spiegel und Drehsinn (GI0)
-- ============================================================

/-- Der **Spiegel** eines Negationsworts: die Umkehr der Werte, auf die Negatorindizes
übertragen (`N_{i+1} ↦ N_{m−i}`, `sw_rev_conj`). -/
def spiegel {m : ℕ} (w : List (Fin m)) : List (Fin m) := w.map Fin.rev

/-- Der **Drehsinn**: dasselbe Wort rückwärts gelesen. -/
def dreh {m : ℕ} (w : List (Fin m)) : List (Fin m) := w.reverse

/-- Die Umkehr der Werte, zweimal auf eine Liste angewandt, ist die Identität. -/
theorem map_rev_map_rev {n : ℕ} : ∀ l : List (Fin n), (l.map Fin.rev).map Fin.rev = l
  | [] => rfl
  | a :: as => by rw [List.map_cons, List.map_cons, Fin.rev_rev, map_rev_map_rev as]

/-- (GI0) Der Spiegel ist eine Involution. -/
theorem spiegel_spiegel {m : ℕ} (w : List (Fin m)) : spiegel (spiegel w) = w :=
  map_rev_map_rev w

/-- (GI0) Der Drehsinn ist eine Involution. -/
theorem dreh_dreh {m : ℕ} (w : List (Fin m)) : dreh (dreh w) = w :=
  List.reverse_reverse w

/-- (GI0) Spiegel und Drehsinn vertauschen. -/
theorem spiegel_dreh_comm {m : ℕ} (w : List (Fin m)) : spiegel (dreh w) = dreh (spiegel w) :=
  List.map_reverse ..

-- ============================================================
-- §II — Der Spiegel erhält den Vollkreis, für jede Wertzahl (GI1)
-- ============================================================

/-- Der gespiegelte Negator, eingefasst in die Umkehr der Werte, ist der Negator. -/
theorem negate_map_rev {m : ℕ} (i : Fin m) (l : List (Fin (m + 1))) :
    (negate (Fin.rev i) l).map Fin.rev = negate i (l.map Fin.rev) := by
  unfold negate
  rw [List.map_map, List.map_map]
  congr 1
  funext v
  show Fin.rev (sw (Fin.rev i) v) = sw i (Fin.rev v)
  rw [← sw_rev_conj, Fin.rev_rev]

/-- Die Stationen des gespiegelten Worts sind die gespiegelten Stationen des Worts, vom
gespiegelten Ausgang aus (Gegenstück zu `endpoint_map_rev` für `stations`). -/
theorem stations_map_rev {m : ℕ} :
    ∀ (w : List (Fin m)) (l : List (Fin (m + 1))),
      stations (w.map Fin.rev) l = (stations w (l.map Fin.rev)).map (List.map Fin.rev)
  | [], _ => rfl
  | i :: is, l => by
    show l :: stations (is.map Fin.rev) (negate (Fin.rev i) l) =
      ((l.map Fin.rev) :: stations is (negate i (l.map Fin.rev))).map (List.map Fin.rev)
    rw [stations_map_rev is, negate_map_rev, List.map_cons, map_rev_map_rev l]

/-- Von der umgekehrten Wertfolge aus durchläuft ein Wort die umgekehrten Stationen
(Gegenstück zu `endpoint_reverse_values` für `stations`). -/
theorem stations_reverse_values {m : ℕ} :
    ∀ (w : List (Fin m)) (l : List (Fin (m + 1))),
      stations w l.reverse = (stations w l).map List.reverse
  | [], _ => rfl
  | i :: is, l => by
    show l.reverse :: stations is (negate i l.reverse) =
      (l :: stations is (negate i l)).map List.reverse
    rw [show negate i l.reverse = (negate i l).reverse from List.map_reverse ..,
      stations_reverse_values is, List.map_cons]

/-- Die Abbildung, die der Spiegel auf den Stationen erzeugt: umkehren, dann Werte umkehren. -/
def stationSpiegel {m : ℕ} (l : List (Fin (m + 1))) : List (Fin (m + 1)) :=
  l.reverse.map Fin.rev

theorem stationSpiegel_stationSpiegel {m : ℕ} (l : List (Fin (m + 1))) :
    stationSpiegel (stationSpiegel l) = l := by
  unfold stationSpiegel
  rw [List.map_reverse, map_rev_map_rev, List.reverse_reverse]

theorem stationSpiegel_perm {m : ℕ} {l : List (Fin (m + 1))} (h : l.Perm (origin m)) :
    (stationSpiegel l).Perm (origin m) := by
  unfold stationSpiegel
  have h1 : (l.reverse.map Fin.rev).Perm ((origin m).map Fin.rev) :=
    ((List.reverse_perm l).trans h).map Fin.rev
  rw [origin_map_rev] at h1
  exact h1.trans (List.reverse_perm _)

theorem stations_spiegel {m : ℕ} (w : List (Fin m)) :
    stations (spiegel w) (origin m) = (stations w (origin m)).map stationSpiegel := by
  unfold spiegel
  rw [stations_map_rev, origin_map_rev, stations_reverse_values, List.map_map]
  rfl

/-- (GI1) **Der Spiegel eines Vollkreises ist ein Vollkreis — für jede Wertzahl.** Allgemeine
Fassung von `NegationCycleSymmetry.mirror_all` (dort vier Werte, über die Tafel). -/
theorem spiegel_full {m : ℕ} {w : List (Fin m)} (h : IsFullCycle w) :
    IsFullCycle (spiegel w) := by
  have hinj : Function.Injective (stationSpiegel (m := m)) :=
    Function.LeftInverse.injective stationSpiegel_stationSpiegel
  refine ⟨?_, ?_, ?_, ?_⟩
  · show endpoint (w.map Fin.rev) (origin m) = origin m
    rw [endpoint_map_rev, origin_map_rev, endpoint_reverse_values, h.closes, List.map_reverse,
      origin_map_rev, List.reverse_reverse]
  · rw [stations_spiegel]
    exact h.nodup.map hinj
  · intro l hl
    rw [stations_spiegel] at hl
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hl
    exact List.mem_permutations'.mpr
      (stationSpiegel_perm (List.mem_permutations'.mp (h.only_arrangements s hs)))
  · intro l hl
    rw [stations_spiegel]
    have hs := h.all_arrangements _
      (List.mem_permutations'.mpr (stationSpiegel_perm (List.mem_permutations'.mp hl)))
    exact List.mem_map.mpr ⟨_, hs, stationSpiegel_stationSpiegel l⟩

-- ============================================================
-- §III — Drei Werte: Spiegel = Drehsinn (GI2)
-- ============================================================

/-- (GI2) **Drei Werte: für jeden Vollkreis ist der Spiegel der Drehsinn.** Aus
`triadic_unique'` (es gibt nur die Tafelfolgen (4) und (5)); die zwei Fälle per `decide`, dieselbe
Rechnung wie `tafelVI5_eq_mirror` und `tafelVI5_eq_reverse`. -/
theorem spiegel_eq_dreh_three (w : List (Fin 2)) (h : IsFullCycle w) : spiegel w = dreh w := by
  rcases triadic_unique' w h with rfl | rfl <;> decide

-- ============================================================
-- §IV — Vier Werte: nirgends (GI3)
-- ============================================================

/-- Eichung über die 88 gerichteten Vollkreise: Spiegel ≠ Drehsinn, nicht spiegelfest, nicht
drehfest. -/
theorem gerichtet_getrennt : ∀ s ∈ gerichtet, spiegel s ≠ dreh s ∧ spiegel s ≠ s ∧ dreh s ≠ s := by
  decide +kernel

/-- (GI3) **Vier Werte: für keinen Vollkreis ist der Spiegel der Drehsinn.** -/
theorem spiegel_ne_dreh_four (w : List (Fin 3)) (h : IsFullCycle w) : spiegel w ≠ dreh w :=
  (gerichtet_getrennt w (mem_gerichtet w h)).1

/-- (GI3) Kein vierwertiger Vollkreis ist spiegelfest. -/
theorem spiegel_ne_self_four (w : List (Fin 3)) (h : IsFullCycle w) : spiegel w ≠ w :=
  (gerichtet_getrennt w (mem_gerichtet w h)).2.1

/-- (GI3) Kein vierwertiger Vollkreis ist drehfest. -/
theorem dreh_ne_self_four (w : List (Fin 3)) (h : IsFullCycle w) : dreh w ≠ w :=
  (gerichtet_getrennt w (mem_gerichtet w h)).2.2

/-- **Jeder vierwertige Vollkreis hat drei verschiedene Partner:** die Bahn unter Spiegel und
Drehsinn hat vier Elemente. Zusammengestellt aus GI0 und GI3, ohne neue Aufzählung. -/
theorem bahn_vier (w : List (Fin 3)) (h : IsFullCycle w) :
    [w, spiegel w, dreh w, spiegel (dreh w)].Nodup := by
  have e1 : w ≠ spiegel w := (spiegel_ne_self_four w h).symm
  have e2 : w ≠ dreh w := (dreh_ne_self_four w h).symm
  have e3 : w ≠ spiegel (dreh w) := fun e =>
    spiegel_ne_dreh_four w h ((congrArg spiegel e).trans (spiegel_spiegel _))
  have e4 : spiegel w ≠ dreh w := spiegel_ne_dreh_four w h
  have e5 : spiegel w ≠ spiegel (dreh w) := fun e =>
    dreh_ne_self_four w h (by rw [← spiegel_spiegel (dreh w), ← e, spiegel_spiegel])
  have e6 : dreh w ≠ spiegel (dreh w) := (spiegel_ne_self_four (dreh w) (reverse_full h)).symm
  refine List.nodup_cons.mpr ⟨?_, List.nodup_cons.mpr ⟨?_, List.nodup_cons.mpr ⟨?_,
    List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩⟩⟩⟩
  · intro hm
    rcases List.mem_cons.mp hm with hm | hm
    · exact e1 hm
    rcases List.mem_cons.mp hm with hm | hm
    · exact e2 hm
    exact e3 (List.mem_singleton.mp hm)
  · intro hm
    rcases List.mem_cons.mp hm with hm | hm
    · exact e4 hm
    exact e5 (List.mem_singleton.mp hm)
  · intro hm
    exact e6 (List.mem_singleton.mp hm)

/-- Der Vertreter einer Bahn: unter `w`, `spiegel w`, `dreh w`, `spiegel (dreh w)` der mit
der kleinsten Stelle in `gerichtet`. -/
def bahnKanon (w : List (Fin 3)) : List (Fin 3) :=
  [spiegel w, dreh w, spiegel (dreh w)].foldl
    (fun a b => if gerichtet.idxOf b < gerichtet.idxOf a then b else a) w

/-- Eichung: die 88 gerichteten Vollkreise zerfallen in 22 Bahnen. -/
theorem bahnen_zweiundzwanzig : (gerichtet.map bahnKanon).dedup.length = 22 := by
  decide +kernel

-- ============================================================
-- §V — Spiegel, Drehsinn und Günthers Familien (GI4)
-- ============================================================

/-- Die Umkehr der Werte vertauscht die Häufigkeiten: `a` im Spiegel so oft wie `rev a` im
Wort. -/
theorem count_map_rev {n : ℕ} (a : Fin n) :
    ∀ w : List (Fin n), (w.map Fin.rev).count a = w.count (Fin.rev a)
  | [] => rfl
  | x :: xs => by
    have hx : (Fin.rev x == a) = (x == Fin.rev a) := by
      rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]
      constructor
      · rintro rfl; rw [Fin.rev_rev]
      · rintro rfl; rw [Fin.rev_rev]
    rw [List.map_cons, List.count_cons, List.count_cons, count_map_rev a xs, hx]

/-- (GI4) **Der Spiegel kehrt die Verteilung der Operatoren um:** `(a, b, c) ↦ (c, b, a)`, für
jedes Wort über drei Negatoren. -/
theorem vert_spiegel (w : List (Fin 3)) :
    vert (spiegel w) = ((vert w).2.2, (vert w).2.1, (vert w).1) := by
  unfold vert spiegel
  rw [count_map_rev, count_map_rev, count_map_rev]
  rfl

/-- (GI4) **Der Drehsinn lässt die Verteilung stehen.** Darum kann Günthers Paarung
10-9-5 / 5-9-10 nicht vom Drehsinn kommen. -/
theorem vert_dreh (w : List (Fin 3)) : vert (dreh w) = vert w := by
  unfold vert dreh
  rw [List.count_reverse, List.count_reverse, List.count_reverse]

/-- Eichung: die vier Verteilungen unter den 88 gerichteten Vollkreisen, 24 · 24 · 32 · 8. -/
theorem familien_zahlen :
    (gerichtet.filter (fun s => vert s == (5, 9, 10))).length = 24 ∧
    (gerichtet.filter (fun s => vert s == (10, 9, 5))).length = 24 ∧
    (gerichtet.filter (fun s => vert s == (6, 12, 6))).length = 32 ∧
    (gerichtet.filter (fun s => vert s == (9, 6, 9))).length = 8 := by
  decide +kernel


-- ============================================================
-- Wachen — Axiom-Profile
-- ============================================================

/-! **Wachen.** Ist-Ausgabe des grünen Builds (v4.30.0-rc2), alle 26 Deklarationen. Kein
`Classical.choice`: Listenrechnung mit `rw`, ohne offenes `simp`; `decide +kernel` nur über
konkrete Listen (`gerichtet`). -/

/-- info: 'Reformulation.Proemial.GegenidentitaetProbe.spiegel' does not depend on any axioms -/
#guard_msgs in #print axioms spiegel

/-- info: 'Reformulation.Proemial.GegenidentitaetProbe.dreh' does not depend on any axioms -/
#guard_msgs in #print axioms dreh

/-- info: 'Reformulation.Proemial.GegenidentitaetProbe.map_rev_map_rev' depends on axioms: [propext] -/
#guard_msgs in #print axioms map_rev_map_rev

/-- info: 'Reformulation.Proemial.GegenidentitaetProbe.spiegel_spiegel' depends on axioms: [propext] -/
#guard_msgs in #print axioms spiegel_spiegel

/-- info: 'Reformulation.Proemial.GegenidentitaetProbe.dreh_dreh' depends on axioms: [propext] -/
#guard_msgs in #print axioms dreh_dreh

/-- info: 'Reformulation.Proemial.GegenidentitaetProbe.spiegel_dreh_comm' depends on axioms: [propext] -/
#guard_msgs in #print axioms spiegel_dreh_comm

/-- info: 'Reformulation.Proemial.GegenidentitaetProbe.negate_map_rev' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms negate_map_rev

/-- info: 'Reformulation.Proemial.GegenidentitaetProbe.stations_map_rev' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms stations_map_rev

/-- info: 'Reformulation.Proemial.GegenidentitaetProbe.stations_reverse_values' depends on axioms: [propext] -/
#guard_msgs in #print axioms stations_reverse_values

/-- info: 'Reformulation.Proemial.GegenidentitaetProbe.stationSpiegel' does not depend on any axioms -/
#guard_msgs in #print axioms stationSpiegel

/-- info: 'Reformulation.Proemial.GegenidentitaetProbe.stationSpiegel_stationSpiegel' depends on axioms: [propext] -/
#guard_msgs in #print axioms stationSpiegel_stationSpiegel

/-- info: 'Reformulation.Proemial.GegenidentitaetProbe.stationSpiegel_perm' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms stationSpiegel_perm

/-- info: 'Reformulation.Proemial.GegenidentitaetProbe.stations_spiegel' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms stations_spiegel

/-- info: 'Reformulation.Proemial.GegenidentitaetProbe.spiegel_full' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms spiegel_full

/-- info: 'Reformulation.Proemial.GegenidentitaetProbe.spiegel_eq_dreh_three' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms spiegel_eq_dreh_three

/-- info: 'Reformulation.Proemial.GegenidentitaetProbe.gerichtet_getrennt' depends on axioms: [propext] -/
#guard_msgs in #print axioms gerichtet_getrennt

/-- info: 'Reformulation.Proemial.GegenidentitaetProbe.spiegel_ne_dreh_four' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms spiegel_ne_dreh_four

/-- info: 'Reformulation.Proemial.GegenidentitaetProbe.spiegel_ne_self_four' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms spiegel_ne_self_four

/-- info: 'Reformulation.Proemial.GegenidentitaetProbe.dreh_ne_self_four' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms dreh_ne_self_four

/-- info: 'Reformulation.Proemial.GegenidentitaetProbe.bahn_vier' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms bahn_vier

/-- info: 'Reformulation.Proemial.GegenidentitaetProbe.bahnKanon' depends on axioms: [propext] -/
#guard_msgs in #print axioms bahnKanon

/-- info: 'Reformulation.Proemial.GegenidentitaetProbe.bahnen_zweiundzwanzig' depends on axioms: [propext] -/
#guard_msgs in #print axioms bahnen_zweiundzwanzig

/-- info: 'Reformulation.Proemial.GegenidentitaetProbe.count_map_rev' depends on axioms: [propext] -/
#guard_msgs in #print axioms count_map_rev

/-- info: 'Reformulation.Proemial.GegenidentitaetProbe.vert_spiegel' depends on axioms: [propext] -/
#guard_msgs in #print axioms vert_spiegel

/-- info: 'Reformulation.Proemial.GegenidentitaetProbe.vert_dreh' depends on axioms: [propext] -/
#guard_msgs in #print axioms vert_dreh

/-- info: 'Reformulation.Proemial.GegenidentitaetProbe.familien_zahlen' depends on axioms: [propext] -/
#guard_msgs in #print axioms familien_zahlen
end Reformulation.Proemial.GegenidentitaetProbe
