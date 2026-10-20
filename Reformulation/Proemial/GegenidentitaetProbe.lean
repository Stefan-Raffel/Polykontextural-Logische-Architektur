import Reformulation.Proemial.NegationCycleThreeCycle   -- vert, mem_gerichtet; über Search/Table: gerichtet

/-!
# Proemial.GegenidentitaetProbe — Umkehr und Drehsinn: in der Triade eins, ab vier Werten überall zwei

STANDALONE, NICHT im Aggregat; Target `Probes`. AxiomGate unberührt. Sonde nach
`KorpusRev2/Sondierung_Gegenidentitaet_Spiegel_Drehsinn_Prompt.md` (Mathematiker, 20. Oktober
2026, auf Anordnung des Architekten). Konsumiert `NegationCycle` (`IsFullCycle`, `stations`,
`endpoint`, `origin`, `reverse_full`, `sw_rev_conj`, `endpoint_map_rev`,
`endpoint_reverse_values`, `origin_map_rev`, `triadic_unique'`), `NegationCycleTable`
(`gerichtet`) und `NegationCycleThreeCycle` (`vert`, `mem_gerichtet`); ändert keines davon.

## Der Name `umkehr` (umbenannt am 20. Oktober 2026, Entscheidung des Architekten „A-eng")

`umkehr w := w.map Fin.rev` ist der **Spiegel des Stammes** (`NegationCycle` Teil 5,
`endpoint_map_rev`; `NegationCycleSymmetry.mirror_all`; `NegationCycleLength.kuerzeste_spiegel`) —
dieselbe Operation, hier unter Günthers Wort: „Umkehrung" (IGN S. 43: die „Umkehrung der ersten
Verteilung der Operatoren 10-9-5, also 5-9-10"; S. 52: „die Abzählrichtung … in ihr Gegenteil zu
verkehren", „die Umkehrung der Viererfolge"). Der Name „Spiegel" wird hier gemieden, weil
„Spiegelbild" bei Günther die **klassische** Negation ist (S. 6, 14, 29), die „originalgetreue
Abbildung des Urbilds", gegen die S. 9 die Gegenidentität absetzt (Hermeneutes, Horistes, 20.
Oktober 2026). Zwei Namen für eine Operation im Bestand — benannt, nicht versteckt. Bis zu dieser
Umbenennung hieß sie hier `spiegel`, die Sätze `spiegel_*`.

## Wo Quelle und Bau sich ohne Lücke treffen: IGN S. 43

Günther rechnet 5-9-10 und 10-9-5 zu **einer** Familie und gibt als Grund ein Wort:
„Umkehrung". Im Bestand ist das die **Umkehr**, nicht der Drehsinn: `vert_umkehr` dreht das
Tripel der Operatorhäufigkeiten, `vert_dreh` lässt es stehen. Das Prädikat „in Familie 5-9-10"
trennt die Bahn (`familie_5_9_10_subjektiv`), Günthers Familie „10-9-5 oder 5-9-10" trennt sie
nicht (`guentherFamilie1_umkehr`, `guentherFamilie1_dreh`). Hier braucht es keine Brücke über zwei
Schriften und keinen fremden Ableitungsschritt (Horistes §6); diese Zeile steht darum über den
Zuordnungen unten.

## Die Quelle

IGN = G. Günther, „Identität, Gegenidentität und Negativsprache" (1979; vordenker-Edition März
2000), Textschicht `KorpusRev1/gunther_identitaet.pdf`, am 20. Oktober gegen die Zitate des
Prompts gehalten.

* S. 9: „dann entwickelt sich aus der primordialen Identität eine »Gegenidentität«. Und da die
  akkretive Kraft des Negierens unerschöpflich erscheint, erneuert sich die Gegenidentität immer
  wieder in Strukturformen höherer und höherer Akkretvität." (*Akkretvität* so in der Edition.)
* S. 16: mit der Triade „treten jetzt Gegenidentitäten gegenüber, und zwar ist es gleich im
  ersten System einer solcherart geschwächten Identität nicht nur ein Gegenbild des in sich
  ruhenden Einen, sondern zwei". *Nur Umfeld:* eine Gleichsetzung „zwei Gegenbilder = Umkehr =
  Drehsinn" trägt nicht — S. 16 zählt drei Einzelidentitäten, die Gruppe bei drei Werten hat zwei
  Elemente (Hermeneutes G4, Horistes §4, 20. Oktober 2026).
* S. 19 f.: die Folgen (4) und (5) unterscheiden sich dadurch, „dass wir den Kreis einmal im
  Uhrzeigersinn und einmal in der Gegenrichtung durchlaufen haben"; „dass diese Vertauschbarkeit
  von N 1 und N 2 nur innerhalb der heterarchischen Ordnung zulässig ist".
* S. 20: „Da die beiden zur Diskussion stehenden Negationsfolgen im Symmetrieverhältnis stehen,
  bilden Identität und Gegenidentität ein Umtauschverhältnis, in dem jede die Stelle der anderen
  einnehmen kann, ohne dass sich dabei ontisch etwas ändert. Sieht man in der Triade die höchste
  Strukturform des Denkens (wie Ch.S. Peirce das tut), dann bleibt Ich und Du in der
  Subjektivität nicht unterscheidbar." Und: mit dem „Fortschreiten zu höheren Wertstufen" werde
  „eine neue Frage akut".
* S. 37 (am Seitenbild, Hermeneutes): „Lassen wir die beiden Negationen derart alternieren, dass
  wir mit der sogenannten zweiten Negation, die jetzt die erste ist, beginnen, so ergibt als
  einzig relevante Änderung, dass durch den Wechsel von N₁ und N₂ ein Vertausch der Drehrichtung
  im Kreis bewirkt wird." („so ergibt als" — „sich" fehlt, so gesetzt.) Der Wechsel N₁ ↔ N₂ ist
  bei drei Werten die Umkehr, der „Vertausch der Drehrichtung" der Drehsinn: Günther sagt
  `umkehr_eq_dreh_three` selbst (BESTÄTIGUNG).
* S. 43, Tafel (18): drei Familien, „10 oder 5 / 9 oder 9 / 5 oder 10", „9 / 6 / 9",
  „6 / 12 / 6" (spaltenweise gedruckt); „Wir haben dabei die Umkehrung der ersten Verteilung der
  Operatoren 10-9-5, also 5-9-10 zur gleichen Familie gerechnet."
* S. 57: „dass Ich und Du nur in einer Gegenidentität als konstruierbar verstanden werden
  können".

## Zwei Lesarten, die in der Triade zusammenfallen

Günthers Text legt bei drei Werten zwei Operationen auf einem Negationswort nahe, ohne sie zu
trennen: den **Drehsinn** `dreh` (dasselbe Wort rückwärts, S. 19: „in der Gegenrichtung") und
die **Umkehr** `umkehr` (die Umkehr der Werte, die `N_{i+1}` in `N_{m−i}` überführt,
`sw_rev_conj`; S. 19 f.: „Vertauschbarkeit von N 1 und N 2"; S. 37: „Wechsel von N₁ und N₂"). Der
Bestand liest dieselbe Stelle
S. 19 f. schon einmal als Drehrichtung (`DirectionChoice`, Kopf (1)) — bei drei Werten ist das
kein Widerspruch, denn dort ist beides dasselbe:

* (GI2) `umkehr_eq_dreh_three` — für **jeden** dreiwertigen Vollkreis ist die Umkehr der
  Drehsinn. Bisher stand das als Gleichung der Tafelfolgen (`tafelVI5_eq_mirror`,
  `tafelVI5_eq_reverse`) und als Prosa in deren Dokstring.
* (GI3) `umkehr_ne_dreh_four`, `umkehr_ne_self_four`, `dreh_ne_self_four` — bei **vier**
  Werten fallen sie für keinen der Vollkreise zusammen; keiner ist umkehr- oder drehfest.
  `bahn_vier`: jeder Kreis hat drei verschiedene Partner. Günthers „neue Frage" (S. 20) als
  Satz: ab vier Werten bilden Umkehr und Drehsinn kein Umtauschverhältnis mehr, sondern mit
  ihrer Verkettung eine Vierheit.
* (GI1) `umkehr_full` — die Umkehr erhält den Vollkreis **für jede Wertzahl**. Für vier Werte
  stand das als `NegationCycleSymmetry.mirror_all`, über die entschiedene Tafel; dessen Kopf
  nennt die allgemeine Fassung „nicht gebaut". Für den Drehsinn steht es im Bestand
  (`reverse_full`).
* (GI4) `vert_umkehr`, `vert_dreh` — die Umkehr kehrt die Verteilung der Operatoren um,
  `(a, b, c) ↦ (c, b, a)`; der Drehsinn lässt sie stehen. Günthers „Umkehrung der ersten
  Verteilung" (S. 43) ist darum die der Umkehr, nicht die des Drehsinns.
  `NegationCycleSymmetry` (Kopf K3) sagte das als Prosa; hier ist es ein Satz.

## Stufen und Marken, je Satz am Beweis bestimmt (CLAUDE.md §4)

| Satz | Stufe | Quellenmarke |
|---|---|---|
| `umkehr_umkehr` | UMBENENNUNG (Beweisterm `map_rev_map_rev`) | — |
| `dreh_dreh`, `umkehr_dreh_comm` | UMBENENNUNG (`List.reverse_reverse`, `List.map_reverse`) | — |
| `umkehr_full` | FOLGERUNG (allgemeine Fassung von `mirror_all`) | — |
| `umkehr_eq_dreh_three` | ZUSAMMENSTELLUNG (`triadic_unique'` und zwei Rechnungen) | BESTÄTIGUNG (S. 37; S. 20) |
| `umkehr_ne_dreh_four`, `…_self_four` (zwei) | ZUSAMMENSTELLUNG (`mem_gerichtet` und die Eichung), wie `no_888_all` | keine — Günther kündigt an, er behauptet nicht |
| `bahn_vier` | ZUSAMMENSTELLUNG (GI0, GI3, `reverse_full`) | — |
| `vert_umkehr` | FOLGERUNG (über `count_map_rev`) | BESTÄTIGUNG der Gruppierung (S. 43) |
| `vert_dreh` | ZUSAMMENSTELLUNG (`List.count_reverse`) | — |
| `gerichtet_getrennt`, `bahnen_zweiundzwanzig`, `familien_zahlen` | EICHUNG über die 88 | — |
| §VI `bahn_ununterscheidbar` | ZUSAMMENSTELLUNG (aus den zwei Voraussetzungen; der Gehalt ist die Form) | — |
| §VI `bahn_drei_umkehr_genuegt` | ZUSAMMENSTELLUNG (`umkehr_eq_dreh_three`) | — |
| §VI `tafelVI_ununterscheidbar'` | UMBENENNUNG (Beweisterm `tafelVI_ununterscheidbar`) | — |
| §VI `hasFar_umkehr`, `altN2_umkehr` | FOLGERUNG (jedes Wort) | — |
| §VI `hasFar_dreh`, `altN2_dreh` | ZUSAMMENSTELLUNG (`mem_gerichtet` und die Eichung) | — |
| §VI `guentherFamilie1_umkehr`, `…_dreh`, `vert_umkehr_symm` | ZUSAMMENSTELLUNG (`vert_umkehr`, `vert_dreh`) | BESTÄTIGUNG der Gruppierung (S. 43) |
| §VI `gerichtet_dreh_praedikate`, `familie_5_9_10_subjektiv` | EICHUNG über die 88 | — |

Hilfssätze, gewacht wie alle Deklarationen: `map_rev_map_rev`, `negate_map_rev`,
`stations_map_rev`, `stations_reverse_values` (die zwei Gegenstücke zu `endpoint_map_rev` und
`endpoint_reverse_values` für `stations`), `stationUmkehr*`, `stations_umkehr`,
`count_map_rev`; in §VI `far_rev`, `getD_rev_eq_one`.

**Was die 22 nicht ist (§12 Regel 11).** Dass die 88 gerichteten Kreise in 22 Bahnen zerfallen,
erzwingt `bahn_vier`: jede Bahn hat vier Elemente, und `gerichtet` ist unter Umkehr und
Drehsinn abgeschlossen (`mirror_gerichtet`, `reverse_full`), also 88 = 22 · 4. Die Eichung
prüft die Rechnung, sie ist kein zusätzliches Indiz.

## §VI — die Bahn und die Prädikate, die sie nicht trennen (Folgezug, 20. Oktober 2026)

Nach `KorpusRev2/Prompt_Folgezug_Bahn_Ununterscheidbarkeit.md` (Mathematiker, auf Anordnung des
Architekten). `bahn_ununterscheidbar`: ein Prädikat, das Umkehr und Drehsinn respektiert, ist auf
der ganzen Bahn konstant, für jede Wertzahl. Bei drei Werten genügt die Umkehr allein
(`bahn_drei_umkehr_genuegt`); darum kam `NegationCycle.tafelVI_ununterscheidbar` mit der Umkehr
aus. Der alte Satz ist **keine** Instanz des neuen — dieser verlangt zusätzlich den Drehsinn für
jedes Wort —, sondern dessen dreiwertiger Grenzfall; `tafelVI_ununterscheidbar'` sagt ihn nur in
der Sprache dieser Datei.

Die Prädikate des Bestandes auf vier Werten, eingeordnet:
* `hasFar` („ein entfernter Schritt", die Klasse „überall K" ist ihr Gegenteil) und `altN2`
  („`N2` an jeder zweiten Stelle") respektieren beide — die Umkehr für jedes Wort, den
  Drehsinn für jeden Vollkreis (der Drehsinn gilt dem Sinn nach für jedes Wort, weil `hasFar`
  zyklisch liest; bewiesen ist nur die Vollkreis-Fassung).
* `vert` respektiert den Drehsinn (`vert_dreh`), nicht die Umkehr: „in Familie 5-9-10" trennt
  die Bahn (`familie_5_9_10_subjektiv`).
* Günthers Familie „10 oder 5 / 9 / 5 oder 10" (S. 43, Tafel (18)) als Klasse
  (`guentherFamilie1`) respektiert beide; die zwei anderen Familien sind als Verteilung
  umkehrfest (`vert_umkehr_symm`). Günthers Zusammenfassung von 5-9-10 und 10-9-5 zu **einer**
  Familie ist genau der Übergang von einem Prädikat, das die Bahn trennt, zu einem, das auf ihr
  konstant ist. Günther sagt das nicht; er tut es (BESTÄTIGUNG seiner Gruppierung; der Grund ist
  ZUORDNUNG).

**ZUORDNUNG zu §VI.** Grundzüge (Grz) S. 46, Kapitel „Hegels Philosophie und traditionelle
Logik", am Bild (`KorpusRev1/gg_Grundzuege_46-47.pdf`, Scan des Architekten, 20. Oktober 2026):
„Auf dem Boden der traditionellen Logik trennt sich die Geltung eines Begriffes für alle unter ihn
fallenden Objekte (interobjektive Allgemeingültigkeit) scharf von der Geltung des Begriffes für
alle ihn denkenden Subjekte (intersubjektive Allgemeinheit, resp. Gewißheit)." Günthers Paar ist
interobjektive **Allgemeingültigkeit** / intersubjektive **Allgemeinheit**; ebenso Grz S. 134 f.
und Kap. 5 (Hermeneutes). Fund-Notiz:
`KorpusRev2/Fund_Intersubjektiv_Transsubjektiv_Grz_IuG51.md`.

IuG S. 51 (gedruckte Seite; Edition PDF-S. 73, am Bild): „dass »Subjektivität-überhaupt«, d.h.
jene Sphäre, in der intersubjektive Allgemeinheit konstituiert ist, in Wahrheit trans-subjektiv
ist" (Bindestrich in der Edition; der Druck schreibt „transsubjektiv", Foto des Architekten).
Gelesen (Horistes, übernommen): die **Sphäre** sind die Vollkreise mit der Wirkung der
Vierergruppe; darin **konstituiert** sind die Bahn und die bahn-invarianten Prädikate — die
intersubjektive Allgemeinheit. Ein Prädikat, das Umkehr und Drehsinn respektiert, heißt hier
intersubjektiv allgemein, weil es keine Position der Bahn von der anderen trennt. Das
„weder subjektiv noch objektiv" / „sowohl subjektiv als auch objektiv" der Seite geht auf die
Sphäre, nicht auf die Bahn; die frühere Zeile „Bahn = transsubjektiv" ist gefallen (eine Bahn ist
eine Klasse von Kreisen, keine dritte Gattung). **Vorbehalt:** zwischen den Kreisen von IGN und
der Subjektivität von IuG gibt es in keinem Text eine Brücke; die Zuordnung ist Zusammenschau
zweier Schriften. Kein Term „Subjekt".

## ZUORDNUNG (nur hier, in keinem Satz)

Dass `umkehr` Günthers Gegenidentität **ist** und `dreh` sein Drehsinn, sagt kein Satz; `umkehr`
hat Rückhalt in der Sache (S. 37, 43, 46, 52 f.), nicht im Wort „Gegenidentität"; ebenso
wenig, dass die Vierheit der Bahn Ich, Du und Objekt trägt. C&V S. 23 (gedruckte Seite, am
PDF geprüft): „the switch in the proemial relationship always involves not two relata but
four!" — die Nähe zur Vierheit von `bahn_vier` ist eine Zuordnung, kein Beleg. Bewiesen ist die
Arithmetik, an der Günther die Gegenidentität festmacht (S. 18–20), nicht die Gegenidentität als
Theorie der Subjektivität. Nichts hier ist die zweite Negation (L07-4 offen).

**Was die Sonde nicht baut.** Keinen Satz für mehr als vier Werte („nie Umkehr = Drehsinn"
für jedes m ≥ 3): gemessen ist nur m = 3; die Vermutung steht im Befund. Keine Deutung der 22
Bahnen. Keine Änderung an `DirectionChoice` oder `NegationCycleSymmetry`.

Kein `sorry`, kein `native_decide`, kein `: True`-Feld, kein `axiom`.
-/

namespace Reformulation.Proemial.GegenidentitaetProbe

open Reformulation.Proemial.NegationCycle
open Reformulation.Proemial.NegationCycleTable (gerichtet)
open Reformulation.Proemial.NegationCycleThreeCycle (vert mem_gerichtet far hasFar altN2)

-- ============================================================
-- §I — Umkehr und Drehsinn (GI0)
-- ============================================================

/-- Die **Umkehr** eines Negationsworts: die Umkehr der Werte, auf die Negatorindizes
übertragen (`N_{i+1} ↦ N_{m−i}`, `sw_rev_conj`). -/
def umkehr {m : ℕ} (w : List (Fin m)) : List (Fin m) := w.map Fin.rev

/-- Der **Drehsinn**: dasselbe Wort rückwärts gelesen. -/
def dreh {m : ℕ} (w : List (Fin m)) : List (Fin m) := w.reverse

/-- Die Umkehr der Werte, zweimal auf eine Liste angewandt, ist die Identität. -/
theorem map_rev_map_rev {n : ℕ} : ∀ l : List (Fin n), (l.map Fin.rev).map Fin.rev = l
  | [] => rfl
  | a :: as => by rw [List.map_cons, List.map_cons, Fin.rev_rev, map_rev_map_rev as]

/-- (GI0) Die Umkehr ist eine Involution. -/
theorem umkehr_umkehr {m : ℕ} (w : List (Fin m)) : umkehr (umkehr w) = w :=
  map_rev_map_rev w

/-- (GI0) Der Drehsinn ist eine Involution. -/
theorem dreh_dreh {m : ℕ} (w : List (Fin m)) : dreh (dreh w) = w :=
  List.reverse_reverse w

/-- (GI0) Umkehr und Drehsinn vertauschen. -/
theorem umkehr_dreh_comm {m : ℕ} (w : List (Fin m)) : umkehr (dreh w) = dreh (umkehr w) :=
  List.map_reverse ..

-- ============================================================
-- §II — Die Umkehr erhält den Vollkreis, für jede Wertzahl (GI1)
-- ============================================================

/-- Der umgekehrte Negator, eingefasst in die Umkehr der Werte, ist der Negator. -/
theorem negate_map_rev {m : ℕ} (i : Fin m) (l : List (Fin (m + 1))) :
    (negate (Fin.rev i) l).map Fin.rev = negate i (l.map Fin.rev) := by
  unfold negate
  rw [List.map_map, List.map_map]
  congr 1
  funext v
  show Fin.rev (sw (Fin.rev i) v) = sw i (Fin.rev v)
  rw [← sw_rev_conj, Fin.rev_rev]

/-- Die Stationen von `w.map Fin.rev` sind die Stationen von `w` unter `Fin.rev`, vom Ausgang
unter `Fin.rev` aus (Gegenstück zu `endpoint_map_rev` für `stations`). -/
theorem stations_map_rev {m : ℕ} :
    ∀ (w : List (Fin m)) (l : List (Fin (m + 1))),
      stations (w.map Fin.rev) l = (stations w (l.map Fin.rev)).map (List.map Fin.rev)
  | [], _ => rfl
  | i :: is, l => by
    show l :: stations (is.map Fin.rev) (negate (Fin.rev i) l) =
      ((l.map Fin.rev) :: stations is (negate i (l.map Fin.rev))).map (List.map Fin.rev)
    rw [stations_map_rev is, negate_map_rev, List.map_cons, map_rev_map_rev l]

/-- Von der rückwärts gelesenen Wertfolge aus durchläuft ein Wort die rückwärts gelesenen Stationen
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

/-- Die Abbildung, die die Umkehr auf den Stationen erzeugt: umkehren, dann Werte umkehren. -/
def stationUmkehr {m : ℕ} (l : List (Fin (m + 1))) : List (Fin (m + 1)) :=
  l.reverse.map Fin.rev

theorem stationUmkehr_stationUmkehr {m : ℕ} (l : List (Fin (m + 1))) :
    stationUmkehr (stationUmkehr l) = l := by
  unfold stationUmkehr
  rw [List.map_reverse, map_rev_map_rev, List.reverse_reverse]

theorem stationUmkehr_perm {m : ℕ} {l : List (Fin (m + 1))} (h : l.Perm (origin m)) :
    (stationUmkehr l).Perm (origin m) := by
  unfold stationUmkehr
  have h1 : (l.reverse.map Fin.rev).Perm ((origin m).map Fin.rev) :=
    ((List.reverse_perm l).trans h).map Fin.rev
  rw [origin_map_rev] at h1
  exact h1.trans (List.reverse_perm _)

theorem stations_umkehr {m : ℕ} (w : List (Fin m)) :
    stations (umkehr w) (origin m) = (stations w (origin m)).map stationUmkehr := by
  unfold umkehr
  rw [stations_map_rev, origin_map_rev, stations_reverse_values, List.map_map]
  rfl

/-- (GI1) **Die Umkehr eines Vollkreises ist ein Vollkreis — für jede Wertzahl.** Allgemeine
Fassung von `NegationCycleSymmetry.mirror_all` (dort vier Werte, über die Tafel). -/
theorem umkehr_full {m : ℕ} {w : List (Fin m)} (h : IsFullCycle w) :
    IsFullCycle (umkehr w) := by
  have hinj : Function.Injective (stationUmkehr (m := m)) :=
    Function.LeftInverse.injective stationUmkehr_stationUmkehr
  refine ⟨?_, ?_, ?_, ?_⟩
  · show endpoint (w.map Fin.rev) (origin m) = origin m
    rw [endpoint_map_rev, origin_map_rev, endpoint_reverse_values, h.closes, List.map_reverse,
      origin_map_rev, List.reverse_reverse]
  · rw [stations_umkehr]
    exact h.nodup.map hinj
  · intro l hl
    rw [stations_umkehr] at hl
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hl
    exact List.mem_permutations'.mpr
      (stationUmkehr_perm (List.mem_permutations'.mp (h.only_arrangements s hs)))
  · intro l hl
    rw [stations_umkehr]
    have hs := h.all_arrangements _
      (List.mem_permutations'.mpr (stationUmkehr_perm (List.mem_permutations'.mp hl)))
    exact List.mem_map.mpr ⟨_, hs, stationUmkehr_stationUmkehr l⟩

-- ============================================================
-- §III — Drei Werte: Umkehr = Drehsinn (GI2)
-- ============================================================

/-- (GI2) **Drei Werte: für jeden Vollkreis ist die Umkehr der Drehsinn.** Aus
`triadic_unique'` (es gibt nur die Tafelfolgen (4) und (5)); die zwei Fälle per `decide`, dieselbe
Rechnung wie `tafelVI5_eq_mirror` und `tafelVI5_eq_reverse`. -/
theorem umkehr_eq_dreh_three (w : List (Fin 2)) (h : IsFullCycle w) : umkehr w = dreh w := by
  rcases triadic_unique' w h with rfl | rfl <;> decide

-- ============================================================
-- §IV — Vier Werte: nirgends (GI3)
-- ============================================================

/-- Eichung über die 88 gerichteten Vollkreise: Umkehr ≠ Drehsinn, nicht umkehrfest, nicht
drehfest. -/
theorem gerichtet_getrennt : ∀ s ∈ gerichtet, umkehr s ≠ dreh s ∧ umkehr s ≠ s ∧ dreh s ≠ s := by
  decide +kernel

/-- (GI3) **Vier Werte: für keinen Vollkreis ist die Umkehr der Drehsinn.** -/
theorem umkehr_ne_dreh_four (w : List (Fin 3)) (h : IsFullCycle w) : umkehr w ≠ dreh w :=
  (gerichtet_getrennt w (mem_gerichtet w h)).1

/-- (GI3) Kein vierwertiger Vollkreis ist umkehrfest. -/
theorem umkehr_ne_self_four (w : List (Fin 3)) (h : IsFullCycle w) : umkehr w ≠ w :=
  (gerichtet_getrennt w (mem_gerichtet w h)).2.1

/-- (GI3) Kein vierwertiger Vollkreis ist drehfest. -/
theorem dreh_ne_self_four (w : List (Fin 3)) (h : IsFullCycle w) : dreh w ≠ w :=
  (gerichtet_getrennt w (mem_gerichtet w h)).2.2

/-- **Jeder vierwertige Vollkreis hat drei verschiedene Partner:** die Bahn unter Umkehr und
Drehsinn hat vier Elemente. Zusammengestellt aus GI0 und GI3, ohne neue Aufzählung. -/
theorem bahn_vier (w : List (Fin 3)) (h : IsFullCycle w) :
    [w, umkehr w, dreh w, umkehr (dreh w)].Nodup := by
  have e1 : w ≠ umkehr w := (umkehr_ne_self_four w h).symm
  have e2 : w ≠ dreh w := (dreh_ne_self_four w h).symm
  have e3 : w ≠ umkehr (dreh w) := fun e =>
    umkehr_ne_dreh_four w h ((congrArg umkehr e).trans (umkehr_umkehr _))
  have e4 : umkehr w ≠ dreh w := umkehr_ne_dreh_four w h
  have e5 : umkehr w ≠ umkehr (dreh w) := fun e =>
    dreh_ne_self_four w h (by rw [← umkehr_umkehr (dreh w), ← e, umkehr_umkehr])
  have e6 : dreh w ≠ umkehr (dreh w) := (umkehr_ne_self_four (dreh w) (reverse_full h)).symm
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

/-- Der Vertreter einer Bahn: unter `w`, `umkehr w`, `dreh w`, `umkehr (dreh w)` der mit
der kleinsten Stelle in `gerichtet`. -/
def bahnKanon (w : List (Fin 3)) : List (Fin 3) :=
  [umkehr w, dreh w, umkehr (dreh w)].foldl
    (fun a b => if gerichtet.idxOf b < gerichtet.idxOf a then b else a) w

/-- Eichung: die 88 gerichteten Vollkreise zerfallen in 22 Bahnen. -/
theorem bahnen_zweiundzwanzig : (gerichtet.map bahnKanon).dedup.length = 22 := by
  decide +kernel

-- ============================================================
-- §V — Umkehr, Drehsinn und Günthers Familien (GI4)
-- ============================================================

/-- Die Umkehr der Werte vertauscht die Häufigkeiten: `a` in der Umkehr so oft wie `rev a` im
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

/-- (GI4) **Die Umkehr kehrt die Verteilung der Operatoren um:** `(a, b, c) ↦ (c, b, a)`, für
jedes Wort über drei Negatoren. -/
theorem vert_umkehr (w : List (Fin 3)) :
    vert (umkehr w) = ((vert w).2.2, (vert w).2.1, (vert w).1) := by
  unfold vert umkehr
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
-- §VI — Die Bahn und die Prädikate, die sie nicht trennen (Folgezug, 20.10.2026)
-- ============================================================

/-- **Bahn-Ununterscheidbarkeit, jede Wertzahl.** Respektiert `f` Umkehr und Drehsinn, dann ist
`f` auf der Bahn `{w, umkehr w, dreh w, umkehr (dreh w)}` konstant. -/
theorem bahn_ununterscheidbar {m : ℕ} {α : Type*} (f : List (Fin m) → α)
    (hs : ∀ w, f (umkehr w) = f w) (hd : ∀ w, f (dreh w) = f w) (w : List (Fin m)) :
    f (umkehr w) = f w ∧ f (dreh w) = f w ∧ f (umkehr (dreh w)) = f w :=
  ⟨hs w, hd w, (hs (dreh w)).trans (hd w)⟩

/-- **Drei Werte: die Umkehr genügt.** Auf einem dreiwertigen Vollkreis folgt die Gleichheit
unter dem Drehsinn aus der unter der Umkehr (`umkehr_eq_dreh_three`) — darum braucht
`tafelVI_ununterscheidbar` nur die Umkehr. -/
theorem bahn_drei_umkehr_genuegt {α : Type*} (f : List (Fin 2) → α)
    (hs : ∀ w, f (umkehr w) = f w) (w : List (Fin 2)) (h : IsFullCycle w) :
    f (dreh w) = f w ∧ f (umkehr (dreh w)) = f w := by
  have hd : f (dreh w) = f w := by rw [← umkehr_eq_dreh_three w h]; exact hs w
  exact ⟨hd, (hs (dreh w)).trans hd⟩

/-- Der alte Satz in der Sprache dieser Datei: `tafelVI_ununterscheidbar` mit `umkehr`. -/
theorem tafelVI_ununterscheidbar' {α : Type*} (f : List (Fin 2) → α)
    (hs : ∀ w, f (umkehr w) = f w) : f tafelVI4 = f tafelVI5 :=
  tafelVI_ununterscheidbar f hs

/-- Die Umkehr der Werte auf drei Negatoren erhält „entfernt" (`N1`, `N3`). -/
theorem far_rev (a b : Fin 3) : far (Fin.rev a) (Fin.rev b) = far a b := by
  revert a b; decide

/-- (a) **`hasFar` respektiert die Umkehr**, für jedes Wort. -/
theorem hasFar_umkehr (w : List (Fin 3)) : hasFar (umkehr w) = hasFar w := by
  cases w with
  | nil => rfl
  | cons x xs =>
    show (((Fin.rev x :: xs.map Fin.rev) ++ [Fin.rev x]).zip
        (((Fin.rev x :: xs.map Fin.rev) ++ [Fin.rev x]).drop 1)).any (fun p => far p.1 p.2) =
      (((x :: xs) ++ [x]).zip (((x :: xs) ++ [x]).drop 1)).any (fun p => far p.1 p.2)
    rw [show (Fin.rev x :: xs.map Fin.rev) ++ [Fin.rev x] = ((x :: xs) ++ [x]).map Fin.rev from
      by rw [List.map_append, List.map_cons, List.map_cons, List.map_nil],
      ← List.map_drop, List.zip_map, List.any_map]
    congr 1
    funext p
    exact far_rev p.1 p.2

/-- Für jede Option über drei Werten: „ist `N2`" ändert sich unter der Umkehr der Werte nicht. -/
theorem getD_rev_eq_one (o : Option (Fin 3)) :
    ((o.map Fin.rev).getD 0 == 1) = (o.getD 0 == 1) := by
  cases o with
  | none => rfl
  | some a => revert a; decide

/-- (b) **`altN2` respektiert die Umkehr**, für jedes Wort. -/
theorem altN2_umkehr (w : List (Fin 3)) : altN2 (umkehr w) = altN2 w := by
  have hk : ∀ k, ((umkehr w).getD k 0 == 1) = (w.getD k 0 == 1) := by
    intro k
    unfold umkehr
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
    exact getD_rev_eq_one _
  unfold altN2
  rw [show (umkehr w).length = w.length from List.length_map ..]
  congr 2 <;> (funext k; rw [hk k])

/-- Eichung über die 88: `hasFar` und `altN2` respektieren den Drehsinn. -/
theorem gerichtet_dreh_praedikate :
    ∀ s ∈ gerichtet, hasFar (dreh s) = hasFar s ∧ altN2 (dreh s) = altN2 s := by
  decide +kernel

/-- (a) **`hasFar` respektiert den Drehsinn**, für jeden vierwertigen Vollkreis. -/
theorem hasFar_dreh (w : List (Fin 3)) (h : IsFullCycle w) : hasFar (dreh w) = hasFar w :=
  (gerichtet_dreh_praedikate w (mem_gerichtet w h)).1

/-- (b) **`altN2` respektiert den Drehsinn**, für jeden vierwertigen Vollkreis. -/
theorem altN2_dreh (w : List (Fin 3)) (h : IsFullCycle w) : altN2 (dreh w) = altN2 w :=
  (gerichtet_dreh_praedikate w (mem_gerichtet w h)).2

/-- (c) **„In Familie 5-9-10" trennt die Bahn:** es gibt einen Vollkreis dieser Verteilung,
dessen Umkehr nicht in ihr liegt. -/
theorem familie_5_9_10_subjektiv :
    ∃ w ∈ gerichtet, vert w = (5, 9, 10) ∧ vert (umkehr w) ≠ (5, 9, 10) := by
  decide +kernel

/-- (d) Günthers erste Familie als Klasse (IGN S. 43, Tafel (18)): 10-9-5 oder 5-9-10. -/
def guentherFamilie1 (w : List (Fin 3)) : Bool :=
  decide (vert w = (5, 9, 10) ∨ vert w = (10, 9, 5))

/-- (d) **Günthers erste Familie respektiert die Umkehr**, für jedes Wort. -/
theorem guentherFamilie1_umkehr (w : List (Fin 3)) :
    guentherFamilie1 (umkehr w) = guentherFamilie1 w := by
  unfold guentherFamilie1
  rw [vert_umkehr]
  obtain ⟨a, b, c⟩ := vert w
  apply decide_eq_decide.mpr
  show (c, b, a) = (5, 9, 10) ∨ (c, b, a) = (10, 9, 5) ↔
    (a, b, c) = (5, 9, 10) ∨ (a, b, c) = (10, 9, 5)
  constructor
  · rintro (h | h)
    · injection h with h1 h2; injection h2 with h2 h3; subst h1 h2 h3; exact Or.inr rfl
    · injection h with h1 h2; injection h2 with h2 h3; subst h1 h2 h3; exact Or.inl rfl
  · rintro (h | h)
    · injection h with h1 h2; injection h2 with h2 h3; subst h1 h2 h3; exact Or.inr rfl
    · injection h with h1 h2; injection h2 with h2 h3; subst h1 h2 h3; exact Or.inl rfl

/-- (d) **Günthers erste Familie respektiert den Drehsinn**, für jedes Wort. -/
theorem guentherFamilie1_dreh (w : List (Fin 3)) :
    guentherFamilie1 (dreh w) = guentherFamilie1 w := by
  unfold guentherFamilie1
  rw [vert_dreh]

/-- (d) **Eine an den Enden symmetrische Verteilung ist umkehrfest** — Günthers zweite und
dritte Familie, 9-6-9 und 6-12-6, sind es als Verteilung. -/
theorem vert_umkehr_symm (w : List (Fin 3)) (h : (vert w).1 = (vert w).2.2) :
    vert (umkehr w) = vert w := by
  rw [vert_umkehr]
  rcases hv : vert w with ⟨a, b, c⟩
  rw [hv] at h
  have h' : a = c := h
  show (c, b, a) = (a, b, c)
  rw [h']

-- ============================================================
-- Wachen — Axiom-Profile
-- ============================================================

/-! **Wachen.** Ist-Ausgabe des grünen Builds (v4.30.0-rc2), alle 41 Deklarationen (26 der Sonde, 15 aus §VI). Kein
`Classical.choice`: Listenrechnung mit `rw`, ohne offenes `simp`; `decide +kernel` nur über
konkrete Listen (`gerichtet`). -/

/-- info: 'Reformulation.Proemial.GegenidentitaetProbe.umkehr' does not depend on any axioms -/
#guard_msgs in #print axioms umkehr

/-- info: 'Reformulation.Proemial.GegenidentitaetProbe.dreh' does not depend on any axioms -/
#guard_msgs in #print axioms dreh

/-- info: 'Reformulation.Proemial.GegenidentitaetProbe.map_rev_map_rev' depends on axioms: [propext] -/
#guard_msgs in #print axioms map_rev_map_rev

/-- info: 'Reformulation.Proemial.GegenidentitaetProbe.umkehr_umkehr' depends on axioms: [propext] -/
#guard_msgs in #print axioms umkehr_umkehr

/-- info: 'Reformulation.Proemial.GegenidentitaetProbe.dreh_dreh' depends on axioms: [propext] -/
#guard_msgs in #print axioms dreh_dreh

/-- info: 'Reformulation.Proemial.GegenidentitaetProbe.umkehr_dreh_comm' depends on axioms: [propext] -/
#guard_msgs in #print axioms umkehr_dreh_comm

/-- info: 'Reformulation.Proemial.GegenidentitaetProbe.negate_map_rev' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms negate_map_rev

/-- info: 'Reformulation.Proemial.GegenidentitaetProbe.stations_map_rev' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms stations_map_rev

/-- info: 'Reformulation.Proemial.GegenidentitaetProbe.stations_reverse_values' depends on axioms: [propext] -/
#guard_msgs in #print axioms stations_reverse_values

/-- info: 'Reformulation.Proemial.GegenidentitaetProbe.stationUmkehr' does not depend on any axioms -/
#guard_msgs in #print axioms stationUmkehr

/-- info: 'Reformulation.Proemial.GegenidentitaetProbe.stationUmkehr_stationUmkehr' depends on axioms: [propext] -/
#guard_msgs in #print axioms stationUmkehr_stationUmkehr

/-- info: 'Reformulation.Proemial.GegenidentitaetProbe.stationUmkehr_perm' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms stationUmkehr_perm

/-- info: 'Reformulation.Proemial.GegenidentitaetProbe.stations_umkehr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms stations_umkehr

/-- info: 'Reformulation.Proemial.GegenidentitaetProbe.umkehr_full' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms umkehr_full

/-- info: 'Reformulation.Proemial.GegenidentitaetProbe.umkehr_eq_dreh_three' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms umkehr_eq_dreh_three

/-- info: 'Reformulation.Proemial.GegenidentitaetProbe.gerichtet_getrennt' depends on axioms: [propext] -/
#guard_msgs in #print axioms gerichtet_getrennt

/-- info: 'Reformulation.Proemial.GegenidentitaetProbe.umkehr_ne_dreh_four' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms umkehr_ne_dreh_four

/-- info: 'Reformulation.Proemial.GegenidentitaetProbe.umkehr_ne_self_four' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms umkehr_ne_self_four

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

/-- info: 'Reformulation.Proemial.GegenidentitaetProbe.vert_umkehr' depends on axioms: [propext] -/
#guard_msgs in #print axioms vert_umkehr

/-- info: 'Reformulation.Proemial.GegenidentitaetProbe.vert_dreh' depends on axioms: [propext] -/
#guard_msgs in #print axioms vert_dreh

/-- info: 'Reformulation.Proemial.GegenidentitaetProbe.familien_zahlen' depends on axioms: [propext] -/
#guard_msgs in #print axioms familien_zahlen

/-- info: 'Reformulation.Proemial.GegenidentitaetProbe.bahn_ununterscheidbar' does not depend on any axioms -/
#guard_msgs in #print axioms bahn_ununterscheidbar

/-- info: 'Reformulation.Proemial.GegenidentitaetProbe.bahn_drei_umkehr_genuegt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms bahn_drei_umkehr_genuegt

/-- info: 'Reformulation.Proemial.GegenidentitaetProbe.tafelVI_ununterscheidbar'' depends on axioms: [propext] -/
#guard_msgs in #print axioms tafelVI_ununterscheidbar'

/-- info: 'Reformulation.Proemial.GegenidentitaetProbe.far_rev' does not depend on any axioms -/
#guard_msgs in #print axioms far_rev

/-- info: 'Reformulation.Proemial.GegenidentitaetProbe.hasFar_umkehr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms hasFar_umkehr

/-- info: 'Reformulation.Proemial.GegenidentitaetProbe.getD_rev_eq_one' depends on axioms: [propext] -/
#guard_msgs in #print axioms getD_rev_eq_one

/-- info: 'Reformulation.Proemial.GegenidentitaetProbe.altN2_umkehr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms altN2_umkehr

/-- info: 'Reformulation.Proemial.GegenidentitaetProbe.gerichtet_dreh_praedikate' depends on axioms: [propext] -/
#guard_msgs in #print axioms gerichtet_dreh_praedikate

/-- info: 'Reformulation.Proemial.GegenidentitaetProbe.hasFar_dreh' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms hasFar_dreh

/-- info: 'Reformulation.Proemial.GegenidentitaetProbe.altN2_dreh' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms altN2_dreh

/-- info: 'Reformulation.Proemial.GegenidentitaetProbe.familie_5_9_10_subjektiv' depends on axioms: [propext] -/
#guard_msgs in #print axioms familie_5_9_10_subjektiv

/-- info: 'Reformulation.Proemial.GegenidentitaetProbe.guentherFamilie1' depends on axioms: [propext] -/
#guard_msgs in #print axioms guentherFamilie1

/-- info: 'Reformulation.Proemial.GegenidentitaetProbe.guentherFamilie1_umkehr' depends on axioms: [propext] -/
#guard_msgs in #print axioms guentherFamilie1_umkehr

/-- info: 'Reformulation.Proemial.GegenidentitaetProbe.guentherFamilie1_dreh' depends on axioms: [propext] -/
#guard_msgs in #print axioms guentherFamilie1_dreh

/-- info: 'Reformulation.Proemial.GegenidentitaetProbe.vert_umkehr_symm' depends on axioms: [propext] -/
#guard_msgs in #print axioms vert_umkehr_symm
end Reformulation.Proemial.GegenidentitaetProbe
