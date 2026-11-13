import Reformulation.Proemial.SpiegelfesteAnordnungen   -- stations_gestalt, stationUmkehr_*; über GegenidentitaetProbe: umkehr, dreh, stations_umkehr
import Reformulation.Kenogram.Fiber                     -- fiberEquiv, MarksLeOne; über Basic: canonicalize, canonicalize_eq_iff

/-!
# Proemial.ReflexionskreisProbe — der Vollkreis durchläuft die totale Negation des Ausgangs, und wo; der Werttausch auf der Faser

STANDALONE, NICHT im Aggregat; Target `Probes`. AxiomGate unberührt. Sonde nach
`KorpusRev2/Sondierung_Totale_Negation_Reflexionskreis_1957_Prompt.md` (Mathematiker, 21. Oktober
2026), auf Grundlage von `KorpusRev2/Fund_1957_Verhaeltnis_zu_sich_Reflexionskreis.md` und
`KorpusRev2/Verortung_Ontische_und_Meontische_Axiomatik_im_Bau.md`. **Aktualisiert am 13. November
2026** nach `KorpusRev2/Prompt_Instanz_Sonde_Reflexionskreis_aktualisiert_AnhangB_Mathematiker.md`
(für Anhang B, B.5, des Blatts „Axiome oder Stufen"): Quellenstand je Zitat nachgetragen, §V (der
Werttausch auf der Faser) neu, die ZUORDNUNG in zwei Teile geteilt.

Konsumiert `SpiegelfesteAnordnungen` (`stations_gestalt`, `stationUmkehr_origin`,
`stationUmkehr_reverse`), `GegenidentitaetProbe` (`umkehr`, `dreh`, `stations_umkehr`),
`NegationCycleLength` (`inv`, `inv_is_min_length`), `NegationCycleSJT` (`sjt`) und, seit dem
13. November, `Kenogram.Fiber` (`fiberEquiv`, Aggregat) mit `Kenogram.canonicalize_eq_iff`; ändert
nichts davon. Zwischen dem 21. Oktober und dem 13. November hat sich an den konsumierten Modulen nur
ein Doc-Kommentar in `NegationCycle` geändert (gemessen: `git diff 79c1b1b..6babafc`).

## Der Gegenstand

1. Die **totale Negation des Ausgangs** ist hier die umgekehrte Wertfolge `(origin m).reverse` —
   Günthers Ziel von Tafel XXII (IGN S. 52 f.: „die Umkehrung der Viererfolge"; im Bestand
   `NegationReversalProbe`). Dass sie die „eigene Negation" von 1957 ist, ist ZUORDNUNG.
2. **Der Werttausch auf der Faser** (§V): Über jedem zweiwertig besetzbaren Muster der Länge vier
   liegen genau zwei Belegungen (`Kenogram.Fiber.fiberEquiv`). Die Ausgabe Rev11 sagt in der Prosa
   von Kapitel 1 (#ah2), die zwei Tafeln gingen „durch globalen Werttausch auseinander — sie stimmen
   an keiner einzigen Stelle überein"; einen Satz dafür hatte der Bestand nicht. §V gibt ihn:
   die punktweise Negation erhält das Muster, für jede Länge, und auf der Faser ist das andere
   Element genau die punktweise Negation des einen.

## Die Sätze und ihre Stufen (CLAUDE.md §4)

| Satz | Aussage | Stufe |
|---|---|---|
| `totale_negation_besucht` (T1) | jeder Vollkreis hat die totale Negation unter seinen Stationen | ZUSAMMENSTELLUNG (`all_arrangements`, `List.reverse_perm`) |
| `totale_negation_fest` (T2) | die Umkehr hält Ausgang und totale Negation fest | UMBENENNUNG (Paar aus `stationUmkehr_origin`, `stationUmkehr_reverse`) |
| `totale_negation_platz_umkehr` (T3) | in `umkehr w` steht sie an denselben Plätzen wie in `w`, jedes Wort | ZUSAMMENSTELLUNG (`stations_umkehr`, `getElem?_map_fest`) |
| `stations_dreh_platz` | Vollkreis, `0 < k < N`: Station `N − k` von `dreh w` = Station `k` von `w` | FOLGERUNG (`stations_gestalt`) |
| `totale_negation_platz_dreh` (T4) | steht sie an Stelle `k`, so im Drehsinn an Stelle `N − k` | INSTANZIIERUNG |
| `totale_negation_platz_ge` (T6) | ihr Platz ist nie kleiner als `inv` des Rücklaufs, jedes Wort | FOLGERUNG (`inv_is_min_length`, `stations_getElem?_endpoint`) |
| `inv_ruecklauf_drei_vier`, `platz_tafelVI4`, `platz_sjt`, `platz_sjt_sechs`, `plaetze_gerichtet` | Eichungen | EICHUNG |
| `canonicalize_not` (W1) | die punktweise Negation einer Belegung `Fin n → Bool` hat dasselbe Muster, jedes `n` | ZUSAMMENSTELLUNG (`canonicalize_eq_iff`, `Bool.not_inj_iff`) |
| `faser_werttausch` (W2) | auf der Faser über einem besetzbaren Muster der Länge vier ist das andere Element die punktweise Negation | FOLGERUNG (dünn; `fiberEquiv` injektiv, der Wert an der ersten Stelle per Definition) |
| `faser_nirgends_gleich` (W3) | die zwei Elemente der Faser stimmen an keiner Stelle überein | FOLGERUNG (dünn; aus W2 und `Bool.not_ne_self`) |

Hilfssätze: `getElem?_map_fest`, `stations_getElem?_endpoint`.

**Nicht gebaut: T5** des Prompts vom 21. Oktober (`closes ∧ umkehr w ≠ w ∧ dreh w ≠ w ∧ T1`). Er wäre
eine bloße Konjunktion vorhandener Sätze ohne eigenen Inhalt. **Neu gegenüber jenem Prompt: T6** —
er erklärt, warum in `plaetze_gerichtet` kein Platz unter 6 liegt.

**Nicht gebaut, mit Absicht (13. November):** ein Satz „der Tausch der zwei Werte ist ein
Isomorphismus der zweiwertigen Struktur, der ∧ und ∨ vertauscht". Er steht im Lean-Kern als
`Bool.not_and : (!(x && y)) = (!x || !y)` und `Bool.not_or : (!(x || y)) = (!x && !y)`, beide
axiomfrei, und in Mathlib als `OrderIso.compl : α ≃o αᵒᵈ` für jede boolesche Algebra
(`[propext, Classical.choice, Quot.sound]`); für `Fin n` als `Fin.revOrderIso` (`[propext,
Quot.sound]`). Gemessen mit `#check`/`#print axioms` unter Lean `4.30.0-rc2`, Mathlib `83a5988`.
Ihn hier zu wiederholen wäre UMBENENNUNG. Im Bestand vertauscht kein Satz die Negation mit
`min`/`max` (gesucht über `Reformulation/`, 13. November).

## Die Eichungen und was sie erzwingt (§12 Regel 11)

* `platz_sjt`, `platz_sjt_sechs`: im SJT-Kreis steht die totale Negation an Platz 3, 12, 64, 389
  bei drei, vier, fünf, sechs Werten; zur Halbzeit (`N/2` = 3, 12, 60, 360) nur bis vier Werte.
* `plaetze_gerichtet`: unter den 88 gerichteten Vollkreisen bei vier Werten die Plätze
  6 : 12, 8 : 8, 10 : 12, 12 : 24, 14 : 12, 16 : 8, 18 : 12. Die **Symmetrie um 12** erzwingt T4
  (`gerichtet` ist unter dem Drehsinn abgeschlossen, Platz `k` ↔ `24 − k`); die **untere Grenze 6**
  erzwingt T6 mit `inv_ruecklauf_drei_vier` (`inv = 6`). Nicht erzwungen sind die Anzahlen selbst
  und dass die 6 erreicht wird.
* `platz_tafelVI4`: Günthers Folge (4) erreicht die totale Negation an Platz 3, der Halbzeit — und
  das ist bei drei Werten zugleich die kürzeste Strecke (`inv = 3`): die erste Hälfte `N1·2·1` ist
  die Genese. **Günthers Folge (4) und `guentherWord` sind nicht vergleichbar:** die eine lebt auf
  drei Werten, das andere auf vier. Bei vier Werten ist die kürzeste Strecke 6
  (`guentherWord`), und T6 sagt, dass kein Vollkreis die totale Negation früher erreicht.
* W3 erzwingt „an keiner einzigen Stelle" der Ausgabe aus W2 allein: `!b ≠ b`. Keine Zahl.

## Quellen: die meontische Axiomatik von 1957

G. Günther, „Metaphysik, Logik und die Theorie der Reflexion", Archiv für Philosophie 7 (1957),
S. 1–44; `KorpusRev1/gg_metaph-logik-refl.pdf`, Seiten = Fußzahl der Edition. Stand je Zitat
(nachgetragen 13. November; kein Wortlaut geändert): **TEXTSCHICHT** = am 21. Oktober an der
Textschicht gegen die Fund-Notiz gehalten; **AM BILD** = von Hermeneutes am Bild gelesen
(12./13. November, wiedergegeben in `KorpusRev2/Entwurf_2026-11-13_Goedel_Guenther_AnhangB_de_Fassung3.md`, B.2).

* S. 28, Gesetz des Selbstbewusstseins: „dass Subjektivität sich nie direkt, sondern stets
  "vermittelt" besitzt und versteht"; „weil alle Subjektivität im Sein immer nur ein Verhältnis zu
  sich selbst gewinnen will. … Das Sein ist dem Geist nur ein Durchgangsstadium". — TEXTSCHICHT
  (die Ausgabe Rev11 zitiert „weil alle Subjektivität …" in ihrem Eingang als am Bild, S. 27 f.).
* S. 29, Satz vom reflektierten Gegensinn: „jedes Sinnmotiv ist bestimmt als geschlossener
  Reflexionskreis, der seine eigene Negation durchläuft". — TEXTSCHICHT
* S. 29, Satz der thematischen Inversion: „jedes Reflexionsmotiv wird als thematische Inversion
  seiner selbst begriffen"; Sinn „stets nur denkbar als Objektivität (d.h. als sein Gegensatz),
  mithin nur als totale Negation seiner selbst". — TEXTSCHICHT
* S. 29, Satz der infiniten Reflexionsfolgen: „jede thematische Inversion ist Objekt und Thema
  einer höheren (allgemeineren) Reflexion". — AM BILD
* S. 30 f., Satz vom transfiniten Ursprung: das Selbst muss „als definite Größe "außerhalb" des
  infiniten Systems der Reflexionsverhältnisse stehen". — TEXTSCHICHT. Am Bild gelesen ist auf
  S. 31 der Satz, der das Axiom benennt: „Damit aber besetzt das Selbstbewusstsein den Ort des
  transfiniten Ursprungs jeder infiniten Reflexionsreihe, womit für jede beliebige
  Bewusstseinsbestimmung, die der meontischen Axiomatik untersteht, ihre introszendentale
  Legitimität gewährleistet ist. Wir nennen dieses letzte Grundgesetz der reflexiven Sinnlogik den
  Satz vom transfiniten Ursprung." — AM BILD
* S. 32, Günthers Tafel der zwei Axiomatiken („Axiomatik der totalen Rationalität"). — AM BILD

Die klassische Spalte, für Teil (b) unten, nach Anhang B, B.1 (Stand dort; hier nicht neu gelesen):
S. 9 der Inbegriff der positiven und der der negativen Bestimmungen „beide restlos durcheinander
vertretbar"; S. 10 „Positivität und Negativität Wertqualitäten von äquivalenter logischer
Mächtigkeit" — beide TEXTSCHICHT nach Anhang B. Dazu Baer bei Günther 1978 (Druck S. 239): die
Negation bildet den Kalkül mit Konjunktion auf den mit Disjunktion ab. — AM BILD (Mathematiker).

## ZUORDNUNG (nur hier, in keinem Satz)

### (a) Die meontische Spalte — geprüft gegen den Wortlaut von Anhang B, B.2 (13. November)

* Axiom 1 (reflektierter Gegensinn) ↔ `IsFullCycle.closes` und T1: der Kreis schließt und
  durchläuft die totale Negation des Ausgangs.
* Axiom 2 (thematische Inversion) ↔ `SpiegelfesteAnordnungen.umkehr_ne_self_all` (kein Vollkreis
  ist seine eigene Umkehr) und T2/T3: die Umkehr hält den Ausgang und seine totale Negation fest —
  und den Platz der Negation im Kreis. Dass sie alles dazwischen vertauscht, ist gerechnet, kein
  Satz dieser Sonde.
* Axiom 3 (infinite Reflexionsfolgen) ↔ `AkkretivitaetsBruecke.phi_full`, einmal für jedes `m`
  ausgesprochen.
* **Axiom 4 (transfiniter Ursprung) ↔ nichts.** Kein Term, keine Zuordnung: der Bestand hat keinen
  Term „Selbst" und keinen Term „Subjekt" (Verortung §II; am 13. November über die Deklarationsnamen
  von `Reformulation/` nachgesucht: keiner; `Kaehr.Kopplung.selbstgekoppelt` ist eine
  Graph-Eigenschaft, kein solcher Term). Die Stelle bleibt leer.

Die Zuordnung ist ZUORDNUNG und geht vor jeder Nennung auf dem Blatt an Horistês und Speculum.

### (b) Die klassische Spalte und der Übergang — UNGEPRÜFT; an Horistês, Speculum

* Drittes klassisches Axiom (S. 9 f.: die zwei Inbegriffe „restlos durcheinander vertretbar",
  „äquivalente logische Mächtigkeit") ↔ W1 bis W3: der Tausch der zwei Werte lässt das Muster
  unverändert und führt die eine Belegung über einem Muster in die andere über. Dazu, nicht im
  Bestand, `Bool.not_and`/`Bool.not_or` (Baers Vertauschung von Konjunktion und Disjunktion).
  Dass „vertretbar" das meint, ist ZUORDNUNG.
* Der Übergang (S. 9: ein Drittes nur bei „höherer logischer Mächtigkeit" des Denkens; S. 21:
  „zusätzliche Reflexionstiefe", keine Anzahl): **keine Zuordnung.** Genannt, nicht zugeordnet:
  `StageAscent.choose_two_succ`, `StageAscent.ascent_proper`, `StageParity.odd_no_neg_compatible`
  (alle drei Träger der Ausgabe Rev11, Kapitel 6) und die Sonde `StufenZusammenfassung.zwei_anders` (zwei Werte
  erfüllen eine Gleichung in `min`/`max`/`negFin`, die drei Werte nicht erfüllen). Alle sprechen
  von Anzahlen, Einbettungen oder Gleichungen, keiner von Reflexionstiefe.
* Viertes klassisches Axiom (zureichender Grund) ↔ **nichts.** Der Bestand hat
  `RecurringGround.Ground` („Der Grund: was unter f es selbst bleibt", ein Fixpunkt); die Ausgabe
  ordnet ihn dem „reflexionslosen Sein" zu (Abschnitt „Die achtfache Thematik", #a2, mit dem
  Träger `RecurringGround.ground_recurs`; der Kopf von `RecurringGround` nennt Beiträge III S. 160), nicht dem Satz
  vom Grunde. Ein Term für den zureichenden Grund steht nicht im Bestand.

## Was die Sonde nicht ist

Die Sonde ist keine meontische Logik. Sie beweist Sätze über eine Struktur innerhalb der
gewöhnlichen (ontischen) Logik. Kein Satz heißt nach einem Axiom, nach „Selbst", „Subjekt",
„Sinn" oder „Reflexion"; die Sätze heißen nach der Sache. Keine Formel für ein meontisches Axiom
(E28).

**Profile.** §I–§IV ohne `Classical.choice`. §V trägt `[propext, Classical.choice, Quot.sound]`:
der Choice liegt in der Sache, in `canonicalize` (noncomputable) und `canonicalize_eq_iff`, deren
Profil dasselbe ist (Fallstrick 21, Route „in der Sache"); `fiberEquiv` trägt es ebenso.

Kein `sorry`, kein `native_decide`, kein `: True`-Feld, kein `axiom`.
-/

namespace Reformulation.Proemial.ReflexionskreisProbe

open Reformulation.Proemial.NegationCycle
open Reformulation.Proemial.GegenidentitaetProbe
open Reformulation.Proemial.SpiegelfesteAnordnungen (stations_gestalt stationUmkehr_origin stationUmkehr_reverse)
open Reformulation.Proemial.NegationCycleLength (inv inv_is_min_length)
open Reformulation.Proemial.NegationCycleTable (gerichtet)
open Reformulation.Proemial.NegationCycleSJT (sjt)

-- ============================================================
-- §I — Der Vollkreis durchläuft die totale Negation des Ausgangs (T1, T2)
-- ============================================================

/-- (T1) **Jeder Vollkreis durchläuft die totale Negation des Ausgangs:** die umgekehrte
Wertfolge ist eine seiner Stationen, für jede Wertzahl. -/
theorem totale_negation_besucht {m : ℕ} {w : List (Fin m)} (h : IsFullCycle w) :
    (origin m).reverse ∈ stations w (origin m) :=
  h.all_arrangements _ (List.mem_permutations'.mpr (List.reverse_perm _))

/-- (T2) **Die Umkehr hält den Ausgang und seine totale Negation fest.** -/
theorem totale_negation_fest {m : ℕ} :
    stationUmkehr (origin m) = origin m ∧ stationUmkehr (origin m).reverse = (origin m).reverse :=
  ⟨stationUmkehr_origin, stationUmkehr_reverse⟩

-- ============================================================
-- §II — Wo: die Umkehr lässt den Platz stehen, der Drehsinn spiegelt ihn (T3, T4)
-- ============================================================

/-- Unter einer Involution, die `r` festhält, steht `r` in der Bildliste an denselben Plätzen. -/
theorem getElem?_map_fest {α : Type*} (φ : α → α) (hφ : ∀ x, φ (φ x) = x) {r : α} (hr : φ r = r)
    (l : List α) (k : ℕ) : (l.map φ)[k]? = some r ↔ l[k]? = some r := by
  rw [List.getElem?_map]
  cases l[k]? with
  | none => exact Iff.rfl
  | some x =>
    show some (φ x) = some r ↔ some x = some r
    constructor
    · intro e
      have e' := Option.some.inj e
      rw [← hφ x, e', hr]
    · intro e
      rw [Option.some.inj e, hr]

/-- (T3) **Die Umkehr lässt den Platz der totalen Negation stehen**, für jedes Wort. -/
theorem totale_negation_platz_umkehr {m : ℕ} (w : List (Fin m)) (k : ℕ) :
    (stations (umkehr w) (origin m))[k]? = some (origin m).reverse ↔
      (stations w (origin m))[k]? = some (origin m).reverse := by
  rw [stations_umkehr]
  exact getElem?_map_fest _ stationUmkehr_stationUmkehr stationUmkehr_reverse _ k

/-- **Der Drehsinn spiegelt die Plätze:** für einen Vollkreis steht an Stelle `N − k` der
Stationen von `dreh w` dasselbe wie an Stelle `k` der Stationen von `w` (`0 < k < N`). -/
theorem stations_dreh_platz {m : ℕ} {w : List (Fin m)} (h : IsFullCycle w) {k : ℕ}
    (hk : 0 < k) (hkN : k < w.length) :
    (stations (dreh w) (origin m))[w.length - k]? = (stations w (origin m))[k]? := by
  obtain ⟨T, hS, hD⟩ := stations_gestalt h
  have hlen : T.length + 1 = w.length := by
    have := stations_length w (origin m)
    rw [hS, List.length_cons] at this
    exact this
  rw [hS, hD]
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have e : w.length - (j + 1) = (T.length - 1 - j) + 1 := by omega
  rw [e, List.getElem?_cons_succ, List.getElem?_cons_succ, List.getElem?_reverse (by omega)]
  congr 1
  omega

/-- (T4) **Steht die totale Negation an Stelle `k`, so im Drehsinn an Stelle `N − k`.** -/
theorem totale_negation_platz_dreh {m : ℕ} {w : List (Fin m)} (h : IsFullCycle w) {k : ℕ}
    (hk : 0 < k) (hkN : k < w.length) :
    (stations (dreh w) (origin m))[w.length - k]? = some (origin m).reverse ↔
      (stations w (origin m))[k]? = some (origin m).reverse := by
  rw [stations_dreh_platz h hk hkN]

-- ============================================================
-- §III — Nicht vor der kürzesten Strecke (T6)
-- ============================================================

/-- Die Station an Stelle `k` ist der Endpunkt des Anfangsstücks der Länge `k`. -/
theorem stations_getElem?_endpoint {m : ℕ} :
    ∀ (w : List (Fin m)) (x y : List (Fin (m + 1))) (k : ℕ),
      (stations w x)[k]? = some y → endpoint (w.take k) x = y
  | [], x, y, k, hk => by
    rw [show stations ([] : List (Fin m)) x = [] from rfl, List.getElem?_nil] at hk
    cases hk
  | i :: is, x, y, 0, hk => by
    rw [show stations (i :: is) x = x :: stations is (negate i x) from rfl,
      List.getElem?_cons_zero] at hk
    exact Option.some.inj hk
  | i :: is, x, y, k + 1, hk => by
    rw [show stations (i :: is) x = x :: stations is (negate i x) from rfl,
      List.getElem?_cons_succ] at hk
    show endpoint (is.take k) (negate i x) = y
    exact stations_getElem?_endpoint is (negate i x) y k hk

/-- (T6) **Kein Wort erreicht die totale Negation vor der kürzesten Strecke:** steht sie an
Stelle `k` der Stationen, so ist `k ≥ inv (Rücklauf)` (`inv_is_min_length`), für jedes Wort. -/
theorem totale_negation_platz_ge {m : ℕ} (w : List (Fin m)) {k : ℕ}
    (hk : (stations w (origin m))[k]? = some (origin m).reverse) :
    inv (origin m).reverse ≤ k := by
  have e := stations_getElem?_endpoint w _ _ k hk
  have hmin := (inv_is_min_length (origin m).reverse
    (List.mem_permutations'.mpr (List.reverse_perm _))).2 _ e
  exact hmin.trans (List.length_take_le _ _)

-- ============================================================
-- §IV — Eichungen
-- ============================================================

/-- Eichung: die kürzeste Strecke zur totalen Negation hat bei drei Werten die Länge 3, bei vier
Werten die Länge 6 (die Länge von `NegationReversalProbe.guentherWord`). -/
theorem inv_ruecklauf_drei_vier : inv (origin 2).reverse = 3 ∧ inv (origin 3).reverse = 6 := by
  decide

/-- (E3) Eichung: Günthers Folge (4) erreicht die totale Negation zur Halbzeit, an Platz 3. -/
theorem platz_tafelVI4 : (stations tafelVI4 (origin 2)).idxOf (origin 2).reverse = 3 := by
  decide

/-- (E1) Eichung: der Platz der totalen Negation im SJT-Kreis — 3, 12, 64 bei drei, vier, fünf
Werten; die Halbzeit (`N/2`) nur bis vier Werte. -/
theorem platz_sjt :
    (stations (sjt 2) (origin 2)).idxOf (origin 2).reverse = 3 ∧
    (stations (sjt 3) (origin 3)).idxOf (origin 3).reverse = 12 ∧
    (stations (sjt 4) (origin 4)).idxOf (origin 4).reverse = 64 := by
  decide +kernel

/-- (E1) Eichung: sechs Werte (`sjt 5`, 720 Stationen) — Platz 389, nicht 360. -/
theorem platz_sjt_sechs : (stations (sjt 5) (origin 5)).idxOf (origin 5).reverse = 389 := by
  decide +kernel

/-- (E2) Eichung: die Plätze der totalen Negation unter den 88 gerichteten Vollkreisen bei vier
Werten — 6 : 12, 8 : 8, 10 : 12, 12 : 24, 14 : 12, 16 : 8, 18 : 12, symmetrisch um 12 (T4). -/
theorem plaetze_gerichtet :
    [6, 8, 10, 12, 14, 16, 18].map
        (fun p => (gerichtet.map (fun s => (stations s (origin 3)).idxOf (origin 3).reverse)).count p)
      = [12, 8, 12, 24, 12, 8, 12] := by
  decide +kernel

-- ============================================================
-- §V — Der Werttausch auf der Faser (W1–W3, 13. November 2026)
-- ============================================================

open Reformulation.Kenogram (RGS canonicalize canonicalize_eq_iff)
open Reformulation.Kenogram.Fiber (fiberEquiv)
open Reformulation.Kenogram.Fillability (MarksLeOne)

/-- (W1) **Die punktweise Negation erhält das Muster**, für jede Länge: zwei Stellen tragen nach
dem Tausch der Werte genau dann denselben Wert, wenn sie es vorher taten. -/
theorem canonicalize_not {n : ℕ} (f : Fin n → Bool) :
    canonicalize (fun i => !f i) = canonicalize f :=
  (canonicalize_eq_iff _ _).mpr fun _ _ => Bool.not_inj_iff

/-- (W2) **Auf der Faser ist das andere Element die punktweise Negation.** Über einem
zweiwertig besetzbaren Muster der Länge vier liegen genau zwei Belegungen (`fiberEquiv`); das
Element zum anderen Wert der ersten Stelle ist die Belegung mit allen Werten getauscht. -/
theorem faser_werttausch {r : RGS 4} (hr : MarksLeOne r)
    (x : {f : Fin 4 → Bool // canonicalize f = r}) :
    (fiberEquiv hr).symm (!(fiberEquiv hr x)) =
      ⟨fun i => !x.1 i, (canonicalize_not x.1).trans x.2⟩ :=
  (fiberEquiv hr).injective (by rw [Equiv.apply_symm_apply]; rfl)

/-- (W3) **Die zwei Belegungen über einem Muster stimmen an keiner Stelle überein.** -/
theorem faser_nirgends_gleich {r : RGS 4} (hr : MarksLeOne r)
    (x : {f : Fin 4 → Bool // canonicalize f = r}) (i : Fin 4) :
    ((fiberEquiv hr).symm (!(fiberEquiv hr x))).1 i ≠ x.1 i := by
  rw [faser_werttausch]
  exact Bool.not_ne_self _

-- ============================================================
-- Wachen — Axiom-Profile
-- ============================================================

/-! **Wachen.** Ist-Ausgabe des grünen Builds (v4.30.0-rc2), alle 16 Deklarationen. §I–§IV
ohne `Classical.choice`; die `decide`-Eichungen sind gegen falsche Werte geprüft (scheitern). §V
(W1–W3, 13. November) trägt ihn über `canonicalize` (siehe Kopf, „Profile"). -/

/-- info: 'Reformulation.Proemial.ReflexionskreisProbe.totale_negation_besucht' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms totale_negation_besucht

/-- info: 'Reformulation.Proemial.ReflexionskreisProbe.totale_negation_fest' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms totale_negation_fest

/-- info: 'Reformulation.Proemial.ReflexionskreisProbe.getElem?_map_fest' depends on axioms: [propext] -/
#guard_msgs in #print axioms getElem?_map_fest

/-- info: 'Reformulation.Proemial.ReflexionskreisProbe.totale_negation_platz_umkehr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms totale_negation_platz_umkehr

/-- info: 'Reformulation.Proemial.ReflexionskreisProbe.stations_dreh_platz' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms stations_dreh_platz

/-- info: 'Reformulation.Proemial.ReflexionskreisProbe.totale_negation_platz_dreh' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms totale_negation_platz_dreh

/-- info: 'Reformulation.Proemial.ReflexionskreisProbe.stations_getElem?_endpoint' depends on axioms: [propext] -/
#guard_msgs in #print axioms stations_getElem?_endpoint

/-- info: 'Reformulation.Proemial.ReflexionskreisProbe.totale_negation_platz_ge' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms totale_negation_platz_ge

/-- info: 'Reformulation.Proemial.ReflexionskreisProbe.inv_ruecklauf_drei_vier' does not depend on any axioms -/
#guard_msgs in #print axioms inv_ruecklauf_drei_vier

/-- info: 'Reformulation.Proemial.ReflexionskreisProbe.platz_tafelVI4' depends on axioms: [propext] -/
#guard_msgs in #print axioms platz_tafelVI4

/-- info: 'Reformulation.Proemial.ReflexionskreisProbe.platz_sjt' does not depend on any axioms -/
#guard_msgs in #print axioms platz_sjt

/-- info: 'Reformulation.Proemial.ReflexionskreisProbe.platz_sjt_sechs' does not depend on any axioms -/
#guard_msgs in #print axioms platz_sjt_sechs

/-- info: 'Reformulation.Proemial.ReflexionskreisProbe.plaetze_gerichtet' depends on axioms: [propext] -/
#guard_msgs in #print axioms plaetze_gerichtet

/--
info: 'Reformulation.Proemial.ReflexionskreisProbe.canonicalize_not' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms canonicalize_not

/--
info: 'Reformulation.Proemial.ReflexionskreisProbe.faser_werttausch' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms faser_werttausch

/--
info: 'Reformulation.Proemial.ReflexionskreisProbe.faser_nirgends_gleich' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms faser_nirgends_gleich

end Reformulation.Proemial.ReflexionskreisProbe
