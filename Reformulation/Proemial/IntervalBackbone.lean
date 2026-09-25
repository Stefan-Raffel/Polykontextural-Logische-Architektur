import Mathlib.Order.Monotone.Basic

/-!
# Reformulation.Proemial.IntervalBackbone — das Intervall-Rückgrat (einundzwanzigste Schicht)

Das **arithmetische Substrat** des Stellen-Trakts: die Anfangs-Wertzahlen der acht
Intervalle der achtfachen Thematik sind die Dreieckszahlen *m = ½·n(n+1)*. Diese
Schicht baut genau diese Arithmetik — die Formel, vier Gesetze (Gauss-Brücke,
Stufung, Naht, Themen-Zahl), den Tafel-Satz und zwei Zitat-Anker.

**Projekt-import-frei:** die Schicht liegt unter allen Stellen-Schichten und
importiert **einen einzigen** Mathlib-Baustein — `Mathlib.Order.Monotone.Basic`,
allein für `strictMono_nat_of_lt_succ` in der Kür. `omega` ist in v4.30 Lean-Kern
(`Init.Omega`); `Mathlib.Tactic.Omega` existiert nicht mehr. Für die Gauss-Brücke
wird nichts importiert (siehe (6)). Jede Mittelstellen-Schicht kann das Rückgrat
importieren (geteilte-Klassen-Ökonomie eine Stufe tiefer).

## (1) Quellen

Formel und Größen-Semantik wörtlich-gebunden: *m = ½·n(n+1)* (Lille S. 10, „Die Formel hat die
Gestalt"); *n* = Intervall-Nummer = Zahl der ontologischen Themen, End-Wertzahl = *m+n*
(S. 11, „so ergibt sich die gesuchte Wertzahl aus m + n"). Tafel IV: S. 8 f. („TAFEL IV"),
erläutert S. 9 („Die folgende Tafel IV veranschaulicht die ansteigende Skala der logischen
Systeme"). Ankerform: Seite und Wortlaut (Sammel-Vollzug 6; zuvor Zeilen der
Volltext-Datei, verschoben); Herkunft BCL-Report 3.0,
„Cybernetics and Transclassical Logic", 1965 (Fn. 2/5) — **Titel-Falle:** NICHT zu
verwechseln mit „Cybernetic Ontology and Transjunctional Operations", 1962 (Fn. 6).
„ein 14-wertiges System formaler Logik" (Lille S. 10). „nicht weniger als 36 Werte
und 8 ontologische Themen" — Marke: **druck-verifiziert (Beiträge III, S. 160;
Doppel-Abgleich 13. Juli)**. Alles Übrige Volltext-verifiziert (Härte-Ökonomie:
einmal geeicht, S. 160, verlängerbar).

## (2) SUBSTRAT-MARKE (prominent)

Diese Schicht ist **kein Differential**. Keine arme Klasse, keine
Unmöglichkeits-Hälfte, keine Zeugen-Fassung: das Rückgrat **zählt die Orte** der
achtfachen Thematik, **es deutet sie nicht**. Was hier term-fest wird, ist
ℕ-Arithmetik und sonst nichts; die Deutungs-Last liegt vollständig bei den
Stellen-Schichten, die dieses Substrat importieren.

## (3) HEGEL-RELATIVITÄTS-MARKE

Günthers „ernsthafte Zweifel" (Lille S. 17) und „nur relativ" (Lille S. 18) treffen
die **inhaltliche Zuordnung** der Hegel-Triaden zu den Intervallen — **nicht** die
hier gebaute Formel-Arithmetik. Die Zuordnungen selbst (Mechanik = II usw.) kommen
in den Stellen-Schichten, jede mit dieser Marke.

## (4) Term-fest werden hiermit

`two_mul_intervalStart` (Gauss-Brücke), `intervalStart_succ` (Stufungs-Gesetz),
`intervalEnd_succ_start` (Naht-Gesetz), `intervalEnd_sub_start` (Themen-Gesetz),
`tafel_IV`, `nature_closes_at_14`, `eighth_starts_at_36`, Kür
(`intervalStart_strictMono`). Dazu das `private` Hilfslemma `succ_mul_succ_succ`
(reine Aufspaltung des nichtlinearen Schritts; kein eigener Posten).

**Seit dem 23. September die Umkehrung** (nach `KorpusRev2/Spec_Wertzahl_Zerlegung.md`,
Fassung 2): `decomp` samt `decomp_succ`, `step`, `decomp_spec` (Gewährschein) und
`decomp_uniq` (Eindeutigkeit), dazu vier Eichwerte. `intervalStart` geht von der Themenzahl
zur Wertzahl, `decomp` zurück — **jede Wertzahl zerfällt in Themenzahl und Überschuss, und
auf genau eine Weise.**

## (4a) Die Umkehrung — was sie sagt und was nicht

`decomp m = (a, r)` heisst: `m = intervalStart a + r` mit `r ≤ a`. Die Rekursion ist der
Gang der Tafel — der Überschuss wächst je Wert um eins und fällt an der Naht auf null.

* **Sie löst `AT-1b` nicht ein.** Der Satz gilt an **jeder** Naht und zeichnet die siebte in
  nichts aus. Zwei Gründe, aus zwei Richtungen: gerechnet, weil die Aussage über **alle** `m`
  quantifiziert; quellenfest, weil das erste Thema nach Lille S. 19 „in allen folgenden
  Reflexionsstufen immer wieder" kehrt (Hermeneutes, S5-6).
* **Kein Günther-Name auf dieser Rechnung.** Nicht „Ur-Designation", nicht „Einwertigkeit",
  nicht „achte Stelle": Günthers Satz nennt das **Hinzukommende**, sein Name sitzt auf dem
  **Entstehenden** (S5-5); `decomp` zählt das Hinzukommende. Die Namen sagen darum die Sache.
* **Kein Rollenwechsel, keine Designation.** Dass eine Zahl designiert, weiss kein Satz des
  Hauses; **Designation ≠ Denotation** gilt fort.
* **Keine Ledger-Zeile, kein `§20`-Anspruch.**

**Die Erschöpfung** (seit dem 23. September, Bauauftrag des Mathematikers auf Entscheid
des Architekten vom 23.9.). `Exhausted m` heisst: der Überschuss hat die Themenzahl
erreicht. **Quellenanker, wörtlich und allgemein, ist Lille S. 9:** *„Ein Intervall endet
dort, wo die Zahl der designationsfreien Werte die Zahl der verfügbaren logischen Themen
erreicht hat. Die nächste wertreichere Struktur repräsentiert dann wieder eine Ontologie und
mit ihr beginnt das nächste Intervall."* Der erste Satz ist `Exhausted`, der zweite
`exhausted_seam`. **Den Namen gibt S. 19**, und zwar einem einzigen Fall: die achte
Thematik geht „aus der Erschöpfung der nicht-designativen Reflexion" hervor — das ist
`Exhausted 35`. „Erschöpfung" steht in Lille genau einmal (gemessen); nach Hermeneutes (H3)
ist es der einzige Übergang der achtfachen Thematik, dem Günther einen Begriff gibt. **Das
Wort auf alle Nähte zu übertragen, ist unsere Wahl** — Günther spricht den allgemeinen
Sachverhalt auf S. 9 ohne Namen aus. `exhausted_seam` **ist** der `else`-Zweig von `decomp_succ`, als Satz: an einer
erschöpften Wertzahl beginnt das nächste Intervall. `not_exhausted_step` ist sein
Gegenstück.

* **Es löst `AT-1b` nicht ein.** Günther setzt für das achte Thema zwei Bedingungen:
  Erschöpfung — hier gebaut — und Designativität, eine Werte-Semantik ausserhalb der
  Hausgrenze.
* **Es gilt an jeder Naht** und zeichnet die siebte nicht aus.
* **Der Name kommt von der Sache.** Kein „achte_stelle", kein „thanatos".
* **Der Bestand trägt Günthers Wort schon einmal:** `ExhaustionTransition.Exhausts`
  (neunzehnte Schicht) fasst die Erschöpfung als Iteration, die einen Fixpunkt erreicht und
  nicht zurückkehrt; `Exhausted` hier fasst sie als Überschuss, der die Themenzahl erreicht.
  **Die zwei Gestalten schliessen einander aus** — `ExhaustionTransition.decomp_never_exhausts`:
  der Gang von `decomp` hat keinen Fixpunkt und fällt darum nie unter `Exhausts`.

**Mathlib-Lage, gemessen:** die Dreiecks-Zerlegung steht dort **nicht**. `Nat.pair`/`unpair`
sind die **Quadrat**-Schale (`Nat.sqrt`), „Triangle" ist Kategorien- und Graphentheorie. Die
Analogie liegt dort, der Satz nicht — damit niemand ihn später sucht oder für zitierbar hält.

## (5) Bauform und Namen

Projekt-import-frei, unterste Schicht des Stellen-Trakts. „Wertzahl", „Thema",
„Intervall" sind **Namen** — Benennung ist kein Satz; term-fest ist die
ℕ-Arithmetik. Keine Werte-Semantik, keine Ophiten-Namen, keine Ablösungs- oder
Wiederholungs-Figur (benannte Posten). **Designation ≠ Denotation** gilt fort.

## (6) Sorry-Bilanz und Axiom-Ist

**0 Sorries.** Axiom-Ist (erster grüner Build, v4.30.0-rc2), bis zur Umkehrung zweigeteilt
exakt entlang der Beweis-Taktik — seit `exhausted_seam` **drei** Klassen, nachgezählt am
23. September über die 18 Wachen: 8 axiom-frei, 1 `[propext]`, 9 `[propext, Quot.sound]`.
Die ursprünglichen acht:

* **axiom-frei** (`decide`-Route): `tafel_IV`, `nature_closes_at_14`,
  `eighth_starts_at_36` — die drei Kern-Rechnungen der Tafel, kernel-ausgewertet.
* **`[propext, Quot.sound]`** (`omega`-Route): `two_mul_intervalStart`,
  `intervalStart_succ`, `intervalEnd_succ_start`, `intervalEnd_sub_start`,
  `intervalStart_strictMono`.

Die Umkehrung fügt sich ein: `decomp_succ` axiom-frei (`rfl`), `step`, `decomp_spec` und
`decomp_uniq` `[propext, Quot.sound]`, die vier Eichwerte **axiom-frei**. Zwei Bau-Hinweise,
beide gemessen und beide in den Beweisen sichtbar: die Eichungen tragen nur mit
`decide +kernel` — mit `decide` schlägt schon `m = 35` an die Rekursionsgrenze, und die
Grenze wird **nicht** heraufgesetzt (Fallstrick 5). Und **konjunktive Ziele werden vor
`omega` zerlegt**: `a ≤ b ∧ b ≤ a := by omega` trägt `Classical.choice`, dasselbe Ziel
zerlegt nicht (Fallstrick 7 in einer vierten Gestalt, gemessen 23. September).
`exhausted_seam` trägt `[propext]` — die dritte Klasse —, `not_exhausted_step`
`[propext, Quot.sound]`; beide schliessen mit offenem `simp`, im Modul gemessen wie in der
Probe (Fallstrick 21: das Profil hängt damit an der Importlage). Die Eichungen `Exhausted 35`,
`¬ Exhausted 34`, `Exhausted 65` stehen als `example` (beim Bau geprüft, kein eigener Satz).

**Hüllen-Vorsicht, hier belegt statt behauptet:** das Paar `[propext, Quot.sound]`
ist **Eigenschaft der `omega`-Hülle, nicht der Aussage** — nachgemessen an
`example (n : ℕ) : n + 0 = n := by omega`, das dasselbe Profil trägt. Es steht
also für gar keine Substanz; die Aussagen selbst sind reine ℕ-Arithmetik. Das ist
die von der Spec (M5/(6)) erwartete Lage („weitgehend axiom-frei, Rest propext"),
mit `Quot.sound` als nachgemessener Zugabe derselben Hülle.

**Abweichung, Verschärfung:** die Gauss-Brücke geht **nicht** die von der Spec
vorgezeichnete Mathlib-Route (`Nat.two_mul_div_two_of_even` ∘
`Nat.even_mul_succ_self`), sondern die dort als Fallback zugelassene Induktion
über `n`. Grund ist gemessen, nicht ästhetisch: die Mathlib-Route trägt
`Classical.choice` herein (Ist der ersten Fassung: `[propext, Classical.choice,
Quot.sound]`) und hätte es über alle vier Gesetze und die Kür weitergereicht. Die
Induktions-Route schneidet `Classical.choice` heraus **und** macht den Import
`Mathlib.Algebra.Group.Nat.Even` entbehrlich — die Schicht wird dadurch zugleich
axiom-ärmer und schmaler.

Wachen am Datei-Ende (Teil 6); sie sind Ist-gebunden auf genau diese Profile
gesetzt.
-/

namespace Reformulation.Proemial.IntervalBackbone

-- ============================================================
-- Teil 1 — Die Definitionen (M1)
-- ============================================================

/-- Anfangs-Wertzahl des n-ten Intervalls: m = n(n+1)/2 (Lille S. 10, End-Wertzahl S. 11;
    n = Intervall-Nummer = Zahl der ontologischen Themen). -/
def intervalStart (n : ℕ) : ℕ := n * (n + 1) / 2

/-- End-Wertzahl des n-ten Intervalls: m + n (Lille S. 11). -/
def intervalEnd (n : ℕ) : ℕ := intervalStart n + n

-- ============================================================
-- Teil 2 — Die Gauss-Brücke (M2)
-- ============================================================

/-- Das Aufspalt-Lemma der Dreieckszahl-Rekursion: die Nichtlinearität des
    Schritts, ein für alle Mal in `n * (n + 1)` zurückgeführt. Es macht die
    beiden sonst unverbundenen omega-Atome `n * (n + 1)` und `(n+1) * (n+2)`
    kommensurabel — ohne dieses Lemma scheitert jede omega-Route am Schritt. -/
private theorem succ_mul_succ_succ (n : ℕ) :
    (n + 1) * (n + 1 + 1) = n * (n + 1) + 2 * (n + 1) := by
  rw [Nat.succ_mul, Nat.mul_succ]
  omega

/-- GAUSS-IDENTITÄT (das Brücken-Lemma): zähmt die ℕ-Division ein für alle Mal —
    danach ist jede Rückgrat-Aussage linear und damit omega-fähig.

    Route: Induktion über `n` (Teil-0-Abweichung, Verschärfung — siehe
    Modul-Doc (6)); die Mathlib-Route über `Nat.two_mul_div_two_of_even` und
    `Nat.even_mul_succ_self` trüge `Classical.choice` herein. -/
theorem two_mul_intervalStart (n : ℕ) : 2 * intervalStart n = n * (n + 1) := by
  unfold intervalStart
  induction n with
  | zero => decide
  | succ n ih =>
    have h := succ_mul_succ_succ n
    omega

-- ============================================================
-- Teil 3 — Die drei Struktur-Gesetze (M3)
-- ============================================================

/-- STUFUNGS-GESETZ: jedes Intervall beginnt um seine eigene Themen-Zahl höher. -/
theorem intervalStart_succ (n : ℕ) :
    intervalStart (n + 1) = intervalStart n + (n + 1) := by
  have h1 := two_mul_intervalStart n
  have h2 := two_mul_intervalStart (n + 1)
  have h3 := succ_mul_succ_succ n
  omega

/-- NAHT-GESETZ: die Intervalle schließen lückenlos und überlappungsfrei
    aneinander — das Werte-Kontinuum der achtfachen Thematik als Theorem. -/
theorem intervalEnd_succ_start (n : ℕ) :
    intervalEnd n + 1 = intervalStart (n + 1) := by
  unfold intervalEnd
  rw [intervalStart_succ]
  omega

/-- THEMEN-GESETZ: Intervall-Nummer = Themen-Zahl = Länge des
    Wertzahl-Abschnitts (die Selbstbezüglichkeit der Formel). -/
theorem intervalEnd_sub_start (n : ℕ) : intervalEnd n - intervalStart n = n := by
  unfold intervalEnd
  omega

-- ============================================================
-- Teil 4 — Tafel IV und die Zitat-Anker (M4)
-- ============================================================

/-- TAFEL IV (Lille S. 8 f., erläutert S. 9; Herkunft: BCL-Report 3.0,
    „Cybernetics and Transclassical Logic", 1965 — Fn. 2/5; NICHT zu verwechseln
    mit „Cybernetic Ontology and Transjunctional Operations", 1962, Fn. 6):
    die acht Intervalle I–VIII mit Anfangs- und End-Wertzahl. -/
theorem tafel_IV :
    (List.range 8).map (fun k => (intervalStart (k + 1), intervalEnd (k + 1)))
      = [(1,2),(3,5),(6,9),(10,14),(15,20),(21,27),(28,35),(36,44)] := by
  decide

/-- „ein 14-wertiges System formaler Logik" (Lille S. 10): die
    Natur-Theorie schließt am Ende des vierten Intervalls. -/
theorem nature_closes_at_14 : intervalEnd 4 = 14 := by decide

/-- „nicht weniger als 36 Werte und 8 ontologische Themen" (Beiträge III,
    S. 160, DRUCK-VERIFIZIERT — Doppel-Abgleich 13. Juli): das achte Intervall
    beginnt bei 36. -/
theorem eighth_starts_at_36 : intervalStart 8 = 36 := by decide

-- ============================================================
-- Teil 5 — Kür (K1)
-- ============================================================

/-- KÜR: die Anfangs-Wertzahlen wachsen strikt — die achtfache Thematik hat
    eine wohlgeordnete Orts-Folge. -/
theorem intervalStart_strictMono : StrictMono intervalStart := by
  apply strictMono_nat_of_lt_succ
  intro n
  rw [intervalStart_succ]
  omega

-- ============================================================
-- Teil 5b — Die Umkehrung: jede Wertzahl zerfällt, und auf genau eine Weise
-- ============================================================

/-- Die **Zerlegung einer Wertzahl**: `.1` ist die Themenzahl, `.2` der Überschuss über
ihrem Intervall-Anfang. Die Rekursion ist der Gang der Tafel — der Überschuss wächst je
Wert um eins und fällt an der Naht auf null, wo er die Themenzahl erreicht hat. -/
def decomp : ℕ → ℕ × ℕ
  | 0 => (0, 0)
  | m + 1 =>
      if (decomp m).2 < (decomp m).1 then ((decomp m).1, (decomp m).2 + 1)
      else ((decomp m).1 + 1, 0)

/-- Die Nachfolger-Gleichung, ausgeschrieben. Ohne sie steht das `if` unter einem `match`,
das die Taktiken nicht sehen. -/
theorem decomp_succ (m : ℕ) :
    decomp (m + 1) =
      if (decomp m).2 < (decomp m).1 then ((decomp m).1, (decomp m).2 + 1)
      else ((decomp m).1 + 1, 0) := rfl

/-- Der Intervall-Schritt in additiver Form — sie macht `omega` über der ℕ-Division
arbeitsfähig. -/
theorem step (a : ℕ) : intervalStart (a + 1) = intervalStart a + a + 1 := by
  have h := intervalEnd_succ_start a
  simp only [intervalEnd] at h
  omega

/-- **Der Gewährschein**: `decomp` leistet, was ihr Name sagt — der Überschuss bleibt unter
der Themenzahl, und beide setzen die Wertzahl wieder zusammen. -/
theorem decomp_spec (m : ℕ) :
    (decomp m).2 ≤ (decomp m).1 ∧ m = intervalStart (decomp m).1 + (decomp m).2 := by
  induction m with
  | zero => exact ⟨le_refl 0, by decide⟩
  | succ m ih =>
    obtain ⟨hle, heq⟩ := ih
    rw [decomp_succ]
    by_cases h : (decomp m).2 < (decomp m).1
    · simp only [h, if_true]
      exact ⟨by omega, by omega⟩
    · simp only [h, if_false]
      have hs := step (decomp m).1
      exact ⟨by omega, by omega⟩

/-- **Die Eindeutigkeit**: es gibt keine zweite Zerlegung. Wer `m` anders als
`intervalStart k + j` mit `j ≤ k` schreibt, schreibt dieselben Zahlen. -/
theorem decomp_uniq (m k j : ℕ) (hjk : j ≤ k) (h : m = intervalStart k + j) :
    (decomp m).1 = k ∧ (decomp m).2 = j := by
  obtain ⟨hle, heq⟩ := decomp_spec m
  rcases lt_trichotomy (decomp m).1 k with hlt | heqk | hgt
  · have h1 : intervalStart (decomp m).1 + (decomp m).1 + 1 ≤ intervalStart k := by
      rw [← step]; exact (intervalStart_strictMono.le_iff_le).mpr hlt
    exact ⟨by omega, by omega⟩
  · subst heqk
    exact ⟨rfl, by omega⟩
  · have h1 : intervalStart k + k + 1 ≤ intervalStart (decomp m).1 := by
      rw [← step]; exact (intervalStart_strictMono.le_iff_le).mpr hgt
    exact ⟨by omega, by omega⟩

/-- **Erschöpft** ist eine Wertzahl, deren Überschuss die Themenzahl erreicht hat: „Ein
Intervall endet dort, wo die Zahl der designationsfreien Werte die Zahl der verfügbaren
logischen Themen erreicht hat" (Lille S. 9). Den Namen gibt S. 19 — „Erschöpfung der
nicht-designativen Reflexion" —, dort für den einen Fall `Exhausted 35`. -/
def Exhausted (m : ℕ) : Prop := (decomp m).2 = (decomp m).1

instance : DecidablePred Exhausted :=
  fun m => inferInstanceAs (Decidable ((decomp m).2 = (decomp m).1))

/-- **Die Naht**: an einer erschöpften Wertzahl beginnt das nächste Intervall. Der
`else`-Zweig von `decomp_succ`, als Satz. -/
theorem exhausted_seam (m : ℕ) (h : Exhausted m) :
    decomp (m + 1) = ((decomp m).1 + 1, 0) := by
  rw [decomp_succ]; simp only [Exhausted] at h; rw [h]; simp

/-- Ohne Erschöpfung wächst nur der Überschuss. -/
theorem not_exhausted_step (m : ℕ) (h : ¬ Exhausted m) :
    decomp (m + 1) = ((decomp m).1, (decomp m).2 + 1) := by
  have := (decomp_spec m).1
  rw [decomp_succ]; simp only [Exhausted] at h
  have hlt : (decomp m).2 < (decomp m).1 := lt_of_le_of_ne this h
  simp [hlt]

example : Exhausted 35 := by decide +kernel
example : ¬ Exhausted 34 := by decide +kernel
example : Exhausted 65 := by decide +kernel

/-- Eichung: Günthers Naht VII → VIII. `35 = intervalStart 7 + 7 = 28 + 7`. -/
theorem decomp_35 : decomp 35 = (7, 7) := by decide +kernel

/-- Eichung: die erste Ontologie des achten Intervalls. -/
theorem decomp_36 : decomp 36 = (8, 0) := by decide +kernel

/-- Eichung: die obere Grenze des zehnten Intervalls. -/
theorem decomp_65 : decomp 65 = (10, 10) := by decide +kernel

/-- Eichung: `intervalStart 11 = 66` — die 66-wertige Logik beginnt ein Intervall. -/
theorem decomp_66 : decomp 66 = (11, 0) := by decide +kernel

-- ============================================================
-- Teil 6 — Die `#guard_msgs`-Wachen (M6; Ist-gebunden)
-- ============================================================

-- Ist-Ausgabe des ersten grünen Builds (v4.30.0-rc2), pro Kern-Satz als Wache.
section

/-- info: 'Reformulation.Proemial.IntervalBackbone.two_mul_intervalStart' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms two_mul_intervalStart

/-- info: 'Reformulation.Proemial.IntervalBackbone.intervalStart_succ' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms intervalStart_succ

/-- info: 'Reformulation.Proemial.IntervalBackbone.intervalEnd_succ_start' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms intervalEnd_succ_start

/-- info: 'Reformulation.Proemial.IntervalBackbone.intervalEnd_sub_start' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms intervalEnd_sub_start

/-- info: 'Reformulation.Proemial.IntervalBackbone.tafel_IV' does not depend on any axioms -/
#guard_msgs in #print axioms tafel_IV

/-- info: 'Reformulation.Proemial.IntervalBackbone.nature_closes_at_14' does not depend on any axioms -/
#guard_msgs in #print axioms nature_closes_at_14

/-- info: 'Reformulation.Proemial.IntervalBackbone.eighth_starts_at_36' does not depend on any axioms -/
#guard_msgs in #print axioms eighth_starts_at_36

/-- info: 'Reformulation.Proemial.IntervalBackbone.intervalStart_strictMono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms intervalStart_strictMono

/-- info: 'Reformulation.Proemial.IntervalBackbone.decomp_succ' does not depend on any axioms -/
#guard_msgs in #print axioms decomp_succ

/-- info: 'Reformulation.Proemial.IntervalBackbone.step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms step

/-- info: 'Reformulation.Proemial.IntervalBackbone.decomp_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms decomp_spec

/-- info: 'Reformulation.Proemial.IntervalBackbone.decomp_uniq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms decomp_uniq

/-- info: 'Reformulation.Proemial.IntervalBackbone.decomp_35' does not depend on any axioms -/
#guard_msgs in #print axioms decomp_35

/-- info: 'Reformulation.Proemial.IntervalBackbone.decomp_36' does not depend on any axioms -/
#guard_msgs in #print axioms decomp_36

/-- info: 'Reformulation.Proemial.IntervalBackbone.decomp_65' does not depend on any axioms -/
#guard_msgs in #print axioms decomp_65

/-- info: 'Reformulation.Proemial.IntervalBackbone.decomp_66' does not depend on any axioms -/
#guard_msgs in #print axioms decomp_66

/-- info: 'Reformulation.Proemial.IntervalBackbone.exhausted_seam' depends on axioms: [propext] -/
#guard_msgs in #print axioms exhausted_seam

/-- info: 'Reformulation.Proemial.IntervalBackbone.not_exhausted_step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms not_exhausted_step

end

end Reformulation.Proemial.IntervalBackbone
