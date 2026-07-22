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

Formel und Größen-Semantik wörtlich-gebunden: *m = ½·n(n+1)* (Lille Z. 530);
*n* = Intervall-Nummer = Zahl der ontologischen Themen, End-Wertzahl = *m+n*
(Z. 544–547). Tafel IV: Z. 407 ff., erläutert Z. 436–455; Herkunft BCL-Report 3.0,
„Cybernetics and Transclassical Logic", 1965 (Fn. 2/5) — **Titel-Falle:** NICHT zu
verwechseln mit „Cybernetic Ontology and Transjunctional Operations", 1962 (Fn. 6).
„ein 14-wertiges System formaler Logik" (Z. 517–519). „nicht weniger als 36 Werte
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

Günthers „ernsthafte Zweifel" (Z. 921–922) und „nur relativ" (Z. 936–938) treffen
die **inhaltliche Zuordnung** der Hegel-Triaden zu den Intervallen — **nicht** die
hier gebaute Formel-Arithmetik. Die Zuordnungen selbst (Mechanik = II usw.) kommen
in den Stellen-Schichten, jede mit dieser Marke.

## (4) Term-fest werden hiermit

`two_mul_intervalStart` (Gauss-Brücke), `intervalStart_succ` (Stufungs-Gesetz),
`intervalEnd_succ_start` (Naht-Gesetz), `intervalEnd_sub_start` (Themen-Gesetz),
`tafel_IV`, `nature_closes_at_14`, `eighth_starts_at_36`, Kür
(`intervalStart_strictMono`). Dazu das `private` Hilfslemma `succ_mul_succ_succ`
(reine Aufspaltung des nichtlinearen Schritts; kein eigener Posten).

## (5) Bauform und Namen

Projekt-import-frei, unterste Schicht des Stellen-Trakts. „Wertzahl", „Thema",
„Intervall" sind **Namen** — Benennung ist kein Satz; term-fest ist die
ℕ-Arithmetik. Keine Werte-Semantik, keine Ophiten-Namen, keine Ablösungs- oder
Wiederholungs-Figur (benannte Posten). **Designation ≠ Denotation** gilt fort.

## (6) Sorry-Bilanz und Axiom-Ist

**0 Sorries.** Axiom-Ist (erster grüner Build, v4.30.0-rc2), zweigeteilt exakt
entlang der Beweis-Taktik:

* **axiom-frei** (`decide`-Route): `tafel_IV`, `nature_closes_at_14`,
  `eighth_starts_at_36` — die drei Kern-Rechnungen der Tafel, kernel-ausgewertet.
* **`[propext, Quot.sound]`** (`omega`-Route): `two_mul_intervalStart`,
  `intervalStart_succ`, `intervalEnd_succ_start`, `intervalEnd_sub_start`,
  `intervalStart_strictMono`.

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

/-- Anfangs-Wertzahl des n-ten Intervalls: m = n(n+1)/2 (Lille Z. 530, 544–547;
    n = Intervall-Nummer = Zahl der ontologischen Themen). -/
def intervalStart (n : ℕ) : ℕ := n * (n + 1) / 2

/-- End-Wertzahl des n-ten Intervalls: m + n (Lille Z. 544–547). -/
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

/-- TAFEL IV (Lille Z. 407 ff., erläutert Z. 436–455; Herkunft: BCL-Report 3.0,
    „Cybernetics and Transclassical Logic", 1965 — Fn. 2/5; NICHT zu verwechseln
    mit „Cybernetic Ontology and Transjunctional Operations", 1962, Fn. 6):
    die acht Intervalle I–VIII mit Anfangs- und End-Wertzahl. -/
theorem tafel_IV :
    (List.range 8).map (fun k => (intervalStart (k + 1), intervalEnd (k + 1)))
      = [(1,2),(3,5),(6,9),(10,14),(15,20),(21,27),(28,35),(36,44)] := by
  decide

/-- „ein 14-wertiges System formaler Logik" (Lille Z. 517–519): die
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

end

end Reformulation.Proemial.IntervalBackbone
