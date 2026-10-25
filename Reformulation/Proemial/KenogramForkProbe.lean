import Reformulation.Kenogram.Descent                 -- extend, descent, descent_extend
import Reformulation.Proemial.TowerAsymmetryProbe     -- Tower, step, ascent_not_determined

/-!
# Proemial.KenogramForkProbe — die Gabelung als Faser, die Spur als Präfix

STANDALONE, NICHT im Aggregat (konsumiert `TowerAsymmetryProbe`, standalone). AxiomGate
unberührt. Sonde nach `KorpusRev2/Sondierung_Proemial_Auf_Ab_Turm_Prompt.md` (Mathematiker,
13. Oktober 2026, auf Anordnung des Architekten); Vorbild `TowerAsymmetryProbe`.

## Die Frage

Der Turm `Tower = Σ n, RGS n` hat drei bewiesene Merkmale (`tower_asymmetric`): `step` ist
rückkehrfrei, das Alte bleibt Präfix, und über jedem `r : RGS n` mit `n ≥ 1` liegen zwei
verschiedene zulässige Fortsetzungen. Diese Sonde fragt nach der **Gabelung** — der Menge
der zulässigen Fortsetzungen eines RGS — und beweist drei Sätze über sie:

- **(a)** Die Gabelung ist vom Präfix bestimmt (`forkWidth_eq`, `forkWidth_of_nil`): ihre
  Weite ist das Präfix-Maximum plus zwei, über der leeren Folge eins.
- **(b)** Der gewählte Schritt bestimmt die nächste Gabelung (`forkWidth_extend`): wer
  wiederholt, lässt die Weite, wie sie ist; wer neu setzt, weitet sie um genau eins.
- **(c)** Die Wahl selbst ist durch nichts im Präfix bestimmt (`choice_undetermined`, aus
  `ascent_not_determined`): ab Stufe 1 ist die Faser nie einelementig.

Und `mem_fork_iff`: die Gabelung IST die Faser von `descent` über `r` — jeder Zweig
descendiert auf dieselbe Spur. Alles sind Sätze über `extend`, `descent` und die
Zulässigkeit; keine Deutung.

## Was die Sonde NICHT tut (Prompt §0)

- Sie definiert **keine zweite Negation** und führt keinen Bezeichner dieses Namens ein.
  L07-4 bleibt offen (`NegationCycle` Teil 6, (a)).
- Sie vermengt **nicht** die Werteebene (N₂ in `NegatorContexture`, `NegationCycle`) mit
  der Turmebene. Günther 1970 hält beides getrennt (Edition S. 13, nach dem Prompt: erste
  Negation intra-kontexturell, zweite Negation = Stufenwechsel).
- Sie behauptet **nichts über die Volition**. C&V S. 23 (nach dem Prompt) nennt den
  Übergang vom Kalkül der Kognition zum Kalkül der Volition eine Umkehrung der *Deutung*
  desselben Algorithmus. Eine Deutung ist kein Term; sie wird hier weder gebaut noch als
  `True`-Feld geführt.
- Jedes Ergebnis ist **ZUORDNUNG**, nicht Satz über Günthers Text (§5 unten).

## Der Träger der Gabelung: eine Liste, kein `Finset` (Abweichung vom Prompt, mit Grund)

Der Prompt schreibt `Fork r : Finset ℕ` über `Finset.range` und `Finset.filter`. Gemessen
am 13. Oktober 2026 (Mathlib 83a5988): `Finset.range` trägt
`[propext, Classical.choice, Quot.sound]` — über `List.nodup_range` (CLAUDE.md §8,
Fallstrick 10, zweite Verschärfung). Der Prompt erwartet `[propext, Quot.sound]` und
„kein `Classical.choice` nötig" (§7). Darum ist `Fork r` hier eine **Liste**:
`(List.range (M + 2)).filter (zulässig)` mit `M = r.val.foldr max 0`, und `forkWidth` ihre
Länge. `List.range` und `List.filter` sind Kern; `List.mem_range`, `List.mem_filter`,
`List.filter_eq_self`, `List.length_range` tragen höchstens `[propext, Quot.sound]`
(gemessen). Die Sätze F1–F5 sind dieselben wie im Prompt; nur das Wort `Finset` fehlt.
Die Liste ist duplikatfrei (`List.range` ist es, `filter` erhält es), also ist die Länge
die Mächtigkeit — das wird hier nicht bewiesen, weil kein Satz es braucht.

## Marken

- F1 `mem_fork_iff`, F2 `forkWidth_eq` / `forkWidth_of_nil` / `forkWidth_nil`,
  F3 `forkWidth_extend`: **UNSER**, Mathematik über `extend`/`descent`.
- F4 `choice_undetermined`: **WIEDERVERWENDUNG** (`ascent_not_determined`, nur Verweis).
- F5 `descent_step`, `stepNew`, `descent_stepNew`, `stepNew_ne_step`: **WIEDERVERWENDUNG**
  (`descent_extend`), aktenkundig gemacht.
- §VII `Choice`, `ascentBy`, `ascentBy_noreturn`, `ascentBy_preserves_substructure`,
  `step_eq_ascentBy_zero` (Folgezug 13.10.): **UNSER** als Sätze, **ZUORDNUNG** als Lesart
  (Richtung und Substruktur sind Eigenschaften des Gehens, nicht der Wahl).
- §5: **ZUORDNUNG**. §6: **MESSUNG**.

## F5 — `step` ist eine Wahl, keine Notwendigkeit

`step` wählt stets die Stelle `0`. Über einer nichtleeren Kette ist das „wiederholen" (die
`0` steht schon an der Spitze); über der leeren Kette ist nur `0` zulässig (`forkWidth_of_nil`),
und dort ist `0` zugleich „neu setzen". `descent_step` zeigt: `step` ist ein Schnitt von `descent` auf
der Stufenkomponente. `stepNew` ist der zweite Schnitt, „neu setzen" (`M + 1`), und
`stepNew_ne_step` zeigt, dass er vom ersten verschieden ist.

**Abweichung vom Prompt, mit Grund:** `stepNew` ist nur über **nichtleeren** Ketten
definiert (ein Beweisargument `h : x.2.val ≠ []`). Über der leeren Folge ist `M + 1 = 1`
nicht zulässig (`h0` verlangt dort `0`); die Gabelung hat Weite 1 (`forkWidth_of_nil`), und
einen zweiten Schnitt gibt es dort nicht. Das ist derselbe Befund wie F4: ab Stufe 1 gibt
es die Wahl, auf Stufe 0 nicht. Die Totalisierung in `TowerAsymmetryProbe` („stets `0`")
ist eine Setzung des Bestandes, kein Satz; das steht dort im Kopf und wird hier nur
aktenkundig.

## §5 — Was die Sonde messen soll, aber nicht beweisen kann (ZUORDNUNG)

C&V S. 20 (nach dem Prompt) gibt die Proemialrelation als zwei Bewegungen: Relator wird
Relatum, nur relativ zu höherer Ordnung; Relatum wird Relator, nur relativ zu niedrigerer.
Günther 1970 S. 12 (nach dem Prompt): ein Glied wird zu dem Umtausch in Beziehung gesetzt,
in dem es selbst steht; das Paar ist geordnet, weil seine Seiten verschiedener Art sind.

Die Zuordnung lautet: `extend` als „Relatum wird Relator" (das Gewählte ordnet fortan),
`descent` als „Relator wird Relatum" (die Spur wird Gegenstand) — eine ROLLEN-Lesart:
„Relatum wird Relator" für `extend` ist nur in der Rolle getragen („elevated", C&V S. 20).
Das ist eine Lesart der Felder `ascent`/`descent` in `AsymmetricDiscontexturalTransition`,
deren Feld-Docstring seit dem 25.10. K-1 nennt (unten). **Diese Sonde bestätigt oder
verwirft die Beschriftung nicht.** Entschieden hat es die Quelle (K-1). Sie stellt fest, welche der drei Eigenschaften (a)–(c) bewiesen
sind — alle drei, siehe oben —, und dass die Gabelung unter `descent` symmetrisch ist
(`mem_fork_iff`: alle Zweige fallen auf dieselbe Spur; von der Spur her sind sie
ununterscheidbar). Ob das Günthers „was in einem gegebenen Objektivzusammenhang symmetrisch
ist" (1970, S. 11, nach dem Prompt; nicht am Bild geprüft) **ist**, sagt kein Satz. Ebenso
ist der Satz des Prompts, die Gabelung sei „vom Gegangenen bestimmt" (zu Kaehrs Labyrinth,
im Prompt ohne Seite), eine Lesart von F2, keine Folgerung aus ihr.

**K-1 (entschieden 24.10.2026;  Hermeneutes am Bild;  Register K-1, PL27/PL28).** Günther hat
zwei „oben":  auf der Achse der logischen Ordnung geht **Relator → Relatum** nach oben (C&V
S. 23;  Formeln S. 20 f.;  Atom/Molekül S. 21;  EuW S. 26, 29);  in der **Rolle** steigt das
Relatum („elevated", C&V S. 20).  „Relatum → Relator" ist auf der Achse der logischen Ordnung
NICHT getragen, nur am Rollen-Wort.  Definitionen §20 („Formaler Ausdruck") führt die Richtung:
„Relator wird Relatum → R_{i+2}(x_{i+1}, y_{i+1})".  Die Lesart oben (`extend` als „Relatum wird
Relator") gilt darum nur für die Rolle.  Vermerk:  Bis 25.10. stand hier, der Kopf von
`AsymmetricDiscontexturalTransition` trage die Beschriftung „(Relatum → Relator)";  nachgeführt
nach K-1.

## §6 — Ebenen-Trennung (MESSUNG, kein Satz dieser Sonde)

`Kenogram.PatternInvariance` sagt: die Negation ändert das Morphogramm nie. Daraus folgt
für die Werteebene: N₂ berührt `Fork`, `extend`, `descent` (Kenogrammebene) nicht — die
Gabelung ist eine Eigenschaft der Spur, nicht der Werte darauf. Die Sonde zitiert den
Satz und zieht die Folgerung hier; sie baut keine Brücke. Ob die zweite Negation
„Kontexturwechsel = Stufenwechsel" ist, bleibt das `True`-Feld `contextureCrossing` —
unverändert.

Kein `sorry`, kein `native_decide`, kein `: True`-Feld, kein `axiom`.
-/

namespace Reformulation.Proemial.KenogramForkProbe

open Reformulation.Kenogram
open Reformulation.Proemial.TowerAsymmetryProbe (Tower step ascent_not_determined)

-- ============================================================
-- §I — Die Gabelung und ihre Weite
-- ============================================================

/-- **Die Gabelung über `r`:** die zulässigen Stellen für den nächsten Schritt, als Liste.
Zulässig ist `k` genau nach `extend` (K-3, Basic.lean: „wiederholen oder neu setzen"):
`k ≤ M + 1` mit `M = r.val.foldr max 0`, und über der leeren Folge nur `0`. Die erste
Bedingung ist der Bereich `List.range (M + 2)`, die zweite der Filter. -/
def Fork {n : ℕ} (r : RGS n) : List ℕ :=
  (List.range (r.val.foldr max 0 + 2)).filter (fun k => decide (r.val = [] → k = 0))

/-- **Die Weite der Gabelung:** die Zahl der zulässigen Fortsetzungen. -/
def forkWidth {n : ℕ} (r : RGS n) : ℕ := (Fork r).length

-- ============================================================
-- §II — F1: Die Gabelung ist Faser über der Spur
-- ============================================================

/-- **F1.** `k` liegt in der Gabelung genau dann, wenn `k` zulässig ist und der Schritt
`extend r k` auf `r` descendiert. Richtung ←: Zulässigkeit aus der Mitgliedschaft. Richtung
→: `descent_extend`. Gehalt: *alle* Zweige der Gabelung descendieren auf dieselbe Spur. -/
theorem mem_fork_iff {n : ℕ} (r : RGS n) (k : ℕ) :
    k ∈ Fork r ↔ ∃ (hk : k ≤ r.val.foldr max 0 + 1) (h0 : r.val = [] → k = 0),
      descent (extend r k hk h0) = r := by
  unfold Fork
  rw [List.mem_filter, List.mem_range, decide_eq_true_iff]
  constructor
  · rintro ⟨hlt, h0⟩
    exact ⟨Nat.lt_succ_iff.mp hlt, h0, descent_extend r k _ h0⟩
  · rintro ⟨hk, h0, -⟩
    exact ⟨Nat.lt_succ_of_le hk, h0⟩

-- ============================================================
-- §III — F2: Die Weite hängt nur vom Präfix-Maximum ab
-- ============================================================

/-- **F2, nichtleer.** Über einer nichtleeren Kette ist der Filter leer: jede Stelle bis
`M + 1` ist zulässig, die Weite ist `M + 2`. -/
theorem forkWidth_eq {n : ℕ} (r : RGS n) (hne : r.val ≠ []) :
    forkWidth r = r.val.foldr max 0 + 2 := by
  unfold forkWidth Fork
  rw [List.filter_eq_self.mpr, List.length_range]
  intro k _
  exact decide_eq_true (fun h => absurd h hne)

/-- **F2, leer, allgemein.** Über der leeren Kette ist nur `0` zulässig: Weite 1. -/
theorem forkWidth_of_nil {n : ℕ} (r : RGS n) (hnil : r.val = []) : forkWidth r = 1 := by
  unfold forkWidth Fork
  rw [hnil]
  decide

/-- **F2, leer, am Zeugen** (Wortlaut des Prompts). -/
theorem forkWidth_nil : forkWidth (⟨[], by decide⟩ : RGS 0) = 1 :=
  forkWidth_of_nil _ rfl

-- ============================================================
-- §IV — F3: Der Schritt bestimmt die nächste Gabelung
-- ============================================================

/-- **F3.** Die Weite nach dem Schritt `extend r k`: unverändert, wenn `k` wiederholt;
um eins weiter, wenn `k` neu setzt (`k = M + 1`); und über der leeren Kette um eins weiter,
weil dort die Weite 1 war und `[0]` die Weite 2 hat. **Der Satz, den die Sonde neu
beiträgt.** Vorprobe (Python, alle RGS bis `n = 8`, Mathematiker): stimmt. -/
theorem forkWidth_extend {n : ℕ} (r : RGS n) (k : ℕ) (hk : k ≤ r.val.foldr max 0 + 1)
    (h0 : r.val = [] → k = 0) :
    forkWidth (extend r k hk h0) =
      forkWidth r + (if k = r.val.foldr max 0 + 1 then 1 else 0)
        + (if r.val = [] then 1 else 0) := by
  have hne : (extend r k hk h0).val ≠ [] := by
    show r.val ++ [k] ≠ []
    exact List.append_ne_nil_of_right_ne_nil _ (List.cons_ne_nil k [])
  rw [forkWidth_eq _ hne]
  show (r.val ++ [k]).foldr max 0 + 2 = _
  rw [foldr_max_append_singleton]
  rcases instDecidableEqList r.val [] with hnil | hnil
  · -- nichtleer: kein Randterm; die Weite wächst genau mit „neu setzen"
    rw [forkWidth_eq r hnil, if_neg hnil]
    rcases Nat.decEq k (r.val.foldr max 0 + 1) with h | h
    · have hkM : k ≤ r.val.foldr max 0 := Nat.lt_succ_iff.mp (Nat.lt_of_le_of_ne hk h)
      rw [Nat.max_eq_left hkM, if_neg h]
    · subst h
      rw [Nat.max_eq_right (Nat.le_succ _), if_pos rfl]
  · -- leer: `k = 0`, die Weite geht von 1 auf 2
    have hk0 := h0 hnil
    subst hk0
    rw [forkWidth_of_nil r hnil, hnil]
    decide

-- ============================================================
-- §V — F4: Die Wahl ist durch nichts im Präfix bestimmt (Wiederverwendung)
-- ============================================================

/-- **F4.** Nur Verweis auf `ascent_not_determined`: ab Stufe 1 liegen über jedem `r` zwei
verschiedene Urbilder. Mit F1 gelesen: die Faser ist die Gabelung, und sie ist ab Stufe 1
nie einelementig (F2 sagt es direkt: `M + 2 ≥ 2`). Der Satz steht über
`Kenogram.descent`; der Verweis trägt, weil `A1DescentProbe.descent` damit definitional
gleich ist (geprüft per `rfl`). -/
theorem choice_undetermined {n : ℕ} (hn : 1 ≤ n) (r : RGS n) :
    ∃ a b : RGS (n + 1), a ≠ b ∧ descent a = r ∧ descent b = r :=
  ascent_not_determined hn r

-- ============================================================
-- §VI — F5: `step` ist eine Wahl, keine Notwendigkeit (Wiederverwendung)
-- ============================================================

/-- **F5 (i).** `step` ist ein Schnitt von `descent` auf der Stufenkomponente. -/
theorem descent_step (x : Tower) : descent (step x).2 = x.2 :=
  descent_extend x.2 0 (Nat.zero_le _) (fun _ => rfl)

/-- **Der zweite Schnitt, „neu setzen":** hänge `M + 1` an. Nur über nichtleeren Ketten
definiert — über der leeren ist `1` nicht zulässig, siehe Dateikopf. -/
def stepNew (x : Tower) (h : x.2.val ≠ []) : Tower :=
  ⟨x.1 + 1, extend x.2 (x.2.val.foldr max 0 + 1) (Nat.le_refl _) (fun hnil => absurd hnil h)⟩

/-- **F5 (ii).** Auch `stepNew` ist ein Schnitt von `descent`. -/
theorem descent_stepNew (x : Tower) (h : x.2.val ≠ []) : descent (stepNew x h).2 = x.2 :=
  descent_extend x.2 _ (Nat.le_refl _) (fun hnil => absurd hnil h)

/-- **F5 (iii).** Die zwei Schnitte sind verschieden: das letzte Zeichen ist `M + 1` gegen
`0`. Damit ist die Totalisierung „stets `0`" in `TowerAsymmetryProbe` eine Wahl. -/
theorem stepNew_ne_step (x : Tower) (h : x.2.val ≠ []) : (stepNew x h).2 ≠ (step x).2 := by
  intro heq
  have hval : x.2.val ++ [x.2.val.foldr max 0 + 1] = x.2.val ++ [0] :=
    congrArg Subtype.val heq
  have h2 := List.append_cancel_left hval
  injection h2 with h3
  exact Nat.succ_ne_zero _ h3

-- ============================================================
-- §VII — Hängt etwas am Esel? Richtung und Substruktur für JEDE Wahlregel
-- ============================================================

/-! **Folgezug** (`KorpusRev2/Prompt_Folgezug_Esel_Abhaengigkeit.md`, Mathematiker, 13. Oktober
2026). Gemessen: kein Beweis des Bestandes hängt an der festen Wahl `0` in `step`
(`TowerAsymmetryProbe`, `TowerAsymmetry`); Merkmal 1 geht über den Rang `Sigma.fst`, der bei
jedem `extend` steigt, Merkmal 2 über `List.prefix_append`, das für jedes angehängte `[k]`
gilt. Nur die **Totalität** von `step` braucht eine feste Stelle, und über der leeren Folge
ist allein `0` zulässig (`forkWidth_of_nil`). Die drei Sätze hier machen das aktenkundig: Richtung
und Substruktur gelten für **jede** Wahlregel, und `step` ist der Sonderfall der konstanten
Wahl `0`. **ZUORDNUNG:** Richtung und Substruktur sind Eigenschaften des Gehens, nicht der
Wahl; der Esel (`step`) ist ein Sonderfall, kein Träger. `AsymmetricDiscontexturalTransition`
bleibt unberührt. -/

open Reformulation.Proemial.IrreversibleAdvance (NoReturn noreturn_of_strict_rank)

/-- **Eine Wahlregel:** zu jedem Turmpunkt eine zulässige Stelle. (Der Name steht im eigenen
Namensraum; der Bestand führt `Choice` sonst nirgends, Lean nur
`Lean.Meta.Grind.EMatch.Choice`, mit anderer Bedeutung.) -/
def Choice : Type :=
  (x : Tower) → {k : ℕ // k ≤ x.2.val.foldr max 0 + 1 ∧ (x.2.val = [] → k = 0)}

/-- **Der Aufstieg nach einer beliebigen Wahlregel.** -/
def ascentBy (c : Choice) : Tower → Tower :=
  fun x => ⟨x.1 + 1, extend x.2 (c x).1 (c x).2.1 (c x).2.2⟩

/-- **Merkmal 1 für JEDE Wahlregel:** der Rang steigt, also keine Rückkehr. Derselbe Beweis
wie `step_noreturn`; `k` kommt darin nicht vor. -/
theorem ascentBy_noreturn (c : Choice) : NoReturn (ascentBy c) :=
  noreturn_of_strict_rank (fun x => x.1) (fun x => Nat.lt_succ_self x.1)

/-- **Merkmal 2 für JEDE Wahlregel:** die alte Kette bleibt Präfix. `List.prefix_append`,
für jedes angehängte `[k]`. -/
theorem ascentBy_preserves_substructure (c : Choice) (x : Tower) :
    x.2.val <+: (ascentBy c x).2.val :=
  List.prefix_append x.2.val [(c x).1]

/-- **`step` ist der Sonderfall der konstanten Wahl `0`.** Definitional. -/
theorem step_eq_ascentBy_zero :
    step = ascentBy (fun _ => ⟨0, Nat.zero_le _, fun _ => rfl⟩) :=
  rfl


-- ============================================================
-- Wachen — Axiom-Profile
-- ============================================================

/-! **Wachen.** Ist-Ausgabe des grünen Builds (v4.30.0-rc2), pro Deklaration eingefroren,
alle siebzehn (Datei-Vollständigkeit; zwölf der Sonde, fünf des Folgezugs §VII). Kein `Classical.choice`: die Gabelung ist eine Liste,
nicht ein `Finset` über `Finset.range` — siehe Dateikopf. -/

/-- info: 'Reformulation.Proemial.KenogramForkProbe.Fork' does not depend on any axioms -/
#guard_msgs in #print axioms Fork

/-- info: 'Reformulation.Proemial.KenogramForkProbe.forkWidth' does not depend on any axioms -/
#guard_msgs in #print axioms forkWidth

/-- info: 'Reformulation.Proemial.KenogramForkProbe.mem_fork_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms mem_fork_iff

/-- info: 'Reformulation.Proemial.KenogramForkProbe.forkWidth_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms forkWidth_eq

/-- info: 'Reformulation.Proemial.KenogramForkProbe.forkWidth_of_nil' does not depend on any axioms -/
#guard_msgs in #print axioms forkWidth_of_nil

/-- info: 'Reformulation.Proemial.KenogramForkProbe.forkWidth_nil' does not depend on any axioms -/
#guard_msgs in #print axioms forkWidth_nil

/-- info: 'Reformulation.Proemial.KenogramForkProbe.forkWidth_extend' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms forkWidth_extend

/-- info: 'Reformulation.Proemial.KenogramForkProbe.choice_undetermined' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms choice_undetermined

/-- info: 'Reformulation.Proemial.KenogramForkProbe.descent_step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms descent_step

/-- info: 'Reformulation.Proemial.KenogramForkProbe.stepNew' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms stepNew

/-- info: 'Reformulation.Proemial.KenogramForkProbe.descent_stepNew' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms descent_stepNew

/-- info: 'Reformulation.Proemial.KenogramForkProbe.stepNew_ne_step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms stepNew_ne_step
/-! Wachen des Folgezugs (§VII), gemessen 13. Oktober 2026. -/

/-- info: 'Reformulation.Proemial.KenogramForkProbe.Choice' does not depend on any axioms -/
#guard_msgs in #print axioms Choice

/-- info: 'Reformulation.Proemial.KenogramForkProbe.ascentBy' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ascentBy

/-- info: 'Reformulation.Proemial.KenogramForkProbe.ascentBy_noreturn' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ascentBy_noreturn

/-- info: 'Reformulation.Proemial.KenogramForkProbe.ascentBy_preserves_substructure' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ascentBy_preserves_substructure

/-- info: 'Reformulation.Proemial.KenogramForkProbe.step_eq_ascentBy_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms step_eq_ascentBy_zero
end Reformulation.Proemial.KenogramForkProbe
