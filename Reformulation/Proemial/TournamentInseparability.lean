import Mathlib.Data.Set.Defs
import Mathlib.Data.Fin.VecNotation

/-!
# Proemial.TournamentInseparability — keine Relation trennt die zyklischen Turniere von den transitiven (C2)

**ERTRAG**, gebaut nach `KorpusRev2/Spec_C2_Unmoeglichkeitssatz.md` (Anker `7a34864`),
Grundlage `KorpusRev2/C2_Klaerung_Unmoeglichkeitssatz.md`.
Die Kennung **C2** ist die der Registrierung vom 12. September auf der Turnier-Achse —
nicht der Buildabdeckungs-Zug C2, unter dem README und `lakefile.toml` dieselbe Kennung
führen.

Auf `Fin 3` gibt es acht lokal-klassische Operationen: auf jeder der drei
Elementarkontexturen `{0,1}`, `{1,2}`, `{0,2}` die Wahl von `min` oder `max`. Jede bestimmt
ein Turnier — `x` schlägt `y`, wenn `x ≠ y` und `o x y = x`. Sechs dieser Turniere sind
transitiv, zwei zyklisch (`transitive_iff`). Der Zielsatz `no_relation_separates`:

> **Erhält eine Relation `R` alle sechs transitiven Operationen, so erhält sie alle acht.**

Die Kontraposition ist die Aussage, um die es geht: keine Relation erhält die sechs und
verletzt auch nur eine der zwei. `R` ist dabei eine Relation **beliebiger Stelligkeit** —
eine Menge von Funktionen `ι → Fin 3` über einem beliebigen Indextyp `ι`; der binäre Fall
ist `ι = Fin 2`.

## Der Beweis, und wo seine Substanz liegt

Zwei Gleichungen und eine Einsetzung, **kein Klon-Begriff**:

* `kkd_eq` — `KKD x y = KKK (KDD x y) (DKD x y)`
* `ddk_eq` — `DDK x y = KDK (DKK x y) (DDD x y)`
* `preserves_comp` — erhält `R` die Operationen `f`, `g`, `h`, so auch
  `fun x y => f (g x y) (h x y)`.

Alle sechs Operationen rechts sind transitiv. **`no_relation_separates` selbst ist als
Einsetzung trivial; die Substanz liegt in den zwei Gleichungen** — dass beide zyklischen
Operationen schon in Tiefe eins aus transitiven entstehen. Wer den Zielsatz zitiert,
zitiert eine Folgerung dieser zwei Rechnungen.

## Was davon bei Günther steht — und was nicht

*Nachgetragen am 16. September 2026 (Berichtigung `C2_steht_bei_Guenther_Berichtigung.md`).*
Gelesen in *Cognition and Volition*, `KorpusRev1/c_and_v.pdf`, Prüfsumme wie im
Quellenanker `Quellenanker_CognitionAndVolition.md`; für S. 24–28 ist die PDF-Seite gegen
die gedruckte Kopfzeile geprüft und gleich.

* **`kkd_eq` formalisiert eine Quellenaussage.** C&V S. 28: *„p KKD q = (p DKD q) KKK
  (p KDD q)"*, dazu *„purely hierarchical orders of values can be used to produce the
  cyclic arrangement"*. Die Tiefe-eins-Darstellung ist eine **Wiederentdeckung**, keine
  eigene Rechnung.
* **`transitive_iff` ist inhaltsgleich mit Günthers Kriterium**, C&V S. 28: zyklisch
  *„when and only when the two values which are not immediate successors are connected
  by a different functor"* als die beiden übrigen Zweiersysteme. Günther spricht von der
  zyklischen Wertordnung, der Satz von der Transitivität des Turniers; auf drei Knoten
  ist das dasselbe, im Wortlaut nicht.
* **`ddk_eq` ist eine andere Zerlegung** als Günthers zweite Formel
  *„p DDK q = (p DKK q) DDD (p KDK q)"* — unter jeder der zwei Wertzuordnungen unten.
* **Der Zielsatz steht nicht bei Günther.** Die Erhaltung von Relationen ist kein Begriff
  von C&V; `no_relation_separates` ist eine Folgerung in einem Begriff, den er nicht
  gebraucht.

**Die Konvention hängt an der Wertzuordnung.** Günther schreibt die Werte `1, 2, 3` mit
`1` als positivem Wert; seine Konjunktion K wählt darum den **höchsten** Wert (Fig. 7–14).
Hier ist K = `min` auf `0, 1, 2`. Welche Buchstaben einander entsprechen, entscheidet die
Zuordnung der Werte, und es gibt zwei naheliegende — außerhalb des Korpus über alle acht
Muster gerechnet (Python), nicht als Satz geführt:

* **Spiegelung `x ↦ 3 − x`:** K bleibt Konjunktion. `KKK`, `KKD`, `DDK`, `DDD` behalten
  ihre Namen, `KDD ↔ DKD` und `KDK ↔ DKK` tauschen (die Kontexturen `{0,1}` und `{1,2}`
  wechseln die Stelle). `kkd_eq` ist darunter Günthers **erste** Formel mit denselben
  Buchstaben.
* **Verschiebung `x ↦ x + 1`:** K und D tauschen durchweg, `KKD ↔ DDK`. `kkd_eq` ist
  darunter Günthers **zweite** Formel.

Unter beiden Zuordnungen ist das zyklische Paar `{KKD, DDK}` dasselbe.

## Was dieses Modul NICHT sagt

* **Nicht, dass Günthers Präferenzmuster Turniere SIND — im Wort.** Die Gleichsetzung
  heterarchisch/zyklisch ist **Günthers eigene** (*„heterarchical (or cyclic)"*, C&V
  S. 27), und seine Präferenz je Zweiersystem zeichnet er als Pfeile (Fig. 15/16, *„The
  arrows always point to the preferred number"*). Lesart bleibt das **Wort** „Turnier" und
  jede Aussage für eine andere Wertezahl als drei; Günther rechnet nur mit drei Werten.
* **Nicht die Klon-Schranke.** Dass Operationen aus `{min, max, neg}` nicht erzeugbar
  sind, ist eine andere Aussage und steht unabhängig (E1, `NonUniformCloneBound`).
  Nicht-Erzeugbarkeit und Nicht-Trennbarkeit sind verschiedene Aussagen; dieses Modul
  importiert die E-Reihe nicht.
* **Nicht, dass die zwei zyklischen ununterscheidbar wären.** Turnier-Zyklizität
  unterscheidet sie (`transitive_iff`) — sie ist nur keine **Erhaltungs**eigenschaft.
* **Keine Ledger-Zeile** für Paragraph 20; C2 gehört zur Turnier- und Klon-Achse.

## Bauform und Axiomprofil

`localOp d01 d12 d02` kodiert die Wahl je Kontextur als Bit, `true` = `max` (D),
`false` = `min` (K), Reihenfolge `{0,1}`, `{1,2}`, `{0,2}` — K = `min` in **dieser**
Fassung, zur Übersetzung in Günthers Buchstaben siehe oben. Das ist die Bit-Konvention von
`NonUniformCloneBound.ofChoices`; die Gleichheit beider Definitionen ist **hier nicht
bewiesen**, weil das Modul die E-Reihe nicht importiert. Die eigene Definition hat einen
gemessenen Grund: dieselbe Gleichung `kkd_eq` über `ofChoices` trägt `[propext]` (dort
entscheidet `decide` über `Prop`-Disjunktionen), über der verschachtelten
Bool-Fallunterscheidung hier ist sie **axiomfrei**. Aus demselben Grund ist `min`/`max`
nicht Mathlibs `Fin`-Ordnung, sondern ein Vergleich an `.val`.

Profile, gemessen und am Dateiende gewacht:

* `kkd_eq`, `ddk_eq`, `transitive_iff`, `preserves_comp` — axiomfrei.
* `no_relation_separates` — `[Quot.sound]`, **in der Sache begründet**: `R` ist eine
  Menge von Funktionen, und die punktweisen Gleichungen werden über `funext` auf die
  Mitgliedschaft gehoben (`preserves_congr`). Kein `Classical.choice`, kein `propext`.
* `witnessRel_preserves_pointwise_iff` — axiomfrei; `witnessRel_preserves_iff` —
  `[propext]`, und das trägt schon die Mengen-Definition `witnessRel` selbst (gemessen an
  der Definition allein; ein Beweis ohne `rw` ändert daran nichts).

Die Nicht-Leere des Zielsatzes (Vorab-Probe P4 der Spec) steht als Satz im Korpus:
`witnessRel` wird von genau vier der acht Operationen erhalten — `KKK`, `DKK`, `DKD`,
`DDD` — (`witnessRel_preserves_iff`) — der Schluss des Zielsatzes ist also keine
Selbstverständlichkeit. Die Zählung über alle binären Relationen (P5 der Spec) bleibt
außerhalb des Korpus.

0 Sorries.
-/

namespace Reformulation.Proemial.TournamentInseparability

universe u

/-! ## Teil 1 — Die acht lokal-klassischen Operationen -/

/-- `min` an `.val`, ohne Mathlibs Ordnungsinstanz. -/
def minF (x y : Fin 3) : Fin 3 := if x.val ≤ y.val then x else y

/-- `max` an `.val`, ohne Mathlibs Ordnungsinstanz. -/
def maxF (x y : Fin 3) : Fin 3 := if x.val ≤ y.val then y else x

/-- Eine lokal-klassische Operation auf `Fin 3`: je Elementarkontextur `{0,1}`, `{1,2}`,
`{0,2}` ein Bit, `true` = `max` (D), `false` = `min` (K). Auf der Diagonale ist sie unter
beiden Wahlen die Identität. Die Kontextur eines Paares `x ≠ y` liest sich an der Summe
`x.val + y.val` ab (1, 3 oder 2). -/
def localOp (d01 d12 d02 : Bool) (x y : Fin 3) : Fin 3 :=
  let pick := fun (d : Bool) => if d then maxF x y else minF x y
  if x.val + y.val = 1 then pick d01
  else if x.val + y.val = 3 then pick d12
  else pick d02

/-! Die acht Muster in der Schreibweise der Spec (Buchstabe je Kontextur, K = `min`,
D = `max`). -/

abbrev KKK := localOp false false false
abbrev KKD := localOp false false true
abbrev KDK := localOp false true false
abbrev KDD := localOp false true true
abbrev DKK := localOp true false false
abbrev DKD := localOp true false true
abbrev DDK := localOp true true false
abbrev DDD := localOp true true true

/-! ## Teil 2 — Turnier und Transitivität -/

/-- Das Turnier einer Operation: `x` schlägt `y`, wenn `x ≠ y` und `o x y = x`. -/
abbrev beats (o : Fin 3 → Fin 3 → Fin 3) (x y : Fin 3) : Prop := x ≠ y ∧ o x y = x

/-- Das Turnier von `o` ist transitiv. -/
abbrev TransitiveOp (o : Fin 3 → Fin 3 → Fin 3) : Prop :=
  ∀ x y z : Fin 3, beats o x y → beats o y z → beats o x z

/-- Das Turnier als Liste der Siegerpaare, für die Eichung gegen die Tafel der Spec. -/
def tournament (o : Fin 3 → Fin 3 → Fin 3) : List (Fin 3 × Fin 3) :=
  [((0 : Fin 3), (1 : Fin 3)), (0, 2), (1, 0), (1, 2), (2, 0), (2, 1)].filter
    fun p => decide (beats o p.1 p.2)

/-- **Die Teilung 6 : 2.** Das Turnier von `localOp d01 d12 d02` ist genau dann
transitiv, wenn nicht die beiden Kontexturen `{0,1}` und `{1,2}` gleich wählen und
`{0,2}` anders. Die zwei Ausnahmen sind `KKD` und `DDK`. -/
theorem transitive_iff :
    ∀ d01 d12 d02 : Bool,
      TransitiveOp (localOp d01 d12 d02) ↔ ¬ (d01 = d12 ∧ d12 ≠ d02) := by
  decide

/-! ## Teil 3 — Die zwei Gleichungen (Tiefe eins) -/

/-- **H1.** Die zyklische Operation `KKD` entsteht aus drei transitiven. -/
theorem kkd_eq : ∀ x y : Fin 3, KKD x y = KKK (KDD x y) (DKD x y) := by
  decide

/-- **H2.** Die zyklische Operation `DDK` entsteht aus drei transitiven. -/
theorem ddk_eq : ∀ x y : Fin 3, DDK x y = KDK (DKK x y) (DDD x y) := by
  decide

/-! ## Teil 4 — Erhaltung, beliebige Stelligkeit -/

/-- `R` wird von `o` erhalten: koordinatenweise angewandt, führt `o` zwei Tupel aus `R`
wieder in `R`. `R` ist eine Relation der Stelligkeit `ι`. -/
def Preserves {ι : Type u} (R : Set (ι → Fin 3)) (o : Fin 3 → Fin 3 → Fin 3) : Prop :=
  ∀ a ∈ R, ∀ b ∈ R, (fun i => o (a i) (b i)) ∈ R

/-- **H3.** Erhaltung ist unter Einsetzung abgeschlossen. -/
theorem preserves_comp {ι : Type u} {R : Set (ι → Fin 3)}
    {f g h : Fin 3 → Fin 3 → Fin 3}
    (hf : Preserves R f) (hg : Preserves R g) (hh : Preserves R h) :
    Preserves R (fun x y => f (g x y) (h x y)) :=
  fun a ha b hb => hf _ (hg a ha b hb) _ (hh a ha b hb)

/-- Erhaltung überträgt sich auf eine punktweise gleiche Operation. Hier tritt
`Quot.sound` ein: die Gleichheit der Tupel braucht `funext`. -/
theorem preserves_congr {ι : Type u} {R : Set (ι → Fin 3)}
    {o o' : Fin 3 → Fin 3 → Fin 3} (e : ∀ x y, o' x y = o x y)
    (h : Preserves R o) : Preserves R o' := by
  intro a ha b hb
  have hfun : (fun i => o' (a i) (b i)) = (fun i => o (a i) (b i)) :=
    funext fun i => e _ _
  rw [hfun]
  exact h a ha b hb

/-! ## Teil 5 — Der Zielsatz -/

/-- **Der Unmöglichkeitssatz C2.** Erhält `R` alle transitiven lokal-klassischen
Operationen, so erhält `R` alle acht. Kontraponiert: keine Relation beliebiger
Stelligkeit erhält die sechs transitiven und verletzt eine der zwei zyklischen. -/
theorem no_relation_separates {ι : Type u} (R : Set (ι → Fin 3))
    (h : ∀ d01 d12 d02 : Bool,
      TransitiveOp (localOp d01 d12 d02) → Preserves R (localOp d01 d12 d02)) :
    ∀ d01 d12 d02 : Bool, Preserves R (localOp d01 d12 d02) := by
  have tr : ∀ d01 d12 d02 : Bool, ¬ (d01 = d12 ∧ d12 ≠ d02) →
      Preserves R (localOp d01 d12 d02) :=
    fun d01 d12 d02 hn => h d01 d12 d02 ((transitive_iff d01 d12 d02).mpr hn)
  intro d01 d12 d02
  cases d01 <;> cases d12 <;> cases d02
  · exact tr _ _ _ (by decide)
  · exact preserves_congr kkd_eq
      (preserves_comp (tr false false false (by decide))
        (tr false true true (by decide)) (tr true false true (by decide)))
  · exact tr _ _ _ (by decide)
  · exact tr _ _ _ (by decide)
  · exact tr _ _ _ (by decide)
  · exact tr _ _ _ (by decide)
  · exact preserves_congr ddk_eq
      (preserves_comp (tr false true false (by decide))
        (tr true false false (by decide)) (tr true true true (by decide)))
  · exact tr _ _ _ (by decide)

/-! ## Teil 6 — Die Gegenprobe: der Schluss ist nicht leer (P4) -/

/-- Die binäre Relation `{(0,0), (1,0), (1,2), (2,2)}` als Tafel über `.val`. -/
def witnessRelB (p q : Fin 3) : Bool :=
  (p.val == 0 && q.val == 0) || (p.val == 1 && q.val == 0) ||
  (p.val == 1 && q.val == 2) || (p.val == 2 && q.val == 2)

/-- Dieselbe Relation als Menge binärer Tupel. -/
def witnessRel : Set (Fin 2 → Fin 3) := {v | witnessRelB (v 0) (v 1) = true}

/-- Die Erhaltung von `witnessRel` auf Koordinaten, ohne Quantor über den Funktionsraum. -/
theorem witnessRel_preserves_pointwise_iff :
    ∀ d01 d12 d02 : Bool,
      (∀ p q r s : Fin 3, witnessRelB p q = true → witnessRelB r s = true →
          witnessRelB (localOp d01 d12 d02 p r) (localOp d01 d12 d02 q s) = true)
        ↔ ((d01 = false ∧ d12 = false ∧ d02 = false) ∨ (d01 = true ∧ d12 = false ∧ d02 = false)
            ∨ (d01 = true ∧ d12 = false ∧ d02 = true) ∨ (d01 = true ∧ d12 = true ∧ d02 = true)) := by
  decide

/-- **Die Gegenprobe.** `witnessRel` wird von genau den vier Operationen `KKK`, `DKK`, `DKD`,
`DDD` erhalten und von den übrigen vier
nicht, darunter zwei transitiven. Erhaltung ist für diese Operationen also keine
Selbstverständlichkeit, und die Hypothese des Zielsatzes schliesst Relationen aus. -/
theorem witnessRel_preserves_iff :
    ∀ d01 d12 d02 : Bool,
      Preserves witnessRel (localOp d01 d12 d02)
        ↔ ((d01 = false ∧ d12 = false ∧ d02 = false) ∨ (d01 = true ∧ d12 = false ∧ d02 = false)
            ∨ (d01 = true ∧ d12 = false ∧ d02 = true) ∨ (d01 = true ∧ d12 = true ∧ d02 = true)) := by
  intro d01 d12 d02
  refine Iff.trans ⟨fun h p q r s hpq hrs => h ![p, q] hpq ![r, s] hrs,
    fun h a ha b hb => h (a 0) (a 1) (b 0) (b 1) ha hb⟩ ?_
  exact witnessRel_preserves_pointwise_iff d01 d12 d02

/-! ## Eichung gegen die Tafel der Spec (§4) -/

/-- info: [(0, 1), (0, 2), (1, 2)] -/
#guard_msgs in #eval tournament KKK
/-- info: [(0, 1), (1, 2), (2, 0)] -/
#guard_msgs in #eval tournament KKD
/-- info: [(0, 1), (0, 2), (2, 1)] -/
#guard_msgs in #eval tournament KDK
/-- info: [(0, 1), (2, 0), (2, 1)] -/
#guard_msgs in #eval tournament KDD
/-- info: [(0, 2), (1, 0), (1, 2)] -/
#guard_msgs in #eval tournament DKK
/-- info: [(1, 0), (1, 2), (2, 0)] -/
#guard_msgs in #eval tournament DKD
/-- info: [(0, 2), (1, 0), (2, 1)] -/
#guard_msgs in #eval tournament DDK
/-- info: [(1, 0), (2, 0), (2, 1)] -/
#guard_msgs in #eval tournament DDD


/-! ## Wachen -/

/-- info: 'Reformulation.Proemial.TournamentInseparability.transitive_iff' does not depend on any axioms -/
#guard_msgs in #print axioms transitive_iff

/-- info: 'Reformulation.Proemial.TournamentInseparability.kkd_eq' does not depend on any axioms -/
#guard_msgs in #print axioms kkd_eq

/-- info: 'Reformulation.Proemial.TournamentInseparability.ddk_eq' does not depend on any axioms -/
#guard_msgs in #print axioms ddk_eq

/-- info: 'Reformulation.Proemial.TournamentInseparability.preserves_comp' does not depend on any axioms -/
#guard_msgs in #print axioms preserves_comp

/-- info: 'Reformulation.Proemial.TournamentInseparability.preserves_congr' depends on axioms: [Quot.sound] -/
#guard_msgs in #print axioms preserves_congr

/-- info: 'Reformulation.Proemial.TournamentInseparability.no_relation_separates' depends on axioms: [Quot.sound] -/
#guard_msgs in #print axioms no_relation_separates

/-- info: 'Reformulation.Proemial.TournamentInseparability.witnessRel_preserves_pointwise_iff' does not depend on any axioms -/
#guard_msgs in #print axioms witnessRel_preserves_pointwise_iff

/-- info: 'Reformulation.Proemial.TournamentInseparability.witnessRel_preserves_iff' depends on axioms: [propext] -/
#guard_msgs in #print axioms witnessRel_preserves_iff

end Reformulation.Proemial.TournamentInseparability
