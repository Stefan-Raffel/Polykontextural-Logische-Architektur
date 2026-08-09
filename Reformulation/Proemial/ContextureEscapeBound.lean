import Reformulation.Proemial.QuaternaryCloneBound

/-!
# Proemial.ContextureEscapeBound — das Zeugnis mit Menge und Punkt

**Ertrag.** Das Erhaltungsargument von `TransjunctionCloneBound` in der Gestalt,
die ein Prüfer benutzen kann, und auf `Fin 4` mit seinen zwei abgeschlossenen
Mengen instanziiert.

* **Z2** (`not_in_clone_of_escapes`) — **das Zeugnis, allgemein**: verlässt eine
  Operation eine unter der Basis abgeschlossene Menge an einem angebbaren
  Punkt, so ist sie kein Term über der Basis. Die Voraussetzung nennt **die
  Menge und den Punkt**; wer den Satz anwendet, legt eine Zelle vor und kein
  Urteil.
* **Z1** (`contexture03`, `contexture12`) — über der Signatur `{min, max, ¬}`
  auf `Fin 4` sind `{0,3}` und `{1,2}` Substrukturen. Gemessen ist auch, dass es
  **keine weiteren** nichttrivialen gibt (siehe unten).
* **Z3** (`avgDown_not_in_clone`) — der abgerundete Durchschnitt verlässt
  `{0,3}` am Punkt `(0,3)` und liegt damit nicht im Klon.
* Dazu `locallyClassical_preserves_both`: jede lokal klassische Operation
  erhält **beide** Mengen. Der Satz verbindet die zwei Zeugnisse des Bestandes
  — wer das eine trägt, trägt das andere nicht.

## Die Grenzformel

**Bewiesen ist, dass eine Operation, die eine unter der Basis abgeschlossene
Menge an einem Punkt verlässt, nicht aus der Basis erzeugbar ist. Über die
Politik, die sie modelliert, sagt der Satz nichts.**

## Hinreichend, nicht notwendig — ausgeschrieben, weil die Umkehrung naheliegt

**Das Fehlen eines solchen Punktes ist kein Zeugnis für Erzeugbarkeit.** Eine
Operation, die beide Mengen erhält, kann trotzdem ausserhalb des Klons liegen;
der Satz sagt darüber nichts, und aus seinem Schweigen folgt nichts. Wer aus
„kein Punkt gefunden" auf „erzeugbar" schliesst, hat den Satz umgedreht, und
die Umkehrung ist nicht bewiesen und nicht wahr.

## Die Reichweite der Basis

Die Aussage hängt an der Kontextur-Treue der Basis: kommt eine Konstante hinzu,
verschwindet die Schranke. Diese Lage ist im Bestand gemessen und ausgeführt —
`TransjunctionCloneBound`, Test 2b (`const_not_closedUnder`,
`no_substructure_with_const`). Hier wird sie nicht wiederholt, sondern genannt.

## Die Anwendungsgrenzen, im Wortlaut der Anwendungsmodule

Diese Datei gibt **keine Sicherheits-, Rechts-, Wahrheits- oder
Retrievalgarantie**. Bewiesen ist, was aus lokalen, kontextur-blinden Prüfern
nicht zusammensetzbar ist.

**Und kein Satz dieser Datei urteilt über ein System.** Aus Z3 folgt nicht, dass
eine Politik, die den abgerundeten Durchschnitt benutzt, irgendeine Eigenschaft
hätte; bewiesen ist, dass diese eine Operation kein Term über `{min, max, ¬}`
ist.

## Was gemessen wurde, und mit welcher Route

**Die abgeschlossenen Mengen sind hier gemessen und nicht übernommen.**
Aufzählung aller 16 Teilmengen von `Fin 4` gegen Abgeschlossenheit unter `min`,
`max` und `negFin4` (`#eval`-Wegwerfprobe auf den Definitionen des Bestandes):
abgeschlossen sind genau `∅`, `{1,2}`, `{0,3}` und `{0,1,2,3}` — **nichttrivial
also genau die zwei**, die Z1 baut. Die Zahl 16 ist die Zahl der angesehenen
Fälle und nicht eine Auswahl.

**Die Bauform ist übernommen, die Struktur nicht neu gebaut.** `L`,
`UnaryFun`, `BinaryFun` kommen aus `TransjunctionCloneBound`, die Interpretation
`struc4` und die Negation `negFin4` aus `QuaternaryCloneBound`. Gemessen am
HEAD: für `L.Structure (Fin 4)` gibt es **zwei** Instanzen im Bestand —
`QuaternaryCloneBound.struc4` und `GeneralCloneBound.strucM` bei `m = 4` —, und
sie stimmen auf der Negation überein (`negFin4 a = negFin 4 a` für alle `a`,
per `decide`). Sind beide sichtbar, wählt die Instanzensuche `struc4`. **Dieses
Modul importiert darum nur `QuaternaryCloneBound`**, damit die Wahl nicht an
einer Reihenfolge hängt.

## Warum das Modul im Proemial-Zweig liegt, und die Modulfrage ausdrücklich

`L` und `struc4` liegen im Proemial-Zweig; ohne sie ist keiner der Sätze
formulierbar. Der Ort ist damit durch die Importrichtung bestimmt.

**Die Modulfrage ist gestellt, weil dieser Zug einen allgemeinen und einen
instanziierten Satz zugleich baut** (Fehlerklasse *Modulschnitt nach dem
speziellsten Bestandteil*). Z2 redet über **jede** Sprache, jede Struktur und
jede Substruktur; Z1 und Z3 reden über `Fin 4`. Die Antwort ist trotzdem **ein**
Modul, und zwar aus einem gemessenen Grund und nicht aus Bequemlichkeit: der
Ort mit Bibliothekscharakter wäre `MathlibExtensions/`, und dieses Target liegt
**ausserhalb der Default-Targets** und ausserhalb des Aggregats
(`docs/build-targets.md`). Ein dort abgelegtes Z2 wäre von Z1 und Z3 nicht
konsumierbar, ohne das Aggregat auf ein Nicht-Aggregat-Target zu stellen. Der
allgemeine Satz steht darum hier — **allgemein formuliert**, damit ein späterer
Zug ihn heben kann, ohne ihn umzuschreiben.

## Profil

**Das Modul ist durchgängig choice-frei** — und das war nicht die Erwartung.
Der Kopf trug vor der Messung den Satz, die `Set`-Maschinerie der
`Substructure` ziehe `Classical.choice`; **gemessen zieht sie ihn nicht.** Die
zwei allgemeinen Sätze sind `[propext]`, die vier über `Fin 4`
`[propext, Quot.sound]`. Die Ist-Profile stehen in den Wachen am Dateiende; die
Erwartung ist hier vermerkt, weil sie gefallen ist und nicht, weil sie zutraf.

## Aggregat-Reife

Konsumiert `Proemial.QuaternaryCloneBound` — Aggregat — sowie Mathlibs
`ModelTheory`. Keine Sonde, keine Setzung.

Kein `sorry`, kein `axiom`, kein `: True`-Feld.
-/

namespace Reformulation.Proemial.ContextureEscapeBound

open FirstOrder Language
open Reformulation.Proemial.TransjunctionCloneBound (L UnaryFun BinaryFun)
open Reformulation.Proemial.QuaternaryCloneBound (negFin4 PreservesPair4 ActsAsMin4
  ActsAsMax4 LocallyClassical4)

/-! ## Teil 1 — Z2, das Zeugnis in seiner allgemeinen Gestalt

Der Satz nennt in seiner Voraussetzung die Menge (`S`) und den Punkt (`a`, `b`).
Er ist über **jeder** Sprache und **jeder** Struktur formuliert; die Instanzen
für `Fin 4` stehen unten. -/

/-- **Z2 — das Zeugnis.** Sind `a` und `b` Elemente einer Substruktur `S` und
liegt `f a b` nicht in `S`, so ist `f` kein Term über der Signatur.

Konsumiert `Term.realize_mem` aus Mathlib — das Erhaltungslemma wird nicht
nachgebaut. **Die Zeugengestalt ist der Zweck:** wer den Satz anwendet, legt
eine Menge und einen Punkt vor. -/
theorem not_in_clone_of_escapes {Lang : Language} {M : Type*} [Lang.Structure M]
    (S : Lang.Substructure M) {f : M → M → M} {a b : M}
    (ha : a ∈ S) (hb : b ∈ S) (hf : f a b ∉ S) :
    ¬ ∃ t : Lang.Term (Fin 2), ∀ v : Fin 2 → M, t.realize v = f (v 0) (v 1) := by
  rintro ⟨t, ht⟩
  have hv : ∀ i : Fin 2, (![a, b] : Fin 2 → M) i ∈ S := Fin.forall_fin_two.mpr ⟨ha, hb⟩
  have hmem := Term.realize_mem t (![a, b]) hv
  rw [ht (![a, b])] at hmem
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hmem
  exact hf hmem

/-! ## Teil 2 — Z1, die zwei Kontexturen als Substrukturen

Die Reduktionen der Interpretation stehen als `rfl`-Lemmata voran; der Bestand
führt sie für `struc4` nicht.

**Ohne `@[simp]`, und das ist gemessen und nicht Geschmack.** Sie werden unten
ausdrücklich in `simp only` genannt, brauchen die Marke also nicht — und die
verbindliche Satzroute (`CLAUDE.md` §3) sieht die Form `@[simp] private lemma`
**nicht**: sie erwartet den Sichtbarkeits-Modifikator vor dem Attribut, während
Leans Grammatik das Attribut voranstellt. Die Kombination kommt im Bestand
bisher **nullmal** vor (Suchlauf über `Reformulation/` und `Foreign/`); dieses
Modul führt sie nicht ein. -/

private lemma funMap4_neg (x : Fin 1 → Fin 4) :
    @Structure.funMap L (Fin 4) _ 1 UnaryFun.neg x = negFin4 (x 0) := rfl

private lemma funMap4_and (x : Fin 2 → Fin 4) :
    @Structure.funMap L (Fin 4) _ 2 BinaryFun.and x = min (x 0) (x 1) := rfl

private lemma funMap4_or (x : Fin 2 → Fin 4) :
    @Structure.funMap L (Fin 4) _ 2 BinaryFun.or x = max (x 0) (x 1) := rfl

private lemma mem_pair03 (a : Fin 4) : a ∈ ({0, 3} : Set (Fin 4)) ↔ a = 0 ∨ a = 3 := by
  simp [Set.mem_insert_iff, Set.mem_singleton_iff]

private lemma mem_pair12 (a : Fin 4) : a ∈ ({1, 2} : Set (Fin 4)) ↔ a = 1 ∨ a = 2 := by
  simp [Set.mem_insert_iff, Set.mem_singleton_iff]

/-- **Z1, erste Hälfte.** Die Randkontextur `{0,3}` ist unter `min`, `max` und
`negFin4` abgeschlossen — als Substruktur über `L`. -/
def contexture03 : L.Substructure (Fin 4) where
  carrier := {0, 3}
  fun_mem := by
    intro n f
    match n, f with
    | 1, .neg =>
        intro x hx
        have h0 := (mem_pair03 _).1 (hx 0); rw [mem_pair03]
        rcases h0 with h0 | h0 <;> simp only [funMap4_neg, h0] <;> decide
    | 2, .and =>
        intro x hx
        have h0 := (mem_pair03 _).1 (hx 0); have h1 := (mem_pair03 _).1 (hx 1)
        rw [mem_pair03]
        rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1 <;>
          simp only [funMap4_and, h0, h1] <;> decide
    | 2, .or =>
        intro x hx
        have h0 := (mem_pair03 _).1 (hx 0); have h1 := (mem_pair03 _).1 (hx 1)
        rw [mem_pair03]
        rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1 <;>
          simp only [funMap4_or, h0, h1] <;> decide

/-- **Z1, zweite Hälfte.** Die innere Kontextur `{1,2}`, ebenso. -/
def contexture12 : L.Substructure (Fin 4) where
  carrier := {1, 2}
  fun_mem := by
    intro n f
    match n, f with
    | 1, .neg =>
        intro x hx
        have h0 := (mem_pair12 _).1 (hx 0); rw [mem_pair12]
        rcases h0 with h0 | h0 <;> simp only [funMap4_neg, h0] <;> decide
    | 2, .and =>
        intro x hx
        have h0 := (mem_pair12 _).1 (hx 0); have h1 := (mem_pair12 _).1 (hx 1)
        rw [mem_pair12]
        rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1 <;>
          simp only [funMap4_and, h0, h1] <;> decide
    | 2, .or =>
        intro x hx
        have h0 := (mem_pair12 _).1 (hx 0); have h1 := (mem_pair12 _).1 (hx 1)
        rw [mem_pair12]
        rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1 <;>
          simp only [funMap4_or, h0, h1] <;> decide

/-- Mitgliedschaft in `contexture03` als entscheidbare Disjunktion. -/
theorem mem_contexture03 (a : Fin 4) : a ∈ contexture03 ↔ a = 0 ∨ a = 3 := mem_pair03 a

/-- Mitgliedschaft in `contexture12` als entscheidbare Disjunktion. -/
theorem mem_contexture12 (a : Fin 4) : a ∈ contexture12 ↔ a = 1 ∨ a = 2 := mem_pair12 a

/-! ## Teil 3 — Z3, ein realer Zeuge

**Warum der abgerundete Durchschnitt.** Er ist unter den in der Sondierung
angesehenen Regeln die verbreitetste Aggregationsform und die, deren Zeugenpunkt
man ohne Rechnung sieht: zwei Randwerte gemittelt ergeben einen inneren. Die
Vorgabe hat ihn empfohlen, und dieser Grund ist am Bau nicht besser geworden und
nicht schlechter. -/

/-- Der **abgerundete Durchschnitt** auf `Fin 4`, über `.val` gebaut — die
`Fin`-Arithmetik wäre modular (`CLAUDE.md` §8.1). -/
def avgDown (a b : Fin 4) : Fin 4 :=
  ⟨(a.val + b.val) / 2, by have := a.isLt; have := b.isLt; omega⟩

/-- **Der Zeugenpunkt, ausgeschrieben.** `0` und `3` liegen in der Kontextur
`{0,3}`, ihr abgerundeter Durchschnitt `1` nicht. Das ist die Zelle, die ein
Prüfer vorlegt. -/
theorem avgDown_escapes :
    (0 : Fin 4) ∈ contexture03 ∧ (3 : Fin 4) ∈ contexture03 ∧
      avgDown 0 3 ∉ contexture03 := by
  refine ⟨(mem_contexture03 _).2 (by decide), (mem_contexture03 _).2 (by decide), ?_⟩
  rw [mem_contexture03]
  decide

/-- **Z3.** Der abgerundete Durchschnitt liegt nicht im Klon von `{min, max, ¬}`
über `Fin 4` — durch Anwendung von Z2 auf die Kontextur `{0,3}` und den Punkt
`(0,3)`. -/
theorem avgDown_not_in_clone :
    ¬ ∃ t : L.Term (Fin 2), ∀ v : Fin 2 → Fin 4, t.realize v = avgDown (v 0) (v 1) :=
  not_in_clone_of_escapes contexture03
    avgDown_escapes.1 avgDown_escapes.2.1 avgDown_escapes.2.2

/-! ## Teil 4 — die zwei Zeugnisse berühren einander nicht -/

/-- **Jede lokal klassische Operation erhält beide Kontexturen.** Damit trägt
keine von ihnen ein Zeugnis dieser Art: das Zeugnis der Mischung
(`PairwiseMixture`) und das Zeugnis des Verlassens schliessen einander aus.

Der Beweis ist keine Aufzählung über den Funktionenraum, sondern liest die zwei
einschlägigen Glieder aus `LocallyClassical4` ab — auf einem Paar wirkt `f` wie
`min` oder wie `max`, und beide verlassen das Paar nicht. -/
theorem locallyClassical_preserves_both (f : Fin 4 → Fin 4 → Fin 4)
    (h : LocallyClassical4 f) :
    PreservesPair4 f 0 3 ∧ PreservesPair4 f 1 2 := by
  constructor
  · rcases h.2.2.1 with hmin | hmax
    · intro a b ha hb
      rw [hmin a b ha hb]
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> decide
    · intro a b ha hb
      rw [hmax a b ha hb]
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> decide
  · rcases h.2.2.2.1 with hmin | hmax
    · intro a b ha hb
      rw [hmin a b ha hb]
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> decide
    · intro a b ha hb
      rw [hmax a b ha hb]
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> decide

/-! ## Teil 5 — Statement-Pins

Voller Wortlaut links, Satz rechts — jede Drift des *Statements* bricht den Bau. -/

-- STATEMENT-PIN
example {Lang : Language} {M : Type} [Lang.Structure M] (S : Lang.Substructure M)
    (f : M → M → M) (a b : M) (ha : a ∈ S) (hb : b ∈ S) (hf : f a b ∉ S) :
    ¬ ∃ t : Lang.Term (Fin 2), ∀ v : Fin 2 → M, t.realize v = f (v 0) (v 1) :=
  not_in_clone_of_escapes S ha hb hf

-- STATEMENT-PIN
example (a : Fin 4) : (a ∈ contexture03 ↔ a = 0 ∨ a = 3) ∧ (a ∈ contexture12 ↔ a = 1 ∨ a = 2) :=
  ⟨mem_contexture03 a, mem_contexture12 a⟩

-- STATEMENT-PIN
example :
    ((0 : Fin 4) ∈ contexture03 ∧ (3 : Fin 4) ∈ contexture03 ∧
        avgDown 0 3 ∉ contexture03) ∧
      ¬ ∃ t : L.Term (Fin 2), ∀ v : Fin 2 → Fin 4,
        t.realize v = avgDown (v 0) (v 1) :=
  ⟨avgDown_escapes, avgDown_not_in_clone⟩

-- STATEMENT-PIN
example (f : Fin 4 → Fin 4 → Fin 4) (h : LocallyClassical4 f) :
    PreservesPair4 f 0 3 ∧ PreservesPair4 f 1 2 :=
  locallyClassical_preserves_both f h

/-! ## Teil 6 — die Axiom-Wachen (Ist-gebunden) -/

/-- info: 'Reformulation.Proemial.ContextureEscapeBound.not_in_clone_of_escapes' depends on axioms: [propext] -/
#guard_msgs in #print axioms not_in_clone_of_escapes

/-- info: 'Reformulation.Proemial.ContextureEscapeBound.mem_contexture03' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms mem_contexture03

/-- info: 'Reformulation.Proemial.ContextureEscapeBound.mem_contexture12' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms mem_contexture12

/-- info: 'Reformulation.Proemial.ContextureEscapeBound.avgDown_escapes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms avgDown_escapes

/-- info: 'Reformulation.Proemial.ContextureEscapeBound.avgDown_not_in_clone' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms avgDown_not_in_clone

/-- info: 'Reformulation.Proemial.ContextureEscapeBound.locallyClassical_preserves_both' depends on axioms: [propext] -/
#guard_msgs in #print axioms locallyClassical_preserves_both

end Reformulation.Proemial.ContextureEscapeBound
