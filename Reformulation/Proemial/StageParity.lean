import Reformulation.Proemial.StageAscent

/-!
# Proemial.StageParity — die Paritaet des Stufenschritts

Drei Saetze in Differential-Form auf einem Traeger: der Stufenschritt `m → m+1` traegt die
volle Signatur `{min, max, neg}` genau dann nicht, wenn m ungerade ist.

* **G1 — die Verortung des Bruchs.** `Fin.castSucc`, die Einbettung, unter der sich die
  Zeugenfamilie aus `StageAscent` reproduziert, ist an **keiner** Stelle
  negationsvertraeglich (`castSucc_negFin_ne`): links steht der Wert `m−1−a`, rechts `m−a`,
  Differenz 1 an jeder Stelle.
* **G2 — die Unmoeglichkeitshaelfte.** Ist m ungerade, so ist **keine** Abbildung
  `Fin m → Fin (m+1)` negationsvertraeglich (`odd_no_neg_compatible`) — ohne
  Injektivitaets- und ohne Monotonie-Voraussetzung. Der Grund ist ein Fixpunkt-Argument:
  `negFin m` hat bei ungeradem m den Fixpunkt `(m−1)/2`, sein Bild muesste Fixpunkt von
  `negFin (m+1)` sein, und `2a = m` ist fuer ungerades m unloesbar.
* **G3 — die Moeglichkeitshaelfte, mit explizitem Zeugen.** Ist m gerade, so ist die
  symmetrische Einbettung `eSym` — sie laesst die Luecke am Mittelplatz `m/2` — streng
  monoton (`eSym_strictMono`) und negationsvertraeglich (`eSym_negFin`).

Dazu, als Zugabe und nicht als Pflichtstueck, die Vertraeglichkeit der `StageAscent`-Zeugen-
familie mit `eSym` (`w_eSym`, ab `m ≥ 4`): auf den geraden Stufen steigt nicht nur die
Signatur auf, sondern der Zeuge mit ihr.

## Ertrag

**Ertrag**, nicht Benennung: drei Saetze mit eigenem Gehalt. **Keine Klon-Schranke wird
konsumiert** — dieses Modul spricht ueber Einbettungen und ueber die Negation der
Korpus-Signatur, nicht ueber Erzeugbarkeit im Termklon. Aus dem Bestand kommen `GCB.negFin`
(die ordnungsumkehrende Negation `a ↦ m−1−a` ueber `.val`) und, fuer die Zugabe,
`SAsc.w`.

## Deutungs-Marken (verbindlich)

1. **Die Lesung ist Deutung, nicht Wortlaut.** Dass hier „das Umtauschverhaeltnis
   stufenrelativ ist" und „der Aufstieg keine signaturtreue Gestalt hat", ist Deutung der
   drei Saetze. Sie steht in keinem Namen und in keinem Satzwortlaut. Der Dateiname sagt,
   was bewiesen ist: eine Paritaetseigenschaft des Stufenschritts.
2. **Was G2 nicht sagt.** Nichts ueber `m → m+2`. Dass sich die symmetrischen Einbettungen
   ueber die geraden Stufen verketten, ist benanntes Folgematerial und hier weder gebaut
   noch behauptet; die Ledger-Zeile L12-4 bleibt unberuehrt offen. Insbesondere ist **„kein
   Kolimes" kein Satz dieser Datei** — es wird kein Grenzobjekt gebaut, keines
   ausgeschlossen und keines behauptet.
3. **Keine Klassifikation.** Behauptet werden Nichtexistenz (G2) und Existenz (G3). Wie
   viele vertraegliche Einbettungen es bei geradem m gibt, bleibt draussen; die Datei
   traegt dazu keine Zahl.
4. **Bezug zu `StageAscent`.** Dort steht, was aufsteigt: der Verband und die Zeugenfamilie
   unter `castSucc`. Hier steht, was nicht aufsteigen kann: die Negation, unter irgendeiner
   Abbildung, bei ungeradem m. `StageAscent` bleibt unangetastet.

## Robustheit (`CLAUDE.md` §9) ist hier gegenstandslos

Es wird **keine** Nicht-Erzeugbarkeits-Schranke gezogen und keine Invariante gebaut. Damit
gibt es nichts, dessen Reflexivitaet zu pruefen waere: die Frage, ob eine Schranke eine
Signatur-Erweiterung um Konstanten uebersteht, hat hier keinen Gegenstand. Das steht hier,
damit niemand eine Pruefung vermisst, die es nicht zu fuehren gibt.

## Eine gemessene Choice-Grenze

`eSym_negFin` und die Zugabe `w_eSym` brauchen die Vertauschung von `eSym` mit `min` und
`max`. Mathlibs `Monotone.map_max` traegt sie fertig — und zieht `Classical.choice` in jeden
Konsumenten (gemessen in der Vorprobe: `[propext, Classical.choice, Quot.sound]` gegen
`[propext, Quot.sound]` bei sonst gleicher Datei). Die Rechnung laeuft darum von Hand ueber
`.val`, mit `Fin.coe_min` und `Fin.coe_max` auf `ℕ` gebracht; `omega` versteht `min` und
`max` dort nativ. Der Weg ist notiert, weil `CLAUDE.md` §2 ihn verlangt, wo er vermeidbar
war.

## Woher das durchgehende `[propext, Quot.sound]` kommt — gemessen, nicht erschlossen

Alle acht Deklarationen tragen dasselbe Profil, auch `negFin_val`, dessen Beweis `rfl` ist.
Der Grund ist eine Wegwerf-Messung an vier Punkten und nicht eine Erzaehlung ueber den Term:

| Konstruktion | Schranke im Wert | Definition | `rfl`-Wert-Auskunft darueber |
|---|---|---|---|
| `Fin.castSucc` | keine | axiomfrei | axiomfrei |
| Handfassung von `negFin` (`Nat.sub_le`, `Nat.sub_lt`) | von Hand | axiomfrei | axiomfrei |
| `GCB.negFin` | `by … omega` | `[propext, Quot.sound]` | `[propext, Quot.sound]` |
| `eSym` (hier) | `by … omega`, beide Zweige | `[propext, Quot.sound]` | — |

Die dritte und die zweite Zeile unterscheiden sich in **einer** Groesse: derselbe Wert
`⟨m − 1 − a.val, _⟩`, einmal mit `omega`-Schranke, einmal mit Handschranke. Damit ist die
Vererbung gemessen und nicht bloss plausibel — die Definition traegt das Profil, und die
Wert-Auskunft erbt es, auch wenn sie `rfl` ist. **Das ist der Grund fuer die Wache auf der
Definition `eSym`:** sie hat ein eigenes, messbares Profil, das driften kann. `SAsc.w` hat
keines und traegt darum dort keine.

Was damit **nicht** gemessen ist: dass `omega` das Axiom auf genau diesem und keinem anderen
Weg in den Term bringt. Gemessen ist die Differenz der Fassungen bei sonst gleicher
Konstruktion (`CLAUDE.md` §8, Vorspann: aufgetreten heisst nicht erklaert).

**Ablage:** setzungsfrei, ohne offene Stelle, konsumiert nur Aggregat-Inhalt — Aggregat.
-/

namespace Reformulation.Proemial.StageParity

open Reformulation.Proemial.GeneralCloneBound
open Reformulation.Proemial.StageAscent (w)

/-! ## Teil 0 — zwei Hilfslemmata

Beide sind reine Wert-Auskuenfte: sie bringen `negFin` und `eSym` auf die `.val`-Ebene, auf
der `omega` rechnet. Ohne sie sieht `omega` `(negFin m a).val` als Atom (in der Vorprobe
gemessen) und kommt an keinem der drei Saetze durch. -/

/-- Der Wert von `GCB.negFin`, definitional. Arbeitsstueck aller Saetze dieser Datei. -/
theorem negFin_val (m : ℕ) (a : Fin m) : (negFin m a).val = m - 1 - a.val := rfl

/-! ## Teil 1 — G1: der Bruch sitzt an `castSucc`

Punktweise Totalform. Links steht der Wert `m−1−a`, rechts `m−a`; die Differenz ist 1 an
jeder Stelle, und darum ist die Aussage kein „nicht ueberall", sondern ein „an keiner
Stelle". `.val`-Arithmetik ohne Fallunterscheidung nach m. -/

/-- **G1 — `castSucc` traegt die Negation nicht, und zwar an keiner Stelle.** Die
Einbettung, unter der sich die Zeugenfamilie aus `StageAscent` reproduziert, vertauscht mit
`negFin` fuer **kein** `m` und fuer **kein** Argument. -/
theorem castSucc_negFin_ne (m : ℕ) (a : Fin m) :
    (negFin m a).castSucc ≠ negFin (m + 1) a.castSucc := by
  intro h
  have hv := congrArg Fin.val h
  simp only [Fin.val_castSucc, negFin_val] at hv
  have := a.isLt
  omega

/-! ## Teil 2 — G2: der Paritaets-No-Go

Der tragende Satz. Das `e` steht als Argument vor der Negation: quantifiziert wird ueber
alle Abbildungen `Fin m → Fin (m+1)`, ohne Injektivitaets- und ohne Monotonie-Voraussetzung,
und im Satzinneren wird ueber keinen Funktionsraum quantifiziert (Fallstrick 3 ist damit
gegenstandslos). Das Argument braucht nur den Fixpunkt und ist darum in der staerksten Form
zugleich das billigste.

Der Fixpunkt steht inline und nicht als drittes Hilfslemma: er wird an genau einer Stelle
gebraucht. Sein `omega`-Ziel ist die atomare Gleichung `m−1−(m−1)/2 = (m−1)/2` — kein
Disjunktions-Ziel, Fallstrick 7 bleibt gemieden. -/

/-- **G2 — bei ungeradem m ist keine Abbildung negationsvertraeglich.** Fuer `m % 2 = 1`
und **jede** Abbildung `e : Fin m → Fin (m+1)` scheitert die Vertraeglichkeit mit der
Negation. Beweis am Fixpunkt `(m−1)/2` von `negFin m`: sein Bild muesste Fixpunkt von
`negFin (m+1)` sein, also `2·(e a).val = m` erfuellen, und das ist fuer ungerades m
unloesbar. -/
theorem odd_no_neg_compatible (m : ℕ) (hm : m % 2 = 1)
    (e : Fin m → Fin (m + 1)) :
    ¬ ∀ a : Fin m, e (negFin m a) = negFin (m + 1) (e a) := by
  intro h
  have hfix : negFin m ⟨(m - 1) / 2, by omega⟩ = ⟨(m - 1) / 2, by omega⟩ :=
    Fin.eq_of_val_eq (show m - 1 - (m - 1) / 2 = (m - 1) / 2 by omega)
  have h0 := h ⟨(m - 1) / 2, by omega⟩
  rw [hfix] at h0
  have hv := congrArg Fin.val h0
  simp only [negFin_val] at hv
  omega

/-! ## Teil 3 — G3: die Moeglichkeitshaelfte

Die symmetrische Einbettung mit Luecke am Mittelplatz `m / 2`. Die Bedingung laeuft ueber
`.val` und nicht ueber die `Fin`-Subtraktion (Fallstrick 1 ist damit gegenstandslos); ein
Entscheidungsverfahren kommt nicht vor, und darum braucht die Datei keine
`Decidable`-Instanz. -/

/-- **Der Zeuge:** die symmetrische Einbettung `Fin m → Fin (m+1)`, die unterhalb des
Mittelplatzes `m / 2` festhaelt und oberhalb um eins schiebt. Die Luecke sitzt genau auf
`m / 2`. -/
def eSym (m : ℕ) (a : Fin m) : Fin (m + 1) :=
  if a.val < m / 2 then ⟨a.val, by omega⟩ else ⟨a.val + 1, by have := a.isLt; omega⟩

/-- Der Wert von `eSym`, als Fallunterscheidung auf `ℕ`. Zweites Arbeitsstueck: damit
rechnen die Saetze unten auf der `.val`-Ebene. -/
theorem eSym_val (m : ℕ) (a : Fin m) :
    (eSym m a).val = if a.val < m / 2 then a.val else a.val + 1 := by
  unfold eSym
  split_ifs <;> rfl

/-- **G3, erste Haelfte — `eSym` ist streng monoton.** Die Einbettung ist ordnungstreu, fuer
jedes m und ohne Paritaetsvoraussetzung. -/
theorem eSym_strictMono (m : ℕ) : StrictMono (eSym m) := by
  intro a b hab
  rw [Fin.lt_def] at hab ⊢
  simp only [eSym_val]
  split_ifs <;> omega

/-- **G3, zweite Haelfte — bei geradem m ist `eSym` negationsvertraeglich.** Zusammen mit
`eSym_strictMono` die Existenzaussage: fuer gerades m gibt es eine ordnungstreue
negationsvertraegliche Einbettung `Fin m → Fin (m+1)`. Bei `m = 0` ist die Aussage leer, weil
`Fin 0` leer ist; das ist zulaessig und hier gesagt. -/
theorem eSym_negFin (m : ℕ) (hm : m % 2 = 0) (a : Fin m) :
    eSym m (negFin m a) = negFin (m + 1) (eSym m a) := by
  have ha := a.isLt
  refine Fin.eq_of_val_eq ?_
  simp only [eSym_val, negFin_val]
  split_ifs <;> omega

/-! ## Teil 4 — Zugabe: der Zeuge steigt mit

Kein Pflichtstueck der Reihe, sondern der Zusatz, der die geraden Stufen vollstaendig macht:
nicht nur die Signatur, auch die Zeugenfamilie `SAsc.w` vertauscht mit `eSym`. Das Argument
ist paritaetsfrei und braucht `m ≥ 4` allein dafuer, dass `m / 2 ≥ 2` gilt und `eSym` die
Werte 0 und 1 festhaelt, ohne dass ein anderes Argument sie trifft.

Die vier Wert-Auskuenfte ueber `eSym` stehen inline, damit die Datei bei zwei Hilfslemmata
bleibt; die Vertauschung mit `min` und `max` laeuft von Hand ueber `.val` (Dateikopf,
gemessene Choice-Grenze). -/

/-- **Zugabe — die Zeugenfamilie steigt ueber `eSym` mit.** Fuer `m ≥ 4` vertauscht `SAsc.w`
mit der symmetrischen Einbettung. Das Gegenstueck zu `SAsc.w_castSucc`, nur fuer die
Einbettung, die bei geradem m auch die Negation traegt. -/
theorem w_eSym (m : ℕ) (hm : 4 ≤ m) (a b : Fin m) :
    w (m + 1) (eSym m a) (eSym m b) = eSym m (w m a b) := by
  have hz : ∀ x : Fin m, x.val = 0 → (eSym m x).val = 0 := by
    intro x hx; simp only [eSym_val]; split_ifs <;> omega
  have ho : ∀ x : Fin m, x.val = 1 → (eSym m x).val = 1 := by
    intro x hx; simp only [eSym_val]; split_ifs <;> omega
  have hz' : ∀ x : Fin m, (eSym m x).val = 0 → x.val = 0 := by
    intro x hx; simp only [eSym_val] at hx; split_ifs at hx; all_goals omega
  have ho' : ∀ x : Fin m, (eSym m x).val = 1 → x.val = 1 := by
    intro x hx; simp only [eSym_val] at hx; split_ifs at hx <;> omega
  have hmax : eSym m (max a b) = max (eSym m a) (eSym m b) := by
    refine Fin.eq_of_val_eq ?_
    simp only [eSym_val, Fin.coe_max]
    split_ifs <;> omega
  have hmin : eSym m (min a b) = min (eSym m a) (eSym m b) := by
    refine Fin.eq_of_val_eq ?_
    simp only [eSym_val, Fin.coe_min]
    split_ifs <;> omega
  unfold w
  by_cases h : (a.val = 0 ∧ b.val = 1) ∨ (a.val = 1 ∧ b.val = 0)
  · rw [if_pos h, if_pos ?_]
    · exact hmax.symm
    · rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨hz a h1, ho b h2⟩
      · exact Or.inr ⟨ho a h1, hz b h2⟩
  · rw [if_neg h, if_neg ?_]
    · exact hmin.symm
    · intro hc
      refine h ?_
      rcases hc with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨hz' a h1, ho' b h2⟩
      · exact Or.inr ⟨ho' a h1, hz' b h2⟩

/-! **Statement-Pins.** Voller Wortlaut links, Satz rechts — jede Drift des *Statements*
bricht den Build. Namenlose `example`s, keine Axiom-Wache. -/

-- STATEMENT-PIN
example (m : ℕ) (hm : m % 2 = 1) (e : Fin m → Fin (m + 1)) :
    ¬ ∀ a : Fin m, e (negFin m a) = negFin (m + 1) (e a) :=
  odd_no_neg_compatible m hm e
-- STATEMENT-PIN
example (m : ℕ) (hm : m % 2 = 0) (a : Fin m) :
    eSym m (negFin m a) = negFin (m + 1) (eSym m a) := eSym_negFin m hm a
-- STATEMENT-PIN
example (m : ℕ) (a : Fin m) :
    (negFin m a).castSucc ≠ negFin (m + 1) a.castSucc := castSucc_negFin_ne m a

/-! ## Teil 5 — die Axiom-Wachen (Ist-gebunden)

Ist-Ausgabe des gruenen Builds (v4.30.0-rc2), pro Deklaration eingefroren
(Datei-Vollstaendigkeits-Regel, einschliesslich beider Hilfslemmata **und der Definition**).
Das durchgehende `[propext, Quot.sound]` und der Grund, warum auch die Definition eine Wache
traegt, stehen im Dateikopf unter „Woher das durchgehende Profil kommt" — dort mit der
Messung, auf die sie sich stuetzen. -/

/-- info: 'Reformulation.Proemial.StageParity.negFin_val' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms negFin_val

/-- info: 'Reformulation.Proemial.StageParity.castSucc_negFin_ne' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms castSucc_negFin_ne

/-- info: 'Reformulation.Proemial.StageParity.odd_no_neg_compatible' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms odd_no_neg_compatible

/-- info: 'Reformulation.Proemial.StageParity.eSym' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms eSym

/-- info: 'Reformulation.Proemial.StageParity.eSym_val' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms eSym_val

/-- info: 'Reformulation.Proemial.StageParity.eSym_strictMono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms eSym_strictMono

/-- info: 'Reformulation.Proemial.StageParity.eSym_negFin' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms eSym_negFin

/-- info: 'Reformulation.Proemial.StageParity.w_eSym' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms w_eSym

end Reformulation.Proemial.StageParity
