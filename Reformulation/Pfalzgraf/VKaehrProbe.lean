import Reformulation.Kaehr.Tableau

/-!
# Reformulation.Pfalzgraf.VKaehrProbe — die Vermutung V in Kaehrs Kleid, und die 24 Zeugen gegen eine Lift-Invariante

**Was das Modul ist (CLAUDE.md §4):** zwei kleine Sätze und ihre Eichungen. V0 ist eine ZUSAMMENSTELLUNG
(der Beweisterm ist zweimal `beweisbar_iff`, sonst nichts), V1 eine FOLGERUNG, deren Inhalt der Kopf von
`Pfalzgraf/Faserung.lean` (K4) seit dem 3. Oktober 2026 in Prosa sagt. Gebaut nach
`KorpusRev2/Prompt_V0_V1_Kaehr_Kleid_und_Lift_Zeugen.md` (Mathematiker, 23.10.2026).

## (1) V0 · V ist die Frage nach Kaehrs Kalkül gegen den Quotienten

Die Vermutung V (Faserung K4): *für jede zulässige Formel folgt aus der Gültigkeit im freien System die im
Quotienten.* Mit `beweisbar_iff` (Kaehr/Tableau, K5: Kaehrs Regeln von 1981, berichtigt, sind für das freie
System korrekt und vollständig) ist das dieselbe Frage wie: *ist Kaehrs Kalkül für zulässige Formeln auch
gegen Günthers Wertsemantik korrekt?* (`V_iff_kaehr_quot`, UNSER). Der Tableau-Bericht von 1993 (Bashford,
Joemann, Kaehr) nennt seinen Regelsatz *„noch nicht vollständig und korrekt“* (PDF-S. 5, an der Textschicht
geprüft). Für das freie System ist das seit Rev10 entschieden; für den Quotienten ist es offen, und das
Offene ist genau V.

Die andere Richtung ist entschieden und falsch: Kaehrs Kalkül ist für den Quotienten nicht vollständig
(`kaehr_quot_unvollstaendig`). Der Zeuge ist Kaehrs Trennfall (Kaehr 1981, S. 3 und 17, am Bild; im Bestand
`trennfall`, `trenn_gegen_zulaessig`): im Quotienten konstant Günthers 1, im freien System nicht gültig.
BESTÄTIGUNG im neuen Kleid, kein neuer Fund.

*Braucht V die Zulässigkeit?* Eine Suche (`#eval`, nicht im Baum) über p ∘ q mit allen 16³ Tripeln und über
p ∘ (q ∘ r) und p ∘ N(q ∘ r) mit Tripeln aus {∧, ∨, ⊃}³ fand **keine** unzulässige Formel, die beweisbar und
im Quotienten ungültig ist. Beide Hälften sind dort einzeln nicht leer (130 beziehungsweise 11776 unter
p ∘ q). Kein Treffer ist kein Satz; V bleibt mit der Einschränkung formuliert.

## (2) V1 · Die 24 Zeugen

Faserung K4 sagt: *die abgeschlossene Relation auf Paaren (freier Vektor, Quotientenwert) umfasst alle 24
Paare und ist zu grob* (Herkunft `KorpusRev2/Vorproben_Spec_B_Teil_I_Impl.md` §5). Hier steht der Satz mit
Zeugen: zu jedem der 2³ · 3 = 24 Paare (x, g) gibt es eine zulässige Formel φ, eine Quotientenbelegung v und
eine zu v kohärente freie Belegung f mit `auswFrei f φ = x` in allen drei Fasern und `auswQuot v φ = g`
(`lift_total`, `lift_total_alle`). Die Zeugen hat der Mathematiker gerechnet (23.10.2026, kürzeste
Ableitungen der Grösse 1, 3 und 5); `decide` prüft sie hier nach. Die Zahl 24 erzwingt nichts als die Zählung
2³ · 3; dass jedes Paar erreicht wird, ist der Satz.

Der Zeuge, der zählt: (T, T, T) bei Günthers 3, also wahr in jeder Faser und im Quotienten undesigniert
(`ttt_bei_drei`, EICHUNG). Er hat drei Variablen; dass es mit weniger nicht geht, sagt die Rechnung des
Mathematikers (kürzeste Ableitung), kein Satz hier: (D, P₂, D) aussen, (D, D, P₁) innen, mit P₁, P₂ den
beiden Projektionen (`opP1`, `opP2`, in Faserung nicht benannt).

Die Kohärenz gilt für die ganze Belegung, nicht nur für die Blätter: Variablen ausserhalb der Blattliste
bekommen ((T, T, T), Günthers 1), und das ist kohärent.

## (3) Die Folge für Beweiswege

Jede Invariante der Gestalt *„J(auswFrei f φ, auswQuot v φ) für EINE feste kohärente Hebung f von v“* ist
total und beweist nichts. Wer V beweist, muss über alle freien Belegungen zugleich sprechen, wie
`gueltigFrei` es tut.

## (4) V1 widerlegt V nicht

V quantifiziert über alle f. Der Zeuge für (T, T, T) bei 3 zeigt eine Hebung, unter der φ in jeder Faser
wahr ist, während der Quotientenwert undesigniert ist; φ ist darum nicht frei gültig, und V sagt über φ
nichts. **V bleibt offen.**

## Die Sätze

```text
V_iff_kaehr_quot             V0   ZUSAMMENSTELLUNG (Brücke beweisbar_iff);  UNSER
kaehr_quot_unvollstaendig    V0b  BESTÄTIGUNG an Kaehr 1981, S. 3, 17 (Trennfall)
lift_total                   V1   FOLGERUNG;  Herkunft Faserung K4 (3.10.)
lift_total_zahl              EICHUNG
lift_total_alle              V1   jedes Paar hat einen Zeugen
lift_paare_nodup             EICHUNG:  die 24 Paare sind paarweise verschieden
ttt_bei_drei                 EICHUNG
gegenprobe_inkohaerent       Gegenprobe:  ein inkohärentes Blatt macht den Zeugen ungültig
gegenprobe_unzulaessig       Gegenprobe:  ⊃⊃⊃ ist nicht zulässig
```

Kein `sorry`, kein `Classical.choice`, kein `native_decide`.
-/

namespace Reformulation.Pfalzgraf.VKaehrProbe

open Reformulation.Pfalzgraf Reformulation.Kaehr.Tableau

/-! ## V0 -/

/-- die Vermutung V (Faserung K4), als Prop -/
def V : Prop := ∀ φ : Fm, zulaessigFm φ = true → gueltigFrei φ → gueltigQuot φ

/-- Kaehrs Kalkül (berichtigt, Beweisbarkeit nach H1) ist für zulässige Formeln gegen den Quotienten korrekt -/
def kaehrQuotKorrekt : Prop := ∀ φ : Fm, zulaessigFm φ = true → beweisbar φ = true → gueltigQuot φ

/-- **V0.**  V genau dann, wenn Kaehrs Kalkül für zulässige Formeln quotientenkorrekt ist -/
theorem V_iff_kaehr_quot : V ↔ kaehrQuotKorrekt :=
  ⟨fun h φ hz hb => h φ hz ((beweisbar_iff φ).mp hb), fun h φ hz hf => h φ hz ((beweisbar_iff φ).mpr hf)⟩

/-- **V0b.**  Kaehrs Kalkül ist für den Quotienten nicht vollständig:  der Trennfall -/
theorem kaehr_quot_unvollstaendig :
    ¬ (∀ φ : Fm, zulaessigFm φ = true → gueltigQuot φ → beweisbar φ = true) := by
  intro h
  have hq : gueltigQuot trenn := fun v => by rw [trennfall.1 v]; rfl
  exact trennfall.2 ((beweisbar_iff trenn).mp (h trenn trenn_gegen_zulaessig.1 hq))

/-! ## V1 -/

/-- die erste Projektion (idempotent) -/
def opP1 : Op := (true, true, false, false)
/-- die zweite Projektion (idempotent) -/
def opP2 : Op := (true, false, true, false)

/-- ein Zeuge:  Formel, je Variable (freier Vektor, Quotientenwert), und das erreichte Paar -/
structure Zeuge where
  φ : Fm
  blaetter : List ((Bool × Bool × Bool) × Wert)
  x : Bool × Bool × Bool
  g : Wert

/-- das Blatt der Variablen n;  ausserhalb der Liste ((T, T, T), Günthers 1), kohärent -/
def Zeuge.blatt (z : Zeuge) (n : ℕ) : (Bool × Bool × Bool) × Wert := z.blaetter.getD n ((true, true, true), 0)
/-- die freie Belegung des Zeugen -/
def Zeuge.f (z : Zeuge) : FreieBelegung := fun n => match z.blatt n with | (b, _) => vec b.1 b.2.1 b.2.2
/-- die Quotientenbelegung des Zeugen -/
def Zeuge.v (z : Zeuge) : Belegung := fun n => (z.blatt n).2
/-- der Zeuge trägt:  φ zulässig, jedes Blatt kohärent, frei x in allen drei Fasern, im Quotienten g -/
def Zeuge.ok (z : Zeuge) : Bool :=
  zulaessigFm z.φ && z.blaetter.all (fun (b, g) => kohaerent (vec b.1 b.2.1 b.2.2) g)
  && (auswFrei z.f z.φ 0 == z.x.1) && (auswFrei z.f z.φ 1 == z.x.2.1) && (auswFrei z.f z.φ 2 == z.x.2.2)
  && (auswQuot z.v z.φ == z.g)

/-- die 24 Zeugen (Mathematiker, 23.10.2026);  Vektoren (Faser 1-2, 2-3, 1-3), Werte in Lean-Zählung -/
def zeugen : List Zeuge := [
  ⟨.junk opP1 opP1 opD (.var 0) (.junk opD opD opP1 (.var 1) (.var 2)),
    [((false, false, false), 2), ((false, true, false), 1), ((true, false, true), 0)],
    (false, false, false), 0⟩,
  ⟨.junk opP1 opP2 opP1 (.var 0) (.var 1),
    [((false, true, false), 1), ((true, false, true), 0)],
    (false, false, false), 1⟩,
  ⟨.var 0,
    [((false, false, false), 2)],
    (false, false, false), 2⟩,
  ⟨.junk opP1 opD opD (.var 0) (.var 1),
    [((false, false, false), 2), ((true, false, true), 0)],
    (false, false, true), 0⟩,
  ⟨.junk opP1 opP2 opD (.var 0) (.var 1),
    [((false, true, false), 1), ((true, false, true), 0)],
    (false, false, true), 1⟩,
  ⟨.junk opD opP1 opD (.var 0) (.var 1),
    [((false, false, false), 2), ((false, true, true), 1)],
    (false, false, true), 2⟩,
  ⟨.junk opP1 opD opD (.var 0) (.junk opD opD opP1 (.var 1) (.var 2)),
    [((false, false, false), 2), ((false, true, false), 1), ((true, false, true), 0)],
    (false, true, false), 0⟩,
  ⟨.var 0,
    [((false, true, false), 1)],
    (false, true, false), 1⟩,
  ⟨.junk opP1 opD opP1 (.var 0) (.var 1),
    [((false, false, false), 2), ((true, true, true), 0)],
    (false, true, false), 2⟩,
  ⟨.junk opP1 opD opD (.var 0) (.var 1),
    [((false, false, false), 2), ((true, true, true), 0)],
    (false, true, true), 0⟩,
  ⟨.var 0,
    [((false, true, true), 1)],
    (false, true, true), 1⟩,
  ⟨.junk opP1 opP2 opD (.var 0) (.junk opD opD opP1 (.var 1) (.var 2)),
    [((false, true, true), 1), ((false, false, false), 2), ((true, true, true), 0)],
    (false, true, true), 2⟩,
  ⟨.junk opD opP2 opP1 (.var 0) (.var 1),
    [((false, true, false), 1), ((true, false, true), 0)],
    (true, false, false), 0⟩,
  ⟨.junk opD opD opP1 (.var 0) (.junk opP1 opP2 opD (.var 1) (.var 2)),
    [((true, false, false), 2), ((false, true, false), 1), ((true, false, true), 0)],
    (true, false, false), 1⟩,
  ⟨.var 0,
    [((true, false, false), 2)],
    (true, false, false), 2⟩,
  ⟨.var 0,
    [((true, false, true), 0)],
    (true, false, true), 0⟩,
  ⟨.junk opD opD opD (.var 0) (.junk opP1 opP2 opD (.var 1) (.var 2)),
    [((true, false, false), 2), ((false, true, false), 1), ((true, false, true), 0)],
    (true, false, true), 1⟩,
  ⟨.junk opD opP2 opD (.var 0) (.var 1),
    [((false, true, true), 1), ((true, false, false), 2)],
    (true, false, true), 2⟩,
  ⟨.junk opD opD opP1 (.var 0) (.var 1),
    [((false, true, false), 1), ((true, false, true), 0)],
    (true, true, false), 0⟩,
  ⟨.junk opD opD opD (.var 0) (.var 1),
    [((false, true, false), 1), ((true, false, false), 2)],
    (true, true, false), 1⟩,
  ⟨.junk opD opD opP1 (.var 0) (.var 1),
    [((false, false, false), 2), ((true, true, true), 0)],
    (true, true, false), 2⟩,
  ⟨.var 0,
    [((true, true, true), 0)],
    (true, true, true), 0⟩,
  ⟨.junk opD opD opD (.var 0) (.var 1),
    [((false, true, true), 1), ((true, false, false), 2)],
    (true, true, true), 1⟩,
  ⟨.junk opD opP2 opD (.var 0) (.junk opD opD opP1 (.var 1) (.var 2)),
    [((false, true, true), 1), ((false, false, false), 2), ((true, true, true), 0)],
    (true, true, true), 2⟩
]

/-- **V1.**  Alle 24 Zeugen tragen -/
theorem lift_total : zeugen.all Zeuge.ok = true := by decide

theorem lift_total_zahl : zeugen.length = 24 := by decide

/-- **V1.**  Jedes Paar (x, g) hat einen Zeugen -/
theorem lift_total_alle : ∀ b0 b1 b2 : Bool, ∀ g : Wert,
    ∃ z ∈ zeugen, z.x = (b0, b1, b2) ∧ z.g = g := by decide

/-- die 24 Paare sind paarweise verschieden -/
theorem lift_paare_nodup : (zeugen.map fun z => (z.x, z.g)).Nodup := by decide

/-- **TTT.**  (T, T, T) bei Günthers 3, mit drei Variablen -/
theorem ttt_bei_drei : ∃ z ∈ zeugen, z.x = (true, true, true) ∧ z.g = 2 ∧ z.blaetter.length = 3
    ∧ z.ok = true := by decide

/-- der Zeuge für (T, T, T) bei 3, Blatt 2 auf ((T, T, F), Günthers 1) gesetzt:  inkohärent -/
def zeugeInkohaerent : Zeuge :=
  ⟨.junk opD opP2 opD (.var 0) (.junk opD opD opP1 (.var 1) (.var 2)),
    [((false, true, true), 1), ((false, false, false), 2), ((true, true, false), 0)],
    (true, true, true), 2⟩

/-- Gegenprobe:  das inkohärente Blatt macht den Zeugen ungültig -/
theorem gegenprobe_inkohaerent : zeugeInkohaerent.ok = false := by decide

/-- Gegenprobe:  ⊃⊃⊃ ist nicht zulässig -/
theorem gegenprobe_unzulaessig : zulaessigFm (.junk opI opI opI (.var 0) (.var 1)) = false := by decide

end Reformulation.Pfalzgraf.VKaehrProbe

/-! ## Wachen -/

/-- info: 'Reformulation.Pfalzgraf.VKaehrProbe.V_iff_kaehr_quot' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Pfalzgraf.VKaehrProbe.V_iff_kaehr_quot

/-- info: 'Reformulation.Pfalzgraf.VKaehrProbe.kaehr_quot_unvollstaendig' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Pfalzgraf.VKaehrProbe.kaehr_quot_unvollstaendig

/-- info: 'Reformulation.Pfalzgraf.VKaehrProbe.lift_total' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Pfalzgraf.VKaehrProbe.lift_total

/-- info: 'Reformulation.Pfalzgraf.VKaehrProbe.lift_total_zahl' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Pfalzgraf.VKaehrProbe.lift_total_zahl

/-- info: 'Reformulation.Pfalzgraf.VKaehrProbe.lift_total_alle' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Pfalzgraf.VKaehrProbe.lift_total_alle

/-- info: 'Reformulation.Pfalzgraf.VKaehrProbe.lift_paare_nodup' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Pfalzgraf.VKaehrProbe.lift_paare_nodup

/-- info: 'Reformulation.Pfalzgraf.VKaehrProbe.ttt_bei_drei' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Pfalzgraf.VKaehrProbe.ttt_bei_drei

/-- info: 'Reformulation.Pfalzgraf.VKaehrProbe.gegenprobe_inkohaerent' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Pfalzgraf.VKaehrProbe.gegenprobe_inkohaerent

/-- info: 'Reformulation.Pfalzgraf.VKaehrProbe.gegenprobe_unzulaessig' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Pfalzgraf.VKaehrProbe.gegenprobe_unzulaessig
