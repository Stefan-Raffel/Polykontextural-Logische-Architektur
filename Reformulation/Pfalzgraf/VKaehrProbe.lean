import Reformulation.Kaehr.Tableau

/-!
# Reformulation.Pfalzgraf.VKaehrProbe — die Vermutung V in Kaehrs Kleid, die 24 Zeugen gegen eine Lift-Invariante, und V ist falsch

**Was das Modul ist (CLAUDE.md §4):** zwei kleine Sätze und ihre Eichungen. V0 ist eine ZUSAMMENSTELLUNG
(der Beweisterm ist zweimal `beweisbar_iff`, sonst nichts), V1 eine FOLGERUNG, deren Inhalt der Kopf von
`Pfalzgraf/Faserung.lean` (K4) seit dem 3. Oktober 2026 in Prosa sagt. Gebaut nach
`KorpusRev2/Prompt_V0_V1_Kaehr_Kleid_und_Lift_Zeugen.md` (Mathematiker, 23.10.2026). **V2** (`nicht_V`,
FOLGERUNG, UNSER) entscheidet die Vermutung, negativ; gebaut nach `KorpusRev2/Prompt_V2_nicht_V_Gegenbeispiel.md`
(Mathematiker, 23.10.2026).

## (1) V0 · V ist die Frage nach Kaehrs Kalkül gegen den Quotienten

Die Vermutung V (Faserung K4): *für jede zulässige Formel folgt aus der Gültigkeit im freien System die im
Quotienten.* Mit `beweisbar_iff` (Kaehr/Tableau, K5: Kaehrs Regeln von 1981, berichtigt, sind für das freie
System korrekt und vollständig) ist das dieselbe Frage wie: *ist Kaehrs Kalkül für zulässige Formeln auch
gegen Günthers Wertsemantik korrekt?* (`V_iff_kaehr_quot`, UNSER). Der Tableau-Bericht von 1993 (Bashford,
Joemann, Kaehr) nennt seinen Regelsatz *„noch nicht vollständig und korrekt“* (PDF-S. 5, an der Textschicht
geprüft). Für das freie System ist das seit Rev10 entschieden; für den Quotienten war es offen, und das
Offene war genau V. Seit V2 ist es entschieden, negativ (`kaehr_quot_inkorrekt`).

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
(`ttt_bei_drei`, EICHUNG). Der Zeuge der Liste hat drei Variablen: (D, P₂, D) aussen, (D, D, P₁) innen, mit
P₁, P₂ den beiden Projektionen (`opP1`, `opP2`, in Faserung nicht benannt). **Eine Variable genügt**
(`ttt_bei_eins`, Zeuge des Mathematikers, Abnahme 23.10.): p ↦ ((T, T, T), Günthers 1), aussen (D, D, P₂) auf
p und innen (D, P₂, D) auf N₁p, N₂N₁p. Die Rechnung des Mathematikers vom Mittag war die kürzeste Ableitung
über frischen Blättern, nicht über Variablen. Auch dieser Zeuge widerlegt V nicht: der andere kohärente
Lift von Günthers 1, (T, F, T), gibt frei (T, F, F); die Formel ist nicht frei gültig.

Die Kohärenz gilt für die ganze Belegung, nicht nur für die Blätter: Variablen ausserhalb der Blattliste
bekommen ((T, T, T), Günthers 1), und das ist kohärent.

## (3) Die Folge für Beweiswege

Jede Invariante der Gestalt *„J(auswFrei f φ, auswQuot v φ) für EINE feste kohärente Hebung f von v“* ist
total und beweist nichts. Das schrieb dieser Kopf, solange V offen war: wer V beweist, müsse über alle
freien Belegungen zugleich sprechen. Seit V2 gibt es nichts mehr zu beweisen; auch über alle freien
Belegungen zugleich trägt keine Invariante, weil eine Formel unter jeder freien Belegung wahr sein und im
Quotienten den dritten Wert tragen kann.

## (4) V1 widerlegt V nicht

V quantifiziert über alle f. Der Zeuge für (T, T, T) bei 3 zeigt eine Hebung, unter der φ in jeder Faser
wahr ist, während der Quotientenwert undesigniert ist; φ ist darum nicht frei gültig, und V sagt über φ
nichts. *Hier stand bis zum 23. Oktober 2026 abends „V bleibt offen“.* Widerlegt ist V durch V2, nicht durch V1.

## (5) V2 · V ist falsch

**Das Gegenbeispiel** (`gegenV`, Mathematiker, `KorpusRev2/Befund_V2_Gegenbeispiel_zu_V.md`): eine zulässige
Formel in EINER Variablen p, Grösse 27 (27 Knoten, neunmal p), nur mit D, P₁, P₂ und den Negatoren N₁, N₂. Sie
ist im freien System gültig, wahr in allen drei Fasern unter jeder Belegung (`gegenV_gueltigFrei`), und hat im
Quotienten bei p = Günthers 1 den Wert Günthers 3, undesigniert (`gegenV_quot`). Aufbau: drei Teilformeln α, β,
γ, jede mit Quotientenwert 3 bei p = 1; α ist in Faser 1-2 konstant wahr (auch in 2-3), β in 2-3, γ in 1-3
(per `#eval` nachgerechnet, nicht im Baum). Die Projektionen setzen die Fasern zusammen: aussen (P₁, P₂, P₂)
über α und (P₁, P₁, P₂)(β, γ). Weil alle drei Teile denselben Quotientenwert haben und P₁, P₂ idempotent sind,
bleibt er 3. Also `nicht_V`, und mit V0 `kaehr_quot_inkorrekt`. Kaehrs Regeln schliessen gegenV
(`gegenV_beweisbar`).

**Warum es existieren musste** (Befund §2, PROSA, kein Satz): Für eine Variable und festen Quotientenwert von p
zerfallen die Terme nach ihrem Quotientenwert in drei Klassen. Innerhalb einer Klasse rekombinieren die
Projektionen faserweise; jede Klasse ist ein Produkt dreier Mengen von Faserfunktionen. Mit ∧, ∨, N₁, N₂ erreicht
jede nichtleere Klasse in jeder Faser alle 256 Funktionen Bool³ → Bool, darunter die Konstante „wahr“. Das ist
gerechnet (`v2_product.py`, Mathematiker), nicht bewiesen.

**Nicht behauptet:** dass 27 minimal ist. Die Suche vom 3. Oktober war bis Grösse 10 leer; dazwischen ist
nichts gesucht.

**Die Folge:** Kaehrs Kalkül ist gegen Günthers Werte für zulässige Formeln weder korrekt (V2) noch
vollständig (V0b). Freies System und Quotient sind zwei Semantiken, nicht eine in zwei Kleidern.

**Offen:** Formelklassen ohne Projektionen (nur ∧, ∨ und Negatoren, wie Kaehrs G^(3,2)). Die Produktstruktur
braucht die Projektionen; ohne sie ist die Frage neu.

## Die Sätze

```text
V_iff_kaehr_quot             V0   ZUSAMMENSTELLUNG (Brücke beweisbar_iff);  UNSER
kaehr_quot_unvollstaendig    V0b  BESTÄTIGUNG an Kaehr 1981, S. 3, 17 (Trennfall)
lift_total                   V1   FOLGERUNG;  Herkunft Faserung K4 (3.10.)
lift_total_zahl              EICHUNG
lift_total_alle              V1   jedes Paar hat einen Zeugen
lift_paare_nodup             EICHUNG:  die 24 Paare sind paarweise verschieden
ttt_bei_drei                 EICHUNG
ttt_bei_eins                 EICHUNG:  dasselbe Paar mit einer Variablen (Zeuge des Mathematikers)
gegenprobe_inkohaerent       Gegenprobe:  ein inkohärentes Blatt macht den Zeugen ungültig
gegenprobe_unzulaessig       Gegenprobe:  ⊃⊃⊃ ist nicht zulässig
nicht_V                      V2   FOLGERUNG, UNSER:  V ist falsch
kaehr_quot_inkorrekt         V2   FOLGERUNG, UNSER:  Kaehrs Kalkül nicht quotientenkorrekt (mit V0)
gegenV_zulaessig, gegenV_frei_acht, gegenV_quot, gegenV_gueltigFrei, gegenV_nicht_gueltigQuot,
  gegenV_beweisbar           EICHUNG am Gegenbeispiel
auswFrei_lokal, gegenV_vars  Hilfssätze
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

/-- (T, T, T) bei Günthers 3 mit EINER Variablen:  p = Günthers 1, Lift (T, T, T) (Mathematiker, 23.10.) -/
def zeugeEine : Zeuge :=
  ⟨.junk opD opD opP2 (.var 0) (.junk opD opP2 opD (.neg₁ (.var 0)) (.neg₂ (.neg₁ (.var 0)))),
    [((true, true, true), 0)], (true, true, true), 2⟩

/-- **TTT.**  Eine Variable genügt -/
theorem ttt_bei_eins : zeugeEine.ok = true ∧ zeugeEine.blaetter.length = 1 := by decide

/-- der Zeuge für (T, T, T) bei 3, Blatt 2 auf ((T, T, F), Günthers 1) gesetzt:  inkohärent -/
def zeugeInkohaerent : Zeuge :=
  ⟨.junk opD opP2 opD (.var 0) (.junk opD opD opP1 (.var 1) (.var 2)),
    [((false, true, true), 1), ((false, false, false), 2), ((true, true, false), 0)],
    (true, true, true), 2⟩

/-- Gegenprobe:  das inkohärente Blatt macht den Zeugen ungültig -/
theorem gegenprobe_inkohaerent : zeugeInkohaerent.ok = false := by decide

/-- Gegenprobe:  ⊃⊃⊃ ist nicht zulässig -/
theorem gegenprobe_unzulaessig : zulaessigFm (.junk opI opI opI (.var 0) (.var 1)) = false := by decide

/-! ## V2 -/

/-- Spiegel von `auswQuot_lokal`:  die freie Auswertung hängt nur von den Variablen der Formel ab (punktweise je
    Faser, darum ohne `funext`) -/
theorem auswFrei_lokal : ∀ (φ : Fm) (f f' : FreieBelegung), (∀ n ∈ vars φ, ∀ i, f n i = f' n i) →
    ∀ i, auswFrei f φ i = auswFrei f' φ i
  | .var n, f, f', h => h n List.mem_cons_self
  | .neg₁ a, f, f', h => by
    have ih := auswFrei_lokal a f f' h
    intro i
    match i with
    | ⟨0, _⟩ => exact congrArg not (ih 0)
    | ⟨1, _⟩ => exact ih 2
    | ⟨2, _⟩ => exact ih 1
  | .neg₂ a, f, f', h => by
    have ih := auswFrei_lokal a f f' h
    intro i
    match i with
    | ⟨0, _⟩ => exact ih 2
    | ⟨1, _⟩ => exact congrArg not (ih 1)
    | ⟨2, _⟩ => exact ih 0
  | .junk o0 o1 o2 a b, f, f', h => by
    intro i
    show ap (oAt o0 o1 o2 i) (auswFrei f a i) (auswFrei f b i) = ap (oAt o0 o1 o2 i) (auswFrei f' a i) (auswFrei f' b i)
    rw [auswFrei_lokal a f f' (fun n hn => h n (List.mem_append_left _ hn)) i,
      auswFrei_lokal b f f' (fun n hn => h n (List.mem_append_right _ hn)) i]

/-- **das Gegenbeispiel zu V** (Mathematiker, 23.10.2026;  `KorpusRev2/Befund_V2_Gegenbeispiel_zu_V.md` §1):  eine Variable,
    Grösse 27;  aussen (P₁, P₂, P₂) über α und (P₁, P₁, P₂)(β, γ) -/
def gegenV : Fm :=
  .junk opP1 opP2 opP2
    (.junk opD opD opP2 (.junk opD opD opD (.var 0) (.neg₁ (.var 0))) (.neg₂ (.neg₁ (.var 0))))
    (.junk opP1 opP1 opP2
      (.junk opD opD opP2 (.junk opD opD opD (.var 0) (.neg₂ (.var 0))) (.neg₂ (.neg₁ (.var 0))))
      (.junk opD opP2 opD (.junk opP2 opD opD (.neg₂ (.var 0)) (.neg₁ (.var 0))) (.neg₂ (.neg₁ (.var 0)))))

/-- nur D, P₁, P₂:  idempotent, also zulässig -/
theorem gegenV_zulaessig : zulaessigFm gegenV = true := by decide
/-- unter allen acht Werten der einen Variablen wahr in allen drei Fasern -/
theorem gegenV_frei_acht : ∀ b0 b1 b2 : Bool, ∀ i : Faser, auswFrei (fun _ => vec b0 b1 b2) gegenV i = true := by decide
/-- bei p = Günthers 1 im Quotienten Günthers 3 -/
theorem gegenV_quot : auswQuot (fun _ => (0 : Wert)) gegenV = 2 := by decide
/-- gegenV hat nur die Variable 0 -/
theorem gegenV_vars : (vars gegenV).all (fun n => Nat.beq n 0) = true := by decide

/-- frei gültig:  jede freie Belegung stimmt auf den Variablen von gegenV mit einer konstanten überein -/
theorem gegenV_gueltigFrei : gueltigFrei gegenV := by
  intro f i
  rw [auswFrei_lokal gegenV f (fun _ => vec (f 0 0) (f 0 1) (f 0 2)) ?_ i]
  · exact gegenV_frei_acht _ _ _ i
  · intro n hn j
    have h0 : n = 0 := Nat.eq_of_beq_eq_true (all_mp gegenV_vars n hn)
    subst h0
    match j with
    | ⟨0, _⟩ => rfl
    | ⟨1, _⟩ => rfl
    | ⟨2, _⟩ => rfl

/-- im Quotienten nicht gültig -/
theorem gegenV_nicht_gueltigQuot : ¬ gueltigQuot gegenV := by
  intro h
  have h0 := h (fun _ => 0)
  rw [gegenV_quot] at h0
  exact absurd h0 (by decide)

/-- **V2.**  V ist falsch -/
theorem nicht_V : ¬ V := fun h => gegenV_nicht_gueltigQuot (h gegenV gegenV_zulaessig gegenV_gueltigFrei)
/-- **V2.**  Kaehrs Kalkül ist für zulässige Formeln gegen den Quotienten nicht korrekt (mit V0) -/
theorem kaehr_quot_inkorrekt : ¬ kaehrQuotKorrekt := fun h => nicht_V (V_iff_kaehr_quot.mpr h)
/-- Kaehrs Regeln schliessen gegenV -/
theorem gegenV_beweisbar : beweisbar gegenV = true := by decide

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

/-- info: 'Reformulation.Pfalzgraf.VKaehrProbe.ttt_bei_eins' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Pfalzgraf.VKaehrProbe.ttt_bei_eins

/-- info: 'Reformulation.Pfalzgraf.VKaehrProbe.auswFrei_lokal' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Pfalzgraf.VKaehrProbe.auswFrei_lokal

/-- info: 'Reformulation.Pfalzgraf.VKaehrProbe.gegenV_zulaessig' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Pfalzgraf.VKaehrProbe.gegenV_zulaessig

/-- info: 'Reformulation.Pfalzgraf.VKaehrProbe.gegenV_frei_acht' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Pfalzgraf.VKaehrProbe.gegenV_frei_acht

/-- info: 'Reformulation.Pfalzgraf.VKaehrProbe.gegenV_quot' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Pfalzgraf.VKaehrProbe.gegenV_quot

/-- info: 'Reformulation.Pfalzgraf.VKaehrProbe.gegenV_vars' does not depend on any axioms -/
#guard_msgs in #print axioms Reformulation.Pfalzgraf.VKaehrProbe.gegenV_vars

/-- info: 'Reformulation.Pfalzgraf.VKaehrProbe.gegenV_gueltigFrei' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Pfalzgraf.VKaehrProbe.gegenV_gueltigFrei

/-- info: 'Reformulation.Pfalzgraf.VKaehrProbe.gegenV_nicht_gueltigQuot' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Pfalzgraf.VKaehrProbe.gegenV_nicht_gueltigQuot

/-- info: 'Reformulation.Pfalzgraf.VKaehrProbe.nicht_V' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Pfalzgraf.VKaehrProbe.nicht_V

/-- info: 'Reformulation.Pfalzgraf.VKaehrProbe.kaehr_quot_inkorrekt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Pfalzgraf.VKaehrProbe.kaehr_quot_inkorrekt

/-- info: 'Reformulation.Pfalzgraf.VKaehrProbe.gegenV_beweisbar' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Pfalzgraf.VKaehrProbe.gegenV_beweisbar
