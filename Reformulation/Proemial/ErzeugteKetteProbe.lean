import Reformulation.Proemial.UebergangMitInhaltProbe   -- waehleNeu, step_iter, stepNeu_iter; über KenogramForkProbe: Choice, ascentBy, Fork
import Reformulation.Proemial.DirectionChoice            -- factorsThroughUnit_iff_constant

/-!
# Proemial.ErzeugteKetteProbe — die erzeugte Kette einer Wahlregel, ihre Faser, die Retraktion, der Ein-Schritt, die Unit-Brücke

STANDALONE, NICHT im Aggregat; Target `Probes`. AxiomGate unberührt. Sonde nach
`KorpusRev2/Prompt_Instanz_Erzeugte_Kette_Bau.md` (Mathematiker, 24.10.2026 22:49;  Architekt 22:47).  Grundlage:
`KorpusRev2/Paragraph20_Turm_Antwort_Mathematiker_auf_Horistes_Speculum.md` (§2 Fasersatz, §3 Ein-Schritt, §4 Namen, §5 K-1),
`Vorprobe_Paragraph20_Traeger_Turm_beide_Richtungen.md` (§1, Nachtrag 22:28), Horistes H1–H5, Speculum S1–S4.
Konsumiert `KenogramForkProbe` (`Choice`, `ascentBy`, `forkWidth`), `UebergangMitInhaltProbe` (`waehleNeu`, `step_iter`),
`TowerAsymmetryProbe` (`Tower`, `step`), `Kenogram` (`isRGS_head`, `isRGS_getElem_le`, `isRGS_concat`), `DirectionChoice`
(`factorsThroughUnit_iff_constant`);  ändert nichts davon.

## WAS — Mathematik des Hauses über dem Turm

Eine Wahlregel `c : Choice` wählt an jedem Turmpunkt ein zulässiges nächstes Zeichen;  `ascentBy c` hängt es an.  **`erzeugt c n`**
ist die Kette, die `c` in `n` Schritten ab der leeren Kette hervorbringt — der Lauf einer Strategie innerhalb der Erzeugungs-Regel
„wiederholen oder neu setzen" (`Kenogram.Stream`, K-3, F-2).  Der Name stützt sich auf K-3, nicht auf EuW S. 7 (dort ist das Erzeugte
„ein Denken, das bloß mentales Bild ist" — die Wortfalle „Bild", Speculum S3).  Verwandt, nicht gleich:  `track` (NegationCycle,
SpurProbe) ist der Weg EINES Werts unter einem Negatorwort;  die Präfix-Spur von `KenogramForkProbe` ist das Bild unter `descent`;
`erzeugt` ist der Lauf EINER Regel.  Drei Gegenstände, kein gemeinsamer Name;  „Spur" steht darum hier nicht.

```text
erzeugt c n            die erzeugte Kette (Listenebene;  als RGS hätte sie den Typ RGS ((…).1), wie step_iter)
aufPfad r x            x liegt auf dem Pfad von r:  x.1 < |r| und x.2 = r.take x.1   (gleichwertig:  echtes Präfix von r, `aufPfad_iff`)
ueberschreibe r hr c₀  auf dem Pfad von r das nächste Zeichen von r, sonst c₀
regelNach r hr         ueberschreibe r hr waehleNull — eine Regel, die r erzeugt
```

## Die Sätze

```text
fasersatz_a        FOLGERUNG   erzeugt c |r| = r  ↔  ∀ i < |r|, c (r.take i) = r_i — die Regel liegt längs des Pfades fest
                               (Horistes H1;  Speculum:  „nah an der Definition" — (a) ist beinahe sie)
fasersatz_b        FOLGERUNG   ueberschreibe r hr c₀ erzeugt r, und stimmt abseits des Pfades mit c₀ überein
faser_iff          FOLGERUNG   erzeugt c |r| = r  ↔  c stimmt überall mit ueberschreibe r hr c überein:  frei sind GENAU die Punkte
                               abseits des Pfades (die Faser ist {ueberschreibe r hr c₀ | c₀} im Wert)
erzeugt_regelNach  FOLGERUNG   die Retraktion:  erzeugt (regelNach r hr) |r| = r
erzeugt_lokal      Hilfssatz   zwei Regeln, die unterhalb n übereinstimmen, erzeugen dieselbe Kette der Länge n;
erzeugt_lokal_pfad FOLGERUNG   die schärfere Fassung:  Übereinstimmung auf dem Pfad genügt
ein_schritt        FOLGERUNG   ascentBy c x = ascentBy c' x ↔ (c x).1 = (c' x).1 (Horistes H4:  E&W S. 26 kennt nur den einen Schritt)
ein_schritt_nicht_injektiv  FOLGERUNG (Zeuge, decide)  an [0,0] derselbe Schritt, an [0,1] verschiedene Wirkung
unit_ist_null, unit_erzeugt, unit_faktor_erzeugt   FOLGERUNG   eine Regel, deren Wert nicht vom Punkt abhängt, wählt überall 0 und
                               erzeugt [0, …, 0] (über step_iter;  die dritte Fassung über factorsThroughUnit_iff_constant)
stufe_zwei_injektiv  FOLGERUNG  an Stufe 2 trennt erzeugt die Wirkungen auf `[0]`
stufe_drei_faser   EICHUNG (decide)  an Stufe 3 nicht:  zwei Paare verschiedener Regeln mit derselben Kette
gabel_abseits      EICHUNG (decide)  die Gabelbreiten abseits des Pfades an Stufe 3:  forkWidth [0,1] = 3, forkWidth [0,0] = 2

inFaser c r        Definition:  c erzeugt r (die Faser über r, als Prädikat)
erzeugt_praefix    Hilfssatz   m ≤ n → erzeugt c m <+: erzeugt c n
faser_praefix      FOLGERUNG   „⇒":  r <+: s → Faser(s) ⊆ Faser(r), ohne Voraussetzung
ordnung_aus_fasern FOLGERUNG   für IsRGS r, IsRGS s, s ≠ []:  r <+: s ↔ Faser(s) ⊆ Faser(r)  (Vorschlag Horistes H-1, Fassung des
                               Mathematikers;  im Fall „s echtes Präfix von r" zwei Überschreibungen von s, die am Punkt s 0 bzw. 1 wählen)
wurzel_kollaps     FOLGERUNG   Faser(`[]`) und Faser(`[0]`) sind beide alle Regeln, `[0]` ist kein Präfix von `[]`;  ohne s ≠ [] fällt
                               ordnung_aus_fasern.  Grund:  über der leeren Kette ist nur 0 zulässig (das Feld von Choice)
alle_regeln        FOLGERUNG   wer von allen Regeln erzeugt wird, ist `[]` oder `[0]`
faser_ordnung_voll FOLGERUNG   (O-3) Faser(s) ⊆ Faser(r) ↔ r <+: s ∨ (s = `[]` ∧ r = `[0]`) — die Präordnung mit genau einem Kollaps
eich_ordnung_drei  EICHUNG (decide)  an Stufe ≤ 3:  regelNach [0,1,2] in Faser([0,1,2]), nicht in Faser([0,0]);  die Überschreibung
                               von [0,1] mit 0 in Faser([0,1]), nicht in Faser([0,1,1]);  Faser([0,1,2]) ⊆ Faser([0,1])

forkWidth_eq_two_iff   FOLGERUNG   (G-1) r ≠ [] → (forkWidth r = 2 ↔ r = replicate n 0);  zwei_glieder_wiederholung:  ↔ r = erzeugt
                                   waehleNull n (n ≥ 1);  eich_zwei_glieder (decide):  auf Stufe 1 … 4 genau eine Kette mit zwei Gliedern
umtausch_identitaet    ZUSAMMENSTELLUNG  (G-2) jede Normalform mit dem Muster von r.map σ ist r, für injektives σ (aus
                                   rgs_unique_of_pattern);  umbenennung_trennt:  r.map σ = s, beide RGS → r = s
gabelung_nicht_vertauschbar  FOLGERUNG  (G-3) keine Umbenennung führt [0,0] in [0,1];  verschiedene Fortsetzungen derselben Kette gehen
                                   durch keine injektive Umbenennung ineinander über
einsortig_unmoeglich_zwei  FOLGERUNG, NEGATIV  (G-4) ¬ ∃ f : W 2 → RGS 3, injektiv — sechs Wirkungen, fünf Ketten
einsortig_moeglich_eins    EICHUNG  (G-5) ∃ f : W 1 → RGS 2, bijektiv — die Gestalt von stufe_zwei_injektiv
zaehlung_drei_vier     EICHUNG (decide)  (G-6) an den Generatorlisten:  Π Gabelbreiten auf Stufe 1, 2, 3 = 2, 6, 216 gegen |rgsList| eine
                                   Stufe höher = 2, 5, 15;  Stufe 4 nur gerechnet (89 579 520 gegen 52)
```

**Die Produktformel** „|Faser über r| = Π der Gabelbreiten abseits des Pfades" ist der Zählschatten von `faser_iff` und hier KEIN Satz
(eine Wahlregel ist eine Funktion auf dem ganzen Turm;  die Zählung braucht ihr Segment unterhalb n als endliches Objekt, das der
Bestand nicht führt).  EICHUNG, gerechnet ausserhalb:  Stufe 3, 12 Segmente, 5 Fasern, je Produkt (3, 3, 2, 2, 2) — Mathematiker
(faser.py) und Instanz (Begutachtung 22:24) unabhängig;  Stufe 4, 2 592 Segmente, 15 Fasern, alle Produkt — Mathematiker.

## SETZUNG (Architekt, 25.10. 09:36;  Register SA1/PL32)

- **Wortlaut:**  „Wird der Relator zum Relatum, so tauschen die Rollen — in beide Richtungen.  Was der Relator als Relatum zeigt, lässt
  ihn nicht zurückgewinnen:  der Verlust trifft den Inhalt, nicht die Richtung."  Klasse DEUTEND:  sie entscheidet Günthers offene Stelle
  „Der Ort und die Rückgewinnbarkeit" für das Haus.
- Was sie hier entscheidet:  **„Glied oder Bild"** — die Gleichsetzung „Regel auf Stufe n wird Kette auf Stufe n + 1" gilt für die
  **Rolle**;  der **Inhalt** ist Quotient.
- ZUORDNUNG zum Bau, **ungeprüft** (Setzung, keine Quellenlesung;  Liste PL27):  „in beide Richtungen" ↔ `erzeugt` / `regelNach`;  „lässt
  ihn nicht zurückgewinnen" ↔ `ein_schritt_nicht_injektiv` (verschiedene Regeln, dieselbe Kette);  dass die Rolle zurückkommt ↔
  `erzeugt_regelNach` (Retraktion:  zu jeder Kette eine Regel, die sie erzeugt).
- **OFFEN (beim Architekten, Register SA1):**  An der ersten Stufe ist der Wortlaut stärker als der Bau — `einsortig_moeglich_eins`:  dort
  geht nichts verloren.
- NICHT:  die Setzung ist nicht A20-4 und gibt §20 keinen Träger.

## LESART (nur hier;  kein Dokstring eines Satzes trägt eine)

- Speculum S1:  Günthers zwei „exchange" — (I) der symmetrische [T27][T57][T63][T64], (II) der Wechsel, den R_pr bewirkt, „not mutual"
  [T49][T10].  Die Gabelung ↔ (I), der Übergang Regel ↔ Kette ↔ (II):  ZUORDNUNG.
- `faser_iff` / `fasersatz_b` und A20-4 (Definitionen §20, Fassung 25.10.:  „Ein Wechsel, zwei Paare, in einem Satz"):  ZUSAMMENSCHAU.
  Ein Biconditional sagt nichts über die Modalität (Horistes H-2);  dass es „ein Vorgang, der beide Paare betrifft" sei, ist Lesart,
  keine Eigenschaft des Satzes.  Ob die zwei Wachen von A20-4 erfüllt sind (nicht von der Kleinheit erzwungen;  auf dem zweiten Paar
  Relator und Relatum selbst), ist NICHT geprüft.
- Vermerk:  Bis 25.10. stand hier „in der BURIDAN-Modalität ([T30]) …, NICHT in der von S. 23" und die alte A20-4-Fassung („bedingt").
  Buridan gegen S. 23 zu stellen war eine Fehllesung von [T30] (Definitionen §20, Buridan-Absatz und Offene Stellen;  Register PL33/PL34).
- Wort „Gabelung", nicht „Schwebe" ([T63] steht in der kognitiven Zeile;  hier volitiv, [T64]).
- „Ordnung" nur mit Index:  O1 (Index) / O2 (Aktualisierung).
- `ordnung_aus_fasern` gewinnt die Präfixordnung der Ketten aus den Fasern des Wechsels, ohne den Index zu benutzen (Horistes' Probe
  „Index-Entzug":  die Aussage spricht über Mengen von Regeln, nicht über Längen) — REICHWEITE:  über einem gestuften Bereich (`Choice`
  lebt auf Σ n, RGS n).  Günther, C&V S. 23:  „the order is only constituted by the fact that the exchange …" — S. 23 stellt ZWEI
  Lesarten nebeneinander („double way";  Speculum S-1 (c));  `ordnung_aus_fasern` realisiert die zweite, als WAHL, die erste (die
  Ordnung vorausgesetzt) bleibt daneben.  „constituted" bindet bei Günther den Wechsel von Relator und Relatum an O1 — das ist die
  Paarung von `ordnung_aus_fasern`, NICHT die von `faser_iff` (Speculum S-2, Horistes H-2).
- `wurzel_kollaps` als Beobachtung:  Faser-Ordnung und Präfixordnung unterscheiden sich nur an der Wurzel (`faser_ordnung_voll`).
  Ob das etwas über Günthers „Unten des Abstiegs" oder über „die 1 ohne Vorgänger" sagt, ist eine FRAGE, kein Satz.

**Was der Turm nicht kann** (G-1 … G-6;  Grundlage `Notiz_Turm_Perspektive_Instanz_Impl.md`, Hermeneutes U):
- (1) Die Gabelung ist „symmetrisch" im Sinn der Unbestimmtheit (`choice_undetermined`), nicht der Invarianz:  Günthers symmetrischer
  Umtausch ist als Operation (Wertpermutation, C&V S. 20 „implemented in the Table of Negation") auf Kenogrammen die Identität
  (`umtausch_identitaet`) — A20-5 Fassung 1;  die Glieder einer Gabelung sind verschiedene Kenogramme (`gabelung_nicht_vertauschbar`),
  eines ist ausgezeichnet (`nichtIntern_iff_akkretiv`).
- (2) Zwei Glieder nur längs der reinen Wiederholung (`forkWidth_eq_two_iff`, `zwei_glieder_wiederholung`);  Günthers Umtausch hat zwei
  Glieder, bei dreien ist die Relation geordnet (C&V S. 14, nach Hermeneutes am Bild) — die Übertragung von Werten auf Fortsetzungen ist UNSER.
- (3) Ein einsortiger Träger mit dem Ein-Schritt („der Relator auf Stufe n wird Relatum auf Stufe n + 1" als Gleichsetzung) ist ab n = 2
  durch Zählung ausgeschlossen (`einsortig_unmoeglich_zwei`), bei n = 1 möglich (`einsortig_moeglich_eins`).  Offen bleiben drei Wege:  den
  Ein-Schritt aufgeben, weniger als die Wirkung kodieren, den Turm verlassen.
- Zusammen:  die Zuordnung „Gabelung = symmetrischer Umtausch" hat drei benannte Grenzen (Vollzug, Zahl, Sinn von „symmetrisch");  die
  Gabelung ist Buridans LAGE, nicht Günthers Umtausch — ZUORDNUNG mit Grenzen.
- Zur Grenze „Vollzug" (LESART):  Was Buridan verlangt, hat der Turm zur Hälfte.  **Notwendig ist, dass gewählt wird** — jede Wahlregel
  wählt an jeder Gabelung ([T66], [T30]);  **offen ist, welches** — `KenogramForkProbe.choice_undetermined` ([T28]).  Was fehlt, ist der
  **Vollzug**:  die Wahlregel ist als Funktion auf dem ganzen Turm im Voraus gegeben, nicht an der Gabelung getroffen.  Die Zuordnung
  „notwendig ↔ Wahlregel total", „offen ↔ choice_undetermined" ist ZUORDNUNG, ungeprüft (Liste PL27).
- Vermerk:  Bis 25.10. hiess die erste Grenze „Auslösen" — gestützt auf die berichtigte Lesung von [T30].
- Vermerk:  dreimal ist der erste Schritt besonders (`wurzel_kollaps`;  zwei Glieder ab `[0]`;  `einsortig_moeglich_eins`) — ein Grund:  über
  der leeren Kette ist nur 0 zulässig.

## K-1 — entschieden

- **K-1 — ENTSCHIEDEN 24.10.** (Hermeneutes am Bild;  Register K-1, PL27/PL28).  Günther hat zwei „oben":  auf der Achse der logischen
  Ordnung geht **Relator → Relatum** nach oben (C&V S. 23;  Formeln S. 20 f.;  Atom/Molekül S. 21;  EuW S. 26, 29);  in der **Rolle**
  steigt das Relatum („elevated", S. 20).  „Relatum → Relator" ist auf der Achse der logischen Ordnung NICHT getragen.  Definitionen §20
  („Formaler Ausdruck") führte die Richtung die ganze Zeit:  „Relator wird Relatum → R_{i+2}(x_{i+1}, y_{i+1})".
- ZUORDNUNG (Quellenlesung wie oben):  `erzeugt` (Regel → Kette, eine Stufe höher) liest den Aufstieg als „Relator wird Relatum" auf der
  Achse der logischen Ordnung;  `regelNach` den Abstieg.
- Vermerk:  Die Beschriftung von `ascent` als „Relatum → Relator" in `AsymmetricDiscontexturalTransition` (Feld `ascent`) und
  `KenogramForkProbe` §5 hängt am Rollen-Wort und widerspricht K-1;  ihre Nachführung ist ein eigener Zug (Register K-1:  „drei Köpfe").
  Dieser Kopf nennt den Widerspruch, ändert die anderen nicht.
- Vermerk:  Bis 25.10. stand hier „OFFEN (K-1) … Dieses Modul schreibt KEINE der beiden Beschriftungen."

## NICHT

Kein Träger für §20;  „§20 ohne Träger" bleibt.  Keine Messung an K4′.  Kein Text in Rev11 (Horistes H5, angenommen 24.10.;  Register
PL31 J5) — eine Frage der Reife, nicht des Gewichts:  der Turm ist der Arbeitsstrang zu §20.  Ob Rev11 einen Absatz „§20 heute" trägt,
der den Turm nennt, entscheidet der Architekt (offen, PL29 §6).  Keine Ledger-Zeile.
**Verboten:**  „Träger für §20", „fast ein Träger", „die Proemialrelation ist gebaut", „trägt A20-4", „Günthers Implikation",
„Buridan formalisiert", „Diskontexturalität aus der Stufe", „der erste Kandidat" ohne die Reihe der zwölf (Standsbericht 13.8.).

**Verboten, ergänzt 25.10.:**  „die Ordnung ist konstituiert" ohne „über einem gestuften Bereich" und ohne „eine der zwei Lesarten von
S. 23";  „constituted" für `faser_iff`;  „Günthers Modalität" für einen Satz;  „die Gabelung ist Günthers Umtausch" ohne die Grenzen;
„einsortig unmöglich" ohne „im Ein-Schritt, ab n = 2";  „der Turm kann die Gleichsetzung nicht" ohne die drei offenen Wege.

**Verboten, ergänzt 25.10. mittags** (nach Definitionen §20, Fassung PL33/PL34):  „Buridans Modalität gegen die von S. 23";  „der Turm löst
aus";  „die Wahl ist frei" (Günther:  Freiheit ist nicht Mangel an Bestimmung, [T67];  positiv „a plus of formal determinating factors"
[T68] (Druck S. 214, am Bild 25.10.;  vordenker S. 10:  „determining"));  „der Turm vollzieht die Wahl".

## Bauweise

`isRGS_take_frei`:  derselbe Satz wie `Kenogram.isRGS_take` (`Kenogram/PlaceSwap.lean`), der dort über `relabel` läuft und
`Classical.choice` trägt (gemessen);  hier per Induktion über `isRGS_concat`, ohne Choice.  `waehleNull`:  die Wahlregel „überall 0"
— der Bestand führt sie nur anonym (`step_eq_ascentBy_zero`).  `max_eq_zero_frei`:  `Nat.max_eq_zero_iff` (Mathlib) trägt
`Classical.choice` (gemessen 25.10.).  G-2 in der Musterform über `rgs_unique_of_pattern` ([propext, Quot.sound]):  die Normalform-Fassung
(`relabel (r.map σ) = r` aus `relabel_map_of_injective` und `relabel_eq_self_of_isRGS`) trägt Choice, ebenso `canonicalize_perm` und
`pattern_characterization`.  G-4 über eine Fallzerlegung der fünf Ketten der Stufe 3 (`rgs3_cases`), ihre Nummer (`codeL`) und das
Schubfach sechs in fünf (`schubfach_sechs_fuenf`, `decide +kernel` über nackte Quantoren über Fin 5) — nicht über `Fintype.card`.

Kein `sorry`, kein `Classical.choice`, kein `native_decide`, kein True-Feld.
-/

namespace Reformulation.Proemial.ErzeugteKetteProbe

open Reformulation.Kenogram
open Reformulation.Proemial.TowerAsymmetryProbe (Tower step)
open Reformulation.Proemial.KenogramForkProbe (Choice ascentBy forkWidth step_eq_ascentBy_zero)
open Reformulation.Proemial.UebergangMitInhaltProbe (waehleNeu step_iter)

/-! ## Werkzeug -/

/-- zwei Turmpunkte mit gleicher Stufe und gleicher Kette sind gleich -/
theorem tower_ext {x y : Tower} (h1 : x.1 = y.1) (h2 : x.2.val = y.2.val) : x = y := by
  obtain ⟨n, r⟩ := x
  obtain ⟨m, s⟩ := y
  simp only at h1 h2
  subst h1
  exact congrArg (Sigma.mk n) (Subtype.ext h2)

/-- Präfixe einer RGS sind RGS — choice-frei (`Kenogram.isRGS_take` trägt `Classical.choice`) -/
theorem isRGS_take_frei {l : List ℕ} (h : IsRGS l) : ∀ k, IsRGS (l.take k)
  | 0 => by rw [List.take_zero]; decide
  | k + 1 => by
    rcases Nat.lt_or_ge k l.length with hk | hk
    · rw [List.take_add_one, List.getElem?_eq_getElem hk, Option.toList_some]
      refine isRGS_concat _ _ (isRGS_take_frei h k) ?_ ?_
      · rcases Nat.eq_zero_or_pos k with h0 | hpos
        · subst h0
          rw [isRGS_head h hk]
          exact Nat.zero_le _
        · exact isRGS_getElem_le h hk hpos
      · intro he
        have hlen : (l.take k).length = min k l.length := List.length_take
        rw [he, List.length_nil] at hlen
        have h0 : k = 0 := by omega
        subst h0
        exact isRGS_head h hk
    · rw [List.take_of_length_le (by omega)]
      exact h

/-- die leere Kette als Turmpunkt -/
def wurzel : Tower := ⟨0, ⟨[], by decide⟩⟩

/-- der Turmpunkt nach i Schritten unter c -/
def stand (c : Choice) (i : ℕ) : Tower := (ascentBy c)^[i] wurzel

/-- **die von c erzeugte Kette der Länge n** -/
def erzeugt (c : Choice) (n : ℕ) : List ℕ := (stand c n).2.val

theorem stand_succ (c : Choice) (i : ℕ) : stand c (i + 1) = ascentBy c (stand c i) :=
  Function.iterate_succ_apply' (ascentBy c) i wurzel

theorem stand_fst (c : Choice) : ∀ i, (stand c i).1 = i
  | 0 => rfl
  | i + 1 => by rw [stand_succ]; exact congrArg (· + 1) (stand_fst c i)

theorem stand_succ_val (c : Choice) (i : ℕ) :
    (stand c (i + 1)).2.val = (stand c i).2.val ++ [(c (stand c i)).1] := by
  rw [stand_succ]; rfl

theorem erzeugt_length (c : Choice) (n : ℕ) : (erzeugt c n).length = n := by
  exact (stand c n).2.property.1.trans (stand_fst c n)

/-- der Turmpunkt auf dem Pfad von r an Stelle i -/
def pfadPunkt (r : List ℕ) (hr : IsRGS r) (i : ℕ) (hi : i ≤ r.length) : Tower :=
  ⟨i, ⟨r.take i, by rw [List.length_take]; omega, isRGS_take_frei hr i⟩⟩

/-! ## Der Pfad -/

/-- x liegt auf dem Pfad von r:  ein echtes Präfix, als Stelle und Kette -/
def aufPfad (r : List ℕ) (x : Tower) : Prop := x.1 < r.length ∧ x.2.val = r.take x.1

instance (r : List ℕ) (x : Tower) : Decidable (aufPfad r x) := inferInstanceAs (Decidable (_ ∧ _))

theorem aufPfad_iff (r : List ℕ) (x : Tower) : aufPfad r x ↔ x.2.val <+: r ∧ x.2.val.length < r.length := by
  have hlen : x.2.val.length = x.1 := x.2.property.1
  rw [hlen, List.prefix_iff_eq_take, hlen]
  exact And.comm

theorem zul_schranke (r : List ℕ) (hr : IsRGS r) (x : Tower) (h1 : x.1 < r.length) (h2 : x.2.val = r.take x.1) :
    r[x.1] ≤ x.2.val.foldr max 0 + 1 := by
  rw [h2]
  rcases Nat.eq_zero_or_pos x.1 with h0 | hpos
  · have e : r[x.1] = 0 := by
      have := isRGS_head hr (by omega : 0 < r.length)
      simp only [h0]; exact this
    rw [e]; exact Nat.zero_le _
  · exact isRGS_getElem_le hr h1 hpos

theorem zul_null (r : List ℕ) (hr : IsRGS r) (x : Tower) (h1 : x.1 < r.length) :
    x.2.val = [] → r[x.1] = 0 := by
  intro he
  have hl : x.2.val.length = x.1 := x.2.property.1
  rw [he, List.length_nil] at hl
  have := isRGS_head hr (by omega : 0 < r.length)
  simp only [← hl]; exact this

/-- **die überschriebene Regel:**  auf dem Pfad von r das nächste Zeichen von r, sonst c₀ -/
def ueberschreibe (r : List ℕ) (hr : IsRGS r) (c₀ : Choice) : Choice := fun x =>
  if h : aufPfad r x then
    ⟨r[x.1]'h.1, zul_schranke r hr x h.1 h.2, zul_null r hr x h.1⟩
  else c₀ x

/-- die Wahlregel „überall 0" (im Bestand nur anonym:  `step_eq_ascentBy_zero`) -/
def waehleNull : Choice := fun _ => ⟨0, Nat.zero_le _, fun _ => rfl⟩

/-- **eine Regel, die r erzeugt** -/
def regelNach (r : List ℕ) (hr : IsRGS r) : Choice := ueberschreibe r hr waehleNull

/-! ## Der Fasersatz -/

theorem pfad_stand (c : Choice) (r : List ℕ) (hr : IsRGS r) :
    ∀ i (hi : i ≤ r.length),
      (∀ j (hj : j < i), (c (pfadPunkt r hr j (by omega))).1 = r[j]'(by omega)) ↔ (stand c i).2.val = r.take i
  | 0, _ => by
    constructor
    · intro _; rfl
    · intro _ j hj; omega
  | i + 1, hi => by
    have ih := pfad_stand c r hr i (by omega)
    have hpt : stand c i = pfadPunkt r hr i (by omega) → (c (stand c i)).1 = (c (pfadPunkt r hr i (by omega))).1 :=
      fun h => by rw [h]
    rw [stand_succ_val, List.take_add_one, List.getElem?_eq_getElem (by omega : i < r.length), Option.toList_some]
    constructor
    · intro H
      have hi' := ih.mp (fun j hj => H j (by omega))
      have heq : stand c i = pfadPunkt r hr i (by omega) := tower_ext (stand_fst c i) hi'
      rw [hpt heq, H i (by omega), hi']
    · intro H
      have hlen : (stand c i).2.val.length = (r.take i).length := by
        rw [List.length_take, (stand c i).2.property.1, stand_fst]; omega
      obtain ⟨h1, h2⟩ := List.append_inj H hlen
      have heq : stand c i = pfadPunkt r hr i (by omega) := tower_ext (stand_fst c i) h1
      intro j hj
      rcases Nat.lt_or_ge j i with hji | hji
      · exact ih.mpr h1 j hji
      · have hj' : j = i := by omega
        subst hj'
        have := List.cons.inj h2
        rw [← hpt heq]; exact this.1

/-- **Fasersatz (a).**  c erzeugt r genau dann, wenn c längs des Pfades von r die Zeichen von r wählt.  Beinahe die Definition. -/
theorem fasersatz_a (c : Choice) (r : List ℕ) (hr : IsRGS r) :
    erzeugt c r.length = r ↔ ∀ i (hi : i < r.length), (c (pfadPunkt r hr i (Nat.le_of_lt hi))).1 = r[i] := by
  have := pfad_stand c r hr r.length (le_refl _)
  rw [List.take_length] at this
  exact this.symm

theorem pfadPunkt_aufPfad (r : List ℕ) (hr : IsRGS r) (i : ℕ) (hi : i < r.length) :
    aufPfad r (pfadPunkt r hr i (Nat.le_of_lt hi)) := ⟨hi, rfl⟩

theorem ueberschreibe_pfad (r : List ℕ) (hr : IsRGS r) (c₀ : Choice) (x : Tower) (h : aufPfad r x) :
    (ueberschreibe r hr c₀ x).1 = r[x.1]'h.1 := by
  simp only [ueberschreibe, dif_pos h]

theorem ueberschreibe_abseits (r : List ℕ) (hr : IsRGS r) (c₀ : Choice) (x : Tower) (h : ¬ aufPfad r x) :
    (ueberschreibe r hr c₀ x).1 = (c₀ x).1 := by
  simp only [ueberschreibe, dif_neg h]

/-- **Fasersatz (b).**  Die überschriebene Regel erzeugt r, und abseits des Pfades ist sie c₀ — für jedes c₀. -/
theorem fasersatz_b (r : List ℕ) (hr : IsRGS r) (c₀ : Choice) :
    erzeugt (ueberschreibe r hr c₀) r.length = r ∧
      ∀ x, ¬ aufPfad r x → (ueberschreibe r hr c₀ x).1 = (c₀ x).1 := by
  refine ⟨(fasersatz_a _ r hr).mpr fun i hi => ?_, ueberschreibe_abseits r hr c₀⟩
  exact ueberschreibe_pfad r hr c₀ _ (pfadPunkt_aufPfad r hr i hi)

/-- **Die Faser über r:**  c erzeugt r genau dann, wenn c überall mit ihrer Überschreibung durch r übereinstimmt — frei sind genau
    die Punkte abseits des Pfades. -/
theorem faser_iff (c : Choice) (r : List ℕ) (hr : IsRGS r) :
    erzeugt c r.length = r ↔ ∀ x, (c x).1 = (ueberschreibe r hr c x).1 := by
  constructor
  · intro H x
    exact (Decidable.byCases (p := aufPfad r x)
      (fun h => by
        rw [ueberschreibe_pfad r hr c x h]
        have heq : x = pfadPunkt r hr x.1 (Nat.le_of_lt h.1) := tower_ext rfl h.2
        have := (fasersatz_a c r hr).mp H x.1 h.1
        rw [← heq] at this; exact this)
      (fun h => (ueberschreibe_abseits r hr c x h).symm))
  · intro H
    refine (fasersatz_a c r hr).mpr fun i hi => ?_
    rw [H]; exact ueberschreibe_pfad r hr c _ (pfadPunkt_aufPfad r hr i hi)

/-- **Die Retraktion.** -/
theorem erzeugt_regelNach (r : List ℕ) (hr : IsRGS r) : erzeugt (regelNach r hr) r.length = r :=
  (fasersatz_b r hr waehleNull).1

/-! ## Der Ein-Schritt und die Lokalität -/

/-- **Der Ein-Schritt.**  Zwei Regeln haben an x denselben Schritt genau dann, wenn sie dort dasselbe Zeichen wählen. -/
theorem ein_schritt (c c' : Choice) (x : Tower) : ascentBy c x = ascentBy c' x ↔ (c x).1 = (c' x).1 := by
  constructor
  · intro h
    have hv : x.2.val ++ [(c x).1] = x.2.val ++ [(c' x).1] := congrArg (fun y : Tower => y.2.val) h
    exact List.cons.inj (List.append_cancel_left hv) |>.1
  · intro h
    exact tower_ext rfl (by show x.2.val ++ [(c x).1] = x.2.val ++ [(c' x).1]; rw [h])

/-- **Lokalität.**  Regeln, die auf allen Punkten unterhalb n übereinstimmen, erzeugen dieselbe Kette der Länge n. -/
theorem erzeugt_lokal (c c' : Choice) (n : ℕ) (h : ∀ x : Tower, x.1 < n → (c x).1 = (c' x).1) :
    erzeugt c n = erzeugt c' n := by
  have key : ∀ i, i ≤ n → stand c i = stand c' i := by
    intro i
    induction i with
    | zero => intro _; rfl
    | succ i ih =>
      intro hi
      rw [stand_succ, stand_succ, ih (by omega)]
      exact (ein_schritt c c' _).mpr (h _ (by rw [stand_fst]; omega))
  exact congrArg (fun y : Tower => y.2.val) (key n (le_refl _))

/-- **Lokalität, schärfer:**  erzeugt c die Kette r, und stimmt c' mit c längs des Pfades von r überein, so erzeugt auch c' sie. -/
theorem erzeugt_lokal_pfad (c c' : Choice) (r : List ℕ) (hr : IsRGS r) (hc : erzeugt c r.length = r)
    (h : ∀ i (hi : i < r.length), (c (pfadPunkt r hr i (Nat.le_of_lt hi))).1 = (c' (pfadPunkt r hr i (Nat.le_of_lt hi))).1) :
    erzeugt c' r.length = r :=
  (fasersatz_a c' r hr).mpr fun i hi => (h i hi).symm.trans ((fasersatz_a c r hr).mp hc i hi)

/-! ## Die Unit-Brücke -/

/-- eine Regel, deren Wert nicht vom Punkt abhängt, wählt überall 0 (über der leeren Kette ist nur 0 zulässig) -/
theorem unit_ist_null (c : Choice) (h : ∃ k, ∀ x, (c x).1 = k) : ∀ x, (c x).1 = 0 := by
  obtain ⟨k, hk⟩ := h
  have h0 : (c wurzel).1 = 0 := (c wurzel).2.2 rfl
  intro x; rw [hk x, ← hk wurzel, h0]

theorem erzeugt_waehleNull (n : ℕ) : erzeugt waehleNull n = List.replicate n 0 := by
  have h : stand waehleNull n = step^[n] wurzel := by
    unfold stand; rw [step_eq_ascentBy_zero]; rfl
  unfold erzeugt; rw [h]; exact step_iter n

/-- **Die Unit-Brücke:**  eine Regel, deren Wert nicht vom Punkt abhängt, erzeugt [0, …, 0] -/
theorem unit_erzeugt (c : Choice) (h : ∃ k, ∀ x, (c x).1 = k) (n : ℕ) : erzeugt c n = List.replicate n 0 := by
  rw [← erzeugt_waehleNull n]
  exact erzeugt_lokal c waehleNull n fun x _ => unit_ist_null c h x

/-- dieselbe Brücke in der Gestalt von `DirectionChoice`:  durch `Unit` faktorisierend -/
theorem unit_faktor_erzeugt (c : Choice) (h : ∃ g : Unit → ℕ, ∀ x, (c x).1 = g ()) (n : ℕ) :
    erzeugt c n = List.replicate n 0 :=
  unit_erzeugt c ((DirectionChoice.factorsThroughUnit_iff_constant (fun x => (c x).1)).mp h) n

/-! ## Stufe 2 und Stufe 3 -/

/-- der Turmpunkt `[0]` -/
def p0 : Tower := ⟨1, ⟨[0], by decide⟩⟩
/-- der Turmpunkt [0,0] -/
def p00 : Tower := ⟨2, ⟨[0, 0], by decide⟩⟩
/-- der Turmpunkt [0,1] -/
def p01 : Tower := ⟨2, ⟨[0, 1], by decide⟩⟩

theorem stand_eins (c : Choice) : stand c 1 = p0 :=
  tower_ext rfl (by rw [stand_succ_val]; show [] ++ [(c wurzel).1] = [0]; rw [(c wurzel).2.2 rfl]; rfl)

theorem erzeugt_zwei (c : Choice) : erzeugt c 2 = [0, (c p0).1] := by
  unfold erzeugt; rw [stand_succ_val, stand_eins]; rfl

/-- **An Stufe 2 trennt erzeugt die Wirkungen auf `[0]`.** -/
theorem stufe_zwei_injektiv (c c' : Choice) : erzeugt c 2 = erzeugt c' 2 ↔ (c p0).1 = (c' p0).1 := by
  rw [erzeugt_zwei, erzeugt_zwei]
  constructor
  · intro h; exact (List.cons.inj (List.cons.inj h).2).1
  · intro h; rw [h]

/-- „0 überall, ausser 2 an [0,1]" -/
def nullAusser01 : Choice := fun x =>
  if h : x.2.val = [0, 1] then ⟨2, by rw [h]; decide, by rw [h]; intro h'; exact absurd h' (by decide)⟩
  else ⟨0, Nat.zero_le _, fun _ => rfl⟩

theorem isRGS_012 : IsRGS [0, 1, 2] := by decide

/-- **Stufe 3:**  zwei Paare verschiedener Regeln mit derselben erzeugten Kette — waehleNull und nullAusser01 ([0,0,0], verschieden
    an [0,1]);  regelNach [0,1,2] und waehleNeu ([0,1,2], verschieden an [0,0]). -/
theorem stufe_drei_faser :
    erzeugt waehleNull 3 = [0, 0, 0] ∧ erzeugt nullAusser01 3 = [0, 0, 0] ∧ (waehleNull p01).1 ≠ (nullAusser01 p01).1 ∧
    erzeugt (regelNach [0, 1, 2] isRGS_012) 3 = [0, 1, 2] ∧ erzeugt waehleNeu 3 = [0, 1, 2] ∧
    (regelNach [0, 1, 2] isRGS_012 p00).1 ≠ (waehleNeu p00).1 := by
  decide

/-- **Der Ein-Schritt ist nicht injektiv auf der Wirkung einer Stufe:**  waehleNull und regelNach [0,1,2] haben an [0,0] denselben
    Schritt und wählen an [0,1] verschieden. -/
theorem ein_schritt_nicht_injektiv :
    ascentBy waehleNull p00 = ascentBy (regelNach [0, 1, 2] isRGS_012) p00 ∧
    (waehleNull p01).1 ≠ (regelNach [0, 1, 2] isRGS_012 p01).1 :=
  ⟨(ein_schritt _ _ _).mpr (by decide), by decide⟩

/-- **Die Gabelbreiten abseits des Pfades an Stufe 3** -/
theorem gabel_abseits :
    forkWidth (⟨[0, 1], by decide⟩ : RGS 2) = 3 ∧ forkWidth (⟨[0, 0], by decide⟩ : RGS 2) = 2 := by
  decide

/-! ## Die Ordnung der Ketten aus den Fasern -/

/-- c liegt in der Faser über r:  c erzeugt r -/
abbrev inFaser (c : Choice) (r : List ℕ) : Prop := erzeugt c r.length = r

/-- die erzeugten Ketten wachsen als Präfixe -/
theorem erzeugt_praefix (c : Choice) (m : ℕ) : ∀ n, m ≤ n → erzeugt c m <+: erzeugt c n
  | 0, h => by rw [Nat.le_zero.mp h]
  | n + 1, h => by
    rcases Nat.eq_or_lt_of_le h with h | h
    · rw [h]
    · refine (erzeugt_praefix c m n (by omega)).trans ?_
      show (stand c n).2.val <+: (stand c (n + 1)).2.val
      rw [stand_succ_val]; exact List.prefix_append _ _

/-- die Wahlregel „1 an s, sonst 0" — zulässig, weil s ≠ [] -/
def einsAn (s : List ℕ) : Choice := fun x =>
  if h : x.2.val = s ∧ s ≠ [] then ⟨1, Nat.le_add_left _ _, fun he => absurd (h.1.symm.trans he) h.2⟩
  else ⟨0, Nat.zero_le _, fun _ => rfl⟩

theorem einsAn_an (s : List ℕ) (hs : s ≠ []) (x : Tower) (h : x.2.val = s) : (einsAn s x).1 = 1 := by
  simp only [einsAn, dif_pos (And.intro h hs)]

/-- **„⇒":**  erzeugt c die Kette s, so erzeugt c jedes Präfix von s — ohne Voraussetzung -/
theorem faser_praefix (c : Choice) (r s : List ℕ) (hrs : r <+: s) (hc : inFaser c s) : inFaser c r := by
  have hle : r.length ≤ s.length := hrs.length_le
  have hp : erzeugt c r.length <+: s := hc ▸ erzeugt_praefix c r.length s.length hle
  have hlen : (erzeugt c r.length).length = r.length := erzeugt_length c r.length
  exact (List.prefix_of_prefix_length_le hp hrs (le_of_eq hlen)).eq_of_length hlen

/-- **Die Ordnung der Ketten aus den Fasern** (über einem gestuften Bereich):  für s ≠ [] ist r genau dann Präfix von s, wenn jede
    Regel, die s erzeugt, auch r erzeugt. -/
theorem ordnung_aus_fasern (r s : List ℕ) (hr : IsRGS r) (hs : IsRGS s) (hne : s ≠ []) :
    r <+: s ↔ ∀ c, inFaser c s → inFaser c r := by
  refine ⟨fun hrs c hc => faser_praefix c r s hrs hc, fun H => ?_⟩
  have hg := H (regelNach s hs) (erzeugt_regelNach s hs)
  rcases Nat.lt_or_ge s.length r.length with hlt | hle
  · -- s ist echtes Präfix von r — zwei Regeln in Faser(s), die am Punkt s verschieden wählen
    exfalso
    have hsr : s <+: r := by
      have hp := erzeugt_praefix (regelNach s hs) s.length r.length (Nat.le_of_lt hlt)
      rw [erzeugt_regelNach s hs] at hp; unfold inFaser at hg; rw [hg] at hp; exact hp
    have htake : r.take s.length = s := (List.prefix_iff_eq_take.mp hsr).symm
    let x := pfadPunkt r hr s.length (Nat.le_of_lt hlt)
    have hx : x.2.val = s := htake
    have hab : ¬ aufPfad s x := fun h => Nat.lt_irrefl _ h.1
    have h0 := (fasersatz_a _ r hr).mp (H _ (fasersatz_b s hs waehleNull).1) s.length hlt
    have h1 := (fasersatz_a _ r hr).mp (H _ (fasersatz_b s hs (einsAn s)).1) s.length hlt
    rw [ueberschreibe_abseits s hs _ x hab] at h0 h1
    rw [einsAn_an s hne x hx] at h1
    exact Nat.zero_ne_one (h0.trans h1.symm)
  · have hp := erzeugt_praefix (regelNach s hs) r.length s.length hle
    rw [erzeugt_regelNach s hs] at hp; unfold inFaser at hg; rw [hg] at hp; exact hp

theorem inFaser_nil (c : Choice) : inFaser c [] := rfl

theorem inFaser_null (c : Choice) : inFaser c [0] :=
  congrArg (fun y : Tower => y.2.val) (stand_eins c)

/-- **Der Kollaps an der Wurzel:**  die Faser über [] und die über `[0]` sind beide alle Regeln — über der leeren Kette ist nur 0
    zulässig —, aber `[0]` ist kein Präfix von [].  Die Faser-Ordnung ist eine Präordnung, und ohne s ≠ [] fällt `ordnung_aus_fasern`. -/
theorem wurzel_kollaps :
    (∀ c, inFaser c []) ∧ (∀ c, inFaser c [0]) ∧ ¬ ([0] <+: ([] : List ℕ)) ∧
    ¬ (∀ r s : List ℕ, IsRGS r → IsRGS s → (r <+: s ↔ ∀ c, inFaser c s → inFaser c r)) := by
  have hnp : ¬ ([0] <+: ([] : List ℕ)) := fun h => absurd h.length_le (by decide)
  refine ⟨inFaser_nil, inFaser_null, hnp, fun H => ?_⟩
  exact hnp ((H [0] [] (by decide) (by decide)).mpr fun c _ => inFaser_null c)

/-- wer von ALLEN Regeln erzeugt wird, ist [] oder `[0]` -/
theorem alle_regeln (r : List ℕ) (h : ∀ c, inFaser c r) : r = [] ∨ r = [0] := by
  match r, h with
  | [], _ => exact Or.inl rfl
  | [a], h =>
    have h1 : erzeugt waehleNull 1 = [a] := h waehleNull
    have h0 : erzeugt waehleNull 1 = [0] := inFaser_null waehleNull
    rw [h0] at h1
    exact Or.inr h1.symm
  | a :: b :: t, h =>
    exfalso
    have key : ∀ c : Choice, (c p0).1 = b := by
      intro c
      have hp := erzeugt_praefix c 2 (t.length + 2) (by omega)
      have hc : erzeugt c (t.length + 2) = a :: b :: t := h c
      rw [hc, erzeugt_zwei] at hp
      have := List.prefix_iff_eq_take.mp hp
      exact (List.cons.inj (List.cons.inj this).2).1
    have k0 := key waehleNull
    have k1 := key (einsAn [0])
    rw [einsAn_an [0] (by decide) p0 rfl] at k1
    exact Nat.zero_ne_one (k0.trans k1.symm)

/-- **Die volle Fassung:**  Faser(s) ⊆ Faser(r) genau dann, wenn r Präfix von s ist oder (s, r) der Kollaps an der Wurzel. -/
theorem faser_ordnung_voll (r s : List ℕ) (hr : IsRGS r) (hs : IsRGS s) :
    (∀ c, inFaser c s → inFaser c r) ↔ r <+: s ∨ (s = [] ∧ r = [0]) := by
  constructor
  · intro H
    match s, hs, H with
    | [], _, H =>
      rcases alle_regeln r (fun c => H c (inFaser_nil c)) with h | h
      · exact Or.inl (h ▸ List.prefix_refl [])
      · exact Or.inr ⟨rfl, h⟩
    | a :: t, hs, H => exact Or.inl ((ordnung_aus_fasern r (a :: t) hr hs (List.cons_ne_nil a t)).mpr H)
  · rintro (h | ⟨-, rfl⟩)
    · exact fun c hc => faser_praefix c r s h hc
    · exact fun c _ => inFaser_null c

/-- **Eichung an Stufe ≤ 3** — der Fall (i):  `[0,0]` ist kein Präfix von `[0,1,2]`, regelNach `[0,1,2]` liegt in Faser(`[0,1,2]`)
    und nicht in Faser(`[0,0]`);  der Fall (iii) an s = `[0,1]`, r = `[0,1,1]`:  die Überschreibung mit 0 liegt in Faser(s), nicht in
    Faser(r);  und `[0,1]` ⊆-Richtung:  jede Regel, die `[0,1,2]` erzeugt, erzeugt `[0,1]`. -/
theorem eich_ordnung_drei :
    inFaser (regelNach [0, 1, 2] isRGS_012) [0, 1, 2] ∧ ¬ inFaser (regelNach [0, 1, 2] isRGS_012) [0, 0] ∧
    inFaser (ueberschreibe [0, 1] (by decide) waehleNull) [0, 1] ∧ ¬ inFaser (ueberschreibe [0, 1] (by decide) waehleNull) [0, 1, 1] ∧
    (∀ c, inFaser c [0, 1, 2] → inFaser c [0, 1]) := by
  refine ⟨by decide, by decide, by decide, by decide, fun c hc => faser_praefix c _ _ ⟨[2], rfl⟩ hc⟩

/-! ## Was der Turm nicht kann -/

/-! ### G-1 · Zwei Glieder nur längs der Wiederholung -/

/-- `max a b = 0` genau dann, wenn beide 0 sind — choice-frei (`Nat.max_eq_zero_iff` trägt `Classical.choice`, gemessen) -/
theorem max_eq_zero_frei (a b : ℕ) : max a b = 0 ↔ a = 0 ∧ b = 0 :=
  ⟨fun h => ⟨Nat.eq_zero_of_le_zero (h ▸ Nat.le_max_left a b), Nat.eq_zero_of_le_zero (h ▸ Nat.le_max_right a b)⟩,
   fun ⟨ha, hb⟩ => by rw [ha, hb]; rfl⟩

theorem foldr_max_eq_zero : ∀ l : List ℕ, l.foldr max 0 = 0 ↔ ∀ x ∈ l, x = 0
  | [] => ⟨fun _ x hx => absurd hx List.not_mem_nil, fun _ => rfl⟩
  | a :: t => by
    rw [List.foldr_cons, max_eq_zero_frei, foldr_max_eq_zero t, List.forall_mem_cons]

/-- **Zwei Glieder genau längs der Wiederholung:**  über einer nichtleeren Kette hat die Gabelung genau dann zwei Glieder, wenn die
    Kette nur aus Nullen besteht. -/
theorem forkWidth_eq_two_iff {n : ℕ} (r : RGS n) (h : r.val ≠ []) : forkWidth r = 2 ↔ r.val = List.replicate n 0 := by
  rw [KenogramForkProbe.forkWidth_eq r h]
  constructor
  · intro e
    have h0 : r.val.foldr max 0 = 0 := by omega
    exact List.eq_replicate_iff.mpr ⟨r.property.1, (foldr_max_eq_zero _).mp h0⟩
  · intro e
    rw [(foldr_max_eq_zero _).mpr (List.eq_replicate_iff.mp e).2]

/-- die zweigliedrige Gabelung auf Stufe n ≥ 1 liegt über der Kette der Regel „überall 0" -/
theorem zwei_glieder_wiederholung {n : ℕ} (hn : 1 ≤ n) (r : RGS n) :
    forkWidth r = 2 ↔ r.val = erzeugt waehleNull n := by
  have hne : r.val ≠ [] := fun h => by
    have := r.property.1; rw [h, List.length_nil] at this; omega
  rw [erzeugt_waehleNull]; exact forkWidth_eq_two_iff r hne

/-- die Gabelbreite, an der Kette gerechnet (definitional `forkWidth`) -/
def fwL (l : List ℕ) : ℕ := ((List.range (l.foldr max 0 + 2)).filter (fun k => decide (l = [] → k = 0))).length

theorem forkWidth_fwL {n : ℕ} (r : RGS n) : forkWidth r = fwL r.val := rfl

/-- **Eichung (decide):**  auf den Stufen 1 bis 4 hat genau eine Kette eine zweigliedrige Gabelung, die Nullkette (`rgsList` ist der
    Generator von Kenogram/Basic). -/
theorem eich_zwei_glieder :
    (rgsList 1).filter (fun l => fwL l == 2) = [[0]] ∧ (rgsList 2).filter (fun l => fwL l == 2) = [[0, 0]] ∧
    (rgsList 3).filter (fun l => fwL l == 2) = [[0, 0, 0]] ∧ (rgsList 4).filter (fun l => fwL l == 2) = [[0, 0, 0, 0]] := by
  decide

/-! ### G-2, G-3 · Die Wertpermutation auf Kenogrammen -/

theorem muster_map {σ : ℕ → ℕ} (hσ : Function.Injective σ) (l : List ℕ) (i j : ℕ) :
    (l.map σ)[i]? = (l.map σ)[j]? ↔ l[i]? = l[j]? := by
  rw [List.getElem?_map, List.getElem?_map]
  exact (Option.map_injective hσ).eq_iff

/-- **Die Wertpermutation wirkt auf Kenogrammen als Identität:**  jede Normalform (RGS) mit dem Muster von r.map σ ist r — für jede
    injektive Umbenennung σ.  Zusammengestellt aus `Kenogram.rgs_unique_of_pattern`. -/
theorem umtausch_identitaet {σ : ℕ → ℕ} (hσ : Function.Injective σ) (r s : List ℕ) (hr : IsRGS r) (hs : IsRGS s)
    (hlen : s.length = r.length) (hpat : ∀ i j : ℕ, s[i]? = s[j]? ↔ (r.map σ)[i]? = (r.map σ)[j]?) : s = r :=
  rgs_unique_of_pattern hs hr hlen fun i j => (hpat i j).trans (muster_map hσ r i j)

/-- verschiedene Kenogramme gehen durch keine injektive Umbenennung ineinander über -/
theorem umbenennung_trennt {σ : ℕ → ℕ} (hσ : Function.Injective σ) (r s : List ℕ) (hr : IsRGS r) (hs : IsRGS s)
    (h : r.map σ = s) : r = s :=
  (umtausch_identitaet hσ r s hr hs (by rw [← h, List.length_map]) fun i j => by rw [h]).symm

/-- **Die Glieder einer Gabelung sind nicht vertauschbar:**  keine Umbenennung führt `[0,0]` in `[0,1]` (für jedes σ, auch ohne
    Injektivität);  und allgemein gehen zwei verschiedene Fortsetzungen derselben Kette durch keine injektive Umbenennung ineinander über. -/
theorem gabelung_nicht_vertauschbar :
    (∀ σ : ℕ → ℕ, [0, 0].map σ ≠ [0, 1]) ∧
    ∀ (r : List ℕ) (a b : ℕ), IsRGS (r ++ [a]) → IsRGS (r ++ [b]) → a ≠ b →
      ¬ ∃ σ : ℕ → ℕ, Function.Injective σ ∧ (r ++ [a]).map σ = r ++ [b] := by
  refine ⟨fun σ h => ?_, fun r a b ha hb hab ⟨σ, hσ, h⟩ => ?_⟩
  · have h1 := List.cons.inj h
    have h2 := List.cons.inj h1.2
    exact Nat.zero_ne_one (h1.1.symm.trans h2.1)
  · have e := umbenennung_trennt hσ _ _ ha hb h
    exact hab (List.cons.inj (List.append_cancel_left e)).1

/-! ### G-4, G-5 · Der einsortige Ein-Schritt -/

/-- die Wirkungen einer Wahlregel auf Stufe n:  je Punkt der Stufe eine der Fortsetzungen -/
abbrev W (n : ℕ) : Type := (r : RGS n) → Fin (forkWidth r)

theorem rgs1_eq (r : RGS 1) : r.val = [0] := by
  obtain ⟨l, hl, h⟩ := r
  match l, hl, h with
  | [a], _, h =>
    simp only [IsRGS, isRGSAux, Bool.and_eq_true, decide_eq_true_eq] at h
    show [a] = [0]; rw [h.1]

theorem rgs2_cases (r : RGS 2) : r.val = [0, 0] ∨ r.val = [0, 1] := by
  obtain ⟨l, hl, h⟩ := r
  match l, hl, h with
  | [a, b], _, h =>
    simp only [IsRGS, isRGSAux, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨ha, hb, -⟩ := h
    subst ha
    match b, hb with
    | 0, _ => exact Or.inl rfl
    | 1, _ => exact Or.inr rfl
    | b + 2, hb => exfalso; omega

theorem rgs3_cases (r : RGS 3) :
    r.val = [0, 0, 0] ∨ r.val = [0, 0, 1] ∨ r.val = [0, 1, 0] ∨ r.val = [0, 1, 1] ∨ r.val = [0, 1, 2] := by
  obtain ⟨l, hl, h⟩ := r
  match l, hl, h with
  | [a, b, c], _, h =>
    simp only [IsRGS, isRGSAux, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨ha, hb, hc, -⟩ := h
    subst ha
    match b, c, hb, hc with
    | 0, 0, _, _ => exact Or.inl rfl
    | 0, 1, _, _ => exact Or.inr (Or.inl rfl)
    | 1, 0, _, _ => exact Or.inr (Or.inr (Or.inl rfl))
    | 1, 1, _, _ => exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
    | 1, 2, _, _ => exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))
    | b + 2, _, hb, _ => exfalso; omega
    | 0, c + 2, _, hc => exfalso; simp only [Nat.max_self] at hc; omega
    | 1, c + 3, _, hc => exfalso; simp only [Nat.zero_max] at hc; omega

/-- die Nummer einer Kette der Stufe 3:  2·b + c für [0, b, c] -/
def codeL (l : List ℕ) : ℕ := 2 * l.getD 1 0 + l.getD 2 0

theorem code3_lt (r : RGS 3) : codeL r.val < 5 := by
  rcases rgs3_cases r with h | h | h | h | h <;> rw [h] <;> decide

theorem code3_inj {r s : RGS 3} (h : codeL r.val = codeL s.val) : r = s := by
  apply Subtype.ext
  rcases rgs3_cases r with hr | hr | hr | hr | hr <;> rcases rgs3_cases s with hs | hs | hs | hs | hs <;>
    rw [hr, hs] at h <;> rw [hr, hs] <;> exact absurd h (by decide)

/-- das Schubfach:  sechs Zahlen unter fünf sind nicht paarweise verschieden -/
theorem schubfach_sechs_fuenf : ∀ a b c d e g : Fin 5,
    (Nat.beq a.val b.val || Nat.beq a.val c.val || Nat.beq a.val d.val || Nat.beq a.val e.val || Nat.beq a.val g.val ||
     Nat.beq b.val c.val || Nat.beq b.val d.val || Nat.beq b.val e.val || Nat.beq b.val g.val ||
     Nat.beq c.val d.val || Nat.beq c.val e.val || Nat.beq c.val g.val ||
     Nat.beq d.val e.val || Nat.beq d.val g.val || Nat.beq e.val g.val) = true := by
  decide +kernel

theorem beq_false_of_ne {x y : ℕ} (h : x ≠ y) : Nat.beq x y = false :=
  Bool.eq_false_iff.mpr fun e => h (Nat.eq_of_beq_eq_true e)

/-- die Punkte `[0,0]` und `[0,1]` der Stufe 2 -/
def q00 : RGS 2 := ⟨[0, 0], by decide⟩
def q01 : RGS 2 := ⟨[0, 1], by decide⟩

theorem fw_q00 (r : RGS 2) (h : r.val = [0, 0]) : forkWidth r = 2 := by rw [forkWidth_fwL, h]; rfl
theorem fw_q01 (r : RGS 2) (h : ¬ r.val = [0, 0]) : forkWidth r = 3 := by
  rw [forkWidth_fwL]; rcases rgs2_cases r with e | e
  · exact absurd e h
  · rw [e]; rfl

/-- die sechs Wirkungen auf Stufe 2:  i / 3 an `[0,0]`, i % 3 an `[0,1]` -/
def wi (i : Fin 6) : W 2 := fun r =>
  if h : r.val = [0, 0] then ⟨i.val / 3, by rw [fw_q00 r h]; omega⟩
  else ⟨i.val % 3, by rw [fw_q01 r h]; exact Nat.mod_lt _ (by decide)⟩

theorem wi_inj {i j : Fin 6} (h : wi i = wi j) : i = j := by
  have h1 : (wi i q00).val = (wi j q00).val := by rw [h]
  have h2 : (wi i q01).val = (wi j q01).val := by rw [h]
  have e1 : (wi i q00).val = i.val / 3 := rfl
  have e2 : (wi j q00).val = j.val / 3 := rfl
  have e3 : (wi i q01).val = i.val % 3 := rfl
  have e4 : (wi j q01).val = j.val % 3 := rfl
  rw [e1, e2] at h1; rw [e3, e4] at h2
  exact Fin.ext (by omega)

/-- **Der einsortige Ein-Schritt ist ab Stufe 2 unmöglich:**  keine Injektion schickt die Wirkungen einer Wahlregel auf Stufe 2 in die
    Ketten der Stufe 3 (sechs Wirkungen, fünf Ketten). -/
theorem einsortig_unmoeglich_zwei : ¬ ∃ f : W 2 → RGS 3, Function.Injective f := by
  rintro ⟨f, hf⟩
  let c : Fin 6 → Fin 5 := fun i => ⟨codeL (f (wi i)).val, code3_lt _⟩
  have ne : ∀ i j : Fin 6, i ≠ j → Nat.beq (c i).val (c j).val = false := fun i j hij =>
    beq_false_of_ne fun e => hij (wi_inj (hf (code3_inj e)))
  have H := schubfach_sechs_fuenf (c 0) (c 1) (c 2) (c 3) (c 4) (c 5)
  rw [ne 0 1 (by decide), ne 0 2 (by decide), ne 0 3 (by decide), ne 0 4 (by decide), ne 0 5 (by decide),
    ne 1 2 (by decide), ne 1 3 (by decide), ne 1 4 (by decide), ne 1 5 (by decide),
    ne 2 3 (by decide), ne 2 4 (by decide), ne 2 5 (by decide), ne 3 4 (by decide), ne 3 5 (by decide),
    ne 4 5 (by decide)] at H
  exact absurd H (by decide)

/-- der Punkt `[0]` der Stufe 1 -/
def q0 : RGS 1 := ⟨[0], by decide⟩

theorem rgs1_q0 (r : RGS 1) : r = q0 := Subtype.ext (rgs1_eq r)

theorem fw_q0 : forkWidth q0 = 2 := rfl

/-- die Wirkung auf Stufe 1 als Kette der Stufe 2 -/
def alsKette (w : W 1) : RGS 2 :=
  ⟨[0, (w q0).val], rfl, by
    have h : (w q0).val < 2 := (w q0).isLt
    exact isRGS_concat [0] _ (by decide) (by show (w q0).val ≤ 0 + 1; omega) (fun h' => absurd h' (by decide))⟩

/-- **Bei Stufe 1 geht es auf:**  die Wirkungen einer Wahlregel auf Stufe 1 SIND die Ketten der Stufe 2 (eine Bijektion);  das ist die
    Gestalt von `stufe_zwei_injektiv`. -/
theorem einsortig_moeglich_eins : ∃ f : W 1 → RGS 2, Function.Bijective f := by
  refine ⟨alsKette, fun w w' h => ?_, fun s => ?_⟩
  · have hv : (w q0).val = (w' q0).val := (List.cons.inj (List.cons.inj (congrArg Subtype.val h)).2).1
    funext r
    obtain rfl := rgs1_q0 r
    exact Fin.ext hv
  · rcases rgs2_cases s with hs | hs
    · refine ⟨fun r => ⟨0, by rw [rgs1_q0 r]; decide⟩, Subtype.ext ?_⟩
      show [0, 0] = s.val; rw [hs]
    · refine ⟨fun r => ⟨1, by rw [rgs1_q0 r]; decide⟩, Subtype.ext ?_⟩
      show [0, 1] = s.val; rw [hs]

/-- **Eichung (decide):**  die Zahl der Wirkungen (Produkt der Gabelbreiten) gegen die Zahl der Ketten eine Stufe höher, an den
    Generatorlisten:  Stufe 1:  2 gegen 2;  Stufe 2:  6 gegen 5;  Stufe 3:  216 gegen 15. -/
theorem zaehlung_drei_vier :
    ((rgsList 1).map fwL).prod = 2 ∧ (rgsList 2).length = 2 ∧
    ((rgsList 2).map fwL).prod = 6 ∧ (rgsList 3).length = 5 ∧
    ((rgsList 3).map fwL).prod = 216 ∧ (rgsList 4).length = 15 := by
  decide

end Reformulation.Proemial.ErzeugteKetteProbe

/-! ## Axiom-Wachen (gemessen, verbatim) -/

/-- info: 'Reformulation.Proemial.ErzeugteKetteProbe.tower_ext' does not depend on any axioms -/
#guard_msgs in #print axioms Reformulation.Proemial.ErzeugteKetteProbe.tower_ext

/-- info: 'Reformulation.Proemial.ErzeugteKetteProbe.isRGS_take_frei' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.ErzeugteKetteProbe.isRGS_take_frei

/-- info: 'Reformulation.Proemial.ErzeugteKetteProbe.stand_succ' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.ErzeugteKetteProbe.stand_succ

/-- info: 'Reformulation.Proemial.ErzeugteKetteProbe.stand_fst' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.ErzeugteKetteProbe.stand_fst

/-- info: 'Reformulation.Proemial.ErzeugteKetteProbe.stand_succ_val' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.ErzeugteKetteProbe.stand_succ_val

/-- info: 'Reformulation.Proemial.ErzeugteKetteProbe.erzeugt_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.ErzeugteKetteProbe.erzeugt_length

/-- info: 'Reformulation.Proemial.ErzeugteKetteProbe.aufPfad_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.ErzeugteKetteProbe.aufPfad_iff

/-- info: 'Reformulation.Proemial.ErzeugteKetteProbe.zul_schranke' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.ErzeugteKetteProbe.zul_schranke

/-- info: 'Reformulation.Proemial.ErzeugteKetteProbe.zul_null' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.ErzeugteKetteProbe.zul_null

/-- info: 'Reformulation.Proemial.ErzeugteKetteProbe.pfad_stand' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.ErzeugteKetteProbe.pfad_stand

/-- info: 'Reformulation.Proemial.ErzeugteKetteProbe.fasersatz_a' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.ErzeugteKetteProbe.fasersatz_a

/-- info: 'Reformulation.Proemial.ErzeugteKetteProbe.pfadPunkt_aufPfad' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.ErzeugteKetteProbe.pfadPunkt_aufPfad

/-- info: 'Reformulation.Proemial.ErzeugteKetteProbe.ueberschreibe_pfad' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.ErzeugteKetteProbe.ueberschreibe_pfad

/-- info: 'Reformulation.Proemial.ErzeugteKetteProbe.ueberschreibe_abseits' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.ErzeugteKetteProbe.ueberschreibe_abseits

/-- info: 'Reformulation.Proemial.ErzeugteKetteProbe.fasersatz_b' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.ErzeugteKetteProbe.fasersatz_b

/-- info: 'Reformulation.Proemial.ErzeugteKetteProbe.faser_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.ErzeugteKetteProbe.faser_iff

/-- info: 'Reformulation.Proemial.ErzeugteKetteProbe.erzeugt_regelNach' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.ErzeugteKetteProbe.erzeugt_regelNach

/-- info: 'Reformulation.Proemial.ErzeugteKetteProbe.ein_schritt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.ErzeugteKetteProbe.ein_schritt

/-- info: 'Reformulation.Proemial.ErzeugteKetteProbe.erzeugt_lokal' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.ErzeugteKetteProbe.erzeugt_lokal

/-- info: 'Reformulation.Proemial.ErzeugteKetteProbe.erzeugt_lokal_pfad' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.ErzeugteKetteProbe.erzeugt_lokal_pfad

/-- info: 'Reformulation.Proemial.ErzeugteKetteProbe.unit_ist_null' does not depend on any axioms -/
#guard_msgs in #print axioms Reformulation.Proemial.ErzeugteKetteProbe.unit_ist_null

/-- info: 'Reformulation.Proemial.ErzeugteKetteProbe.erzeugt_waehleNull' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.ErzeugteKetteProbe.erzeugt_waehleNull

/-- info: 'Reformulation.Proemial.ErzeugteKetteProbe.unit_erzeugt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.ErzeugteKetteProbe.unit_erzeugt

/-- info: 'Reformulation.Proemial.ErzeugteKetteProbe.unit_faktor_erzeugt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.ErzeugteKetteProbe.unit_faktor_erzeugt

/-- info: 'Reformulation.Proemial.ErzeugteKetteProbe.stand_eins' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.ErzeugteKetteProbe.stand_eins

/-- info: 'Reformulation.Proemial.ErzeugteKetteProbe.erzeugt_zwei' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.ErzeugteKetteProbe.erzeugt_zwei

/-- info: 'Reformulation.Proemial.ErzeugteKetteProbe.stufe_zwei_injektiv' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.ErzeugteKetteProbe.stufe_zwei_injektiv

/-- info: 'Reformulation.Proemial.ErzeugteKetteProbe.isRGS_012' does not depend on any axioms -/
#guard_msgs in #print axioms Reformulation.Proemial.ErzeugteKetteProbe.isRGS_012

/-- info: 'Reformulation.Proemial.ErzeugteKetteProbe.stufe_drei_faser' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.ErzeugteKetteProbe.stufe_drei_faser

/-- info: 'Reformulation.Proemial.ErzeugteKetteProbe.ein_schritt_nicht_injektiv' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.ErzeugteKetteProbe.ein_schritt_nicht_injektiv

/-- info: 'Reformulation.Proemial.ErzeugteKetteProbe.gabel_abseits' does not depend on any axioms -/
#guard_msgs in #print axioms Reformulation.Proemial.ErzeugteKetteProbe.gabel_abseits

/-- info: 'Reformulation.Proemial.ErzeugteKetteProbe.erzeugt_praefix' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.ErzeugteKetteProbe.erzeugt_praefix

/-- info: 'Reformulation.Proemial.ErzeugteKetteProbe.einsAn_an' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Proemial.ErzeugteKetteProbe.einsAn_an

/-- info: 'Reformulation.Proemial.ErzeugteKetteProbe.faser_praefix' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.ErzeugteKetteProbe.faser_praefix

/-- info: 'Reformulation.Proemial.ErzeugteKetteProbe.ordnung_aus_fasern' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.ErzeugteKetteProbe.ordnung_aus_fasern

/-- info: 'Reformulation.Proemial.ErzeugteKetteProbe.inFaser_nil' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.ErzeugteKetteProbe.inFaser_nil

/-- info: 'Reformulation.Proemial.ErzeugteKetteProbe.inFaser_null' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.ErzeugteKetteProbe.inFaser_null

/-- info: 'Reformulation.Proemial.ErzeugteKetteProbe.wurzel_kollaps' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.ErzeugteKetteProbe.wurzel_kollaps

/-- info: 'Reformulation.Proemial.ErzeugteKetteProbe.alle_regeln' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.ErzeugteKetteProbe.alle_regeln

/-- info: 'Reformulation.Proemial.ErzeugteKetteProbe.faser_ordnung_voll' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.ErzeugteKetteProbe.faser_ordnung_voll

/-- info: 'Reformulation.Proemial.ErzeugteKetteProbe.eich_ordnung_drei' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.ErzeugteKetteProbe.eich_ordnung_drei

/-- info: 'Reformulation.Proemial.ErzeugteKetteProbe.max_eq_zero_frei' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Proemial.ErzeugteKetteProbe.max_eq_zero_frei

/-- info: 'Reformulation.Proemial.ErzeugteKetteProbe.foldr_max_eq_zero' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Proemial.ErzeugteKetteProbe.foldr_max_eq_zero

/-- info: 'Reformulation.Proemial.ErzeugteKetteProbe.forkWidth_eq_two_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.ErzeugteKetteProbe.forkWidth_eq_two_iff

/-- info: 'Reformulation.Proemial.ErzeugteKetteProbe.zwei_glieder_wiederholung' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.ErzeugteKetteProbe.zwei_glieder_wiederholung

/-- info: 'Reformulation.Proemial.ErzeugteKetteProbe.forkWidth_fwL' does not depend on any axioms -/
#guard_msgs in #print axioms Reformulation.Proemial.ErzeugteKetteProbe.forkWidth_fwL

/-- info: 'Reformulation.Proemial.ErzeugteKetteProbe.eich_zwei_glieder' does not depend on any axioms -/
#guard_msgs in #print axioms Reformulation.Proemial.ErzeugteKetteProbe.eich_zwei_glieder

/-- info: 'Reformulation.Proemial.ErzeugteKetteProbe.muster_map' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Proemial.ErzeugteKetteProbe.muster_map

/-- info: 'Reformulation.Proemial.ErzeugteKetteProbe.umtausch_identitaet' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.ErzeugteKetteProbe.umtausch_identitaet

/-- info: 'Reformulation.Proemial.ErzeugteKetteProbe.umbenennung_trennt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.ErzeugteKetteProbe.umbenennung_trennt

/-- info: 'Reformulation.Proemial.ErzeugteKetteProbe.gabelung_nicht_vertauschbar' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.ErzeugteKetteProbe.gabelung_nicht_vertauschbar

/-- info: 'Reformulation.Proemial.ErzeugteKetteProbe.rgs1_eq' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Proemial.ErzeugteKetteProbe.rgs1_eq

/-- info: 'Reformulation.Proemial.ErzeugteKetteProbe.rgs2_cases' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.ErzeugteKetteProbe.rgs2_cases

/-- info: 'Reformulation.Proemial.ErzeugteKetteProbe.rgs3_cases' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.ErzeugteKetteProbe.rgs3_cases

/-- info: 'Reformulation.Proemial.ErzeugteKetteProbe.code3_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.ErzeugteKetteProbe.code3_lt

/-- info: 'Reformulation.Proemial.ErzeugteKetteProbe.code3_inj' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.ErzeugteKetteProbe.code3_inj

/-- info: 'Reformulation.Proemial.ErzeugteKetteProbe.schubfach_sechs_fuenf' does not depend on any axioms -/
#guard_msgs in #print axioms Reformulation.Proemial.ErzeugteKetteProbe.schubfach_sechs_fuenf

/-- info: 'Reformulation.Proemial.ErzeugteKetteProbe.beq_false_of_ne' does not depend on any axioms -/
#guard_msgs in #print axioms Reformulation.Proemial.ErzeugteKetteProbe.beq_false_of_ne

/-- info: 'Reformulation.Proemial.ErzeugteKetteProbe.fw_q00' does not depend on any axioms -/
#guard_msgs in #print axioms Reformulation.Proemial.ErzeugteKetteProbe.fw_q00

/-- info: 'Reformulation.Proemial.ErzeugteKetteProbe.fw_q01' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.ErzeugteKetteProbe.fw_q01

/-- info: 'Reformulation.Proemial.ErzeugteKetteProbe.wi_inj' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.ErzeugteKetteProbe.wi_inj

/-- info: 'Reformulation.Proemial.ErzeugteKetteProbe.einsortig_unmoeglich_zwei' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.ErzeugteKetteProbe.einsortig_unmoeglich_zwei

/-- info: 'Reformulation.Proemial.ErzeugteKetteProbe.rgs1_q0' depends on axioms: [propext] -/
#guard_msgs in #print axioms Reformulation.Proemial.ErzeugteKetteProbe.rgs1_q0

/-- info: 'Reformulation.Proemial.ErzeugteKetteProbe.fw_q0' does not depend on any axioms -/
#guard_msgs in #print axioms Reformulation.Proemial.ErzeugteKetteProbe.fw_q0

/-- info: 'Reformulation.Proemial.ErzeugteKetteProbe.einsortig_moeglich_eins' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Reformulation.Proemial.ErzeugteKetteProbe.einsortig_moeglich_eins

/-- info: 'Reformulation.Proemial.ErzeugteKetteProbe.zaehlung_drei_vier' does not depend on any axioms -/
#guard_msgs in #print axioms Reformulation.Proemial.ErzeugteKetteProbe.zaehlung_drei_vier
