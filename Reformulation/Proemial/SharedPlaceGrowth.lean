import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Choose.Basic

/-!
# Proemial.SharedPlaceGrowth — die Zahl der Subsystempaare mit gemeinsamer Stelle wächst streng

**Ertrag.** Ein Satz, den Mathlib nicht führt und den man ohne den PKL-Begriff nicht
formuliert hätte: in einem balancierten `m`-wertigen System wächst die Zahl der Paare
`(m-1)`-wertiger balancierter Subsysteme, die eine Belegung gemeinsam haben, **streng** mit
`m`. Der Bau folgt `Spec_Vermittlungsmass.md` (KorpusRev2, Stand 14. September 2026).

Der Satz ist die **Sättigungsprobe**; nach der Spec sind vier andere Masskandidaten an
genau ihr gefallen — die Klon-Grösse (bei `m = 3` und `m = 4` gleich 82), `C(m,2)` (fällt
auf „`m` wächst" zurück), der Morphogramm-Vorrat und die Variablenachse (von Günther
selbst als gesättigt bezeichnet).

## Die drei Marken

**TRÄGER — SETZUNG.** Dass die *wert-eingeschränkten und variablen-fixierten* Subsysteme
die Träger des Masses sind, ist gesetzt. Günther wählt keine Art ausdrücklich; die Spec
begründet die Wahl damit, dass seine Grössenordnungs-Aussage über diese Art laufe — ein
Rang-Anspruch der Spec, von diesem Bau nicht nachgezählt. Die
beiden übrigen Arten (nur wert-eingeschränkt, nur variablen-fixiert) sind nicht gebaut; die
Spec vermerkt sie als gemessen und ebenfalls streng monoton.

**KRITERIUM — QUELLENFEST, aber nicht von diesem Bau geprüft.** Die Spec führt sieben
quellenfeste Posten (Lille S. 24, 25, 27, 29, 33/34): die Definition der Vermittlung
(mindestens zwei Werte **und** zwei Variablen, mit Ausschlussklausel), die Definition von
*balanciert*, das Kriterium der gegenseitigen Abhängigkeit, das vermittelnde Element und
die Wahl des Masses gegen den Funktionsreichtum. **Dieser Bau hat keine dieser Stellen an
der Quelle nachgeschlagen** — er übernimmt sie aus Spec und Appendix-Befund. Das Etikett
*quellenfest* gehört dort hin und nicht hierher (CLAUDE.md §8, zwanzigster Fallstrick).
Quellenfest ist, **dass** es ein Kriterium gibt (S. 27), nicht **welches** — siehe die
Marke darunter. Den Appendix hat inzwischen der Mathematiker am Original gelesen; dieser
Bau weiterhin nicht.

**ANWENDUNG — SETZUNG** *(bis zum Nachtrag unten: LESART)*. Dass Günthers Kriterium der
gegenseitigen Abhängigkeit auf *diese* Subsysteme anzuwenden ist und dass eine gemeinsame
Stelle das vermittelnde Element ist, ist gesetzt. Günther führt das Kriterium an
variablen-fixierten Subsystemen vor; die Übertragung ist unbelegt und unbestritten.

*Nachtrag (14. September 2026, auf Auftrag des Architekten): die Marke ist von LESART auf
SETZUNG gehoben.* Der Lille-Appendix gibt neben dem gebauten Kandidaten — (B), die beiden
teilen eine **Stelle** (S. 29) — drei weitere, alle textgestützt: (A) verschiedene
**fixierte Variable** (S. 27), (C) die Konjunktion beider, (D) das Teilen einer
**Diagonalstelle** (S. 29, Tafel X). Günthers durchgerechneter Fall an Tafel VIII
unterscheidet (A) und (B) nicht. Eine Deutung mit drei Alternativen im Blick ist eine Wahl
und keine Auslegung. Bei `m = 4` liefern (A), (B), (C), (D) 1536, 960, 864 und 264 Paare.
**Bewiesen ist die strenge Monotonie für (B)**; für (A), (C) und (D) ist sie für
`m = 2..5` gerechnet, ausserhalb des Korpus — vom Mathematiker und unabhängig davon beim
Nachtrag, alle sechzehn Zahlen gleich. Die Hebung trüge (A) und (C) mit denselben
Bauteilen, weil der Zeuge in beiden liegt und `lift` verschiedene fixierte Variable ebenso
erhält wie `sharesPlace_lift` die gemeinsame Stelle; für (D) reicht `extend` nicht, weil es
eine Diagonalstelle nicht auf eine Diagonalstelle hebt. Beides ist argumentiert und nicht
gebaut. **Die Wahl von (B) ändert die Zahl; dass sie den Satz nicht ändert, ist gerechnet
und nicht bewiesen.** Die Spec führt die Anwendung weiterhin als Lesart (§1 L1, A5); der
Kopf folgt dem jüngeren Auftrag.

## Was dieses Modul NICHT leistet

- **Nicht die zweite Negation.** Sie hat im Korpus keine Definition, und dieses Modul gibt
  ihr keine.
- **Nicht die Vermittlung selbst.** Gezählt wird eine Inzidenz zwischen Belegungsmengen;
  erklärt wird sie nicht.
- **Kein Anspruch, dass Günther diese Zählung meint.** Er zählt an drei Tafeln drei
  verschiedene Arten.
- **Keine Ledger-Zeile für §20.** Das Mass gehört zu §7 / der Verbundkontextur, nicht zur
  Proemialrelation; `19 von 20` bleibt stehen.

Darum trägt auch **kein Deklarationsname die Sache „Vermittlung"**, wo er die Sache sagen
kann — die Relation heisst `SharesPlace` und nicht `Mediates`. Dieselbe Zurückhaltung übt
der Kopf von `CompoundContexture`, und aus demselben Grund. Die beiden Namen, die die Spec
wörtlich vergibt (`mediationCount`, `mediation_strictly_monotone`), bleiben stehen: sie
benennen das *Mass* und nicht die Sache, und die Marken oben sagen, was daran gesetzt ist.

## Zwei Abweichungen vom Wortlaut der Spec, beide gemeldet

1. **`Mediates` (D4) heisst hier `SharesPlace`.** Der Name ist im Bestand besetzt —
   `Proemial.ComplementaryMediation.Mediates (f : α → α)` bezeichnet die Koexistenz eines
   wiederkehrenden und eines nie zurückkehrenden Punktes unter Iteration, eine andere
   Sache. Nach CLAUDE.md §12 Regel 9 entscheidet die Bedeutung und nicht die Nähe.
2. **Die Wertmenge `W` (D2) ist durch ihren Fehlwert kodiert.** Eine `(m-1)`-elementige
   Teilmenge von `Fin m` ist genau das Komplement eines Wertes; `wertmenge` schreibt `W`
   aus und `card_wertmenge` hält D2s Wortlaut fest. Der Gewinn ist ein Träger ohne
   Teilmengen-Maschinerie und damit `Fintype`/`DecidableEq` ohne `deriving Fintype`
   (CLAUDE.md §8, zehnter Fallstrick).

## Die Gegenstände

`Subsystem m` ist das Tripel aus D2; `wertmenge` und `places` sind D2 und D3; `SharesPlace`
ist D4; `mediatingPairs` und `mediationCount` sind D5, als ungeordnete Paare über
`powersetCard 2` und darum ohne Halbierung.

## Die Sätze

- `mediation_strictly_monotone` — der Zielsatz Z der Spec.
- `mediation_lt_succ` — derselbe Schritt ohne die Trägerbedingung; gebaut wird er über die
  **Hebung**: `lift` bettet jedes Subsystem der Stufe `m` in die Stufe `m+1` ein, `extend`
  hebt eine gemeinsame Stelle mit, und der Zeuge `witPair` ist ein vermittelndes Paar der
  Stufe `m+1`, dessen Wertmenge den obersten Wert ausschliesst und das darum in keinem Bild
  liegt. Kein Abzählen, keine geschlossene Formel.
- `mediation_le_pow` — der Zusatzsatz Z' der Spec, `mediationCount m ≤ m^6`, über
  `(m^3).choose 2`.
- `sharesPlace_iff_kriterium` — die Auflösung von D4 in eine Bedingung über den drei
  Bestandteilen. Sie trägt die **Rechenform**: über sie läuft die `Decidable`-Instanz, mit
  der die Eichwerte ausgewertet werden.

## Warum die Instanz über das Kriterium läuft, gemessen

Mit der naheliegenden Instanz — `places S ∩ places T` bilden und auf Bewohntheit prüfen —
ist `mediationCount 5` nicht auswertbar: der Lauf wurde nach **27 Minuten ohne Ergebnis**
abgebrochen (`m ≤ 4` läuft dort durch). Über `decidable_of_iff` und das Kriterium liefert
derselbe Ausdruck alle vier Eichwerte in rund **zwei Sekunden**. **Die Definition von
`SharesPlace` bleibt dabei D4** — getauscht ist nur der Entscheidungsweg, und dass er
denselben Wert entscheidet, ist `sharesPlace_iff_kriterium`.

## Die Vorab-Bauprobe der Spec, beantwortet

- **P1 (D4 entscheidbar?)** — ja, und zweimal: naiv über den endlichen Schnitt, brauchbar
  über das Kriterium. `Classical.choice` steht trotzdem im Profil, aber nicht deswegen
  (siehe Axiomlage).
- **P2 (terminiert ohne Guard?)** — ja, strukturell. Kein Guard, keine Setzung.
- **P3 (Randfall `m = 2`)** — `mediationCount 2 = 4`, nicht 0. D2 und D4 sind damit an
  Günthers erstem Vermittlungssystem gehalten.
- **P4 (`m = 1` ausgeschlossen?)** — **nicht durch die Definition.** `mediationCount 1 = 0`
  und `mediationCount 0 = 0` sind beide definiert und ausgewertet; ausgeschlossen wird
  `m = 1` allein durch die Hypothese `2 ≤ m` des Zielsatzes. Das ist die zweite der beiden
  Antworten, die P4 zulässt, und sie steht hier, damit niemand die erste unterstellt.
- **P5 (ungeordnete Paare ohne Doppelung?)** — ja: `powersetCard 2` zählt Mengen, keine
  Tupel; `mediationCount 3 = 135` und nicht 270.
- **P6 (fällt Z auf „`m` wächst" zurück?)** — nein. Der Quotient `mediationCount m / m^3`
  ist 5, 15, 34 für `m = 3, 4, 5` und damit nicht konstant; die Eichwert-Wachen halten ihn
  fest. Stärker noch: `mediation_lt_succ` wächst nicht mit der Grundmenge, sondern über
  einen Zeugen, der in keinem Bild der Hebung liegt.

## Die Variante aus N3, identifiziert und gemessen

Die Spec lässt offen, ob „Wiederholungspaare" mitzählen, und vermerkt für die Variante ohne
sie 99 / 744 / 3450. **Gemessen:** die Einschränkung auf Paare mit **verschiedener
Wertmenge** liefert genau diese drei Zahlen, und die Differenz bei `m = 4` ist genau
**216** — die Zahl, über die die Spec ausdrücklich nicht entscheidet. Gemessen ist damit
die Gleichheit der Zahlen; **nicht** gemessen ist, dass diese Einschränkung die von der
Spec gemeinte ist, und erst recht nicht, dass Günthers 216 diese ist.

## Ein Fund an zwei fremden Dokumenten — gemeldet, dann entschieden

Die Eichwerte-Tafel der Spec liest Günthers zwei durchgerechnete Zahlen als
**Subsystem**-Zahlen (27 und 64). Der Appendix-Befund des Hermeneutes (§5, L6) und die
N1-Messung des Mathematikers lesen dieselben Zahlen als seine zwei durchgerechneten Fälle
der **Relation** — „(3, 64)". Auf der zweiten Lesart reproduziert dieses Mass Günthers 64
nicht: `mediationCount 4 = 960`. So stand der Fund beim Bau: gemeldet und nicht
entschieden, mit der Spec, die ihn selbst als offenen Posten führt (N1, O3).

*Nachtrag (14. September 2026, nach der Begutachtung des Mathematikers §2): der Fund ist
entschieden, und zwar gegen die beiden älteren Dokumente.* Die Klärung
`Knoten_Begrenzung_Relation_Antwort_Hermeneutes.md` trennt die zwei Zahlen, und sie führt
die Trennung als quellenfest: die „nur dreimal" (K3) gilt den **variablen-fixierten
überbalancierten** Subsystemen der Tafel XII, also einem *anderen System*; die 64 (K1, K4)
gilt der **kombinierten** Art — der Art dieses Moduls — und ist dort eine **obere Schranke
in einem Grössenordnungs-Argument, keine Zählung**. Zwei Fälle derselben Grösse sind sie
darum nicht, und **die Spec liest richtig**. Dass `mediationCount 4 = 960` die 64 nicht
trifft, ist danach kein Mangel: die 64 gehört zu `card_subsystem` und nicht zum Mass. Die
Klärung ist jünger als die beiden Dokumente; ihre Berichtigung steht aus und liegt
ausserhalb dieses Repositoriums.

*Und eine Marke, die dieselbe Klärung setzt und die A1 betrifft:* die Formel `m³` steht
**nicht** im Text (K2, dort **erschlossen** und ausdrücklich nicht quellenfest).
`card_subsystem` trifft mit ihr Günthers 27 und 64; quellenfest sind die zwei Zahlen, nicht
ihr Bildungsgesetz.

*Und zu Ende gebracht (14. September 2026, Auftrag des Mathematikers §5, F1 und F2):* die
„nur dreimal" ist überhaupt **keine Relationen-Zahl**. Sie zählt **Stellen** — die Diagonale
von S³(p,q) mit den Stellen 1, 5 und 9 —, und ihre Zahl ist `m`. Damit nennt Günther
**keine** Zahl, an der sich ein Relationen-Mass eichen liesse: die drei zählt Stellen, die
64 Subsysteme, und die Relationen-Zahl heisst bei ihm nur „relativ bescheiden" — wahr für
alle vier Kandidaten, weil jeder eine Teilmenge derselben `(m³).choose 2` Paare zählt (für
(B) als `mediation_le_pow` bewiesen, für die übrigen argumentiert). **Die Paar-Eichwerte
4 / 135 / 960 / 4250 eichen darum den Bau gegen die Spec und nicht das Mass gegen Günther;**
gegen Günther geeicht sind allein die Subsystem-Zahlen 27 und 64. F1 ist aus dem fünften
Befund dieses Baus hervorgegangen; die Lesung am Original ist die des Mathematikers.

## Axiomlage, gemessen

`Classical.choice` steht in siebzehn der neunzehn Sätze dieses Moduls, und **die Ursache
ist gemessen und nicht vermutet**: `Fin.fintype` trägt selbst
`[propext, Classical.choice, Quot.sound]`, und jeder Term, in dem `univ` über `Fin m`
vorkommt, erbt es — `Finset.mem_univ` allein ist `[propext, Quot.sound]`, die Instanz ist
es nicht. Damit ist der Vermerk im Kopf von `CompoundContexture` verschärft, und dort steht
der Nachtrag: es liegt nicht an der `Finset`-Gestalt über Funktionsräumen, sondern schon am
Trägertyp.

Das Differential steht im Modul selbst. Über alle neunzehn Sätze gemessen bleiben genau
zwei choice-frei, und es sind genau die beiden, deren Beweisterm keine `Finset` berührt:
`lift_injective` mit `[propext]` und das private `wit_ne` mit `[propext, Quot.sound]`.
Gewacht ist das erste; das zweite steht hier, weil eine Aussage über *alle* Sätze sonst
über vierzehn gemessen und über neunzehn behauptet wäre.

## Aggregat-Reife

Konsumiert nur Mathlib. Keine Sonde, keine Setzung im technischen Sinn — kein `sorry`, kein
`axiom`, kein `: True`-Feld. Nachbarschaft, nicht konsumiert:
`CompoundContexture.two_elem_contextures_iff` (die Mindestdreiwertigkeit),
`ContextureOverlap.IsElemContexture` (die Wert-Zweiermenge), `ChoiceVectors.card_pairs`.
-/

open Finset

namespace Reformulation.Proemial.SharedPlaceGrowth

/-! ## Teil 1 — der Träger (D1, D2, D3) -/

/-- **Ein `(m-1)`-wertiges, `(m-1)`-variabliges Subsystem eines balancierten `m`-wertigen
Systems** (D2). Die Wertmenge `W` ist durch ihren **Fehlwert** kodiert: eine
`(m-1)`-elementige Teilmenge von `Fin m` ist genau das Komplement eines Wertes. -/
structure Subsystem (m : ℕ) where
  /-- der ausgeschlossene Wert; die Wertmenge ist `univ.erase fehlwert` -/
  fehlwert : Fin m
  /-- die fixierte Variable `v` -/
  fixVar : Fin m
  /-- der Wert `x`, auf den `v` fixiert ist -/
  fixWert : Fin m
  deriving DecidableEq

/-- Die Tripel-Gestalt des Trägers, ausgeschrieben. Sie trägt die `Fintype`-Instanz; eine
`deriving Fintype`-Instanz wird vermieden (CLAUDE.md §8, zehnter Fallstrick). -/
def subsystemEquiv (m : ℕ) : Subsystem m ≃ Fin m × Fin m × Fin m where
  toFun S := (S.fehlwert, S.fixVar, S.fixWert)
  invFun p := ⟨p.1, p.2.1, p.2.2⟩
  left_inv := by rintro ⟨a, b, c⟩; rfl
  right_inv := by rintro ⟨a, b, c⟩; rfl

instance (m : ℕ) : Fintype (Subsystem m) :=
  Fintype.ofEquiv (Fin m × Fin m × Fin m) (subsystemEquiv m).symm

/-- **Die Subsystem-Zahl ist `m³`** — Günthers 27 und 64 in allgemeiner Gestalt, und die
Rechnung dahinter: `m` Wertmengen mal `m` Variablen mal `m` Fixwerte. -/
theorem card_subsystem (m : ℕ) : Fintype.card (Subsystem m) = m ^ 3 := by
  rw [Fintype.card_congr (subsystemEquiv m)]
  simp [Fintype.card_prod, pow_succ, pow_zero]
  exact (mul_assoc m m m).symm

/-- Die Wertmenge `W` des Subsystems, ausgeschrieben (D2). -/
def wertmenge {m : ℕ} (S : Subsystem m) : Finset (Fin m) := univ.erase S.fehlwert

theorem mem_wertmenge {m : ℕ} (S : Subsystem m) (y : Fin m) :
    y ∈ wertmenge S ↔ y ≠ S.fehlwert := by
  simp [wertmenge]

/-- **D2 im Wortlaut:** die Wertmenge ist `(m-1)`-elementig, das Subsystem also
balanciert. -/
theorem card_wertmenge {m : ℕ} (S : Subsystem m) : (wertmenge S).card = m - 1 := by
  simp [wertmenge, Finset.card_erase_of_mem]

/-- **D1:** die Stellen des ganzen Systems sind die Belegungen, `m^m` Stück. -/
theorem card_places_univ (m : ℕ) : Fintype.card (Fin m → Fin m) = m ^ m := by
  simp

/-- **Die Stellen des Subsystems** (D3): die Belegungen, die `v` auf `x` setzen und sonst
nur Werte aus `W` annehmen. -/
def places {m : ℕ} (S : Subsystem m) : Finset (Fin m → Fin m) :=
  univ.filter fun a => a S.fixVar = S.fixWert ∧ ∀ i, i ≠ S.fixVar → a i ∈ wertmenge S

theorem mem_places {m : ℕ} (S : Subsystem m) (a : Fin m → Fin m) :
    a ∈ places S ↔ a S.fixVar = S.fixWert ∧ ∀ i, i ≠ S.fixVar → a i ≠ S.fehlwert := by
  simp [places, mem_wertmenge]

/-! ## Teil 2 — die Relation und ihre Auflösung (D4) -/

/-- **D4.** Zwei Subsysteme stehen in der Relation, wenn ihre Stellenmengen eine Stelle
gemeinsam haben — die gesetzte Fassung des vermittelnden Elements, eine von vier (Modulkopf,
Marke ANWENDUNG). Der Name sagt die Sache; „`Mediates`"
ist im Bestand anders besetzt (`ComplementaryMediation`), siehe Modulkopf. -/
def SharesPlace {m : ℕ} (S T : Subsystem m) : Prop := (places S ∩ places T).Nonempty

theorem sharesPlace_iff_exists {m : ℕ} (S T : Subsystem m) :
    SharesPlace S T ↔ ∃ a, a ∈ places S ∧ a ∈ places T := by
  simp [SharesPlace, Finset.Nonempty, Finset.mem_inter]

/-- Die Bedingung, in die D4 zerfällt: Verträglichkeit an den beiden fixierten Variablen,
und — sobald es eine dritte Variable gibt — ein Wert, den beide Wertmengen führen. -/
def Kriterium {m : ℕ} (S T : Subsystem m) : Prop :=
  (S.fixVar = T.fixVar → S.fixWert = T.fixWert) ∧
  (S.fixVar ≠ T.fixVar → S.fixWert ≠ T.fehlwert ∧ T.fixWert ≠ S.fehlwert) ∧
  ((∃ i : Fin m, i ≠ S.fixVar ∧ i ≠ T.fixVar) →
    ∃ c : Fin m, c ≠ S.fehlwert ∧ c ≠ T.fehlwert)

instance {m : ℕ} (S T : Subsystem m) : Decidable (Kriterium S T) := by
  unfold Kriterium; infer_instance

/-- Die Rückrichtung, aus der Belegung heraus gebaut: `v` auf `x`, `w` auf `y`, alles
übrige auf einen Wert, den beide Wertmengen führen. -/
private theorem sharesPlace_of_witness {m : ℕ} {S T : Subsystem m}
    (h1 : S.fixVar = T.fixVar → S.fixWert = T.fixWert)
    (h2 : S.fixVar ≠ T.fixVar → S.fixWert ≠ T.fehlwert ∧ T.fixWert ≠ S.fehlwert)
    (c : Fin m)
    (hc : ∀ i : Fin m, i ≠ S.fixVar → i ≠ T.fixVar → c ≠ S.fehlwert ∧ c ≠ T.fehlwert) :
    SharesPlace S T := by
  refine (sharesPlace_iff_exists S T).mpr
    ⟨fun i => if i = S.fixVar then S.fixWert else if i = T.fixVar then T.fixWert else c,
      ?_, ?_⟩
  · refine (mem_places S _).mpr ⟨by simp, ?_⟩
    intro i hi
    simp only [if_neg hi]
    split_ifs with hT
    · exact ((h2 (fun h => hi (hT.trans h.symm))).2)
    · exact (hc i hi hT).1
  · refine (mem_places T _).mpr ⟨?_, ?_⟩
    · split_ifs with hS hT
      · exact h1 hS.symm
      · rfl
      · exact absurd rfl hT
    · intro i hi
      by_cases hS : i = S.fixVar
      · simp only [if_pos hS]
        exact (h2 (fun h => hi (hS.trans h))).1
      · simp only [if_neg hS, if_neg hi]
        exact (hc i hS hi).2

/-- **Die Auflösung von D4.** Sie trägt die Rechenform des Masses: über sie läuft die
`Decidable`-Instanz, mit der die Eichwerte ausgewertet werden. -/
theorem sharesPlace_iff_kriterium {m : ℕ} (S T : Subsystem m) :
    SharesPlace S T ↔ Kriterium S T := by
  constructor
  · intro h
    obtain ⟨a, haS, haT⟩ := (sharesPlace_iff_exists S T).mp h
    obtain ⟨hSv, hSj⟩ := (mem_places S a).mp haS
    obtain ⟨hTv, hTj⟩ := (mem_places T a).mp haT
    refine ⟨fun h => ?_, fun h => ⟨?_, ?_⟩, fun ⟨i, hi1, hi2⟩ => ⟨a i, hSj i hi1, hTj i hi2⟩⟩
    · rw [← hSv, ← hTv, h]
    · rw [← hSv]; exact hTj _ h
    · rw [← hTv]; exact hSj _ (Ne.symm h)
  · rintro ⟨h1, h2, h3⟩
    by_cases hfree : ∃ i : Fin m, i ≠ S.fixVar ∧ i ≠ T.fixVar
    · obtain ⟨c, hc1, hc2⟩ := h3 hfree
      exact sharesPlace_of_witness h1 h2 c (fun _ _ _ => ⟨hc1, hc2⟩)
    · exact sharesPlace_of_witness h1 h2 S.fixWert
        (fun i hi1 hi2 => absurd ⟨i, hi1, hi2⟩ hfree)

instance {m : ℕ} (S T : Subsystem m) : Decidable (SharesPlace S T) :=
  decidable_of_iff _ (sharesPlace_iff_kriterium S T).symm

/-! ## Teil 3 — die Zählung (D5) -/

/-- Die vermittelnden Paare als **Mengen** und nicht als Tupel: `powersetCard 2` zählt
jedes ungeordnete Paar einmal, ohne Halbierung. -/
def mediatingPairs (m : ℕ) : Finset (Finset (Subsystem m)) :=
  ((univ : Finset (Subsystem m)).powersetCard 2).filter
    fun p => ∃ S ∈ p, ∃ T ∈ p, S ≠ T ∧ SharesPlace S T

/-- **D5 — das Mass.** -/
def mediationCount (m : ℕ) : ℕ := (mediatingPairs m).card

/-- Die Variante aus N3 der Spec: nur Paare mit **verschiedener** Wertmenge. Nicht der
Gegenstand des Zielsatzes; sie steht hier, weil die Spec ihre Zahlen vermerkt und weil eine
ausserhalb gerechnete Zahl im Korpus nichts zu suchen hat. -/
def mediationCountDistinct (m : ℕ) : ℕ :=
  (((univ : Finset (Subsystem m)).powersetCard 2).filter
    fun p => ∃ S ∈ p, ∃ T ∈ p, S.fehlwert ≠ T.fehlwert ∧ SharesPlace S T).card

/-! ## Teil 4 — die Hebung -/

/-- Jedes Subsystem der Stufe `m` wird eines der Stufe `m+1`: alle drei Bestandteile gehen
über `castSucc`, die Wertmenge wächst dabei um den obersten Wert. -/
def lift {m : ℕ} (S : Subsystem m) : Subsystem (m + 1) :=
  ⟨S.fehlwert.castSucc, S.fixVar.castSucc, S.fixWert.castSucc⟩

theorem lift_injective (m : ℕ) : Function.Injective (lift (m := m)) := by
  rintro ⟨a, b, c⟩ ⟨a', b', c'⟩ h
  simp only [lift, Subsystem.mk.injEq, Fin.castSucc_inj] at h
  simp [h.1, h.2.1, h.2.2]

/-- Die mitgehobene Belegung: die neue Variable bekommt den neuen Wert, alles übrige geht
über `castSucc`. -/
def extend {m : ℕ} (a : Fin m → Fin m) : Fin (m + 1) → Fin (m + 1) :=
  Fin.lastCases (Fin.last m) (fun i => (a i).castSucc)

theorem mem_places_extend {m : ℕ} {S : Subsystem m} {a : Fin m → Fin m}
    (h : a ∈ places S) : extend a ∈ places (lift S) := by
  obtain ⟨hv, hj⟩ := (mem_places S a).mp h
  refine (mem_places (lift S) _).mpr ⟨?_, ?_⟩
  · simp only [lift, extend, Fin.lastCases_castSucc, hv]
  · intro i hi
    induction i using Fin.lastCases with
    | last =>
      simp only [extend, Fin.lastCases_last, lift]
      exact (Fin.castSucc_lt_last S.fehlwert).ne'
    | cast i =>
      simp only [extend, Fin.lastCases_castSucc, lift, Ne, Fin.castSucc_inj]
      exact hj i (by simpa [lift, Fin.castSucc_inj] using hi)

theorem sharesPlace_lift {m : ℕ} {S T : Subsystem m} (h : SharesPlace S T) :
    SharesPlace (lift S) (lift T) := by
  obtain ⟨a, haS, haT⟩ := (sharesPlace_iff_exists S T).mp h
  exact (sharesPlace_iff_exists _ _).mpr
    ⟨extend a, mem_places_extend haS, mem_places_extend haT⟩

/-- **Die Hebung trägt die Zählung mit:** jedes vermittelnde Paar der Stufe `m` liefert
eines der Stufe `m+1`. -/
theorem image_lift_subset (m : ℕ) :
    (mediatingPairs m).image (Finset.image lift) ⊆ mediatingPairs (m + 1) := by
  intro p hp
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
  obtain ⟨hq2, hqm⟩ := Finset.mem_filter.mp hq
  obtain ⟨_, hcard⟩ := Finset.mem_powersetCard.mp hq2
  obtain ⟨S, hS, T, hT, hST, hmed⟩ := hqm
  refine Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, ?_⟩, ?_⟩
  · rw [Finset.card_image_of_injective _ (lift_injective m), hcard]
  · exact ⟨lift S, Finset.mem_image_of_mem _ hS, lift T, Finset.mem_image_of_mem _ hT,
      fun h => hST (lift_injective m h), sharesPlace_lift hmed⟩

/-! ## Teil 5 — der Zeuge

Zwei Subsysteme der Stufe `n+2`, deren Wertmenge gerade den **obersten** Wert ausschliesst
und die sich nur in der fixierten Variablen unterscheiden. Die Nullbelegung liegt in beiden
Stellenmengen; und weil jede Hebung ihren Fehlwert über `castSucc` bezieht, liegt das Paar
in keinem Bild. -/

private def wit0 (n : ℕ) : Subsystem (n + 2) :=
  ⟨Fin.last (n + 1), ⟨0, by omega⟩, ⟨0, by omega⟩⟩

private def wit1 (n : ℕ) : Subsystem (n + 2) :=
  ⟨Fin.last (n + 1), ⟨1, by omega⟩, ⟨0, by omega⟩⟩

private def witPair (n : ℕ) : Finset (Subsystem (n + 2)) := {wit0 n, wit1 n}

private theorem wit_ne (n : ℕ) : wit0 n ≠ wit1 n := by
  simp [wit0, wit1, Subsystem.mk.injEq]

private theorem wit_shares (n : ℕ) : SharesPlace (wit0 n) (wit1 n) := by
  refine (sharesPlace_iff_exists _ _).mpr ⟨fun _ => ⟨0, by omega⟩, ?_, ?_⟩
  · refine (mem_places _ _).mpr ⟨rfl, fun i _ => ?_⟩
    simp [wit0, Fin.ext_iff]
  · refine (mem_places _ _).mpr ⟨rfl, fun i _ => ?_⟩
    simp [wit1, Fin.ext_iff]

private theorem wit_mem (n : ℕ) : witPair n ∈ mediatingPairs (n + 2) := by
  refine Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, ?_⟩, ?_⟩
  · rw [witPair, Finset.card_insert_of_notMem (by simpa using wit_ne n), Finset.card_singleton]
  · exact ⟨wit0 n, by simp [witPair], wit1 n, by simp [witPair], wit_ne n, wit_shares n⟩

private theorem wit_not_mem_image (n : ℕ) :
    witPair n ∉ (mediatingPairs (n + 1)).image (Finset.image lift) := by
  intro h
  obtain ⟨q, _, hq⟩ := Finset.mem_image.mp h
  have h0 : wit0 n ∈ Finset.image lift q := by rw [hq]; simp [witPair]
  obtain ⟨S, _, hS⟩ := Finset.mem_image.mp h0
  have : S.fehlwert.castSucc = Fin.last (n + 1) := by
    rw [show S.fehlwert.castSucc = (lift S).fehlwert from rfl, hS]; rfl
  exact (Fin.castSucc_lt_last S.fehlwert).ne this

/-! ## Teil 6 — der Zielsatz -/

/-- Der Schritt, ohne die Trägerbedingung: das Bild der Hebung ist eine **echte**
Teilmenge, weil der Zeuge vermittelt und in keinem Bild liegt. -/
theorem mediation_lt_succ (n : ℕ) : mediationCount (n + 1) < mediationCount (n + 2) := by
  have hcard : ((mediatingPairs (n + 1)).image (Finset.image lift)).card
      = mediationCount (n + 1) :=
    Finset.card_image_of_injective _ (Finset.image_injective (lift_injective (n + 1)))
  have hss : (mediatingPairs (n + 1)).image (Finset.image lift) ⊂ mediatingPairs (n + 2) :=
    (Finset.ssubset_iff_of_subset (image_lift_subset (n + 1))).mpr
      ⟨witPair n, wit_mem n, wit_not_mem_image n⟩
  calc mediationCount (n + 1)
      = ((mediatingPairs (n + 1)).image (Finset.image lift)).card := hcard.symm
    _ < (mediatingPairs (n + 2)).card := Finset.card_lt_card hss
    _ = mediationCount (n + 2) := rfl

/-- **Der Zielsatz Z: das Mass sättigt nicht.** Jede erneute Anwendung erhöht die
Komplexität des Gesamtsystems — Günthers Kriterium (C) in messbarer Gestalt.

Die Trägerbedingung `2 ≤ m` ist Günthers Ausschlussklausel (Q1) und trägt den Satz nicht:
`mediation_lt_succ` gilt schon ab `m = 1`. Sie steht hier, weil unterhalb von zwei Werten
kein Vermittlungssystem vorliegt, über das der Satz etwas aussagen dürfte. -/
theorem mediation_strictly_monotone {m : ℕ} (hm : 2 ≤ m) :
    mediationCount m < mediationCount (m + 1) := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 2 := ⟨m - 2, by omega⟩
  exact mediation_lt_succ (n + 1)

/-- **Der Zusatzsatz Z': das Mass bleibt polynomial.** Gegen `m^(m^m)` ist das Günthers
„relativ bescheiden" in beweisbarer Form; gemessen wächst es wie `m^5`, `m^6` ist eine
grosszügige und billig zu haltende Schranke. -/
theorem mediation_le_pow (m : ℕ) : mediationCount m ≤ m ^ 6 := by
  have h1 : mediationCount m ≤ ((univ : Finset (Subsystem m)).powersetCard 2).card :=
    Finset.card_filter_le _ _
  rw [Finset.card_powersetCard, Finset.card_univ, card_subsystem] at h1
  calc mediationCount m ≤ (m ^ 3).choose 2 := h1
    _ = m ^ 3 * (m ^ 3 - 1) / 2 := Nat.choose_two_right _
    _ ≤ m ^ 3 * (m ^ 3 - 1) := Nat.div_le_self _ _
    _ ≤ m ^ 3 * m ^ 3 := Nat.mul_le_mul le_rfl (Nat.sub_le _ _)
    _ = m ^ 6 := (pow_add m 3 3).symm

/-! ## Teil 7 — die Eichwerte (A1, A2)

Nicht `#eval` allein: `#guard_msgs` friert die Ausgabe ein, sonst bliebe der Bau grün, wenn
sich eine Zahl bewegt. Dieselbe Unterscheidung wie bei den Axiom-Wachen (CLAUDE.md §8,
sechzehnter Fallstrick) — gedruckt gegen gewacht. -/

/-- info: (8, 27, 64, 125) -/
#guard_msgs in #eval (Fintype.card (Subsystem 2), Fintype.card (Subsystem 3),
  Fintype.card (Subsystem 4), Fintype.card (Subsystem 5))

/-- info: (4, 135, 960, 4250) -/
#guard_msgs in #eval (mediationCount 2, mediationCount 3, mediationCount 4, mediationCount 5)

/-- info: true -/
#guard_msgs in #eval decide (mediationCount 2 < mediationCount 3 ∧
  mediationCount 3 < mediationCount 4 ∧ mediationCount 4 < mediationCount 5)

/-- info: (5, 15, 34) -/
#guard_msgs in #eval (mediationCount 3 / 27, mediationCount 4 / 64, mediationCount 5 / 125)

/-- info: (0, 0) -/
#guard_msgs in #eval (mediationCount 0, mediationCount 1)

/-- info: (99, 744, 3450) -/
#guard_msgs in #eval (mediationCountDistinct 3, mediationCountDistinct 4,
  mediationCountDistinct 5)

/-- info: 216 -/
#guard_msgs in #eval mediationCount 4 - mediationCountDistinct 4

/-! ## Teil 8 — Statement-Pins

Ein Pin nagelt den vollen Wortlaut fest: ein geschwächter Satz mit gleichem Axiomprofil
käme durch eine Wache hindurch, aber nicht hier vorbei. -/

-- STATEMENT-PIN
example (m : ℕ) : Fintype.card (Subsystem m) = m ^ 3 := card_subsystem m
-- STATEMENT-PIN
example {m : ℕ} (S : Subsystem m) : (wertmenge S).card = m - 1 := card_wertmenge S
-- STATEMENT-PIN
example {m : ℕ} (S T : Subsystem m) :
    SharesPlace S T ↔
      (S.fixVar = T.fixVar → S.fixWert = T.fixWert) ∧
      (S.fixVar ≠ T.fixVar → S.fixWert ≠ T.fehlwert ∧ T.fixWert ≠ S.fehlwert) ∧
      ((∃ i : Fin m, i ≠ S.fixVar ∧ i ≠ T.fixVar) →
        ∃ c : Fin m, c ≠ S.fehlwert ∧ c ≠ T.fehlwert) := sharesPlace_iff_kriterium S T
-- STATEMENT-PIN
example {m : ℕ} (hm : 2 ≤ m) : mediationCount m < mediationCount (m + 1) :=
  mediation_strictly_monotone hm
-- STATEMENT-PIN
example (m : ℕ) : mediationCount m ≤ m ^ 6 := mediation_le_pow m

/-! ## Teil 9 — die Axiom-Wachen (Ist-gebunden)

Ist-Ausgabe des grünen Builds (v4.30.0-rc2), je Deklaration eingefroren — gemessen und
nicht erwartet. Zur Ursache des `Classical.choice` siehe den Modulkopf; `lift_injective`
ist das Differential. -/

/-- info: 'Reformulation.Proemial.SharedPlaceGrowth.card_subsystem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms card_subsystem

/-- info: 'Reformulation.Proemial.SharedPlaceGrowth.card_wertmenge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms card_wertmenge

/--
info: 'Reformulation.Proemial.SharedPlaceGrowth.sharesPlace_iff_kriterium' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms sharesPlace_iff_kriterium

/-- info: 'Reformulation.Proemial.SharedPlaceGrowth.lift_injective' depends on axioms: [propext] -/
#guard_msgs in #print axioms lift_injective

/-- info: 'Reformulation.Proemial.SharedPlaceGrowth.image_lift_subset' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms image_lift_subset

/-- info: 'Reformulation.Proemial.SharedPlaceGrowth.mediation_lt_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms mediation_lt_succ

/--
info: 'Reformulation.Proemial.SharedPlaceGrowth.mediation_strictly_monotone' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms mediation_strictly_monotone

/-- info: 'Reformulation.Proemial.SharedPlaceGrowth.mediation_le_pow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms mediation_le_pow

end Reformulation.Proemial.SharedPlaceGrowth
