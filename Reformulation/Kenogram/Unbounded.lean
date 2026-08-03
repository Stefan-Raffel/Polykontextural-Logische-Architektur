import Reformulation.Kenogram.Bridge
import Reformulation.Kenogram.Fillability

/-!
# Kenogram.Unbounded — kein endlicher Wertvorrat traegt einen unbeschraenkten Strom

**Ertrag.** Zwei Teile, ein Traeger.

* **U1 — die verallgemeinerte Bruecke** (`marksLt_iff_fillable`): ein RGS hat alle Marken
  `< k` **genau dann**, wenn er die Normalform einer `k`-wertigen Wertfolge
  `Fin n → Fin k` ist. Das ist die Wertseite: „hoechste Marke unter `k`" *ist*
  „von einem `k`-wertigen System erfuellt", fuer jedes `k` und jedes `n`.
* **U2/U3 — die Strom-Seite** (`unbounded_not_fillable`, `idRGSStream_not_fillable`):
  ein kenogrammatischer Strom mit unbeschraenkten Marken wird von **jedem** endlichen
  Wertvorrat ueberschritten — zu jedem `k` gibt es eine Praefixlaenge, ab der das
  Praefix von keiner `k`-wertigen Wertfolge mehr erzeugt wird. Zeuge im Korpus: der
  Identitaetsstrom, hier als **benanntes** Objekt.

Die Randlagen sind mitbehauptet und stimmen: bei `k = 0` und `n ≥ 1` sind in U1 beide
Seiten falsch (eine Marke `< 0` gibt es nicht, eine Folge nach `Fin 0` auch nicht), bei
`n = 0` sind beide leer wahr.

## Verhaeltnis zu `Fillability` (Z1) — U1 ersetzt es nicht

`marksLeOne_iff_fillable` (ueber `Bool`) bleibt unangetastet der §16-Traeger. U1 ueber
`Fin k` ist ein anderes Statement — `Fin 2` ist nicht `Bool` —, und eine Uebersetzung
zwischen beiden ist nicht gebaut und nicht geschuldet. Was gebaut ist, ist die billige
Praedikat-Seite: `marksLeOne_iff_marksLt_two` sagt, dass die beiden *syntaktischen*
Kriterien dasselbe sind. Ueber die semantischen Seiten sagt sie nichts.

## Verhaeltnis zu Strang G (`Proemial.StageParity`) — ein Satz

Dort: der Aufstieg hat keine signaturtreue Gestalt (die Negation steigt bei ungeradem m
unter keiner Abbildung mit). Hier: kein endlicher Vorrat traegt ihn. Komplementaer, und
ohne Code-Abhaengigkeit in irgendeine Richtung — die beiden Dateien wissen nichts
voneinander.

## Deutungs-Marken (verbindlich)

1. **Kenogramm ist nicht Kontextur — der Sprung ist markiert.** Die Lesung von
   `Fin k`-Folgen als „`k`-wertiges System" haengt an U1, und U1 stuetzt sie als *Satz*.
   Die Lesung von U2 und U3 als „sich unendlich erweiternde Kontexturen" ist dagegen
   **Deutung**: sie traegt kein Satz, sie steht in keinem Namen, und der Weg vom
   Kenogramm zur Kontextur ist im Korpus nicht gebaut. Der Dateiname sagt, was bewiesen
   ist: Unbeschraenktheit schlaegt jeden endlichen Vorrat.
2. **Kein Grenzobjekt behauptet.** Der Strom ist Korpus-Objekt in der Subtyp-Traegerwahl
   von S2 (`Kenogram.Stream`); der M-Typ bleibt dort [Kandidat], und diese Datei ruehrt
   ihn nicht an. Die Def6-Totalitaet wird nicht behauptet; die Ledger-Zeile L06-1 bleibt
   `Offen`.
3. **Die A3/J-Frage bleibt unberuehrt offen** (`Stream.lean`, Phase 4). Diese Datei nimmt
   zu Deutero-Bloecken keine Stellung — sie zaehlt Marken, sie vergroebert nichts.
4. **Der Identitaetsstrom ist gewaehlter Zeuge.** Jeder unbeschraenkte kenogrammatische
   Strom taete es genauso; die Wahl faellt auf den, den der Bestand schon kennt. Dass er
   unbeschraenkt
   ist, steht als Illustration schon in `Stream.lean`; hier ist er benannt, damit ein Satz
   ihn konsumieren kann. Die anonyme Illustration dort **bleibt stehen** — dieselbe
   unschaedliche Doppelung wie `card_rgs_four` gegen die Phase-4-Reihe: beide bewiesen,
   Drift unmoeglich, und `Stream.lean` bleibt unangetastet.

## Robustheit (`CLAUDE.md` §9) ist hier gegenstandslos

Keine Klon-Schranke, keine Nicht-Erzeugbarkeit im Termklon, keine Invariante — nichts,
dessen Reflexivitaet zu pruefen waere. Die Nichtexistenz-Aussage dieser Datei ist eine
Kardinalitaets-Aussage ueber Wertvorraete, keine Schranke ueber einer Signatur. Das steht
hier, damit niemand eine Pruefung vermisst, die es nicht zu fuehren gibt.

## Zum Axiom-Profil

Der Kenogram-Zweig traegt `Classical.choice` ueber `instFintypeRGS` und die
`Finset`-Kette von `IsRGSStream`/`canonicalize` (B1-Choice-Analyse im Doc von
`Basic.lean`, B2 in `Stream.lean`). Die Saetze dieser Datei **erben** ihn; er kommt aus
dem konsumierten Bestand und nicht aus einer vermeidbaren Route dieser Datei. Das
`choose` in der U1-Rueckrichtung faellt darum nicht ins Gewicht: `canonicalize` steht
schon im Statement. Vier Deklarationen liegen **unter** der Erwartung, und das ist
Befund, kein Fehler — `MarksLt` und `marksLeOne_iff_marksLt_two` sind axiomfrei,
`le_foldr_max` zieht `[propext]`, `mem_of_le_mem` `[propext, Quot.sound]`; keine von
ihnen beruehrt `Finset` oder `canonicalize`. Eine Wache ist Driftschutz, keine
Ertragsmarke.

**Ablage:** setzungsfrei, ohne offene Stelle, konsumiert nur Aggregat-Inhalt — Aggregat.
-/

namespace Reformulation.Kenogram.Unbounded

open Reformulation.Kenogram
open Reformulation.Kenogram.Stream
open Reformulation.Kenogram.Bridge
open Reformulation.Kenogram.Fillability (MarksLeOne canonicalize_rgsFun)

/-! ## Teil 1 — die vier Definitionen

`MarksLt k` ist das Wertseiten-Praedikat, `prefixRGS` der Anschnitt eines Stroms als
endlicher RGS (Wohlgeformtheit ist Konsum von `isRGSStream_take`, die Laengenkomponente
`Stream'.length_take`), `Unbounded` die Marken-Unbeschraenktheit und `idRGSStream` der
benannte Zeuge. Die Datei zaehlt nichts und entscheidet nichts; darum keine
`Decidable`-Instanz. -/

/-- **Wertseiten-Praedikat:** kein Eintrag des RGS erreicht die Marke `k`. Fuer `k = 2`
faellt es mit `Fillability.MarksLeOne` zusammen (`marksLeOne_iff_marksLt_two`). -/
def MarksLt {n : ℕ} (k : ℕ) (r : RGS n) : Prop := ∀ v ∈ r.1, v < k

/-- **Der Anschnitt:** das `N`-Praefix eines kenogrammatischen Stroms als endlicher RGS.
Beide Komponenten sind Konsum — `Stream'.length_take` fuer die Laenge,
`Bridge.isRGSStream_take` fuer die Wohlgeformtheit. -/
def prefixRGS (r : RGSStream) (N : ℕ) : RGS N :=
  ⟨r.1.take N, ⟨Stream'.length_take N r.1, isRGSStream_take r.1 r.2 N⟩⟩

set_option linter.dupNamespace false in
/-- **Unbeschraenktheit:** die Marken des Stroms uebersteigen jede Schranke.

Der volle Name ist `Reformulation.Kenogram.Unbounded.Unbounded`, und der
`dupNamespace`-Linter meldet die Wiederholung zu Recht. Sie ist hier gewollt: Dateiname
und Praedikatname sagen beide dasselbe, und beide sind gesetzt (Dateiname nach der
Namensregel — der Name sagt das Bewiesene —, Praedikatname als der, den die Saetze
tragen). Der Linter wird an dieser einen Stelle stillgestellt und nicht global. -/
def Unbounded (r : RGSStream) : Prop := ∀ k : ℕ, ∃ n : ℕ, k ≤ r.1.get n

/-- **Der benannte Zeuge:** der Identitaetsstrom `n ↦ n`. Wohlgeformt, weil jede Position
das bisherige Maximum um genau eins uebersteigt. Die anonyme Illustration in
`Stream.lean` bleibt stehen; hier steht die konsumierbare Fassung. -/
def idRGSStream : RGSStream :=
  ⟨fun n => n, ⟨rfl, fun n => by
    show n + 1 ≤ (Finset.range (n + 1)).sup (fun i => i) + 1
    have hle : n ≤ (Finset.range (n + 1)).sup (fun i => i) :=
      Finset.le_sup (f := fun i => i) (Finset.mem_range.mpr (Nat.lt_succ_self n))
    omega⟩⟩

/-! ## Teil 2 — zwei Hilfslemmata

Beide arbeiten auf der Listenseite und bringen die Dichtheit aus `Basic` in die Form, die
U1 braucht: `rgs_take_mem` spricht ueber Praefixe, U1 braucht die ganze Liste. -/

/-- Ein Listenglied ist hoechstens das Listen-Maximum. Elementar, per Induktion; Mathlib
fuehrt die `foldr max 0`-Form nicht, und `Basic` rechnet sie nur lokal aus. -/
theorem le_foldr_max {l : List ℕ} {v : ℕ} (h : v ∈ l) : v ≤ l.foldr max 0 := by
  induction l with
  | nil => cases h
  | cons a t ih =>
    simp only [List.foldr_cons]
    rcases List.mem_cons.mp h with rfl | h'
    · exact le_max_left _ _
    · exact le_trans (ih h') (le_max_right _ _)

/-- **Dichtheit auf der ganzen Liste:** kommt eine Marke `v` in einem RGS vor, so kommt
jede kleinere Marke darin vor. `Basic.rgs_take_mem` fuer das volle Praefix, ueber
`List.take_length` zurueckgeholt. -/
theorem mem_of_le_mem {n : ℕ} (r : RGS n) {v w : ℕ} (hv : v ∈ r.1) (hw : w ≤ v) :
    w ∈ r.1 := by
  have hpos : 0 < r.1.length := List.length_pos_of_mem hv
  have hmax : w ≤ ((r.1).take r.1.length).foldr max 0 := by
    rw [List.take_length]; exact le_trans hw (le_foldr_max hv)
  have := rgs_take_mem r.2.2 r.1.length (le_refl _) hpos w hmax
  rwa [List.take_length] at this

/-! ## Teil 3 — U1: die verallgemeinerte Bruecke

*Von den Marken zur Wertfolge:* liegen alle Marken unter `k`, so ist `i ↦ ⟨r.1[i], _⟩`
eine Folge nach `Fin k` mit demselben Gleichheitsmuster wie die Wertfunktion des RGS;
`canonicalize_eq_iff` und `canonicalize_rgsFun` schliessen.

*Von der Wertfolge zu den Marken:* gaebe es eine Marke `v ≥ k`, so kaemen nach der
Dichtheit alle `v+1` Marken `0 … v` vor. Ueber das Muster liefert das `v+1` paarweise
verschiedene Werte von `f` in `Fin k` — und `v + 1 ≤ k` widerspricht `k ≤ v`. Das
Kardinalitaets-Argument (`Fintype.card_le_of_injective`) ist Beweismittel und kein Satz
dieser Datei. -/

/-- **U1 — die Bruecke (der tragende Satz der Wertseite).** Ein RGS hat alle Marken `< k`
genau dann, wenn er die Normalform einer `k`-wertigen Wertfolge ist. Allgemeines `n` und
allgemeines `k`; die Randlagen `k = 0` und `n = 0` sind mitbehauptet (Dateikopf). -/
theorem marksLt_iff_fillable {n k : ℕ} (r : RGS n) :
    MarksLt k r ↔ ∃ f : Fin n → Fin k, canonicalize f = r := by
  constructor
  · intro h
    have hlt : ∀ i : Fin n, rgsFun r i < k := fun i => h _ (List.getElem_mem _)
    refine ⟨fun i => ⟨rgsFun r i, hlt i⟩, ?_⟩
    calc canonicalize (fun i => (⟨rgsFun r i, hlt i⟩ : Fin k))
        = canonicalize (rgsFun r) :=
          (canonicalize_eq_iff _ _).mpr (fun i j =>
            ⟨fun hE => congrArg Fin.val hE, fun hE => Fin.ext hE⟩)
      _ = r := canonicalize_rgsFun r
  · rintro ⟨f, hf⟩ v hv
    by_contra hge
    have hvk : k ≤ v := by omega
    have hker := (canonicalize_eq_iff f (rgsFun r)).mp (by rw [hf, canonicalize_rgsFun])
    have hex : ∀ w : Fin (v + 1), ∃ i : Fin n, rgsFun r i = w.val := by
      intro w
      have hw : w.val ∈ r.1 := mem_of_le_mem r hv (by omega)
      obtain ⟨p, hp, hpv⟩ := List.mem_iff_getElem.mp hw
      exact ⟨⟨p, by rw [← r.2.1]; exact hp⟩, hpv⟩
    choose g hg using hex
    have hinj : Function.Injective (fun w : Fin (v + 1) => f (g w)) := by
      intro a b hab
      have hE := (hker (g a) (g b)).mp hab
      rw [hg a, hg b] at hE
      exact Fin.ext hE
    have hcard := Fintype.card_le_of_injective _ hinj
    simp only [Fintype.card_fin] at hcard
    omega

/-! ## Teil 4 — U2: Unbeschraenktheit schlaegt jede Schranke -/

/-- **U2a — die Praefixform.** Zu jeder Schranke `k` gibt es eine Praefixlaenge, deren
Anschnitt eine Marke `≥ k` traegt. Zeuge ist `N = n + 1` fuer das `n` der
Unbeschraenktheit; der Eintrag an Position `n` liegt im Praefix. -/
theorem unbounded_exceeds (r : RGSStream) (hr : Unbounded r) (k : ℕ) :
    ∃ N : ℕ, ¬ MarksLt k (prefixRGS r N) := by
  obtain ⟨n, hn⟩ := hr k
  refine ⟨n + 1, ?_⟩
  intro hc
  have hmem : r.1.get n ∈ (prefixRGS r (n + 1)).1 := by
    show r.1.get n ∈ r.1.take (n + 1)
    have h := take_val_getElem? r.1 (n + 1) n
    rw [if_pos (Nat.lt_succ_self n)] at h
    exact List.mem_of_getElem? h
  have := hc _ hmem
  omega

/-- **U2b — die zitierbare Form: kein endlicher Wertvorrat.** Zu jedem `k` gibt es eine
Praefixlaenge, ab der das Praefix von **keiner** `k`-wertigen Wertfolge erzeugt wird.
Kontraposition von U1 auf U2a — kein eigener Beweismittelbau. -/
theorem unbounded_not_fillable (r : RGSStream) (hr : Unbounded r) (k : ℕ) :
    ∃ N : ℕ, ¬ ∃ f : Fin N → Fin k, canonicalize f = prefixRGS r N := by
  obtain ⟨N, hN⟩ := unbounded_exceeds r hr k
  exact ⟨N, fun hf => hN ((marksLt_iff_fillable _).mpr hf)⟩

/-! ## Teil 5 — U3: der benannte Zeuge

Die Instanziierung ist drei Zeilen lang und ist der Satz, den der Strang zitiert: **der
Identitaetsstrom wird von jedem endlichen Wertesystem ueberschritten.** Dass ein solcher
Strom im Korpus existiert, ist der Unterschied zwischen einer bedingten und einer
unbedingten Aussage. -/

/-- **U3, erste Haelfte — der Identitaetsstrom ist unbeschraenkt.** An Position `k` steht
der Wert `k`. -/
theorem idRGSStream_unbounded : Unbounded idRGSStream := fun k => ⟨k, le_refl k⟩

/-- **U3, zweite Haelfte — die unbedingte Form.** Der Identitaetsstrom wird von jedem
endlichen Wertesystem ueberschritten: zu jedem `k` gibt es eine Praefixlaenge, deren
Anschnitt von keiner `k`-wertigen Wertfolge erzeugt wird. Reine Instanziierung von U2b am
benannten Zeugen. -/
theorem idRGSStream_not_fillable (k : ℕ) :
    ∃ N : ℕ, ¬ ∃ f : Fin N → Fin k, canonicalize f = prefixRGS idRGSStream N :=
  unbounded_not_fillable idRGSStream idRGSStream_unbounded k

/-! ## Teil 6 — die Praedikat-Seite gegen `Fillability`

Die billige Haelfte des Verhaeltnisses zu Z1: die beiden **syntaktischen** Kriterien
fallen zusammen. Ueber die semantischen Seiten (`Fin 2` gegen `Bool`) sagt der Satz
nichts, und eine Uebersetzung ist nicht geschuldet (Dateikopf). -/

/-- Marke `≤ 1` und Marke `< 2` sind dasselbe Kriterium. Bindeglied zu
`Fillability.marksLeOne_iff_fillable` auf der Praedikat-Seite, nicht auf der
Wertfolgen-Seite. -/
theorem marksLeOne_iff_marksLt_two {n : ℕ} (r : RGS n) : MarksLeOne r ↔ MarksLt 2 r :=
  ⟨fun h v hv => Nat.lt_succ_of_le (h v hv), fun h v hv => Nat.lt_succ_iff.mp (h v hv)⟩

/-! **Statement-Pins.** Voller Wortlaut links, Satz rechts — jede Drift des *Statements*
bricht den Build. Namenlose `example`s, keine Axiom-Wache. -/

-- STATEMENT-PIN
example {n k : ℕ} (r : RGS n) : MarksLt k r ↔ ∃ f : Fin n → Fin k, canonicalize f = r :=
  marksLt_iff_fillable r
-- STATEMENT-PIN
example (r : RGSStream) (hr : Unbounded r) (k : ℕ) :
    ∃ N : ℕ, ¬ ∃ f : Fin N → Fin k, canonicalize f = prefixRGS r N :=
  unbounded_not_fillable r hr k
-- STATEMENT-PIN
example (k : ℕ) :
    ∃ N : ℕ, ¬ ∃ f : Fin N → Fin k, canonicalize f = prefixRGS idRGSStream N :=
  idRGSStream_not_fillable k

/-! ## Teil 7 — die Axiom-Wachen (Ist-gebunden)

Ist-Ausgabe des gruenen Builds (v4.30.0-rc2), pro Deklaration eingefroren
(Datei-Vollstaendigkeits-Regel, einschliesslich der vier Definitionen und beider
Hilfslemmata). Der `Classical.choice`-Anteil ist der geerbte des Kenogram-Zweigs
(Dateikopf, „Zum Axiom-Profil"), kein neuer; die vier Deklarationen, die ihn
unterbieten, beruehren weder `Finset` noch `canonicalize`. -/

/-- info: 'Reformulation.Kenogram.Unbounded.MarksLt' does not depend on any axioms -/
#guard_msgs in #print axioms MarksLt

/-- info: 'Reformulation.Kenogram.Unbounded.prefixRGS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms prefixRGS

/-- info: 'Reformulation.Kenogram.Unbounded.Unbounded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Unbounded

/-- info: 'Reformulation.Kenogram.Unbounded.idRGSStream' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms idRGSStream

/-- info: 'Reformulation.Kenogram.Unbounded.le_foldr_max' depends on axioms: [propext] -/
#guard_msgs in #print axioms le_foldr_max

/-- info: 'Reformulation.Kenogram.Unbounded.mem_of_le_mem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms mem_of_le_mem

/-- info: 'Reformulation.Kenogram.Unbounded.marksLt_iff_fillable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms marksLt_iff_fillable

/-- info: 'Reformulation.Kenogram.Unbounded.unbounded_exceeds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms unbounded_exceeds

/-- info: 'Reformulation.Kenogram.Unbounded.unbounded_not_fillable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms unbounded_not_fillable

/-- info: 'Reformulation.Kenogram.Unbounded.idRGSStream_unbounded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms idRGSStream_unbounded

/-- info: 'Reformulation.Kenogram.Unbounded.idRGSStream_not_fillable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms idRGSStream_not_fillable

/-- info: 'Reformulation.Kenogram.Unbounded.marksLeOne_iff_marksLt_two' does not depend on any axioms -/
#guard_msgs in #print axioms marksLeOne_iff_marksLt_two

end Reformulation.Kenogram.Unbounded
