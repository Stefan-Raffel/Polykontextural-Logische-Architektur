import Reformulation.Proemial.InteractiveTransjunction
import Reformulation.Proemial.TransjunctionCloneBound

/-!
# Reformulation.Diagnostics.HeteroreferenzProbe — Machbarkeits-Sonde SO2 (kein Satz, keine Schicht)

**Reine Sonde — kein Eingriff, NICHT im Aggregat** (kein Import in `Proemial.lean`).
Prüft am Term, ob der Bestand einen benennbaren **Heteroreferenz-Anschluss** trägt:
eine definierte Eigenschaft `HeteroReferent` von Operationen, die der Interaktions-Zeuge
der dreizehnten Schicht beweisbar *hat* und intra-kontexturale Operationen beweisbar
*nicht* haben. Wird nur behalten, wenn sorry-frei.

Ausführen: `lake env lean Reformulation/Diagnostics/HeteroreferenzProbe.lean`

## Die Sache

Günthers Selbstreferenz/Heteroreferenz: ein System bezieht sich auf sich — oder auf sein
*Anderes*. Der operationale Befund (Plan Rev2, quellenseitig strukturparallel): die
Transjunktion *verwirft* die Wertungs-Kontextur — sie wertet nicht *in* ihr, sondern
verweist *von ihr weg*. Diese Sonde prüft, ob dieses Fundament einen benennbaren
Term-Anschluss trägt.

## S1 — die Definitions-Fassung (zwei Kandidaten)

**Fassung (a) — Transjunktions-Fassung (Empfehlung, sie sitzt am benannten Fundament).**
Über dem Substrat der dreizehnten Schicht (`InteractiveTransjunction`): eine Operation ist
`HeteroReferent`, wenn ihr Rejektions-Ziel an KEINER punktweisen Ein-Argument-Wahl
festmachbar ist — formal: sie liegt **außerhalb der punktweise gemischten unären Familie**
`InExtendedUnaryMixed` (dem maximalen unären Rahmen, der `InExtendedUnary` UND
`InExtendedUnarySnd` subsumiert). Das ist „verweist von der Kontextur weg" am Term: das
Rejektions-Ziel ist an keiner einzelnen Argument-Koordinate (Quelle *oder* Ziel-Stelle)
ablesbar, sondern allein an der *Interaktion* beider — dem Anderen der Wertung.

Die Definition ist **keine Umformulierung eines einzelnen Satzes**: sie trägt drei
unabhängige Instanz-Urteile (§S2) — ein Ja (`exTransjectI`), zwei Nein (Projektion und die
unäre Überschreitung `exTransjectB`). Insbesondere trennt sie die *rejizierende* Operation
`exTransjectB` (die die Kontextur verlässt, aber quell-referentiell) von der heteroreferenten
`exTransjectI`: Heteroreferenz ist echt feiner als „rejiziert überhaupt"
(`rejection_not_sufficient`). Damit ist sie ein Klassifikator mit Unterscheidungskraft, keine
Benennung im Definitions-Gewand.

**Fassung (b) — Denotations-Fassung (nur der Vollständigkeit halber, die SCHWÄCHERE Lesart).**
Über `L.Term`/`realize` (Sprache der achtzehnten Schicht): ein Term hängt heteroreferent von
der *fremden* Belegungs-Stelle ab. Sie trägt (§S2b), ist aber flach und steht unter einer
doppelten Wache (siehe Modul-Ende und §S5). Sie wird hier gezeigt, um das **Fassungs-Gefälle**
term-konkret zu machen, NICHT als tragende Fassung.

## S3 — Abgrenzungen (verbindlich)

* **Selbstreferenz-Seite unberührt.** Der Lawvere- bzw. Diagonal-Trakt (`LawvereVorSonde`,
  `ReflexionsrestProbe`) wird nicht angetastet — eigene Sprache, eigene Sonde.
* **Stelle-8-Lesart bleibt Deutung.** „Erschöpfung als Rückgabe an das Andere" (AP5-Stelle-8)
  ist Reifungs-Anlass, nicht Beweis-Gegenstand; kein Satz nimmt sie auf.
* **Kein Einlösungs-Anspruch.** Kein Satz und kein Doc-Wort behauptet, mit `HeteroReferent`
  sei „die Heteroreferenz" Günthers eingelöst — sondiert wird ein *Anschluss*, die Zuordnung
  bleibt strukturanalytisch. Die Bindung an Günthers *Designation* verbietet die achtzehnte/
  neunzehnte Schicht ausdrücklich: **Designation ≠ Denotation** (Wache unten).

## S4 — Ort und Hygiene

Datei außerhalb des Aggregats; kein bestehendes Modul angetastet. `#print axioms` je
Kandidat-Satz am Datei-Ende. Behaltbar nur sorry-frei (0 Sorries, siehe Ende).
-/

namespace Reformulation.Diagnostics.HeteroreferenzProbe

open Reformulation.Proemial.SubstantialTransjunction
open Reformulation.Proemial.InteractiveTransjunction

-- ============================================================
-- Fassung (a) — Transjunktions-Fassung (die tragende, am Fundament)
-- ============================================================

/-- **DIE HETEROREFERENZ-EIGENSCHAFT (Fassung a).** Eine Operation `t` ist heteroreferent,
    wenn ihr Rejektions-Ziel an KEINER punktweisen Ein-Argument-Wahl festmachbar ist — sie
    liegt außerhalb der punktweise gemischten unären Familie `InExtendedUnaryMixed` (dem
    maximalen unären Rahmen der dreizehnten Schicht). „Verweist von der Kontextur weg": das
    Ziel hängt an der Interaktion beider Argumente, nicht an einer einzelnen Koordinate.

    Generisch über beliebigen Trägern `S, K` gefasst; die Urteile unten instanziieren an
    `S = ℕ`, `K = ℕ → Bool` (substantielles `K` der zwölften/dreizehnten Schicht). -/
def HeteroReferent {S K : Type*} (t : S → S → (S ⊕ K)) : Prop :=
  ¬ InExtendedUnaryMixed t

/-- Hilfssatz: die Erst-Argument-Familie ist in der gemischten Familie enthalten
    (`sw ≡ true` wählt stets `g a`). Damit zieht jede unäre Fassung eine Nicht-Heteroreferenz
    nach sich. -/
theorem mixed_of_fst {S K : Type*} (t : S → S → (S ⊕ K))
    (h : InExtendedUnary t) : InExtendedUnaryMixed t := by
  obtain ⟨op, sel, g, hg⟩ := h
  exact ⟨op, sel, g, g, fun _ _ => true, fun a b => hg a b⟩

-- ── S2: Instanz und Gegen-Instanzen (ein Ja, zwei Nein) ─────────────────────

/-- **JA-URTEIL (Instanz):** der Interaktions-Zeuge `exTransjectI` der dreizehnten Schicht
    IST heteroreferent — er erfüllt `HeteroReferent` per vorhandenem Satz
    (`exTransjectI_outside_mixed`). Sein Rejektions-Ziel `φ_{a+b}` ist an keiner
    Ein-Argument-Wahl festmachbar. -/
theorem exTransjectI_heteroreferent : HeteroReferent exTransjectI :=
  exTransjectI_outside_mixed

/-- Eine reine intra-kontexturale Operation: die Projektion aufs erste Argument. Sie
    *verlässt die Kontextur nie* (Bild stets `Sum.inl`), ist also selbst-referentiell im
    stärksten Sinn — der klarste Nicht-Heteroreferent. -/
def proj : ℕ → ℕ → (ℕ ⊕ (ℕ → Bool)) := fun a _ => Sum.inl a

/-- Die Projektion liegt in der gemischten Familie (`sel ≡ true`, der `inr`-Zweig entfällt). -/
theorem proj_in_mixed : InExtendedUnaryMixed proj :=
  ⟨fun a _ => a, fun _ _ => true, fun _ _ => false, fun _ _ => false, fun _ _ => true,
   fun _ _ => rfl⟩

/-- **NEIN-URTEIL 1 (Gegen-Instanz):** die Projektion ist NICHT heteroreferent — ein
    unabhängiges Urteil (keine Anwendung von `exTransjectI_outside_mixed`), das die
    Definition zum Klassifikator mit Ja/Nein-Instanzen macht. -/
theorem proj_not_heteroreferent : ¬ HeteroReferent proj := fun h => h proj_in_mixed

/-- **NEIN-URTEIL 2 (die scharfe Gegen-Instanz):** die unäre Überschreitung `exTransjectB g`
    der zwölften Schicht — sie REJIZIERT (verlässt die Kontextur zu `Sum.inr`), aber ihr Ziel
    hängt allein am Quell-Argument (`g a`). Sie ist quell-referentiell, NICHT heteroreferent.
    (Via `exTransjectB_inside` + `mixed_of_fst`.) -/
theorem exTransjectB_not_heteroreferent (g : ℕ → (ℕ → Bool)) :
    ¬ HeteroReferent (exTransjectB g) :=
  fun h => h (mixed_of_fst _ (exTransjectB_inside g))

/-- **DER UNTERSCHEIDUNGS-BELEG (gegen „Benennung im Definitions-Gewand"):** `HeteroReferent`
    trennt zwei *rejizierende* Operationen — `exTransjectB g` rejiziert (`= Sum.inr (g 0)` bei
    `(0,1)`) und ist doch NICHT heteroreferent. Heteroreferenz ist damit echt feiner als
    „rejiziert überhaupt": nicht das Verlassen der Kontextur bindet, sondern die
    Nicht-Festmachbarkeit des Ziels an einer Argument-Koordinate. -/
theorem rejection_not_sufficient (g : ℕ → (ℕ → Bool)) :
    exTransjectB g 0 1 = Sum.inr (g 0) ∧ ¬ HeteroReferent (exTransjectB g) :=
  ⟨rfl, exTransjectB_not_heteroreferent g⟩

/-- **DAS DISKRIMINATIONS-URTEIL (Zusammenfassung von §S2):** die Definition trägt zugleich
    ein Ja (`exTransjectI`) und ein Nein (`proj`) — der geforderte Anschluss-Beleg. -/
theorem heteroreferent_discriminates :
    HeteroReferent exTransjectI ∧ ¬ HeteroReferent proj :=
  ⟨exTransjectI_heteroreferent, proj_not_heteroreferent⟩

-- ============================================================
-- Fassung (b) — Denotations-Fassung (SCHWÄCHER, nur Fassungs-Gefälle)
-- ============================================================

section Denotation

open FirstOrder Language
open Reformulation.Proemial.TransjunctionCloneBound

/-- **Fassung (b), die SCHWÄCHERE Lesart.** Ein Term hängt heteroreferent (bzgl. der eigenen
    Stelle 0) von der *fremden* Belegungs-Stelle ab: es gibt zwei Belegungen, die an der
    eigenen Stelle 0 übereinstimmen und dennoch verschiedene Denotationen liefern — die
    Differenz kann also nur von der fremden Stelle 1 kommen.

    WACHE (i) — **Designation ≠ Denotation** (neunzehnte Schicht): dies ist `realize`-Semantik,
    NICHT Günthers Designation (Einwertigkeit/Seins-These). Kein gemeinsamer Gehalt; die
    Benennung „heteroreferent" ist hier rein strukturanalytisch.
    WACHE (ii) — **Fassungs-Gefälle**: Abhängigkeits-Heteroreferenz ist SCHWÄCHER als die
    Kontextur-Verwerfung der Fassung (a). Sie misst Argument-Abhängigkeit, nicht das
    Verweisen-weg-von-der-Wertungskontextur. Darum ist (a) die Empfehlung. -/
def DependsOnForeign (u : L.Term (Fin 2)) : Prop :=
  ∃ v v' : Fin 2 → Fin 3, v 0 = v' 0 ∧ u.realize v ≠ u.realize v'

/-- JA-URTEIL (b): `var 1` (die *fremde* Projektion) hängt von der fremden Stelle ab. -/
theorem var1_depends_foreign : DependsOnForeign (Term.var 1) :=
  ⟨![0, 0], ![0, 1], rfl, by simp [Term.realize]⟩

/-- NEIN-URTEIL (b): `var 0` (die *eigene* Projektion) hängt NICHT von der fremden Stelle ab. -/
theorem var0_not_depends_foreign : ¬ DependsOnForeign (Term.var 0) := by
  rintro ⟨v, v', hv0, hne⟩
  exact hne (by simp [Term.realize, hv0])

end Denotation

-- ============================================================
-- Wachen — Axiom-Profile
-- ============================================================

/-! **Wachen (Zug B).** Ist-Ausgabe des grünen Builds (v4.30.0-rc2), pro Satz
eingefroren. Sie ersetzen die sieben vormals nackten `#print axioms`-Aufrufe: ein
gedrucktes Profil sichert nichts, es druckt bei einer Änderung das neue und der Bau
bleibt grün.

`proj_not_heteroreferent` ist **axiomfrei** und trägt darum den anderen der beiden
Ausgabe-Wortlaute (`CLAUDE.md` §8 Fallstrick 15); eingefroren ist das gemessene
Axiomfrei-Sein, nicht ein leeres Profil.

Zwei Sätze dieser Datei bleiben nach der Vorgabe ungewacht — `mixed_of_fst` und
`proj_in_mixed` tragen weder Aufruf noch fremdes Zitat, der Bestand setzt dort keine
Marke. -/

-- Fassung (a):

/-- info: 'Reformulation.Diagnostics.HeteroreferenzProbe.exTransjectI_heteroreferent' depends on axioms: [propext] -/
#guard_msgs in #print axioms exTransjectI_heteroreferent

/-- info: 'Reformulation.Diagnostics.HeteroreferenzProbe.proj_not_heteroreferent' does not depend on any axioms -/
#guard_msgs in #print axioms proj_not_heteroreferent

/-- info: 'Reformulation.Diagnostics.HeteroreferenzProbe.exTransjectB_not_heteroreferent' depends on axioms: [propext] -/
#guard_msgs in #print axioms exTransjectB_not_heteroreferent

/-- info: 'Reformulation.Diagnostics.HeteroreferenzProbe.rejection_not_sufficient' depends on axioms: [propext] -/
#guard_msgs in #print axioms rejection_not_sufficient

/-- info: 'Reformulation.Diagnostics.HeteroreferenzProbe.heteroreferent_discriminates' depends on axioms: [propext] -/
#guard_msgs in #print axioms heteroreferent_discriminates

-- Fassung (b):

/-- info: 'Reformulation.Diagnostics.HeteroreferenzProbe.var1_depends_foreign' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms var1_depends_foreign

/-- info: 'Reformulation.Diagnostics.HeteroreferenzProbe.var0_not_depends_foreign' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms var0_not_depends_foreign

end Reformulation.Diagnostics.HeteroreferenzProbe
