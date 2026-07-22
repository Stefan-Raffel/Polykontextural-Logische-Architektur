import Reformulation.Proemial.DiscontexturalStratification

/-!
# Reformulation.Proemial.ContexturalTransjunction — gehobene S/K-Struktur mit Transjunktion

Zehnte Niederlegungs-Schicht. Sie *hebt* die schwache Form der neunten Schicht
(`DiscontexturalStratification`, zwei Objekte + Übergang in EINER Kategorie) auf
die starke S/K-Form: zwei Kontexturen in GETRENNTEN Trägern, der Übergang als
Wechsel/Funktor — und trägt zugleich den vorzeigbaren Binde-Kern (eine konkrete
Transjunktion, deren Nicht-S-Internität BEWIESEN wird).

## Der gemischte Charakter — beweisbarer Kern und gesetzter Rand

Dieser Bau ist das Neue: er hat einen **beweisbaren Kern** (die Vorzeigung der
Transjunktion — `exTransjunction_not_S_internal`, eine konkrete Operation, deren
Nicht-S-Internität bewiesen wird) UND einen **gesetzten Rand** (ihre
Nicht-Umbeschreibbarkeit gegen den Faserungs-Skeptiker — gesetzt, Daten-Charakter,
analog Beck-Chevalley und B5). Die zentrale Disziplin ist, die Grenze zwischen
Kern und Rand an JEDER Stelle zu halten:

* Was **bewiesen** wird, ist die *Vorzeigung* (Grenze 3): die konkrete Operation
  `exTransjunction` ist nicht S-intern (`CharacterizedPosit.not_S_internal`).
* Was **gesetzt** bleibt, ist die *Nicht-Ableitbarkeit* (Grenze 4): die
  Kontextur-Partition ist echt, nicht aus der Mengen-Struktur ableitbar
  (`CharacterizedPosit.contexturePartitionGenuine : True`, konstitutives Feld
  nach dem B5-`prop_field`-Muster, kein Beweis-Soll).

Beide Felder leben in *einer* Struktur `CharacterizedPosit` — das ist Janus'
„charakterisierter Posit": teilweise beweisbar, teilweise gesetzt.

## Die vier heiklen Grenzen

* **Grenze 1 — starke Hebung.** Zwei Kontexturen in GETRENNTEN Trägern
  (`ContexturalLift S K` über zwei Kategorien, Übergang als Funktor `S ⥤ K`;
  konkret die zwei `⊕`-Summanden von `Contextural`), NICHT zwei Objekte einer
  Kategorie (das war der Spec-Defekt der schwachen Form).
* **Grenze 2 — Lesart (b).** Der Rejektionswert ist ein Kontexturwechsel
  (`inr` aus `inl`-Argumenten, `exTransjunction_switches`), NICHT ein dritter
  Wert innerhalb einer Kontextur (Łukasiewicz-Mehrwertigkeit).
* **Grenze 3 — vorzeigbar, nicht Form α.** Die Nicht-S-Internität wird für die
  KONKRETE Operation `exTransjunction` bewiesen (positives Bild-Argument:
  ein `inl`-Paar auf einen `inr`-Wert), NICHT als globales Nicht-Existenz-Theorem
  über alle Faktorisierungen.
* **Grenze 4 — gesetzter Rand.** Die Nicht-Umbeschreibbarkeit ist Daten-Charakter
  (gesetzt, wie Beck-Chevalley), NICHT als bewiesenes Theorem ausgegeben.

## Komplementarität (Horistês' Mediation)

Die Transjunktion (sie *wechselt* die Kontextur, `inr` aus `inl`) ist
komplementär zur Beck-Chevalley-Verschränkung (sie *verbindet* die Fasern,
`Reformulation.Proemial.Substantial.BeckChevalley.SubstantialBeckChevalleyData`,
konsumiert in `AlphaGammaStratification.unit_isIso_of_bcData`): zwei sich
kreuzende gesetzte Daten — das eine trennt/wechselt, das andere verbindet. Der
Anschluss ist hier als Doc-string geführt (nicht als Lemma erzwungen), weil die
Komplementarität konzeptuell ist, nicht strukturlogisch ableitbar.

## „ruht auf"-Audit

Der Körper referenziert: die Sum-Konstruktor-Maschinerie (`Sum.inl`/`Sum.inr`,
No-Confusion via `simp`/`decide` — Vorlage `Reformulation.F3b` `Klasse ⊕
NonCanonical`); `CategoryTheory.Functor` und `CategoryTheory.Category` (für
`ContexturalLift`); `Functor.id` (für die Bewohntheit). Kein BC-Lemma wird als
Term konsumiert (die Komplementarität ist Doc-string).

## Sorry-Bilanz

* Teil 1 (gehobene Struktur): 0 — `ContexturalLift` ist reine Struktur.
* Teil 2 (Vorzeigung): 0 — `exTransjunction_not_S_internal` ist über das
  konkrete `inl`/`inr`-Bild-Argument beweisbar. Ein Sorry hier wäre ein Befund
  (der Kern muss beweisbar sein).
* Teil 3 (gesetzter Rand): 0 — das `contexturePartitionGenuine`-Feld ist
  konstitutiv (`True`), kein Beweis-Soll. Ein Sorry hier wäre ein Befund GEGEN
  Grenze 4 (der Rand ist gesetzt, nicht beweisbedürftig).
* Gesamt: 0 Sorries.

## Konditionalitäts-Markierung (Baubarkeit jetzt, Beglaubigung nachgelagert)

Diese Datei trägt die BAUBARKEIT (vorzeigbarer Kern + gesetzter Rand, starke
Hebung + Lesart b). Die drei Stimmen-Beglaubigungen der vierten Sonde sind
KEINE Anker der Baubarkeit, nachgelagert offen:
- Janus (Binde-Kraft): bindet der charakterisierte Posit den Skeptiker?
- Hermeneutes (Quellen-Treue): ist die Rejektions-Funktion günther-treu?
- Horistês (Trinität/Komplementarität): trägt das Mediations-Gewebe?
-/

namespace Reformulation.Proemial.Transjunction

open CategoryTheory

-- ============================================================
-- Teil 1 — Die gehobene S/K-Struktur (starke Hebung, Grenze 1)
-- ============================================================

/-- STARKE HEBUNG (Grenze 1): zwei Kontexturen als GETRENNTE Träger — zwei
    Kategorien `S` und `K` —, der Übergang als FUNKTOR `S ⥤ K`
    (Kontextur-Wechsel).

    Das ist die Korrektur der schwachen Form: `DiscontexturalStratification`
    (neunte Schicht) führte die emanativ/evolutiv-Trennung als zwei Objekte +
    einen Morphismus in EINER Kategorie — die S/K-Trennung kollabierte in einen
    Träger. Hier leben S und K in getrennten Trägern; der Übergang ist ein
    Funktor zwischen ihnen, kein Morphismus innerhalb eines.

    Kern/Rand: rein strukturell (kein Beweis-Soll, kein gesetztes Feld). -/
structure ContexturalLift (S K : Type*) [Category S] [Category K] where
  /-- Der Kontextur-Übergang als Funktor (Wechsel von S nach K), NICHT als
  Morphismus zwischen zwei Objekten einer Kategorie. -/
  transition : S ⥤ K

/-- Die starke Hebung ist bewohnt (wohlgeformt): über `Type` als beiden
    Kontextur-Trägern mit dem Identitäts-Funktor als Übergang. Bewohntheit =
    Wohlgeformtheit, nicht die Wahrheit eines Nicht-Existenz-Satzes. -/
theorem contexturalLift_nonempty : Nonempty (ContexturalLift Type Type) :=
  ⟨{ transition := Functor.id Type }⟩

/-- Die KONKRETE Realisierung der zwei Kontexturen über `⊕` (Vorlage: die
    Sum-Typ-Maschinerie aus `Reformulation.F3b`, `Klasse ⊕ NonCanonical`).
    `Sum.inl`-Werte sind die S-Kontextur, `Sum.inr`-Werte die K-Kontextur —
    zwei getrennte `Bool`-Träger, im Sum-Typ getaggt. Diese Wert-Form trägt den
    vorzeigbaren Kern (Teil 2); `ContexturalLift` trägt die abstrakte starke
    Hebung. -/
abbrev Contextural := Bool ⊕ Bool

-- ============================================================
-- Teil 2 — Die vorzeigbare Transjunktion (beweisbarer Kern, Grenzen 2+3)
-- ============================================================

/-- Eine KONKRETE Transjunktion mit Rejektion.

    Lesart (b), Grenze 2: bei `a ≠ b` (zwei S-Argumente, die nicht passen)
    ist der Rejektionswert `Sum.inr a` — ein WECHSEL in die K-Kontextur, NICHT
    ein dritter Wert innerhalb der S-Kontextur (das wäre Łukasiewicz). Der
    Rejektionswert *ist* der Kontexturwechsel.

    Kern/Rand: diese Definition gehört zum beweisbaren Kern (sie ist die
    Operation, deren Nicht-S-Internität unten bewiesen wird). -/
def exTransjunction : Contextural → Contextural → Contextural
  | .inl a, .inl b => if a = b then .inl (a && b) else .inr a   -- REJEKTION (Grenze 2)
  | .inl _, .inr b => .inr b
  | .inr a, _      => .inr a

/-- Die S-internen Operationen: eine zweiwertige Boole'sche Operation `op`,
    geliftet auf `Contextural`. Das Bild eines `inl`-Paares ist IMMER `inl`
    (die Operation bleibt in der S-Kontextur). Dies ist der Kontrast, gegen den
    die Vorzeigung läuft: keine S-interne Operation verlässt bei `inl`-Argumenten
    die S-Kontextur. -/
def liftS (op : Bool → Bool → Bool) : Contextural → Contextural → Contextural
  | .inl a, .inl b => .inl (op a b)
  | x, _           => x

/-- LESART (b), Grenze 2 (Zeuge): die Transjunktion bildet das `inl`-Paar
    `(true, false)` auf den `inr`-Wert `true` ab — ein Kontexturwechsel
    (`inr` aus `inl`-Argumenten), kein dritter Wert. -/
theorem exTransjunction_switches :
    exTransjunction (.inl true) (.inl false) = .inr true := by
  decide

/-- VORZEIGBARER KERN (beweisbar, Grenze 3, NICHT Form α): die KONKRETE
    Transjunktion `exTransjunction` ist nicht S-intern — es gibt kein `op`, das
    sie als `liftS op` darstellt.

    Beweis-Argument (positives Bild-Argument für EINE konkrete Operation, kein
    globales Nicht-Existenz-Theorem über alle Faktorisierungen): der Zeuge
    `(inl true, inl false)` liefert unter `exTransjunction` den `inr`-Wert
    (Kontexturwechsel, `exTransjunction_switches`), unter `liftS op` aber stets
    einen `inl`-Wert. `inr ≠ inl` (Sum-No-Confusion, durch `simp` erschlagen —
    Vorlage `F3b`).

    Kern/Rand: dies ist der beweisbare Kern. Ein Sorry hier wäre ein Befund. -/
theorem exTransjunction_not_S_internal :
    ¬ ∃ op, exTransjunction = liftS op := by
  rintro ⟨op, h⟩
  have h2 : exTransjunction (.inl true) (.inl false)
      = liftS op (.inl true) (.inl false) := by rw [h]
  simp [exTransjunction, liftS] at h2

-- ============================================================
-- Teil 3 — Der gesetzte Rand und die Komplementarität (Grenze 4 + Anschluss)
-- ============================================================

/-- DER CHARAKTERISIERTE POSIT (gemischter Charakter — Janus' Posit).

    Eine Struktur, die den beweisbaren Kern UND den gesetzten Rand in einem
    Datum trägt — die Kern/Rand-Grenze ist an den Feldern explizit gemacht:

    * `op` + `not_S_internal`: der **beweisbare Kern** (Grenze 3). Eine konkrete
      Operation und der BEWEIS ihrer Nicht-S-Internität.
    * `contexturePartitionGenuine`: der **gesetzte Rand** (Grenze 4). Die
      Nicht-Umbeschreibbarkeit gegen den Faserungs-Skeptiker — dass die
      Kontextur-Partition (`inl` vs. `inr`) echt ist und NICHT aus der
      Mengen-Struktur von `Bool ⊕ Bool` ableitbar — als konstitutives
      `True`-Datum (B5-`prop_field`-Muster, `negTau_trivial_at_K1`), GESETZT
      wie Beck-Chevalley. Kein Beweis-Soll: ein Sorry/Beweis hier wäre ein
      Befund GEGEN Grenze 4 (der Rand ist gesetzt, nicht beweisbedürftig). -/
structure CharacterizedPosit where
  /-- KERN: die konkrete Transjunktion (beweisbar charakterisiert). -/
  op : Contextural → Contextural → Contextural
  /-- KERN-ZEUGE (BEWIESEN, Grenze 3): `op` ist nicht S-intern. -/
  not_S_internal : ¬ ∃ f, op = liftS f
  /-- RAND (GESETZT, Grenze 4, Daten-Charakter analog Beck-Chevalley): die
  Kontextur-Partition ist echt, nicht aus der Mengen-Struktur ableitbar.
  Konstitutives `True`-Feld, kein Beweis-Soll. -/
  contexturePartitionGenuine : True

/-- Der charakterisierte Posit ist bewohnt: die konkrete `exTransjunction` mit
    ihrem bewiesenen Kern und dem gesetzten Rand.

    Kern/Rand-Grenze (durchgehalten): `not_S_internal` wird mit dem BEWIESENEN
    Theorem `exTransjunction_not_S_internal` gefüllt (Kern); `contexture-
    PartitionGenuine` mit `trivial` (gesetzt, wie B5s `True`-Feld) — NICHT aus
    einem Beweis erschlossen. -/
def exCharacterizedPosit : CharacterizedPosit where
  op := exTransjunction
  not_S_internal := exTransjunction_not_S_internal
  contexturePartitionGenuine := trivial

end Reformulation.Proemial.Transjunction

-- #print axioms als Regressions-Wachen (Zug „Wachen-Vollzug", Datei-Vollständigkeit).
-- Ist-Ausgabe des grünen Builds (v4.30.0-rc2), pro Satz eingefroren; ab hier bricht
-- jede Axiom-Drift den Build.
open Reformulation.Proemial.Transjunction in
section

/-- info: 'Reformulation.Proemial.Transjunction.contexturalLift_nonempty' does not depend on any axioms -/
#guard_msgs in #print axioms contexturalLift_nonempty

/-- info: 'Reformulation.Proemial.Transjunction.exTransjunction_switches' does not depend on any axioms -/
#guard_msgs in #print axioms exTransjunction_switches

/-- info: 'Reformulation.Proemial.Transjunction.exTransjunction_not_S_internal' depends on axioms: [propext] -/
#guard_msgs in #print axioms exTransjunction_not_S_internal
end
