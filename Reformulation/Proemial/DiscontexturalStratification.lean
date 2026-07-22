import Reformulation.Proemial.AlphaGammaStratification

/-!
# Reformulation.Proemial.DiscontexturalStratification — Diskontexturalitäts-Setzung (Form β)

Neunte Niederlegungs-Schicht (über F-1, F-3, F-3.4/5, F-3.6, F-3.6.a,
F-3.6.a.1+b, F-3.6.a.2+3, F-3.6.a.5/6). Diese Datei *setzt* die
Diskontexturalität — sie *beweist* sie nicht. Das ist das Ergebnis der drei
Sonden: die Diskontexturalität ist intra-kontextural nicht beweisbar (ein
intra-kontexturaler Beweis der Nicht-Intra-Kontexturalität wäre ein
Selbstwiderspruch); sie gehört GESETZT, wie die Anfangs-Singularität B5 und
die Beck-Chevalley-Verträglichkeit.

Drei Teile:

1. **Setzungs-Struktur** `DiscontexturalStratification`: die emanativ/evolutiv-
   Trennung als gesetztes Strukturmerkmal auf der Kontextur-Achse 𝒞. Das
   Feld `discontextural` ist ein KONSTITUTIVES Setzungs-Feld nach dem
   B5-`prop_field`-Muster (`Reformulation.F3d.ModalTwoCategoryWithNegations.
   negTau_trivial_at_K1 : True`), kein Beweis-Soll.
2. **Bewohntheit** `discontexturalStratification_nonempty`: die Setzung ist
   wohlgeformt (eine konkrete Instanz). Bewohntheit = Wohlgeformtheit, NICHT
   die Wahrheit eines Nicht-Existenz-Satzes.
3. **Anschluss** `ofBewohnteSchicht` + `transition_isIso_ofBewohnteSchicht`:
   Hebung der emanativ/evolutiv-Trennung von der Adjunktions-Formulierung
   (𝒪-seitig, `AlphaGammaStratification`) auf die Träger-Kategorie — die
   material-adressierte Hebung der zweiten Sonde. Reichweiten-Vorbehalt: die
   Hebung landet konstruktiv auf der Quell-Kategorie `S` (per
   `AlphaGammaSubstantial`-Doc die emanative Schicht), nicht nachweislich auf
   einer eigenständigen Kontextur-Achse 𝒞 — siehe Anschluss-Doc unten.

## Die kritische Grenze — Setzung, nicht Beweis

Die größte Gefahr der Niederlegung wäre, versehentlich ein BEWEISBARES
Nicht-Existenz-Statement zu bauen (`¬ ∃ o-path, …` — „es gibt keine
𝒪-Faktorisierung"). Das wäre Form (α), gegen die Spec, intra-kontextural
nicht baubar und ein Selbstwiderspruch. Das `discontextural`-Feld ist
stattdessen KONSTITUTIV: die Instanz *hat* es (wie B5), es folgt nicht aus
der Instanz. Kein `¬∃`-Faktorisierungs-Statement tritt in dieser Datei auf.

## Klasse-B-Befunde

**B-1 (positiv) — B5-`prop_field`-Muster trägt direkt:** B5 wird in der
Drei-Negationen-Form (`F3d/Negations.lean`) als `negTau_trivial_at_K1 : True`
geführt — ein konstitutives `True`-Setzungs-Feld, kein Beweis-Soll. Die
Wahl `discontextural : True` (statt eines freien `discontextural : Prop`-
Daten-Felds) trifft dieses Muster exakt: die Instanz trägt es trivial
(`trivial`), es ist gesetzt, nicht beweisbedürftig.

**B-2 — die KONSUMIERTE Anschluss-Stelle ist `unit_isIso_of_bcData`**
(aus `AlphaGammaStratification`), nicht das unkonditionale Schicht-Selektions-
Theorem `bcData_nonempty_iff_unconditional` (das liegt in
`…Substantial.Rounding` und wird hier nur als konzeptueller Hintergrund
GENANNT, nicht aufgerufen): BC-Instanz ⇒ unit punktweise iso ⇒ der gehobene
Übergang ist reversibel. Folge: `AlphaGammaRounding` wird NICHT importiert
(der Import wäre ungenutzt); einziger Import ist `AlphaGammaStratification`.

**B-3 — `private abbrev BCData` Konvention:** wie in `…Stratification`
referenziert (`SubstantialBeckChevalleyData`); das dortige `BCData` ist
private und nicht über den Namespace sichtbar.

## Sorry-Bilanz

- Teil 1 (Setzungs-Struktur): 0 Sorries — das `discontextural`-Feld ist
  konstitutiv (`True`), kein Beweis-Soll.
- Teil 2 (Bewohntheit): 0 Sorries.
- Teil 3 (Anschluss): 0 Sorries.
- Gesamt: 0 Sorries.

Ein Sorry im `discontextural`-Feld selbst wäre ein Befund GEGEN die Form
(ein versehentliches Form-α-Kippen) — es tritt nicht auf.

## Konditionalitäts-Markierung (Baubarkeit jetzt, Beglaubigung nachgelagert)

Diese Datei trägt die BAUBARKEIT der Setzung. Ihre BEGLAUBIGUNG ruht auf
drei offenen Stimmen-Fragen, die hier NICHT präjudiziert werden:
- Hermeneutes (günther-Treue): ist Günthers Diskontexturalität gesetzt oder
  erschlossen?
- Horistês (Nicht-Inflation): drittes gesetztes Grund-Datum als Vertiefung
  oder Inflation?
- Janus (Binde-Kraft): bindet eine gesetzte Diskontexturalität den Skeptiker?
Keine dieser drei wird hier behauptet — die Setzung ist ehrlich, ihre
Geltung als Zeuge ist nachgelagert (siehe Final-Notiz).
-/

namespace Reformulation.Proemial.Discontextural

open CategoryTheory CategoryTheory.Limits
open Reformulation.Proemial.Substantial
open Reformulation.Proemial.Substantial.Stratification

-- Die F-3.6-BC-Struktur, qualifiziert referenziert wie in
-- AlphaGammaStratification.lean (das dortige BCData ist private). B-3-Befund.
private abbrev BCData := Reformulation.Proemial.Substantial.BeckChevalley.SubstantialBeckChevalleyData

-- ============================================================
-- Teil 1 — Die Setzungs-Struktur
-- ============================================================

/-- DISKONTEXTURALE SCHICHT-TRENNUNG (Strukturmerkmal, GESETZT analog B5,
    nicht bewiesen).

    Die emanativ/evolutiv-Unterscheidung lebt auf der Kontextur-Achse 𝒞:
    die emanativ-reversible und die evolutiv-irreversible Schicht sind zwei
    Kontexturen (zwei 𝒞-Objekte), ihr Übergang ist ein 𝒞-Morphismus
    (Kontextur-Wechsel), nicht ein 𝒪-Morphismus (Schema-Wechsel in fester
    Kontextur).

    Dass dieser Übergang nicht intra-kontextural (durch 𝒪) einholbar ist,
    ist GESETZT — wie die Anfangs-Singularität B5 und die Beck-Chevalley-
    Verträglichkeit —, nicht aus tieferen Daten bewiesen: Diskontexturalität
    ist intra-kontextural NICHT beweisbar (ein intra-kontexturaler Beweis der
    Nicht-Intra-Kontexturalität wäre ein Selbstwiderspruch), sondern
    Grundverfassung (Günther, *Life as Polycontexturality*).

    Das Feld `discontextural` ist die Setzungs-Markierung: ein konstitutives
    `True`-Datum nach dem B5-`prop_field`-Muster
    (`F3d.ModalTwoCategoryWithNegations.negTau_trivial_at_K1 : True`). Die
    Instanz *hat* es (trägt es trivial), es folgt NICHT aus der Instanz —
    es ist kein beweisbares Nicht-Existenz-Statement (`¬∃`, das wäre Form α).

    Beglaubigung (günther-Treue / Nicht-Inflation / Binde-Kraft) ist
    nachgelagerte Stimmen-Frage; diese Struktur trägt nur die Baubarkeit. -/
structure DiscontexturalStratification (𝒞 : Type*) [Category 𝒞] where
  /-- Die emanativ-reversible Schicht als Kontextur (𝒞-Objekt). -/
  emanative : 𝒞
  /-- Die evolutiv-irreversible Schicht als Kontextur (𝒞-Objekt). -/
  evolutive : 𝒞
  /-- Der Kontextur-Übergang als 𝒞-Morphismus (Kontextur-Wechsel),
  nicht als 𝒪-Morphismus (Schema-Wechsel). -/
  transition : emanative ⟶ evolutive
  /-- SETZUNGS-MARKIERUNG (GESETZT analog B5, nicht bewiesen): die
  Diskontexturalität als konstitutives `True`-Datum, getragen wie B5s
  `negTau_trivial_at_K1` (`prop_field`-Muster). Diskontexturalität ist
  intra-kontextural nicht beweisbar (Selbstwiderspruch); das Feld ist
  konstitutiv, kein Beweis-Soll, KEIN `¬∃`-Faktorisierungs-Statement. -/
  discontextural : True

-- ============================================================
-- Teil 2 — Bewohntheit (die Setzung ist wohlgeformt)
-- ============================================================

/-- Die Diskontexturalitäts-Setzung ist bewohnt: über `Type` (die einfachste
    tragfähige Zeugen-Kontextur) gibt es eine wohlgeformte Instanz mit zwei
    Kontexturen (hier `PUnit`) und einem Übergang (`𝟙 PUnit`).

    Bewohntheit zeigt die WOHLGEFORMTHEIT der Setzung, NICHT die Wahrheit
    eines Nicht-Existenz-Satzes: das `discontextural`-Feld wird hier mit
    `trivial` getragen (wie B5s `True`-Feld), nicht aus einem `¬∃` erschlossen.
    Beglaubigung bleibt nachgelagert. -/
theorem discontexturalStratification_nonempty :
    Nonempty (DiscontexturalStratification Type) :=
  ⟨{ emanative := PUnit
     evolutive := PUnit
     transition := 𝟙 PUnit
     discontextural := trivial }⟩

-- ============================================================
-- Teil 3 — Anschluss an das Schicht-Selektions-Theorem
-- ============================================================

/-- ANSCHLUSS (Hebung auf die Träger-Kategorie): aus einer
    `ProemialAdjunctionSubstantial S K` wird eine
    `DiscontexturalStratification S` gehoben:

    * `emanative := s` und `evolutive := (L ⋙ R).obj s` sind zwei Objekte;
    * `transition := unit.app s` ist der Übergang.

    Konzeptueller Hintergrund (NICHT als Term konsumiert): das
    Schicht-Selektions-Theorem `bcData_nonempty_iff_unconditional`
    (`…Rounding`) charakterisiert die emanativ-reversible Schicht; die
    Reversibilität des Übergangs wird unten an einer BC-Instanz tatsächlich
    eingelöst (`transition_isIso_ofBewohnteSchicht`).

    REICHWEITEN-VORBEHALT (ehrlich benannt, gegen Bewertungs-Frage 2): die
    Hebung landet konstruktiv auf `S`. Nach `AlphaGammaSubstantial` ist `S`
    die EMANATIVE Schicht und `K` die evolutive; `(L ⋙ R).obj s` ist der
    Monaden-Rücklauf in `S`, KEIN Objekt der evolutiven Kategorie `K`. Beide
    Objekte und der Übergang leben in `S`. Die Identifikation von `S` mit
    einer eigenständigen Kontextur-Achse 𝒞 (deren Objekte ganze Kontexturen
    sind) ist damit NICHT erbracht — sie ist die Lesart, die der Anschluss
    voraussetzt, nicht beweist. Die starke Form der zweiten Sonde (Hebung der
    S/K-Trennung auf eine 𝒞-Achse) steht aus; geliefert ist die schwache Form
    (zwei Objekte + Übergang in einer Kategorie).

    Die Setzung HEBT (sie ersetzt das Schicht-Selektions-Theorem nicht); das
    `discontextural`-Feld bleibt konstitutiv (`trivial`, GESETZT analog B5). -/
noncomputable def ofBewohnteSchicht
    {S K : Type*} [Category S] [Category K]
    (PAS : ProemialAdjunctionSubstantial S K)
    (s : S) :
    DiscontexturalStratification S where
  emanative := s
  evolutive := (PAS.L ⋙ PAS.R).obj s
  transition := PAS.adj.unit.app s
  discontextural := trivial

/-- Die emanativ-reversible Eigenschaft der Hebung: bei vorliegender
    BC-Instanz ist der gehobene Übergang `transition` REVERSIBEL (iso) — die
    emanativ-reversible Schicht (LZEE S. 23: „Im emanativen Bereich [...]
    reversibel"). Konsumiert direkt `unit_isIso_of_bcData` (aus
    `AlphaGammaStratification`), NICHT `bcData_nonempty_iff_unconditional`.

    SPANNUNGS-VORBEHALT (ehrlich benannt): ein ISO-Übergang zwischen den
    beiden „Kontexturen" ist die Reversibilität der emanativen Schicht — aber
    er macht emanative und evolutive Objekt zugleich ISOMORPH und sagt nichts
    über die evolutiv-IRREVERSIBLE Seite (den eigentlichen diskontexturalen
    Bruch). Das Theorem hebt die Reversibilitäts-Substanz, nicht die
    Irreversibilitäts-Substanz. Das `discontextural`-Feld wird NICHT verwendet
    (es ist gesetzt, nicht beweis-tragend). -/
theorem transition_isIso_ofBewohnteSchicht
    {S K : Type*} [Category S] [Category K]
    {PAS : ProemialAdjunctionSubstantial S K}
    (BC : BCData S K PAS) (s : S) :
    IsIso (ofBewohnteSchicht PAS s).transition :=
  unit_isIso_of_bcData BC s

end Reformulation.Proemial.Discontextural
