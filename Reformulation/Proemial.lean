import Reformulation.Proemial.AlphaGamma
import Reformulation.Proemial.AlphaGammaSubstantial
import Reformulation.Proemial.AlphaGammaSubstantialRefined
import Reformulation.Proemial.AlphaGammaBeckChevalley
import Reformulation.Proemial.AlphaGammaRelPullback
import Reformulation.Proemial.AlphaGammaWitnesses
import Reformulation.Proemial.AlphaGammaTransport
import Reformulation.Proemial.AlphaGammaStratification
import Reformulation.Proemial.AlphaGammaRounding
import Reformulation.Proemial.DiscontexturalStratification
import Reformulation.Proemial.ContexturalTransjunction
import Reformulation.Proemial.RealizedTransjunction
import Reformulation.Proemial.SubstantialTransjunction
import Reformulation.Proemial.TransjunctionCloneBound
import Reformulation.Proemial.NonUniformCloneBound
import Reformulation.Proemial.QuaternaryCloneBound
import Reformulation.Proemial.GeneralCloneBound
import Reformulation.Proemial.M3CloneWitness
import Reformulation.Proemial.StageAscent
import Reformulation.Proemial.StageParity
import Reformulation.Proemial.ChoiceVectors
import Reformulation.Proemial.InteractiveTransjunction
import Reformulation.Proemial.IntransitivityDifferential
import Reformulation.Proemial.DirectionChoice
import Reformulation.Proemial.IrreversibleAscent
import Reformulation.Proemial.NoUniformSwap
import Reformulation.Proemial.ExtensionalCollapse
import Reformulation.Proemial.ExhaustionTransition
import Reformulation.Proemial.RecurringGround
import Reformulation.Proemial.ArrowAscent
import Reformulation.Proemial.RetractionBracket
import Reformulation.Proemial.RelabelInvariance
import Reformulation.Proemial.IntervalBackbone
import Reformulation.Proemial.ReversibleExchange
import Reformulation.Proemial.IrreversibleAdvance
import Reformulation.Proemial.ComplementaryMediation
import Reformulation.Proemial.ContentReflexivity
import Reformulation.Proemial.MediationProcess
import Reformulation.Proemial.SelfDetermination
import Reformulation.Proemial.BranchingCoalgebra
import Reformulation.Proemial.FlowIteration
import Reformulation.Proemial.CoalgebraMorphism
import Reformulation.Proemial.ContexturalFibration
import Reformulation.Proemial.StageAggregation
import Reformulation.Proemial.PolicyCheck
import Reformulation.Proemial.RAGAuthority
import Reformulation.Proemial.ContextureOverlap
import Reformulation.Proemial.RegimeThreshold
import Reformulation.Proemial.ElementaryCycle
import Reformulation.Proemial.CompoundContexture
import Reformulation.Proemial.PairwiseMixture
import Reformulation.Proemial.ContextureEscapeBound
import Reformulation.Proemial.TowerAsymmetry

/-!
# Reformulation.Proemial — α+γ-Form der Proemialrelation (Aggregat)

Aggregat-Datei für das Proemial-Modul.

Enthält:
- `Proemial.AlphaGamma`: α+γ-Form der Proemialrelation in der PKL-Doppelfaserung.
  Zwei primitive Funktoren L ⊣ R (α-Komponente) plus 2-Morphismus γ mit
  Beck-Chevalley-Verschränkung (γ-Komponente, Lesart B). F-1-Niederlegung (invariante
  Schicht).
- `Proemial.AlphaGammaSubstantial`: substantielle Tiefe der α+γ-Form. F-3-Niederlegung
  mit Aufhebung der drei F-1-Schwächen (γ-V/F-S-Differenzierung, BC-Spezialisierung,
  B-3-Tautologie). Zwei verschiedene Kategorien S ≠ K; α-N via Functor.IsEquivalence.
- `Proemial.AlphaGammaSubstantialRefined`: F-3.4/5-Folge-Iterationen. Additiv zu F-3.
  F-3.4: `naturality_K_from_S` als Theorem (aus `naturality_S` + Dreieck-Identität).
  F-3.5: `TritoStellungsVielfaltExists_substantial` mit `¬ IsIso σ.rel`-Substanz.
- `Proemial.AlphaGammaBeckChevalley`: F-3.6 BC-Architektur-Niederlegung plus drei
  Anschluss-Aufgaben (F-3.4.a/b, F-3.5.a). Eigenstängige BC-Konstruktion mit Pullback-
  Daten; `ProemialGammaMorphismTrulyMinimal` ohne Phantom-BC; γ-V ohne Sorry bewiesen.
- `Proemial.AlphaGammaRelPullback`: F-3.6.a Pullback-getragene rel-Substanz (Pfad D,
  modifizierte Sub-Substanz H). Diagonal-Form mit `h_rel_not_iso` wesentlich verwendet
  und `BC.pullback_K` operativ; dritte PKL-Konstruktion; 0 Sorries.
- `Proemial.AlphaGammaWitnesses`: F-3.6.a.1 + F-3.6.b Zeugen-Einheit. Äquivalenz
  `tritoStellungsVielfalt_iff_substantial` (ersetzt die falsche Nicht-Implikations-
  Aussage; Spec-Stopp-Befund, Sub-Substanz I); Bewohntheits-Zeuge mit Anwendungs-
  Korollar durch das Diagonal-Theorem; 𝟙-Kontrast-Zeuge; punktweiser
  Unabhängigkeits-Zeuge via Types.tensorProductAdjunction; 0 Sorries.
- `Proemial.AlphaGammaTransport`: F-3.6.a.2 + F-3.6.a.3 Transport- und
  Deprecation-Einheit. Treue-Brücke; Haupt-Theorem `rel_diagonal_transport`
  (Diagonal-Bruch auf der S-Seite, `BC.pullback_S` erstmals Statement-tragend);
  Verschränkungs-Gleichung `diagonal_transport_eq` mit iso-dichter Verschärfung
  (Anker-5-Einlösung); Stufe-5-Kandidat `bcIso_diagonal_transport` eingelöst;
  positives Faktorisierungs-Lemma plus formale Negations-Anker zu den zwei
  Option-B-deprecierten F-3.6-Aussagen (Memorial-Block in
  AlphaGammaBeckChevalley.lean); 0 Sorries.
- `Proemial.AlphaGammaStratification`: F-3.6.a.5 Schicht-Formalisierungs-Einheit.
  Zentrum-Lemma `unit_isIso_of_natIso` (Konditionalitäts-Auflösung der
  Weichen-Entscheidung Lesart A′); Vorbehalts-Korollar; Schicht-Selektions-Theorem
  `bcData_nonempty_iff_unit_isIso` (BC-Daten bewohnt genau bei iso Einheit);
  Negativ-Lemma `prodHomWitness_not_bcData` (prodHomWitness als Kontrast-Zeuge:
  Trito-geltend, nicht emanativ-reversibel); 0 Sorries.
- `Proemial.AlphaGammaRounding`: F-3.6.a.6 Abrundungs-Paket (erster reiner
  Abrundungs-Zyklus; Anfügung von Wahrheit statt Änderung). End-Lemma
  `end_id_comm` (Zentrum End(𝟭 S) kommutativ); unkonditionale Charakterisierung
  `bcData_nonempty_iff_unconditional`; Rück-Richtungs-Korollar `identityWitnessBC'`
  mit compat-Vergleich und voller Struktur-Gleichheit zum handgebauten Zeugen;
  Konsistenz-Korollar `prodHomWitness_not_unconditional`; Taktik-Konventions-Block
  und Erzähl-Präzisierungs-Block als Modul-Doc; 0 Sorries.

- `Proemial.DiscontexturalStratification`: Diskontexturalitäts-Setzung (Form β,
  neunte Schicht). Die emanativ/evolutiv-Trennung als GESETZTES Strukturmerkmal
  auf der Kontextur-Achse 𝒞 (analog B5/Beck-Chevalley, nicht bewiesen).
  Struktur `DiscontexturalStratification` mit konstitutivem `discontextural_posited : True`-
  Feld (B5-`prop_field`-Muster); Bewohntheit `discontexturalStratification_nonempty`
  (Wohlgeformtheit, nicht Nicht-Existenz-Wahrheit); Anschluss `ofBewohnteSchicht`
  plus `transition_isIso_ofBewohnteSchicht` (Hebung der emanativ/evolutiv-Trennung
  von 𝒪 auf 𝒞; auf der BC-bewohnten Schicht ist der gehobene Übergang reversibel).
  Setzung nicht Beweis: kein `¬∃`-Statement. 0 Sorries.

- `Proemial.ContexturalTransjunction`: gehobene S/K-Struktur mit Transjunktion
  (zehnte Schicht; hebt die schwache Form der neunten auf die starke). Gemischter
  Charakter: beweisbarer Kern + gesetzter Rand. Teil 1 `ContexturalLift` (starke
  Hebung über zwei getrennte Kategorien S, K mit Übergangs-Funktor — Korrektur des
  schwachen Spec-Defekts) + `Contextural := Bool ⊕ Bool` (konkrete ⊕-Realisierung).
  Teil 2 `exTransjunction`/`liftS` mit `exTransjunction_not_S_internal` (VORZEIGBARER
  Kern, BEWIESEN, konkrete Operation nicht Form α) und `exTransjunction_switches`
  (Lesart b, Kontexturwechsel inr aus inl, nicht Łukasiewicz). Teil 3
  `CharacterizedPosit` (Kern-Felder `op`/`not_S_internal` BEWIESEN, Rand-Feld
  `contexturePartitionGenuine : True` GESETZT analog B5/Beck-Chevalley) +
  `exCharacterizedPosit`; Komplementarität zu Beck-Chevalley als Doc-string.
  Kern/Rand-Grenze durchgehalten. 0 Sorries.

- `Proemial.RealizedTransjunction`: die Realisierungs-Naht (elfte Schicht). Webt
  die zwei Inseln der zehnten Schicht (operationslose Hebung `ContexturalLift` /
  hebungsloser Kern `exTransjunction`) auf EINEM parametrischen Trägerpaar `S, K`
  zusammen. Teil 1 `LiftedTransjunctiveC` (Naht-Struktur: `transition : S ⥤ K`
  Hebung-Funktor + `transject : S → S → (S ⊕ K)` Operation als SEPARATES Feld +
  `rejects`-Zeuge — beide Daten in EINEM Term, die Einwebung; `toContexturalLift`
  rekonstruiert die erste Insel, `switchOfTransition` subsumiert `switch` via
  `.obj`). Teil 2 `no_generic_switch` (axiom-frei, Zeuge `Bool/Empty` — der
  gehaltvolle Ersatz des `True`-Rand-Felds der zehnten Schicht). Teil 3
  `exLifted : LiftedTransjunctiveC (Discrete Bool) (Discrete Unit)` (NICHT-
  degenerierter Zeuge: zwei verschiedene Träger, konstanter Übergang kein 𝟙 —
  Behebung 1 gegen II.5; `exLifted_transition_collapses`/`exLifted_domain_distinct`
  bezeugen die echte Getrenntheit) + `exTransject_not_internal` (VORZEIGBARER
  Kern, BEWIESEN, konkret auf `Bool/Unit`, kein Form α) relativ zur benannten
  `internalS`-Definitions-Wahl (Behebung 2 gegen II.4). Der ehrliche Preis
  (`transition` Funktor / `transject` Operation bleiben zwei Felder, 2-stellig vs
  1-stellig — strukturelle Tatsache, kein Defekt) markiert. 0 Sorries.

- `Proemial.SubstantialTransjunction`: die bindende Transjunktion (Pfad A, zwölfte
  Schicht). Füllt die Naht der elften Schicht mit einem SUBSTANTIELLEN `K` statt
  binde-leerem `K = Unit`. Stelligkeits-Pointe: der Binde-Ort ist die Stelligkeit
  der ÜBERSCHREITUNG (des `inr`-Ziels), nicht die Substanz von `K`; unäre
  Überschreitung (`g a`, funktoriell) bindet nicht, binär-interaktive (`g a b`)
  bindet — Funktorialität ist Unarität, Binde-Kraft Binarität. Teil 1
  `InExtendedUnary` (Stelligkeits-Kriterium) + `unit_captures_all` (bei `K = Unit`
  total — Janus' Befund formal: Unit bindet nicht). Teil 2 `exTransjectA` über
  `S = ℕ` / `K = ℕ → Bool` (Rejektion zur charakteristischen Funktion von `{b}` —
  Ziel kodiert das ZWEITE Argument, binär-interaktiv) + `exTransjectA_outside`
  (VORZEIGBARER Kern, instanzgebunden über `(0,1)`/`(0,2)`, kein Form α) +
  `rejection_targets_injective` (trägt ii, unendliches S). Teil 3
  `exTransjectB_inside` (unäre Überschreitung bindet nicht — der Funktor-Befund) +
  `binary_captures_all` (binäre trivialisiert — Grenz-Markierung, die Unär-Schranke
  ist nicht willkürlich, NICHT Teil der bindenden Substanz). Teil 4 `exLiftedA :
  LiftedTransjunctiveC (Discrete ℕ) (Discrete (ℕ → Bool))` (die Naht über
  substantiellem `K`; `transject`-Feld IST die gehobene `exTransjectA` via
  `liftToDiscrete`/`exLiftedA_transject_eq`; `exLiftedA_transition_nontrivial`
  Nicht-Degeneration). Bindend ist die binär-TRANS-KONTEXTURALE Form, nicht
  Binarität als solche (die Multiplikation ist binär-intra-kontextural). Die eine
  offene Naht (≤unäre Lesart von „kanonisch", Janus' Achse) ist als Grenze geführt,
  nicht geschlossen (dritte Sonde). 0 Sorries.

- `Proemial.TransjunctionCloneBound`: die Transjunktion als bewiesene Klon- bzw.
  Definierbarkeits-Schranke (D, Verschaltung auf Mathlibs `ModelTheory.Substructures`).
  Trägt die negative Seite der Akkretion (Horistês: Transzendenz — die Operation gehört
  dem intra-kontexturalen System nicht an) deutungsdicht, ohne `True`-Feld. Tragender Satz
  `T_not_in_clone`: die Transjunktion `T a b = if (a,b)=(0,2) then 1 else max a b` auf
  `Fin 3` liegt nicht im von `{∧,∨,¬}` erzeugten Klon — bewiesen durch Konsum von
  `Term.realize_mem` (das Erhaltungs-Lemma per Term-Induktion, der harte Teil frei) plus
  `T 0 2 = 1 ∉ {0,2}`. Drei Deutungs-Tests am Term tragen die Transzendenz-Deutung: Test 1
  (`test1_*`, Iso `{0,2} ≃ Bool` mit Operations-Verträglichkeit, Kontextur-Treue), Test 2a
  (`term_preserves_contextur` + `T_leaves_contextur`, die Schranke ist das Verlassen, keine
  Schranke innerhalb), Test 2b (`const_not_closedUnder` + `no_substructure_with_const`, die
  Schranke verschwindet bei Hinzunahme der `1`-Konstante — zugleich K-D.2: keine Konstante
  in der Basis). Die positive Neuheits-Seite (K-D.5) erscheint NICHT im Korpus (kein
  `axiom`/`True`/getarntes Theorem), nur als nicht-formalisierte hermeneutische Aussage im
  Doc-String benannt. Kern-Sätze axiom-sauber (`propext, Quot.sound`, kein `sorryAx`).
  0 Sorries.

- `Proemial.NonUniformCloneBound`: der zweite Zeuge der Klon-Schranke (Kairos, Sonde 15 —
  Nicht-Internalität ohne Transzendenz). Der Zeuge `W` (Muster min/max/min) erhält alle
  drei Elementarkontexturen (`W_contexture_faithful`), wirkt auf jeder klassisch
  (`W_min_01`/`W_max_12`/`W_min_02`) — und liegt trotzdem nicht im Klon
  (`W_not_in_clone`; Existenz-Fassung `nonuniform_witness_exists`). Grund ist nicht
  Transzendenz, sondern die UNEINHEITLICHKEIT der lokalen Wahl (`W_uneven`): das
  Strukturprinzip (Konjunktion/Disjunktion) wechselt beim Kontexturwechsel, ohne dass
  eine Grenze verletzt wird. Beweismittel ist die Begleit-Relation
  `ρ(x,y) ⟺ y Extrem ∧ x in der gemischten Kontextur von y` (`rho_companion`), Basis-
  erhalten und darum Term-invariant (`rho_is_invariant`, dieselbe `Term.realize_mem`-
  Verschaltung wie `tolerance_is_invariant`); `W` bricht `ρ` genau an der
  Uneinheitlichkeits-Stelle (`rho_breaks_at_uneven_site`). Gegenrichtung als Schärfung:
  vier Wahlmuster sind mit expliziten Termen erzeugbar (`pattern_*_in_clone`, darunter
  zwei echte Kompositionen mit `¬`). E1-Nachzug (nach Sonde 16): die volle
  KLASSIFIKATION — drei weitere Zeugen `W2`/`W3`/`W4` (W2 direkt über `ρ`, W3/W4 per
  `conj`-Transport: der Klon ist unter der `neg`-Konjugation abgeschlossen,
  `clone_closed_under_conj` via Term-Konstruktion `¬ t[¬x,¬y]`; die 4/4-Teilung damit
  als symmetrisch belegt), Struktursatz `locally_classical_iff` + `ofChoices_injective`
  (lokal klassisch ⟺ Wahlvektor, die Zählung 2^3=8 im Korpus) und Hauptsatz
  `four_of_eight_generatable`: von den acht Wahlmustern sind GENAU VIER erzeugbar und
  GENAU VIER nicht (`locally_classical_dichotomy` als Ops-Fassung). Die übrigen Zahlen
  der Sonden 15/16 (Klon-Größe 82, Befunde für m ≥ 4: dort nur `min`/`max` erzeugbar)
  bleiben außerhalb des Korpus; ob kontextur-relative Operationswahl Günthers
  Vermittlung IST, bleibt unentschieden (Marke 3). 0 Sorries.

- `Proemial.QuaternaryCloneBound`: die Charakterisierung bei m = 4 (Kairos, E2 — nach
  Sonde 17 samt Gegenrechnung). Zielsatz `locally_classical_in_clone_iff4`: eine
  lokal-klassische Operation auf `Fin 4` liegt GENAU DANN im Klon von `{min, max, neg}`,
  wenn sie `min` oder `max` ist — die Verschärfung von E1 (dort vier von acht
  Wahlmustern erzeugbar) zur Charakterisierung (nur die Basiselemente selbst).
  Beweismittel ist die EINE Invariante `R₄` (Nachbarschaft der linearen Ordnung, an
  beiden Enden randgebrochen, `r4_neighbor`; explizite Tafel über `.val` — die
  `Fin`-Subtraktion wäre modular): basis-erhalten (`min_pres`/`max_pres`/`neg_pres`),
  darum Term-invariant (`r4_is_invariant`, dieselbe `Term.realize_mem`-Verschaltung
  wie E1), und JEDE gemischte Wahl bricht sie (`mixed_breaks`, EIN `decide` statt 62
  Einzelbeweise, `[propext]` dank Sechs-Argument-Bauform des Wahlvektors `ofC` — die
  `Fin 6 → Bool`-Form zöge `Classical.choice` über die Fintype-Instanz).
  Struktursatz `locally_classical_iff4` + `ofC_injective` (lokal klassisch ⟺
  Wahlvektor; die Zählung 2^6 im Korpus in Bijektions-Form), Wahlvektor-Fassung
  `two_of_sixtyfour_generatable` (erzeugbar ⟺ Null- oder Eins-Vektor).
  Robustheitssatz `mixed_not_in_constant_clone`: `R₄` ist reflexiv (`r4_diag`), die
  Schranke überlebt darum die um ALLE VIER Konstanten erweiterte Signatur `Lc` —
  Kontrast zu Test 2b in D, wo die `{0,2}`-Schranke an der `1`-Konstante fiel. Die
  übrigen Zahlen der Sonde 17 (62 Zeugen, 35 basis-erhaltene Relationen) bleiben
  außerhalb des Korpus; die uniforme Formel `R_m` für alle m ist Gegenstand von E3,
  nicht dieser Datei; Marke 3 unverändert. Kein Satz zieht `Classical.choice` oder
  `sorryAx`; `r4_neighbor`/`r4_diag` axiom-frei. 0 Sorries.

- `Proemial.GeneralCloneBound`: die Charakterisierung für ALLE m ≥ 4 (Kairos, E3 —
  nach Sonde 18 korrigiert und Sonde 19). Zielsatz `locally_classical_in_clone_iff`:
  für jedes m ≥ 4 liegt eine lokal-klassische Operation auf `Fin m` GENAU DANN im
  Klon von `{min, max, neg}`, wenn sie `min` oder `max` ist — kein `decide`, keine
  Fallunterscheidung nach m (Rang-Einordnung „erster Satz ohne feste Wertzahl" der
  E3-Spezifikation zugeschrieben, Dateikopf). Die Schranke m ≥ 4 ist WESENTLICH:
  bei m = 3 ist die Aussage falsch (E1). Beweismittel: die uniforme Invariante `R m`
  (Nachbarschaft, an beiden Enden randgebrochen, in DISJUNKTIONSFORM — die negierte
  Konjunktion als Hypothese zöge `Classical.choice` über `omega`) plus das
  Sonde-19-Kantengerüst: sechs Familien-Lemmata (`break_F1/F2/D/D'/Xb/Xt`) mit
  geschlossenen Bruchstellen; `Xb`/`Xt` brechen über die AUSSCHLUSSPUNKTE `(0,1)`
  und `(m−1,m−2)` selbst — die herausgenommenen Randpaare tragen den Abstieg, ihre
  Kollision mit dem Gerüst bei m = 3 IST der Sonderfall. Bauform: Propagation statt
  Weg-Datenstruktur (`step_min`/`step_max`, `Nat.le_induction`-Ketten,
  `min_propagates`/`max_propagates` → `preserving_is_min_or_max`). Klon-Ebene wie
  E1/E2 (`R_is_invariant` über `Term.realize_mem`); `min`/`max` für allgemeines m
  DEFINITIONAL erzeugbar (`rfl` statt `decide`). Robustheit `constant_clone_min_or_max`:
  `R m` reflexiv (`R_diag`, m ≥ 2 scharf), die Schranke überlebt alle m Konstanten
  (`Lc m`). Neuer gemessener Fallstrick: `omega` mit Disjunktion im ZIEL zieht
  `Classical.choice`; Heilung `ne_or_ne_of_imp` (dite über `Nat.decEq`, axiom-frei).
  Kanten- und Belegungszahlen (14/31/57, 62/1022/32766) bleiben in Sonde 18/19;
  Marke 3 unverändert. Kein Satz zieht `Classical.choice` oder `sorryAx`. 0 Sorries.

- `Proemial.M3CloneWitness`: die M3-Grenze als Satz (ERTRAG). Zielsatz
  `m3_mixed_term_exists`: auf dem kleinsten flachen Verband `M3` existiert ein Term
  über derselben Basis `{∧, ∨, ¬}` wie D/E1/E2/E3, dessen Realisierung auf JEDEM
  VERGLEICHBAREN Paar klassisch wirkt und global weder `meet` noch `join` ist —
  Zeuge `tM3 = (x ∧ y) ∨ ((x ∨ y) ∧ (¬x ∧ ¬y))`, Widerlegungspunkte
  `fM3 bot a1 = a1 ≠ bot` und `fM3 bot top = bot ≠ top`. Damit steht die Grenze der
  E3-Charakterisierung auf demselben Grund wie die Charakterisierung selbst; sie war
  die letzte handgerechnete tragende Aussage der Architektur. Die LEICHTE Hälfte des
  Differentials (Existenz mit explizitem Zeugen); die schwere steht seit
  `GeneralCloneBound`. Träger ist ein EIGENER induktiver Typ, nicht `Fin 5`: eine
  zweite `L.Structure (Fin 5)`-Instanz neben der globalen `strucM` erzeugte im
  Aggregat eine stille Instanz-Ambiguität, und ein `abbrev` genügte nicht (reducible).
  Folgerichtig keine Mathlib-`Lattice`/`Order`-Instanz — die Verbandsgesetze und die
  Involution stehen als benannte `decide`-Lemmata. `meet_leaves_incomparable` bringt
  die Begriffsgrenze an den Satz: auf einem unvergleichbaren Paar verlässt `meet` die
  Zweiermenge, sie ist dann keine Elementarkontextur (`Definitionen.md` §2) — darum
  quantifiziert `LocallyClassicalCmp` nur über vergleichbare Paare; die Begründung
  stand bisher als Prosa im `StageAggregation`-Doc — als DICHOTOMIE geführt:
  `cmp_pair_closed` (vergleichbare Paare sind abgeschlossen, die tragende Hälfte),
  `incomparable_pair_not_closed` (∀-Fassung der negativen), `meet_leaves_incomparable`
  als benannter Einzelfall. `le_iff_meet`/`le_iff_join` binden die Ordnung an die
  Tafeln — ohne sie wären `le` und `meet` zwei zufällig zueinander passende
  Gegenstände. Neuer Fallstrick (CLAUDE.md §8, Nr. 10): `deriving Fintype` trägt
  `Classical.choice` in jeden `decide`-Satz über `∀ x : M3`; gemessen ist die Differenz
  zweier Fassungen (dreizehn Sätze), nicht der Mechanismus — die Handinstanz heilt es.
  Wortlaut-Grenzen: „E3 fällt auf nicht-linearen Verbänden" ist LESART, keine formale
  Negation von E3 (E3 ist auf `Fin m` formuliert, eine Verbands-Fassung gibt es nicht);
  die Basis ist GEWÄHLT, nicht gefunden (die Involution ist auf `M3` nicht eindeutig,
  die Atome sind permutierbar); keine Charakterisierung der auf `M3` erzeugbaren
  Operationen; die Zahlen der Sondierung bleiben außerhalb (`CLAUDE.md` §6); die
  Robustheits-Pflicht §9 greift nicht (positive Hälfte, keine Schranke). Vier
  Statement-Pins; Axiom-Ist je Satz `#guard_msgs`-verwacht (19 Wachen) — kein
  `Classical.choice`, kein `sorryAx`. 0 Sorries.

- `Proemial.StageAscent`: der Stufenaufstieg als Probe (ERTRAG mit ausgewiesenem
  KONSUM-Anteil). Negativer Kern, uniform in m:
  `exists_locally_classical_not_in_clone` — für JEDES m ≥ 4 ist die Lücke der
  E3-Charakterisierung bewohnt, Zeuge die Familie `w m` (Maximum auf dem untersten
  Paar `{0,1}`, sonst Minimum). Der Klon-Ausschluss selbst ist reiner KONSUM:
  `w_not_in_clone` ist die Kontraposition der E3-Iff, `w_not_in_constant_clone` die
  der Konstanten-Fassung — keine eigene Invariante, kein kopiertes Kantenlemma, keine
  eigene Terminduktion. Positive Hälfte: `w_castSucc` — auf dem eingebetteten Quadrat
  stimmt die Stufe m+1 mit der Stufe m überein, die Familie ist EINE Regel auf allen
  Stufen; `ascent_proper` — das Bild der Vorstufe verfehlt das neue Element;
  `choose_two_succ` — jeder Schritt bringt genau m neue Paare, aus
  `Nat.choose_succ_succ` bewiesen und nicht zitiert. Arbeitet auf `strucM`, KEIN
  eigener Träger und keine zweite `L.Structure`-Instanz (Gegensatz zu
  `M3CloneWitness`, wo genau das nötig war). Kein `decide` in der Datei; die
  Fallzüge laufen von Hand. Gemessener Fallstrick-7-Fall: ein `by omega` mit
  DISJUNKTIONS-Ziel zog `Classical.choice` in vier Sätze; geheilt durch
  Konstruktion des Disjunkts am Term. Wortlaut-Grenzen: die Stufen-Lesung
  („Kontexturen erweitern sich") ist DEUTUNG und steht in keinem Satz und keinem
  Namen; „unendlich" erscheint nur als ∀ über Stufen, kein Grenzobjekt; die
  Max-Insel `{0,1}` ist gewählte Basis; die Robustheits-Pflicht §9 greift nicht
  (keine neue Schranke, die konsumierte trägt ihre Konstanten-Fassung, und die Datei
  konsumiert sie). Drei Statement-Pins; Axiom-Ist je Satz `#guard_msgs`-verwacht
  (10 Wachen) — kein `Classical.choice`, kein `sorryAx`. 0 Sorries.

- `Proemial.StageParity`: die Parität des Stufenschritts (ERTRAG, kein Konsum einer
  Klon-Schranke). Drei Sätze in Differential-Form über `GCB.negFin`, der Negation der
  Korpus-Signatur: G1 `castSucc_negFin_ne` — die Einbettung, unter der sich `SAsc.w`
  reproduziert, ist an KEINER Stelle negationsverträglich (links `m−1−a`, rechts `m−a`,
  Differenz 1 punktweise, ohne Fallunterscheidung nach m); G2 `odd_no_neg_compatible` —
  bei ungeradem m ist ÜBERHAUPT keine Abbildung `Fin m → Fin (m+1)` negationsverträglich,
  ohne Injektivitäts- und ohne Monotonie-Voraussetzung, bewiesen am Fixpunkt `(m−1)/2` von
  `negFin m` und der Unlösbarkeit von `2a = m`; G3 `eSym_strictMono` und `eSym_negFin` —
  bei geradem m trägt die symmetrische Einbettung `eSym` (Lücke am Mittelplatz `m/2`) beides,
  Ordnungstreue und Negationsverträglichkeit. Zugabe `w_eSym`: ab m ≥ 4 steigt über `eSym`
  auch die Zeugenfamilie mit — auf den geraden Stufen also Signatur samt Zeuge. Eine
  Definition (`eSym`), zwei Hilfslemmata (`negFin_val`, `eSym_val`, beide Wert-Auskünfte auf
  der `.val`-Ebene, beide verwacht); kein Entscheidungsverfahren, keine `Decidable`-Instanz,
  keine Änderung an `GeneralCloneBound` oder `StageAscent`. Gemessene Choice-Grenze:
  Mathlibs `Monotone.map_max` zieht `Classical.choice`, die Handrechnung über `.val` mit
  `Fin.coe_min`/`Fin.coe_max` nicht — darum läuft sie von Hand. Wortlaut-Grenzen: die Lesung
  („das Umtauschverhältnis ist stufenrelativ") ist DEUTUNG und steht in keinem Satz und
  keinem Namen; nichts über `m → m+2`, keine Verkettung, kein Grenzobjekt — „kein Kolimes"
  ist KEIN Satz dieser Datei, L12-4 bleibt unberührt offen; keine Zählung verträglicher
  Einbettungen. Die Robustheits-Pflicht §9 ist gegenstandslos (keine Schranke, keine
  Invariante). Drei Statement-Pins; Axiom-Ist je Deklaration `#guard_msgs`-verwacht
  (8 Wachen, die Definition eingeschlossen), durchgehend `[propext, Quot.sound]` — kein `Classical.choice`, kein
  `sorryAx`. 0 Sorries.

- `Proemial.ChoiceVectors`: die lokal klassischen Operationen als Wahlvektoren (ERTRAG mit
  ausgewiesenem KONSUM-Anteil). Der Name meint Günther-seitige Wahlmuster, NICHT das
  Auswahlaxiom (Dateikopf sagt es in Zeile 1). R0 `card_pairs` — der Träger der Wahl hat
  C(m,2) Stellen. R1 `ofChoices_locallyClassical` und `locallyClassicalEquiv` — das Theorem:
  jeder Wahlvektor ist lokal klassisch, und die Zuordnung ist eine BIJEKTION; damit ist
  „lokal klassisch" Bauplan und nicht bloß Eigenschaft. R2 `card_locallyClassical` — als
  Korollar genau 2^C(m,2) lokal klassische Operationen; die Marken 8/64/1024 des
  Arbeitspapiers sind damit Instanzen eines Satzes und bleiben selbst außerhalb. R3
  `clone_locallyClassical_eq` — die Erreichbarkeits-Seite als MENGENGLEICHHEIT (bewusst
  keine Karte: „im Klon liegen" ist nicht entscheidbar), reiner Konsum der E3-Iff und von
  `min_in_clone`/`max_in_clone`; `min_ne_max` trägt die „Zwei". R4
  `card_locallyClassical_lt` — das Wachstum je Stufenschritt, Konsum von
  `SAsc.choose_two_succ`. Zugabe `two_lt_card_locallyClassical` — ab m ≥ 3 mehr als zwei.
  Verhältnis zu E2: `QCB.ofC` ist dieselbe Gestalt bei festem m = 4 mit sechs
  Bool-Argumenten; hier uniform in m und als Bijektion, ohne Umbau an E2 — die Zahlen
  treffen sich (C(4,2) = 6, also 2^6 = 64). Wortlaut-Grenzen: „wachsender struktureller
  Reichtum bei konstanter Erreichbarkeit" ist DEUTUNG des Paars R2/R3 samt R4 und steht in
  keinem Namen; kein Satz über die Def6-Totalität, L06-1 bleibt offen; L03-3 (Grenznotiz A)
  wird nicht entschieden; die Klon-Reihe bleibt unberührt und choice-frei. Die
  Robustheits-Pflicht §9 greift nicht (keine neue Schranke). Vier Statement-Pins; Axiom-Ist
  je Deklaration `#guard_msgs`-verwacht (18 Wachen, Definitionen und Instanzen
  eingeschlossen). GEMESSENE SCHICHTGRENZE: die ganze Äquivalenz-Schicht bleibt choice-frei
  (bis `[propext, Quot.sound]`), der `Classical.choice`-Anteil sitzt in der
  `Fintype`-Maschinerie — schon `Fintype (Pairs m)` und `Fintype.card_fin` tragen ihn, jede
  `Fintype.card`-Aussage erbt ihn. Dass die Bijektion frei davon bleibt, hängt an der
  Konversionsform: die Hinrichtung läuft über `if _ = _ then true else false`
  (`instDecidableEqFin`); dieselbe Datei mit `==` zieht `Classical.choice` in die Bijektion,
  über Mathlibs `Std.LawfulBEqOrd`-Instanz für `Fin m`. Beide Fassungen gemessen. 0 Sorries.

- `Proemial.InteractiveTransjunction`: der Interaktions-Zeuge (dreizehnte Schicht).
  Präzisiert die „binär-interaktiv"-Erzählung der zwölften Schicht am Term (die alte
  Schicht bleibt unangetastet). Teil 1 gespiegelte Familie `InExtendedUnarySnd` +
  Buchung `exTransjectA_inside_snd`: `exTransjectA` ist der ASYMMETRISCHE Zeuge (Ziel
  `φ_b` am zweiten Argument allein), gefangen von der Zweit-Argument-Familie — kein
  interaktiver. Teil 2 der echte Interaktions-Zeuge `exTransjectI` (Rejektions-Ziel
  `φ_{a+b}`, an BEIDEN Argumenten): `exTransjectI_outside_fst`/`_snd`/`_either` — außer-
  halb beider unärer Familien; instanzgebunden `(0,1)/(0,2)` bzw. `(1,0)/(2,0)`, kein
  Form α. Teil 3 (Kür) `InExtendedUnaryMixed` + `exTransjectI_outside_mixed`: auch außer-
  halb der punktweise gemischten Familie (Taubenschlag über `1,2 × 5,6,7`) — Ausschluss
  im unären Regime unbedingt. Teil 4 (Kür) `exLiftedI` Naht über substantiellem `K` mit
  dem interaktiven `transject`-Feld. Reichweite unverändert konditional: `binary_captures_all`
  bleibt wahr, die Unär-Lesart bleibt gesetzte Prämisse — Symmetrisierung, nicht Zwang;
  „Interaktion = Akkretion" bleibt Deutung. 0 Sorries.

- `Proemial.IntransitivityDifferential`: das Intransitivitäts-Differential
  (vierzehnte Schicht) — das erste *vollständige* Differential der Architektur:
  beide Richtungen als Theoreme, in EINER Sprache (Ordnungssprache), von Null.
  Reiche Seite: der minimale relationale Zeuge `cyc3` auf `Fin 3` (orientierter
  3-Zyklus `b = a+1`) mit den Ehrlichkeits-Sätzen `cyc3_holds`/`cyc3_irrefl`/
  `cyc3_not_transitive` — er existiert, ist irreflexiv und verlässt die arme
  Klasse EXAKT an der Transitivität. Arme Klasse (`IsTrans`+`Std.Irrefl` =
  `IsIrrefl`, instanz-quantifiziert): `no_cycle_in_strict_order` (nackte Fassung, Günthers
  Reduktion 1937 gespiegelt — Verkettung/Gegenprinzip/Kollaps; Druck-Zählung:
  (2)+(1) gegen (3)) und
  `cyc3_not_representable` (Darstellbarkeits-Fassung: kein relations-erhaltendes
  `f` in irgendeine strikte Ordnung). Kür `no_return` (keine Rückkehr in
  beliebig vielen Schritten via `Relation.transGen_eq_self`). KEINE Aussage über
  die modale Triade (deren Asymmetrie bleibt Design-Datum, A3; Swap-Satz = AP7).
  Konditional ist hier nichts. 0 Sorries; axiom-frei bis auf die Kern-Axiome
  von `decide`/`propext`.

- `Proemial.DirectionChoice`: die Drehrichtungs-Wahl (fünfzehnte Schicht) — die
  dritte Wille-Funktion als GESETZTE Funktion mit echtem Stellungs-Argument
  (Rev3-Signatur eingelöst; Konkordanz Stellung ≙ `CompositionSite`,
  KompositionsRichtung ≙ `Turn`, choose ≙ `directionChoice`). Kern-Lemma
  `factorsThroughUnit_iff_constant` (typunabhängige volle Äquivalenz: durch `Unit`
  faktorisieren ↔ konstant sein) charakterisiert das arme Modell exakt; das
  Differential mit textuell verankerter negativer Richtung — die gesetzte Wahl ist
  nicht-konstant (`directionChoice_not_constant`) und faktorisiert darum NICHT durch
  `Unit` (`directionChoice_no_unit_factorization`, Günther 1971 als Beweis-Spiegel:
  „ein Wille, der nichts als sich selbst will, hätte nichts Konkretes"). Kür
  `card_unit_choices = 2` vs. `card_site_choices = 8` (die Verarmung als
  Kardinalität). Richtungs-Marke: Richtung 1 (kein Wollen ohne Vorstellung)
  eingelöst, Richtung 2 offen (V2). Kein PathC-Import, kein Satz über τ/δ/ω —
  die Stellen-Namen sind semantische Verweise; Swap-Satz = AP7. 0 Sorries.

- `Proemial.IrreversibleAscent`: der irreversible Aufstieg (sechzehnte Schicht) —
  das zweite Zeit-Differential in Zeugen-Fassung, dual zur vierzehnten
  (`IntransitivityDifferential`): dort kein Zyklus in strikter Ordnung, hier kein
  strikter Aufstieg in Periodik. Eine Sprache (Iteration/Gleichheit), selbsttragend
  (kein Kenogramm-, F3- oder PathC-Import). Arme Klasse `PointwisePeriodic` = Günthers
  Maßstab-Grenzfall (Vorwort Beiträge III, S. XI — Zusammenlesung); ihre Symmetrie
  ist Satz (`reach_returns`), nicht Definitions-Zutat, ebenso die
  Nicht-Darstellbarkeit des injektiven Aufstiegs (`no_injective_trajectory`). Zeuge
  `Nat.succ` (rückkehrfrei: `succ_no_return`/`succ_not_pointwise_periodic`). Das
  Rang-Lemma `no_return_of_strict_rank` (samt Korollar) reduziert die
  Fixpunkt-Freiheits-Setzung der Architektur auf eine prüfbare Term-Eigenschaft
  (strikt wachsender ℕ-Rang). Marke: der Zeuge trägt die Stufen-Zahl, nicht die
  Kontextur-Substanz; die Vorwort-Stelle bleibt behauptete negative Richtung. Kür
  `orbit_pred_exists` (Orbit-Vorgänger). 0 Sorries; Axiome `propext` (+ `Quot.sound`
  in den ℕ-tragenden Sätzen), kein Classical, kein decide.

- `Proemial.NoUniformSwap`: der Swap-Satz (siebzehnte Schicht) — das älteste
  „benannt, nicht gebaut" der Architektur (NE3, kein kanonischer Swap) erhält seinen
  Satz in Paar-Fassung. Kategorien-Sprache, Zeuge auf `Discrete (Fin 2)` (F = const ⟨0⟩,
  G = swap; `comp_obj_ne`). **Bewiesen:** punktuelle Existenz (`swap_exists_self`, Kür
  `swap_exists_of_comm`: Kommutation ⟹ Swap via `eqToIso`); **bewiesen:** keine uniforme
  Swap-Zuordnung über alle Endofunktor-Paare (`no_swap_witness` Instanz, `no_uniform_swap`
  mit `Category.{0}`-Pin, via `Discrete.eq_of_hom`). **Benannt, nicht behauptet:** die
  Triaden-Fassung — Paar-Uniformität ist stärker, ihre Widerlegung impliziert die
  Triaden-Widerlegung NICHT; der einzige heute baubare `ModalTwoCategory`-Bewohner ist
  degeneriert und kommutiert → Folge-Posten 17b (der nicht-degenerierte Bewohner).
  Naht-Prüfstelle: nicht als Wahl-Echtheit noch als Triaden-Asymmetrie erzählt. Die Sonde
  `Diagnostics/SwapSatzProbe.lean` bleibt unangetastet (historischer Beleg). Axiom-Ist:
  `propext`, `Classical.choice`, `Quot.sound` (Herkunft CategoryTheory- und Iso-Maschinerie,
  kein `sorryAx`, kein `decide`-Axiom). **Abweichung vom Spec-Wortlaut (am Term):** `Classical.choice`
  tritt NICHT erstmals mit dieser Schicht ins Aggregat-Profil — es ist bereits präsent (via PathC
  `ModalEndofunctor.tauOmega` und via Proemial `AlphaGamma.pbv_gamma_isIso`, das bis Zug A
  `form_inhalt_vertauschungs_operativitaet` hiess; das Profil ist dasselbe geblieben).
  0 Sorries.

- `Proemial.ExtensionalCollapse`: der extensionale Kollaps (achtzehnte Schicht) — das
  Schicht-I-Differential (Klassifizieren ≠ Klassifiziertes) in Zeugen-Fassung, gehoben aus
  den Vor-Sonden `ReflexionsrestProbe`/`LawvereVorSonde` (beide byte-unverändert als
  historische Belege). Zeugen-Paar `s = ∨(x₀,x₀)` (Komposition, `func`) gegen `t = x₀`
  (Projektion, `var`) mit dem Scharnier `witness_equiv` (identische Denotation `v ↦ v 0`).
  Kollaps-Satz `no_extensional_separation` instanz-quantifiziert über die arme Klasse
  `DenotationInvariant` (jede denotations-invariante Klassifikation identifiziert das Paar —
  der dünnste Satz der Phase, eine Zeile über dem Scharnier). Der Überschuss als benannte
  Funktion `isComposite` samt Preis: `discriminator_separates` (trennt das Paar),
  `witness_ne` (positive Hälfte via `congrArg`), `discriminator_not_invariant` (der
  Diskriminator verlässt die arme Klasse). Schere beidseitig: `extension_without_intension`
  (Konsum von `T_not_in_clone` — Extension ohne Intension). Kür `evalAt_separates_semantic`
  (die arme Klasse trennt bis zur semantischen Differenz `var 0` gegen `var 1`, endet am
  Zeugen-Paar). E&W-Marke: bewiesen ist die *formale* Term-Intensionalität (Konstruktor-
  Verschiedenheit — von `propext` nicht einebnbar; der `witness_ne`-Beweis selbst zieht
  `propext`, minimal); die *intensionale* E&W-Stufe wird NICHT eingelöst (V2). Kollaps
  struktur-relativ (`Fin 3`).
  2b (γ-Anbindung) vertagt (Typ-Spalt-Befund `LawvereVorSonde`). Erste Schicht unter der
  `#guard_msgs`-Wache (Plan Rev4 §1): Axiom-Ist `propext` (`witness_ne`) bzw.
  `propext, Quot.sound` (übrige Kern-Sätze), kein `Classical`, je Kern-Satz Ist-gebunden
  verwacht. 0 Sorries.

- `Proemial.ExhaustionTransition`: der Erschöpfungs-Übergang (neunzehnte Schicht) —
  die achte Stelle der achtfachen Form in Zeugen-Fassung („Die Subjektivität geht, wie
  Hegel sagen würde, in ihren Grund, d.h. in das Sein zurück", Lille Z. 1018–1032, —
  S. 160 (druck-verifiziert; Doppel-Abgleich 13. Juli); der Tod als Rückgabe der Reflexivität, 1957). Erste Schicht-zu-Schicht-Abhängigkeit unter den
  Niederlegungs-Schichten: die arme Klasse `PointwisePeriodic` wird aus der
  sechzehnten (`IrreversibleAscent`) **term-identisch** importiert, nicht dupliziert
  — Aufstieg und Erschöpfung messen am selben Maßstab-Grenzfall. Merkmal `Exhausts`
  vierteilig (irreversibles Verlassen, absorbierender Bestand, Nicht-Wiederkehr,
  Bestand ≠ Anfang als Folge). Die strukturelle Nicht-Identität Bestand ≠ Anfang als
  Lemma (`exhausts_ne`; die Grund-Formel ist Projekt-Deutung, kein Zitat — Autopsie
  13.7.). Negative Hälfte `no_exhaustion_in_periodic` (keine Erschöpfung im
  Maßstab-Grenzfall — der dünnste Satz des Pakets, hier axiom-frei). Zeuge `collapse`
  auf `Fin 2` (`collapse_exhausts`: 0 verlassen, 1 absorbierender Bestand). Der
  Phasenwechsel als Wohlfundiertheits-Theorem `fixpoint_reached_of_strict_descent`
  (strikt fallender ℕ-Rang außerhalb der Fixpunkte ⟹ jede Trajektorie erreicht einen
  Fixpunkt) — das Spiegel-Stück zu `no_return_of_strict_rank` (16.): steigender Rang →
  nie Bestand, fallender Rang → Bestand erreicht. Kür `exhausted_stays` (der Bestand
  bleibt). Marken: die Stellen-Zuordnung ist strukturanalytisch, die 1957-Stelle
  bleibt behauptete negative Richtung (behauptet ≠ bewiesen), **Designation ≠
  Denotation** (Vier-Begriffe-Wache gegen die achtzehnte Schicht). Axiom-Ist je
  Kern-Satz `#guard_msgs`-verwacht; Abweichung: das Descent-Lemma zieht
  `Classical.choice` (`by_cases` über beliebigem Träger ohne `DecidableEq`,
  gewöhnliche Notiz), die drei anderen bleiben im Bereich `propext`/`Quot.sound`
  (`no_exhaustion_in_periodic` sogar axiom-frei). 0 Sorries.

- `Proemial.RecurringGround`: der wiederkehrende Grund (zwanzigste Schicht) — die
  **erste Stelle** der achtfachen Thematik in Zeugen-Fassung. Grund als Fixpunkt
  (`Ground f a := f a = a`); der Anker-Satz als Wiederkehr-Lemma `ground_recurs`
  („das reflexionslose Sein … das in allen folgenden Reflexionsstufen immer
  wiederkehrt", **druck-verifiziert**, Beiträge III S. 160 — erster druck-
  verifizierter Anker; via `Function.iterate_fixed`-Konsum, Teil 0 (1)). Arme
  Klasse `FixpointFree` mit negativer Hälfte `no_ground_in_fixpointfree` (keine
  Gründe in der fixpunktfreien Welt — definitorisch dünn). Geteilte Zeugen am
  `collapse` (19., term-identisch): `collapse_ground` (1 ist Grund) /
  `collapse_not_ground_zero` (0 nicht) — dieselbe Funktion bedient beide
  Rand-Stellen. **Bogen-Satz** `exhausts_ground` (was die Erschöpfung erreicht,
  trägt die St.1-Invarianz — eine Projektion `h.1`, Dünnheit ausgesprochen) samt
  `exhausts_ground_recurs`. Kür `swap`-Zeuge (`swap_fixpointfree`,
  `swap_pointwise_periodic`, `swap_no_ground`, `swap_no_exhaustion`: weder Grund
  noch Erschöpfung an einer Instanz) und `classes_differ` (die zwei armen Klassen
  der Rand-Stellen sind verschieden). Bauform-Deutung: die **Rand-Klammer** der
  1+3+3+1 — zwei Rollen desselben Fixpunkts, in einer Sprache; **Kette 16→19→20**.
  Marken: Stellen-Zuordnung strukturanalytisch, Fixpunkt↔reflexionslos Deutung,
  Einwertigkeits-Lesart benannter Folge-Posten St.1b (nicht versprochen);
  Designation ≠ Denotation gilt fort. Axiom-Ist je Kern-Satz `#guard_msgs`-verwacht:
  das Ist **unterschreitet** den erwarteten Bereich `propext`/`Quot.sound` (kein
  `Quot.sound`, **kein `Classical`** — dritter Datenpunkt der Spiegel-Asymmetrie
  auf der Rechen-Seite): `ground_recurs`/`no_ground_in_fixpointfree`/
  `exhausts_ground`/`exhausts_ground_recurs` axiom-frei (Verschärfung; `ground_recurs`
  via `Function.iterate_fixed`-Konsum), `collapse_ground`/`swap_no_exhaustion`/
  `classes_differ` `[propext]`. 0 Sorries.

- `Proemial.IntervalBackbone`: das Intervall-Rückgrat (einundzwanzigste Schicht) —
  das **arithmetische Substrat des Stellen-Trakts**. Die Anfangs-Wertzahlen der
  acht Intervalle der achtfachen Thematik sind die Dreieckszahlen: `intervalStart n
  := n * (n + 1) / 2`, `intervalEnd n := intervalStart n + n` (Lille Z. 530,
  544–547). Die Gauss-Brücke `two_mul_intervalStart` zähmt die ℕ-Division ein für
  alle Mal (danach ist jede Rückgrat-Aussage linear); darauf die drei Struktur-
  Gesetze: `intervalStart_succ` (Stufung — jedes Intervall beginnt um seine eigene
  Themen-Zahl höher), `intervalEnd_succ_start` (**Naht** — die Intervalle schließen
  lückenlos und überlappungsfrei aneinander: das Werte-Kontinuum der achtfachen
  Thematik als Theorem), `intervalEnd_sub_start` (Themen-Gesetz — Intervall-Nummer
  = Themen-Zahl = Abschnitts-Länge, die Selbstbezüglichkeit der Formel). Dazu
  `tafel_IV` (die acht Intervalle I–VIII, Lille Z. 407 ff.; BCL-Report 3.0, 1965 —
  Titel-Falle in Fn. 2/5 notiert) und die zwei Zitat-Anker `nature_closes_at_14`
  („ein 14-wertiges System formaler Logik", Z. 517–519) sowie `eighth_starts_at_36`
  („nicht weniger als 36 Werte und 8 ontologische Themen", **druck-verifiziert**,
  Beiträge III S. 160 — zweiter druck-gesiegelter Anker). Kür
  `intervalStart_strictMono` (wohlgeordnete Orts-Folge). **SUBSTRAT, KEIN
  DIFFERENTIAL:** keine arme Klasse, keine Unmöglichkeits-Hälfte, keine
  Zeugen-Fassung — das Rückgrat zählt die Orte, es deutet sie nicht; die
  Stellen-Schichten importieren es (geteilte-Klassen-Ökonomie eine Stufe tiefer).
  **Hegel-Relativitäts-Marke:** Günthers „ernsthafte Zweifel" (Z. 921–922) und
  „nur relativ" (Z. 936–938) treffen die inhaltliche Zuordnung der Triaden zu den
  Intervallen, **nicht** diese Formel-Arithmetik; die Zuordnungen (Mechanik = II
  usw.) kommen in den Stellen-Schichten, jede mit dieser Marke. „Wertzahl/Thema/
  Intervall" sind Namen — term-fest ist die ℕ-Arithmetik; keine Werte-Semantik,
  keine Ophiten-Namen, keine Ablösungs- oder Wiederkehr-Figur (benannte Posten);
  Designation ≠ Denotation gilt fort. **Projekt-import-frei** (einziger
  Mathlib-Import: `Order.Monotone.Basic` für die Kür). Axiom-Ist je Kern-Satz
  `#guard_msgs`-verwacht, taktik-scharf zweigeteilt: die drei `decide`-Sätze (`tafel_IV`,
  `nature_closes_at_14`, `eighth_starts_at_36`) **axiom-frei**, die fünf
  `omega`-Sätze `[propext, Quot.sound]` — nachgemessen als **Hüllen-Profil** der
  `omega`-Taktik (`n + 0 = n` trägt dasselbe), nicht als Substanz.
  **Abweichung/Verschärfung:** Gauss-Brücke per Induktion statt per
  `Nat.two_mul_div_two_of_even` — die Mathlib-Route trüge `Classical.choice`
  herein und hätte es an alle vier Gesetze weitergereicht. 0 Sorries.

- `Proemial.ReversibleExchange`: der reversible Umtausch (zweiundzwanzigste
  Schicht) — die **erste Mittelstelle**: „Im zweiten Intervall tritt die Zeit
  ausschließlich in ihrer reversiblen Form auf" (Lille Z. 486–487,
  Volltext-verifiziert) wird als Involution gefasst (`Reversible f := ∀ x,
  f (f x) = x`). Die **Brücke** `reversible_pointwise_periodic` (reversibel →
  punktweise periodisch, Periode 2) legt Stelle 2 beweisbar in die arme Klasse,
  gegen die Aufstieg (16.) und Erschöpfung (19.) unmöglich sind — sie ist der
  **einzige Satz der Schicht mit eigenem Beweis-Gehalt (Konsum-Ehrlichkeit)**.
  Die „ausschließlich"-Sätze sind benannter Konsum über die Brücke:
  `reversible_returns` (`reach_returns`, 16. — jeder erreichte Zustand kehrt
  zurück) und `reversible_no_exhaustion` (`no_exhaustion_in_periodic`, 19. — die
  achte Stelle liegt nicht im zweiten Intervall). Dazu die geteilten Zeugen
  `swap_reversible` (20.) und `collapse_not_reversible` (19.) — die Trennung
  St.2 ↔ St.8 in beiden Richtungen — sowie der Rückgrat-Ort `interval_II_start`
  (= 3) / `interval_II_end` (= 5) als erster Stellen-Konsum des Substrats (21.,
  Z. 517–519); Kür `reversible_bijective` (der Umtausch verliert nichts).
  **Erste Schicht auf beiden Strängen** (belegt am Import-Graph dieser
  Lieferung: Substrat `IntervalBackbone` + Kette `RecurringGround`); die Kette
  wird 16→19→20→22, alles term-identisch konsumiert, nichts dupliziert.
  **Bauform-These der Mittelstellen:** Merkmal + Ort + Anschlüsse, **kein neuer
  Apparat** — die Stelle *liegt in* einer bestehenden armen Klasse, das ist ihr
  Befund, kein Differential-Ersatz. **Hegel-Relativitäts-Marke:** „Mechanik =
  Intervall II" ist Lesart der Hegel-Stufe, nicht Satz — Günthers „ernsthafte
  Zweifel" (Z. 921–922), „nur relativ" (Z. 936–938); gesichert nur „je drei
  Intervalle". Involution ↔ „Umtausch" ist Deutung, Fin-2-Träger Modellwahl,
  „zweiwertig" Themen-Rede (keine Werte-Semantik); Designation ≠ Denotation gilt
  fort; kein St.3/St.4-Vorgriff. Axiom-Ist je Satz `#guard_msgs`-verwacht:
  Brücke, `reversible_no_exhaustion`, beide Orts-Sätze und die Kür **axiom-frei**,
  `reversible_returns` `[propext]` (von `reach_returns` geerbt), die zwei
  `decide`-Zeugen `[propext]` (Hüllen-Profil der Taktik). **Abweichung in beide
  Richtungen (Verschärfung):** die Spec-Erwartung (Brücke/Konsum propext,
  decide axiom-frei) trifft nicht — Brücke und Konsum-Satz unterschreiten sie,
  die decide-Sätze überschreiten sie um das Hüllen-`propext`. Kein neues
  `Classical`. **Kür-Messung:** `Function.Involutive.bijective`-Konsum und
  Eigenbeweis beide axiom-frei — Gleichstand, geliefert wird der Konsum
  (Ökonomie). 0 Sorries.

- `Proemial.IrreversibleAdvance`: der irreversible Fortgang (dreiundzwanzigste
  Schicht) — die **zweite Mittelstelle**: das dritte Intervall, die irreversible
  Zeit („müssen wir mindestens zum dritten Intervall übergehen … zum ersten Mal
  eine dreiwertige Thematik", Lille Z. 493–496, Volltext-verifiziert), gefasst
  als **Rückkehrfreiheit** (`NoReturn f := ∀ x n, 0 < n → f^[n] x ≠ x` — echt
  stärker als `FixpointFree`, dessen n=1-Fall sie ist). Die
  **Natur-Nachbar-Trennung** steht in beiden Fassungen: `noreturn_not_periodic`
  (St.3 liegt außerhalb der armen Klasse, in der St.2 zuhause ist) und
  `noreturn_not_reversible` (direkt, über die Brücke der 22.) — die
  Nonempty-Bedingung ist Voraussetzungs-Ehrlichkeit (leerer Träger: beide
  Prädikate leer wahr), keine Setzung. Die **„kommt nirgends an"-Sätze**
  `noreturn_no_ground` und `noreturn_no_exhaustion` zeigen: die rein irreversible
  Welt kennt weder Grund (20.) noch Erschöpfungs-Ziel (19.). Das Rang-Lemma
  erscheint als **Stellen-Fassung per Konsum** (`noreturn_of_strict_rank`) —
  **kein Duplikat: das Aufstiegs-Differential bleibt Eigentum der 16.** Zeugen:
  `succ_noreturn` (die Stufung selbst; **erster ℕ-Zeuge einer Stelle** — Ist-
  geprüft an 19./20./21./22., wo alle Zeugen `Fin 2` tragen bzw. die 21. als
  Substrat gar keine führt; ausdrücklich **kein** erster ℕ-Zeuge überhaupt, die
  16. führt `Nat.succ` bereits für ihr Differential) sowie die geteilten
  Gegen-Zeugen `swap_not_noreturn` (Periode 2) und `collapse_not_noreturn`
  (Grund bei 1). Orts-Sätze `interval_III_start` (= 6) / `interval_III_end`
  (= 9), Substrat-Abruf aus der 21. (Z. 517–519). Kette 16→19→20→22→23, ein
  Import, alles term-identisch konsumiert, kein Mathlib-Import über die
  transitive Hülle hinaus. **Hegel-Relativitäts-Marke:** „Physik = Intervall
  III" ist Lesart der Hegel-Stufe, nicht Satz („ernsthafte Zweifel" Z. 921–922,
  „nur relativ" Z. 936–938). **Symmetrie-Bruch-Marke:** Günthers Bruch betrifft
  wörtlich Position/Negation der **Werte-Struktur** — Werte-Semantik, außerhalb
  dieses Baus; die Verbindung zur term-gebauten St.2/St.3-Trennung ist Deutung.
  `NoReturn` ↔ irreversibel ist Deutung, „dreiwertig" Themen-Rede, „kommt
  nirgends an" markierte Struktur-Aussage (kein Zitat), die Träger `Fin 2` und
  `ℕ` Modellwahl; Designation ≠ Denotation gilt fort; kein St.4-Vorgriff.
  Axiom-Ist je Satz `#guard_msgs`-verwacht (zwölf Wachen): die fünf Sätze der
  Trennung und des „kommt nirgends an" sowie beide Orts-Sätze **axiom-frei**, die zwei
  `decide`-Zeugen `[propext]`, `noreturn_of_strict_rank`/`succ_noreturn`/Kür
  `[propext, Quot.sound]` (`omega`-Hülle). **Kein `Classical`** — auch die
  Nonempty-Sätze nicht (`obtain ⟨x⟩ := ‹Nonempty α›` auf Prop-Ziel bleibt
  axiom-frei; verwacht statt behauptet). **Abweichung:** die Erwartung „Konsum
  frei bis `propext`" trifft für `noreturn_of_strict_rank` nicht — die
  `omega`-Hülle des konsumierten `no_return_of_strict_rank` (16.) reist mit dem
  Konsum mit; Konsum erbt das Profil des Konsumierten und unterbietet es nicht.
  **Zwei-Routen-Messung (K1):** `succ_noreturn` (direkt, `succ_iterate'` +
  `omega`) und `succ_noreturn_via_rank` (Konsum, Rang = `id`) tragen **dasselbe
  Profil** — an einer ℕ-Iterations-Aussage kauft der Konsum kein schärferes
  Profil; ein Befund über die Hülle, nicht über die Routen. 0 Sorries.

- `Proemial.ComplementaryMediation`: die komplementäre Vermittlung
  (vierundzwanzigste Schicht) — die **Schluss-Stelle der Natur**: das vierte
  Intervall, die Komplementarität als „Vermittlung" („Strukturen …, die
  Zweiwertigkeit und Dreiwertigkeit miteinander vermitteln", Lille Z. 506–508,
  Volltext-verifiziert), gefasst als **Koexistenz** (`Mediates f` — ein Träger
  mit einem wiederkehrenden UND einem nie zurückkehrenden Punkt). Die
  **Schnitt-Leere** `reversible_noreturn_empty` verschärft die Trennung der 23.
  zur Disjunktheit; die **Dritt-Klassen-Sätze** `mediates_not_reversible` und
  `mediates_not_noreturn` legen St.4 beweisbar außerhalb **beider** Nachbarn —
  damit sind die drei Natur-Klassen **paarweise getrennt**. Der Zeuge ist
  wörtlich die **Summe der Nachbar-Zeugen**: `mediator := Sum.map swap Nat.succ`
  (links kreist die 20., rechts steigt die 23.); `mediator_mediates` läuft über
  zwei eigene punktweise Iterations-Helfer (Mathlib führt kein
  `Sum.map`-Iterations-Lemma) und konsumiert im Übrigen `swap_reversible` (22.,
  da `f^[2] x` defeq zu `f (f x)`) und `succ_noreturn` (23.). Orts-Sätze
  `interval_IV_start` (= 10) und `interval_IV_end` (= 14) — letzterer **Konsum
  des Zitat-Ankers** `nature_closes_at_14` (21.): die Natur schließt 14-wertig.
  Kür `swap_not_mediates` und `succ_not_mediates`: jede der drei Natur-Klassen
  hat einen Zeugen in genau ihrer Klasse. Kette 16→19→20→22→23→24, ein Import,
  kein Mathlib-Import über die transitive Hülle hinaus. **Hegel-Relativitäts-
  Marke:** „Organik = Intervall IV" ist Lesart der Hegel-Stufe, nicht Satz
  („ernsthafte Zweifel" Z. 921–922, „nur relativ" Z. 936–938).
  **Vermittlungs-Marke:** Günthers „vermitteln" betrifft wörtlich die
  **Werte-Struktur** (Zweiwertigkeit und Dreiwertigkeit) — Werte-Semantik,
  außerhalb dieses Baus; die Koexistenz-Lesart ist Deutung; **der Quanten-Sinn
  der Komplementarität (Weizsäcker, Scheibe; Lille Fn. 9 und Fn. 10) wird nicht
  formalisiert und nicht beansprucht**. Summen-Träger `Fin 2 ⊕ ℕ` Modellwahl;
  Designation ≠ Denotation gilt fort; kein Hebdomas-Vorgriff. **Bauform-These,
  dritte Einlösung:** eigener Gehalt in Schnitt-Leere, Dritt-Klassen-Sätzen und
  Helfern, Zeugen-Bau und Orts-Ende sind Konsum. Axiom-Ist je Satz
  `#guard_msgs`-verwacht (acht Wachen): Schnitt-Leere, beide Dritt-Klassen-Sätze
  und beide Orts-Sätze **axiom-frei**, `swap_not_mediates` `[propext]`,
  `mediator_mediates` und `succ_not_mediates` `[propext, Quot.sound]`
  (`omega`-Hülle). **Kein `Classical`** — auch der Nonempty-Satz nicht.
  **Profil-Rechnung vorab, sechs von acht getroffen:** der Vererbungs-Satz sagt
  `interval_IV_end` axiom-frei (Anker axiom-frei) und die succ-Konsumenten auf
  `omega`-Niveau korrekt voraus; die Dritt-Klassen-Sätze **unterbieten** die
  Erwartung `[propext]` (axiom-frei), weil nur `reversible_pointwise_periodic`
  einläuft, nicht die `decide`-Zeugen der 22. — Lehre: die Rechnung wird am
  Quell-**Satz** angesetzt, nicht an der Quell-Schicht. 0 Sorries.

- `Proemial.ContentReflexivity`: die Reflexivität der Inhalte (fünfundzwanzigste
  Schicht) — die **erste Geist-Stelle**: das fünfte Intervall, die „Reflexivität
  der Bewusstseinsinhalte" (Lille Z. 605–607, bestätigt Z. 804,
  Volltext-verifiziert), gefasst als **Hebung** (`reflect f := Set.image f` —
  derselbe Prozess auf seinen Inhalten; Mengen von Zuständen werden selbst
  Zustände). Das **Iterations-Gesetz** `reflect_iterate` (die gehobene Iteration
  ist die Iteration der Bilder) und der **Erbe-Satz** `reflect_reversible` (die
  Inhalte eines reversiblen Prozesses sind reversibel — der Umtausch der 22.
  hebt sich mit) tragen eigenen Beweis-Gehalt. Der **Kern-Satz**
  `reflect_ground_empty` („der leere Inhalt steht still" — ∅ ist Fixpunkt jeder
  Reflexion) trägt den **Bruch der Irreversibilität an den Inhalten**
  `reflect_not_noreturn` (Konsum von `noreturn_no_ground`, 23. — keine
  reflektierte Welt ist rückkehrfrei) und, als reine Delegation, den Zeugen-Satz
  `reflect_succ_not_noreturn` (die Stufung selbst wird an ihren Inhalten
  rückkehr-fähig). Orts-Sätze `interval_V_start` (= 15) / `interval_V_end`
  (= 20), Substrat-Abruf aus der 21.; Kür `reflect_monotone` (die Reflexion
  achtet die Inhalts-Ordnung). Kette 16→19→20→22→23→24→25, ein Import, kein
  Mathlib-Import über die transitive Hülle hinaus. **Marken-Trias (W1-F3,
  erstmals im Vollzug):** lokale Hegel-Relativitäts-Fassung (die Stufen-Zuordnung
  ist „eine vorläufige", Z. 811–816), Substrat-Erbe (das Rückgrat zählt, diese
  Schicht deutet), Monas-Struktur-Marke (ein positiver Wert, alle anderen seine
  Reflexionen, Z. 1015–1017 — Günthers Wort, jede Werte-Formalisierung außerhalb
  dieses Baus). **Verzichts-Marke:** der Hegel-Hintergrund (Enzyklopädie,
  Paragraph 387 folgend) ist benannt, nicht beigezogen. **Grenze:** Bewusstsein
  wird nicht formalisiert; Reflexivität als Hebung ist Deutung, „der leere Inhalt
  steht still" markierte Struktur-Aussage (kein Zitat); Set-Träger Modellwahl;
  Designation ist nicht Denotation. **Konstruktions-Merkmal (R1-Ist-geprüft):**
  `reflect : Set α → Set α` ist eine Konstruktion, keine Eigenschaft — die erste
  unter den fünf gebauten Stellen-Schichten [19./20./22./23./24.] mit
  Konstruktions- statt Eigenschafts-Merkmal (dort alle `: Prop`); die
  Bereichs-Qualifikation ist unverlierbar. Axiom-Ist je Satz
  `#guard_msgs`-verwacht (acht Wachen): `interval_V_start`, `interval_V_end` und
  die Kür `reflect_monotone` **axiom-frei**, die fünf Mengen-Sätze
  `[propext, Quot.sound]`. **Routen-Befund (Teil 0), zweifach classical-frei
  aufgelöst:** `Set.image_empty` und `Set.image_mono` tragen in diesem Mathlib
  `Classical.choice`; `reflect_ground_empty` geht darum über
  `Set.eq_empty_iff_forall_notMem`, die Kür über den Eigenbeweis statt
  `Set.image_mono` — **kein `Classical`** an keiner der acht Stellen. 0 Sorries.

- `Proemial.MediationProcess`: der Vermittlungsprozess (sechsundzwanzigste
  Schicht) — die **zweite Geist-Stelle**: das sechste Intervall, „der
  Subjektivität als Vermittlungsprozess gewidmet" (Lille Z. 805–806,
  Volltext-verifiziert). **Bauform-Entscheid: kein eigenes Merkmal** — die Stufe
  verortet `Mediates` (24.) auf dem `reflect`-Träger (25.); das Merkmal ist ganz
  Anschluss (die Bauform-These an ihrer reinsten Stelle, kein Definitions-Defizit;
  R1-Ist-geprüft: erste unter den sechs gebauten Stellen-Schichten
  [19./20./22./23./24./25.] ohne eigene Merkmals-Konstante). Das **Bahn-Gesetz**
  `reflect_singleton` (`(reflect f)^[n] {x} = {f^[n] x}`, Konsum von
  `reflect_iterate`) und der **Kern-Satz** `reflect_mediates_of_noreturn` („die
  Vermittlung entsteht in der Reflexion" — jeder rückkehrfreie Prozess vermittelt
  an seinen Inhalten: der leere Inhalt kehrt wieder, der Einer-Inhalt flieht)
  tragen eigenen Beweis-Gehalt; was die Natur-Stufe 4 als vorgefundene Koexistenz
  kennt, erzeugt die Geist-Stufe 6 aus der Reflexion. **Echter Dritter**
  `reflect_noreturn_not_reversible` (an beiden Sätzen keiner der Nachbarn; erste
  Hälfte ist `reflect_not_noreturn` der 25.). **Duett mit der 24.**
  `reflect_succ_mediates`: dieselbe Stufung, die unten nicht vermittelt
  (`succ_not_mediates`), vermittelt an ihren Inhalten (Anwendung des Kern-Satzes
  auf `succ_noreturn`). Orts-Sätze `interval_VI_start` (= 21) / `interval_VI_end`
  (= 27), Substrat-Abruf. Kür `reflect_reversible_not_mediates` (Kontrast: die
  Reflexion des Reversiblen vermittelt NICHT — die Vermittlung entsteht in der
  Reflexion genau des Irreversiblen). Kette 16→19→20→22→23→24→25→26, ein Import,
  kein Mathlib-Import über die transitive Hülle hinaus. **Marken-Trias (W1-F3):**
  lokale Hegel-Relativitäts-Fassung („eine vorläufige", Z. 811–816),
  Substrat-Erbe, Monas-Struktur-Marke (Z. 1015–1017, Günthers Wort;
  Werte-Formalisierung außerhalb). **Verzichts-Marke:** Hegel-Hintergrund benannt,
  nicht beigezogen. **Grenze:** Subjektivität wird nicht formalisiert;
  Vermittlungsprozess als gehobene Koexistenz ist Deutung, „die Vermittlung
  entsteht in der Reflexion" markierte Struktur-Aussage (kein Zitat); Set-Träger
  Modellwahl; Designation ist nicht Denotation. Axiom-Ist je Satz
  `#guard_msgs`-verwacht (sieben Wachen): `interval_VI_start`/`interval_VI_end`
  **axiom-frei**, die fünf Prozess-Sätze `[propext, Quot.sound]`. **Routen-Befund
  (Teil 0):** `Set.image_singleton` trägt in diesem Mathlib `Classical.choice`;
  `reflect_singleton` geht darum den Eigenbeweis (`Set.ext` +
  `Set.mem_singleton_iff`), die Singleton-Extraktion nutzt das reine
  `Set.singleton_injective` — **kein `Classical`** an keiner der sieben Stellen.
  Sieben von sieben Profilen der R2-Rechnung getroffen. 0 Sorries.

- `Proemial.SelfDetermination`: das Subjekt für sich (siebenundzwanzigste
  Schicht) — die **letzte Stelle** der achtfachen Thematik: das siebte Intervall,
  „der sich in sich bestimmende Geist … das Subjekt für sich, das sich ganz in
  seine private Einsamkeit zurückgezogen hat" (Lille Z. 807–810,
  Volltext-verifiziert). **Bauform-Entscheid: kein eigenes Merkmal** — die Stufe
  wendet die Hebung `reflect` (25.) auf sich selbst an, `reflect (reflect f)` auf
  `Set (Set α)` (zweiter Merkmals-freier Fall nach der 26.; R1-Ist-geprüft am
  Bestand). **Selbst-Anwendungs-Gesetz** `reflect_reflect_iterate` und **Ankommen
  der zweiten Hebung** `reflect_reflect_not_noreturn` sind reine Instanziierungen
  der 25. (der Sach-Befund der Stufe: „sich in sich" als ein Beweis-Term).
  Eigenen Beweis-Gehalt tragen der **Einsamkeits-Satz** `solitude_ground` („die
  Einsamkeit steht still" — `{∅}` ist Fixpunkt der zweiten Stufe: das Subjekt,
  ganz zurückgezogen, bei sich) und der **Fortsetzungs-Satz**
  `reflect_reflect_mediates_of_noreturn` („die Vermittlung setzt sich fort" —
  jeder rückkehrfreie Prozess vermittelt auch an den Inhalts-Inhalten: `{∅}` kehrt
  wieder, `{{x}}` flieht, `singleton_injective` zweifach; der Kern-Satz der 26.
  ist hier NICHT instanziierbar, denn `reflect f` ist gerade nicht rückkehrfrei).
  **Dritte Duett-Etage** `reflect_reflect_succ_mediates`: unten nicht vermittelnd
  (24.), an den Inhalten vermittelnd (26.), an den Inhalts-Inhalten vermittelnd
  (27.) — Anwendung auf `succ_noreturn`. Orts-Sätze `interval_VII_start` (= 28) /
  `interval_VII_end` (= 35), Substrat-Abruf. Kür `reflect_reflect_reversible`:
  der Umtausch erbt sich durch beide Hebungen (Doppel-Konsum von
  `reflect_reversible`). Kette 16→19→20→22→23→24→25→26→27, ein Import, kein
  Mathlib-Import über die transitive Hülle hinaus. **Marken-Trias (W1-F3):**
  lokale Hegel-Relativitäts-Fassung („eine vorläufige", Z. 811–816),
  Substrat-Erbe, Monas-Struktur-Marke (Z. 1015–1017, Günthers Wort;
  Werte-Formalisierung außerhalb). **Verzichts-Marke:** Hegel-Hintergrund benannt,
  nicht beigezogen. **Grenze:** Geist und Subjekt werden nicht formalisiert; „für
  sich" als zweite Stufe ist Deutung, „die Einsamkeit steht still" markierte
  Struktur-Aussage (kein Zitat); `Set (Set α)`-Träger Modellwahl; die **28 als
  vollkommene Zahl** von-Foerster-Beobachtung, benannter Posten, nicht gebaut;
  Designation ist nicht Denotation. Axiom-Ist je Satz `#guard_msgs`-verwacht (acht
  Wachen): `interval_VII_start`/`interval_VII_end` **axiom-frei**, die sechs
  Mengen- und Prozess-Sätze `[propext, Quot.sound]` — **kein `Classical`** (alles
  Konsum aus 25./26. plus dem rein gemessenen `Set.singleton_injective`); acht von
  acht Profilen der R2-Rechnung getroffen. 0 Sorries. **Der Reihen-Satz
  (R1-konform, Ist-geprüft über die acht Stellen): alle acht Stellen der
  achtfachen Thematik sind gebaut.**

- `Proemial.BranchingCoalgebra`: die Verzweigungs-Koalgebra (achtundzwanzigste
  Schicht) — **AP6-Fundament, kein Stellen-Bau** (kein Intervall-Anspruch, keine
  Orts-Sätze, keine Marken-Trias): neben der geschlossenen Stellen-Reihe tritt die
  Verzweigung als Set-Koalgebra `Branching α := α → Set α`, jedem Zustand seine
  Möglichkeiten. Der **Fluss** `flow` ist die auf Inhalte gehobene Koalgebra
  (setOf-Form `fun S => {b | ∃ a ∈ S, b ∈ c a}` per Teil-0-Routen-Entscheid: die
  `⋃`-Form läge außerhalb der Import-Hülle, die setOf-Form ist classical-frei,
  hüllen-treu und macht die Kür axiom-frei). Der **Anschluss-Satz** `flow_det`
  sagt wörtlich, dass die Geist-Reihe der gabellose Spezialfall war:
  `flow (det f) = reflect f` (`reflect` der 25. war die deterministische
  Verzweigung). Die **Miniatur** `fork_not_lifted` (ehrlich als solche, kein Rang
  neben den großen Differentialen): die Gabel `fork := fun _ => {0, 1}` ist von
  keiner Funktions-Hebung erzeugt — die Verzweigung übersteigt die Reflexion (am
  Einer-Inhalt liefert die Hebung Einer, die Gabel Zweier; `0 ≠ 1` per `decide`).
  Leichte Hälfte `deterministic_flow_lifted` (der Funktions-Zeuge wird
  durchgereicht). **Kollaps-Figur** `Collapses b a := b ∈ c a` mit
  `det_collapse_unique` (ohne Gabel genau ein Ausgang) und
  `fork_collapse_not_unique` (an der Gabel fällt die Eindeutigkeit); die
  Irreversibilität des Kollapses bleibt Deutungs-Anschluss, kein Satz. Kür
  `flow_monotone` (der Möglichkeits-Fluss achtet die Inhalts-Ordnung, axiom-frei).
  Kette 16→19→20→22→23→24→25→26→27→28, ein Import, kein Mathlib-Import über die
  transitive Hülle hinaus. **Quellen-Härten-Trennung:** die Chaos-Negation
  quellen-fest (A2-Bestand), ihre Anwendung Lesart; Möglichkeit → Kollaps →
  Aktualität Projekt-Rede (Gestalt §5); „eingefrorene Zufälle" extern, nur benannt
  (Cramer-Umfeld, nicht autopsiert). **Deutungs-Marken:** Set-Werte als
  Möglichkeiten Deutung; „über den Kontexturen" A5-Anbindung; kein Physik-Anspruch
  (Determinismus und Indeterminismus als Struktur-Begriffe); Designation ist nicht
  Denotation. Konstruktions-Entscheid: `Deterministic` in Funktions-Fassung
  (punktweise wäre choice-pflichtig). Axiom-Ist je Satz `#guard_msgs`-verwacht
  (sechs Wachen): `det_collapse_unique` und die Kür `flow_monotone` **axiom-frei**,
  `fork_collapse_not_unique` `[propext]`, die drei Set-ext-Sätze
  `[propext, Quot.sound]` — **kein `Classical`**; Vormessung beider Fluss-Formen
  classical-frei, die setOf-Wahl ist Hüllen-Treue (R1: kein Rang erhoben). 0
  Sorries.

- `Proemial.FlowIteration`: der Iterations-Fluss (neunundzwanzigste Schicht) —
  **AP6-Zug-2, reiner Term-Zug** (kein Stellen-Bau): auf dem Fundament der 28.
  macht die Erreichbarkeits-Menge `reachSet c n a := (flow c)^[n] {a}` das
  Langzeit-Verhalten der Verzweigung messbar. **Iterierter Anschluss**
  `flow_iterate_det` (`(flow (det f))^[n] S = f^[n] '' S`, Umschreibung via
  `flow_det` plus Iterations-Gesetz der 25.). **Bahn gegen Sättigung** als
  iterierte Miniatur der 28.: `det_reach` (ohne Gabel bleibt die Möglichkeit Einer
  für alle Zeit, `reachSet (det f) n a = {f^[n] a}`) gegen `fork_reach` (die Gabel
  sättigt in einem Schritt und die Sättigung bleibt, `reachSet fork n a = {0, 1}`
  für `0 < n`), getragen vom Sättigungs-Lemma `fork_flow_full` (auf bewohntem
  Inhalt füllt die Gabel den Raum). Kür `flow_iterate_monotone` (der iterierte
  Fluss achtet die Inhalts-Ordnung, Induktion über die 28.-Kür). **NAMENS-MARKE:**
  `reachSet` ist die Erreichbarkeits-Menge der Koalgebra, ohne Beziehung zur
  Reichweiten-Disziplin des Hauses (Struktur- gegen Methoden-Begriff). „Bahn" und
  „Sättigung" markierte Struktur-Aussagen; kein neuer Differential-Anspruch, kein
  Physik-Anspruch; Designation ist nicht Denotation. Kette 16→…→28→29, ein Import,
  kein Mathlib-Import über die transitive Hülle hinaus. Der **Ketten-Satz** ist
  benannt, nicht gebaut (Kandidat Zug 3). Mit diesem Zug ist der **Sammelposten
  der 28. geheilt** (doc-only: `flow_singleton` ist öffentlicher, vom
  Iterations-Fluss konsumierter Helfer). Axiom-Ist je Satz `#guard_msgs`-verwacht
  (fünf Wachen): alle fünf `[propext, Quot.sound]` — **kein `Classical`**;
  Vormessung `Function.iterate_succ_apply'` ergab `[propext, Quot.sound]` (nicht
  axiom-frei), darum die Kür im propext-Bereich statt axiom-frei (ehrliche
  Abweichung, keine Verschärfung). 0 Sorries.

- `Proemial.CoalgebraMorphism`: die Koalgebra-Morphismen (dreißigste Schicht) —
  **AP6-Zug-3, reiner Term-Zug** (kein Stellen-Bau): der Morphismus zwischen
  Verzweigungen als **Bild-Vertauschung** `IsMorphism h c d := ∀ a, h '' c a =
  d (h a)` (strikte Fassung; die laxe `⊆`-Variante benannt, nicht gebaut).
  Identität `morphism_id` und Komposition `morphism_comp` (Konsum der
  classical-freien Bild-Lemmata `Set.image_id`/`Set.image_comp`, per Vormessung).
  **Haupt-Satz** `morphism_flow` („der Fluss ist morphismus-treu":
  `h '' flow c S = flow d (h '' S)` — die punktweise Bedingung hebt sich auf die
  Inhalte, das Hebungs-Motiv der Geist-Reihe zwischen zwei Koalgebren, Eigenbeweis
  auf den setOf-Routen der 28.). **Zeuge** `det_selfmorphism` (Selbst-Äquivarianz:
  jede Funktion ist Morphismus ihrer eigenen deterministischen Verzweigung — reine
  Konsum-Zeile am Defeq, `reflect_singleton` der 26. am Punkt). Kür `morphism_reach`
  („die Bahnen-Verpflanzung": `h '' reachSet c n a = reachSet d n (h a)`, Induktion
  über den Haupt-Satz; Basis heterogenes Einer-Bild per privatem Helfer
  `image_singleton_het`, Eigenbeweis statt des `Classical`-tragenden
  `Set.image_singleton`). **Abgrenzungs-Marke:** elementare kategoriale Rede, kein
  Apparat — **kein Kategorien-Framework, kein Konsum des F1-Coalgebraic-Massivs**;
  keine Kategorie als Objekt. `reflect`-Verwandtschaft benannt (endo gegen
  allgemein: für heterogenes `h` tritt `Set.image h` direkt an). Kette 16→…→29→30,
  ein Import, kein Mathlib-Import über die transitive Hülle hinaus. Der
  **Ketten-Satz** bleibt benannt, nicht gebaut (nach den Morphismen schöner: Ketten
  unter Morphismen-Bildern erhalten); die **Kontextur-Faserung ist Zug 4, der
  AP6-Schluss**. Axiom-Ist je Satz `#guard_msgs`-verwacht (fünf Wachen): alle fünf
  `[propext, Quot.sound]` — **kein `Classical`** (die Bild-Lemmata `image_id` und
  `image_comp` sind gemessen classical-frei). 0 Sorries.

- `Proemial.ContexturalFibration`: die Kontextur-Faserung (einunddreißigste
  Schicht) — **AP6-Zug-4, der Schluss** (reiner Term-Zug, kein Stellen-Bau): der
  gefaserte Träger `ι × α` (jeder Zustand trägt seinen Kontextur-Index) und die
  **Faser-Treue** `FiberPreserving c := ∀ i a, ∀ p ∈ c (i, a), p.1 = i` als
  strukturelle **Schwester der Diskontexturalität** (Deutung, markiert; die
  Setzung des F-Strangs wird nicht konsumiert, nicht behauptet). **Haupt-Satz**
  `fiber_emb_morphism` (bei Faser-Treue ist die Einbettung `emb i := (i, ·)` ein
  Koalgebra-Morphismus — Konsum der 30. `IsMorphism`). „Kein Kollaps kreuzt"
  `fiber_preserving_no_crossing` (Faser-Treue in der Kollaps-Sprache der 28.
  `Collapses`, reine Anwendung, axiom-frei). Der **Springer** `hopper := fun _ =>
  {(1, 0)}` mit `crossing_not_fiber_preserving` (die Bedingung ist echt, keine
  Tautologie). Der det-Anschluss `detFam_fiber_preserving` (axiom-frei) und der
  **Familien-Bogen** `fiber_detFam` (`fiber (detFam F) i = det (F i)`, Schluss zur
  28.). Kür `reach_stays_in_fiber` („die Bahn verlässt die Kontextur nie": jede
  erreichbare Möglichkeit liegt in der Start-Kontextur — Konsum der 29. `reachSet`).
  **Der Schluss konsumiert die drei Vorgänger-Begriffe in je einem eigenen Satz
  (Begriffs-, kein Satz-Konsum; am 28.-Begriff nominell — der substanzielle
  Rückgriff ist der Familien-Bogen)** (28.
  `Collapses`, 29. `reachSet`, 30. `IsMorphism`). Kette 16→…→30→31, ein Import,
  kein Mathlib-Import über die transitive Hülle hinaus. **Reichweiten-Marke:**
  Kontextur-Benennung Deutung (A5-Anbindung mit Term); Diskontexturalität als
  Faser-Treue markiert (Setzung nicht konsumiert); Transjunktions-Anschluss
  benannt, kein Satz; Produkt-Träger Modellwahl (abhängige Faserung benannter
  Folge-Posten); kein Physik-Anspruch; Designation ist nicht Denotation. Axiom-Ist
  je Satz `#guard_msgs`-verwacht (sechs Wachen): `fiber_preserving_no_crossing` und
  `detFam_fiber_preserving` **axiom-frei**, `crossing_not_fiber_preserving`
  `[propext]`, die drei Set-ext-Sätze `[propext, Quot.sound]` — **kein `Classical`**;
  Prod-Vormessung: eta-Defeq trägt (`p = (p.1, p.2)` ist `rfl`, axiom-frei), kein
  Prod-Lemma nötig. 0 Sorries. **Mit dieser Schicht ist AP6 geschlossen.**

- `Proemial.StageAggregation`: die Anwendungsbrücke (E4) — **BENENNUNG, kein
  Ertrag**: der Anwendungssatz `agg_nicht_erzeugbar` ist eine INSTANZ von E3
  (`locally_classical_in_clone_iff` bei m = 4); neu sind allein die Daten (der
  Zeuge `agg`, zwei Widerlegungspunkte), nicht der Satz. Lesart: `Fin 4` als vier
  linear geordnete Autorisierungsstufen, `agg` als Aggregationspolitik
  (konservativ = `min`, außer zwischen den beiden höchsten Stufen, dort permissiv
  = `max`), ein Term über `L` als Verschaltung lokaler, kontextur-blinder Prüfer
  (intra-kontexturell, `Definitionen.md` §9) — eine in verschiedenen
  Stufenbereichen verschieden aggregierende Politik ist aus solchen Prüfern nicht
  zusammensetzbar. Robustheit nach CLAUDE.md §9: `agg_nicht_erzeugbar_konstanten`
  über `constant_clone_min_or_max` — auch mit BELIEBIGEN KONSTANTEN Prüfern als
  Bausteinen bleibt `agg` unkomponierbar (`R 4` reflexiv). **Anwendungsschwelle
  vier Stufen:** bei m = 3 wäre der Satz falsch (E1, vier der acht Wahlmuster
  erzeugbar) — vier ist die erste Wertzahl, ab der JEDE echt gemischte
  lokal-klassische Politik unkomponierbar ist. **Grenze im Begriff, nicht im
  Beweis:** `{x,y}` ist unter `min`/`max` genau dann abgeschlossen, wenn `x,y`
  vergleichbar sind — nur dann ist die Zweiermenge eine Elementarkontextur
  (`Definitionen.md` §2); auf nicht-linearen Verbänden fällt die Charakterisierung
  (bereits am kleinsten flachen Verband `M3` — bewiesen in `M3CloneWitness`,
  `m3_mixed_term_exists`; die Klon-Zählungen der Sondierung bleiben außerhalb des
  Korpus). Ein Übergangsgraph benannter Rollen ohne
  Stufenordnung wird von dieser Schranke NICHT getragen. Wortlaut-Grenzen: keine
  Behauptung über AI-Systeme (Anwendungsannahme, keine Folgerung), keine
  Sicherheitsgarantie; Marke 3 unverändert (`StageAggregation`, nicht
  `Mediation`). Drei Statement-Pins; Axiom-Ist je Satz `#guard_msgs`-verwacht
  (drei Wachen): `agg_lokal` `[propext]`, die beiden Schranken-Sätze
  `[propext, Quot.sound]` — **kein `Classical`**. 0 Sorries.

- `Proemial.PolicyCheck`: die zweite Anwendung (Werkzeug-Freigabepolitik) —
  **BENENNUNG, kein Ertrag**: beide Schranken-Sätze sind INSTANZEN von E3
  (`freigabe_nicht_erzeugbar` die `mp`-Richtung von
  `locally_classical_in_clone_iff` bei m = 4, `freigabe_nicht_erzeugbar_konstanten`
  die Konstanten-Fassung `constant_clone_min_or_max`); neu sind allein die Daten
  (die Politik `freigabe`, zwei Widerlegungspunkte) und die Lesart. Lesart:
  `Fin 4` als vier Freigabestufen `0 blocked < 1 needs_review < 2 approved <
  3 privileged` (Namen sind Lesart, term-fest ist `Fin 4`), `freigabe` als
  Freigabepolitik — permissiv (`max`) nur zwischen den beiden NIEDRIGSTEN Stufen,
  sonst konservativ (`min`): was `blocked` und `needs_review` zusammenführt, fällt
  nicht still auf `blocked`, sondern steigt zur Prüfung. **Andere Mischstelle als
  `StageAggregation`: unten statt oben** — punktweise verschieden an genau vier
  Stellen (`(0,1)`, `(1,0)`, `(2,3)`, `(3,2)`). Zweck ist der ZWEITE KONSUMENT
  desselben generischen Satzes (der Beleg, dass die Schranke nicht an der
  Mischstelle von `StageAggregation` hängt), ausdrücklich KEINE zweite Quelle: kein
  Satz-Statement wiederholt eine Aussage des Bestands. Robustheit nach CLAUDE.md
  §9: die Invariante des konsumierten Satzes ist `R 4`, reflexiv (`R_diag`), darum
  überlebt die Schranke alle vier Konstanten — ein konstanter Prüfer („liefere
  immer approved") ist der natürlichste Baustein einer Freigabepolitik.
  Anwendungsschwelle vier Stufen (bei m = 3 wäre der Satz falsch, E1) als Verweis,
  nicht als Wiederholung. Wortlaut-Grenzen:
  **keine Sicherheits-, Rechts-, Wahrheits- oder Retrievalgarantie**;
  keine Behauptung über AI-Systeme
  (Anwendungsannahme, keine Folgerung); die Schranke trägt nur auf linear
  gestuften Trägern (M3-Grenze, Doc-String von `StageAggregation`); Marke 3
  unverändert — der Name nennt den Anwendungsgegenstand, nicht einen bewiesenen
  Vermittlungs- oder Sicherheitsgehalt (Rückfallname `ToolAuthorization`). Drei
  Statement-Pins; Axiom-Ist je Satz `#guard_msgs`-verwacht (drei Wachen):
  `freigabe_lokal` `[propext]`, die beiden Schranken-Sätze
  `[propext, Quot.sound]` — **kein `Classical`**. 0 Sorries.

- `Proemial.RAGAuthority`: die dritte Anwendung (Quellenautorität für Retrieval) —
  **BENENNUNG, kein Ertrag**: beide Schranken-Sätze sind INSTANZEN von E3
  (`autoritaet_nicht_erzeugbar` die `mp`-Richtung von
  `locally_classical_in_clone_iff` bei m = 4, `autoritaet_nicht_erzeugbar_konstanten`
  die Konstanten-Fassung `constant_clone_min_or_max`); neu sind allein die Daten
  (die Politik `autoritaet`, zwei Widerlegungspunkte) und die Lesart. Lesart:
  `Fin 4` als vier Autoritätsstufen `0 Notiz < 1 Teamdokument < 2 Policy <
  3 Gesetz` (Namen sind Lesart, term-fest ist `Fin 4`; Skala aus
  `PKL-Anwendungsfaelle.md` §2), `autoritaet` als Autoritätspolitik — die
  schwächere Quelle zählt (`min`), mit der einen Ausnahme des internen
  Governance-Korridors: wo Teamdokument und Policy kollidieren, gilt der Vorrang
  der Policy (`max` auf `{1,2}`). **Mischstelle MITTE: der dritte Zeuge nach
  `PolicyCheck.freigabe` (unten, `{0,1}`) und `StageAggregation.agg` (oben,
  `{2,3}`)** — die Schranke hängt an der Mischung, nicht am Ort der Mischstelle.
  Punktweise verschieden von `agg` an `(1,2)`, `(2,1)`, `(2,3)`, `(3,2)` und von
  `freigabe` an `(0,1)`, `(1,0)`, `(1,2)`, `(2,1)`; das ist Definitionsbefund und
  KEIN Satz — kein Vergleichssatz im Korpus, keine zweite Quelle. Robustheit nach
  CLAUDE.md §9: die Invariante des konsumierten Satzes ist `R 4`, reflexiv
  (`R_diag`), darum überlebt die Schranke alle vier Konstanten — ein konstanter
  Prüfer („diese Quelle gilt immer als Policy") ist der natürlichste Baustein.
  Anwendungsschwelle vier Stufen (bei m = 3 wäre der Satz falsch, E1) als Verweis,
  nicht als Wiederholung. Wortlaut-Grenzen:
  **keine Sicherheits-, Rechts-, Wahrheits- oder Retrievalgarantie**;
  Autorität ist nicht Evidenz (der Satz sagt nichts über die Wahrheit von
  Quellinhalten); keine Behauptung über RAG-Systeme (Anwendungsannahme, keine
  Folgerung); die Schranke trägt nur auf linear gestuften Trägern, gleichrangige
  Quellen ohne Stufenachse werden nicht getragen (M3-Grenze, Doc-String von
  `StageAggregation`); Marke 3 unverändert — der Name nennt den
  Anwendungsgegenstand, nicht einen bewiesenen Retrieval- oder Wahrheitsgehalt
  (Rückfallname `SourceAuthority`). Drei Statement-Pins; Axiom-Ist je Satz
  `#guard_msgs`-verwacht (drei Wachen): `autoritaet_lokal` `[propext]`, die beiden
  Schranken-Sätze `[propext, Quot.sound]` — **kein `Classical`**. 0 Sorries.

- `Proemial.ContextureOverlap`: die Überlappungsrelation des Kontexturengitters
  **satzförmig** (ERTRAG, klein). `elem_contexture_overlap_le_one` — je zwei
  verschiedene Elementarkontexturen (Zweiermengen über `Fin m`) überlappen in
  höchstens einem Wert; `three_contextures_overlap` — die drei `Fin 3`-Kontexturen
  paarweise in genau dem geteilten Wert, prädikativ (`a = x ∨ a = y` wie
  `LocallyClassical`) und darum `Classical`-frei. Schließt die Kontexturgrenze auf
  dem wertbasierten Kontextur-Begriff der D/E-Reihe, **ohne** Setzung. Zwei Wachen
  (`[propext, Quot.sound]` / `[propext]`), 0 Sorries.
- `Proemial.RegimeThreshold`: der Schwellensatz (ERTRAG).
  `regime_threshold_at_four` bindet Wert-Aufstieg und Nicht-Erzeugbarkeit an dem
  einen Ort echter Verbindung — dem Schritt `m = 3 → 4`: eine gemischte
  lokal-klassische Operation ist bei `m = 3` erzeugbar (E1,
  `pattern_max_min_min_in_clone`), bei `m = 4` nicht (E3,
  `locally_classical_in_clone_iff`). Qualitativer Regimewechsel, kein Zähler.
  Konsumiert nur Aggregat-Inhalt. Grenze: fällt auf `M3`/Verbundgitter — bewiesen
  in `M3CloneWitness` (`m3_mixed_term_exists`). Eine Wache
  (`[propext, Quot.sound]`), 0 Sorries.
- `Proemial.ElementaryCycle`: die Elementarkontextur als **Zweierbahn einer
  Involution** (ERTRAG). `card_orb_le_two` — jede Bahn einer Involution hat
  höchstens zwei Elemente (in dieser Darstellung Spezialisierung von Mathlibs
  `isPeriodicPt_iff_minimalPeriod_dvd`, wie `minimalPeriod_dvd_two`);
  `isElemContexture_orb_iff` — die Bahn durch `x` ist genau dann eine
  Elementarkontextur, wenn `x` kein Fixpunkt ist; `exists_involutive_orb_eq` —
  der tragende Teil: **jede** Elementarkontextur ist als Bahn realisiert, an der
  Transposition. Damit ist der Zyklusbegriff (`Definitionen.md` §2/§14) an den
  wertbasierten Kontexturbegriff der D/E-Reihe gebunden, ohne freistehende
  Zyklentheorie und ohne Setzung. Der Selbstzyklus trägt keinen eigenen Satz: er
  ist der Zweig, der die Dichotomie erschöpfend macht. Sieben Wachen, Profil
  durchgängig `[propext, Classical.choice, Quot.sound]` — externer Träger über
  `Function.minimalPeriod`; die Involutionsaussage `isPeriodicPt_two` davor zieht
  nur `[Quot.sound]`. 0 Sorries.

- `Proemial.ContextureEscapeBound`: das **Zeugnis mit Menge und Punkt** (ERTRAG).
  `not_in_clone_of_escapes` — allgemein über jeder Sprache, jeder Struktur und
  jeder Substruktur: verlässt eine Operation eine abgeschlossene Menge an einem
  angebbaren Punkt, so ist sie kein Term über der Signatur; die Voraussetzung
  nennt die Menge **und** den Punkt. `contexture03` und `contexture12` heben die
  Bauform von `TransjunctionCloneBound` auf `Fin 4` (die zwei nichttrivial
  abgeschlossenen Mengen, exhaustiv über alle 16 Teilmengen gemessen);
  `avgDown_not_in_clone` instanziiert am abgerundeten Durchschnitt, der `{0,3}`
  am Punkt `(0,3)` verlässt. `locallyClassical_preserves_both` setzt die zwei
  Zeugnisse des Bestandes zueinander: jede lokal klassische Operation erhält
  beide Kontexturen, trägt also nie ein Zeugnis dieser Art. **Hinreichend, nicht
  notwendig** — das Fehlen eines Punktes ist kein Zeugnis für Erzeugbarkeit.

- `Proemial.TowerAsymmetry`: der **Verbindungssatz der asymmetrischen
  Diskontexturalität**, aus `Proemial.TowerAsymmetryProbe` gehoben (die Sonde
  bleibt byte-unverändert als historischer Beleg). Über der kumulierten
  Stufenskala `Tower := Σ n, RGS n` und dem kanonischen Schritt `step` bindet
  `tower_asymmetric` die drei Merkmale, die Günthers asymmetrische
  Diskontexturalität zugleich verlangt, in **einem** Satz: `step_noreturn`
  (Richtung, geerbt aus `noreturn_of_strict_rank`), `step_preserves_substructure`
  (die alte Kette bleibt Präfix, definitional) und `ascent_not_determined`
  (über jedem `r : RGS n` mit `n ≥ 1` liegen zwei verschiedene Urbilder unter
  `descent` — der einzige der drei mit eigenem Gehalt, und die Verallgemeinerung
  von `Kenogram.fiber_nontrivial` auf alle Stufen ab 1). Konsum aus
  `Kenogram.Descent` und `Proemial.IrreversibleAdvance`, kein Nachbau. Vier
  Wachen, Profil durchgängig `[propext, Quot.sound]`. **Die Stufenachse ist die
  Stellenzahl, nicht Günthers Relationsordnung; kein Satz dieser Datei trägt
  einen §20-Anspruch, und „RGS-Stufe = Kontextur" bleibt Setzung.**

Weitere Proemial-Belegungen (F-5, etc.) werden als Sub-Module hier eingehängt.
-/
