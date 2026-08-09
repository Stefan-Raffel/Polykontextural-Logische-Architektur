# Definition-Ledger — die Begriffe von `Definitionen.md` und ihre Träger im Korpus

Diese Tabelle ordnet jedem Begriff der Vorlage `Definitionen.md` den Träger im Lean-Korpus
zu — oder hält fest, dass es keinen gibt. Sie ist Ledger Rev. 19.

**Woher die Vorlage kommt.** `Definitionen.md` ist eine projektinterne Arbeitsfassung der
Begriffe aus Günther (1970), (1968) und (1971); sie ist **nicht veröffentlicht**. Massgeblich
sind die dort genannten Quellen und nicht die Fassung; dieser Ledger führt Träger und Grenzen,
nicht den Wortlaut. Die Fassung zieht drei Texte zusammen, wählt aus und paraphrasiert, zählt
die Paragraphen selbst und trägt in §3 einen dokumentierten Off-by-one gegenüber der Bauform
des Korpus — siehe **Grenznotiz A**.

**Alle Kennzahlen dieser Datei beziehen sich auf den Commit `5e1f30e`.** Ein Bau-Zug macht
jede ausgestellte Zahl still veraltet; darum trägt sie hier ihren Stand.

**Die Trägerspalte wird beim Bau geprüft.** `Reformulation/Proemial/DefinitionLedger.lean`
hält jeden Namen dieser Tabelle gegen die Aggregatumgebung (R1) und den Trägerstatus gegen
die Deklarationsart (R2); ein falscher Name oder ein falscher Status bricht `lake build` und
nennt die Zeilen-ID. R3 bis R8 sind Textprüfungen in `doc_lint.sh`, angesetzt auf diese
Datei.

## Bauzustand

Diese Tabelle führt keine Bau-Kennzahlen. Sie führte bis `9c48adc` vier — geprüfte
Konstanten, Wachen geschrieben und erzwungen, ausgewiesene Lücken —, und keine davon
stützte eine ihrer Spalten: R1 prüft Namen gegen die Aggregatumgebung, R2 die
Deklarationsart, die Wachenspalte trägt Profile je Zeile und keine Summe. Der laufende
Stand steht im `README.md`, der Gate-Stand in der `AxiomGate`-Zeile des Baus.

Alle Träger dieser Tabelle liegen im Aggregat; dass R1 sie dort auflöst, prüft der Bau
bei jedem Lauf. Dass ihre Wachen auch erzwungen sind, prüft heute keine Route — der
Posten ist benannt (Hüllensonde, `Vorgang4b_Kopf_und_Huelle_Befund.md` §4).

## Selbstauskunft der Tabelle, mit Route

Route: `grep -cE '^\| (L[0-9]{2}-[0-9]+) \|' docs/definition-ledger.md`

| | Wert |
|---|---:|
| Zeilen gesamt | 110 |
| Zeilen mit Träger | 96 |
| verschiedene Trägernamen | 88 |
| TS `Theorem` | 72 |
| TS `Definition` | 23 |
| TS `Setzung` | 1 |
| TS `Offen` | 14 |
| Paragraphen von `Definitionen.md` | 19 von 20 |

**Fünf** Träger erscheinen in mehr als einer Zeile — `CO.three_contextures_overlap` (3×),
`GCB.locally_classical_in_clone_iff` (4×), `NUCB.W_not_in_clone`, `TCB.T_not_in_clone` und
`TCB.T_rejective` (je 2×). Das sind **acht** überzählige Zeilen, daher 96 Zeilen bei 88
Namen. Das ist Redundanz mit Absicht: die Bindung ist die Zeilen-ID, nicht der Name.

**Warum „19 von 20": §20 (Proemialrelation) ist ein Quellenparagraph, für den der Korpus
keinen formalen Träger beansprucht.** Das ist die Statuslage und keine Lücke, die zu füllen
wäre — eine Zeile dort wiese ihren Träger als Träger des Begriffs aus, und genau das
bestreiten die Deutungsgrenzen der Module, die an der Stelle arbeiten
(`Kenogram/OccupancySeparation.lean`). Die Träger, die aus der Quellenstelle des §20
hervorgegangen sind, stehen unter §16, wo die Wertbesetzungs-Linie liegt: L16-17 bis
L16-19. Entschieden in der Abnahme zum Trennsatz-Zug (9. August 2026).

*Berichtigung (Ledger Rev. 9):* bis Rev. 8 stand hier „Acht Träger erscheinen in mehr als
einer Zeile". Die Acht ist die Differenz `Zeilen mit Träger − verschiedene Namen`, also die
Zahl der überzähligen Zeilen, nicht die Zahl der mehrfach auftretenden Träger; die ist fünf
und war es auch schon in Rev. 8. Gemessen über die Zeilenroute oben mit Häufigkeitszählung
je Trägername.

## Schema

- **Trägerstatus (TS)** — was ist das Lean-Objekt?
  - `Theorem` — `thmInfo`, Schluss nicht `True`.
  - `Definition` — `defnInfo`; umfasst `def`, `abbrev`, `instance`. Eine `structure` ist
    `inductInfo` und wird nicht akzeptiert; tritt eine als Träger auf, bricht der Bau, und
    der Fall wird ausdrücklich entschieden.
  - `Setzung` — eine Deklaration, deren Typ nach Auflösung aller Binder auf `True`
    schließt. An der Deklarationsart von `Theorem` nicht zu unterscheiden, am Schluss des
    Typs schon. Dies ist dasselbe Kriterium, an dem `CLAUDE.md` §10 hängt.
  - `Offen` — kein Träger.
- **Zuordnungsstatus (ZS)** — wofür steht der Träger? `Operationalisierung`, `Benennung`,
  `Deutung`, `Setzung`, `Offen`. Redaktionell, nie prüfbar.
- **Wache** — `ja` mit Profil verbatim, oder `keine` mit Grund.

**Prüfregeln:** R1 Träger löst gegen die Aggregatumgebung auf · R2 TS stimmt mit der
Deklarationsart überein · R3 kein ZS `Theorem` · R4 TS `Offen` erzwingt leere Trägerspalte ·
R5 alle 19 Paragraphen vertreten (die 19 ist die Statuslage, nicht eine vergessene
Obergrenze — siehe „Warum 19 von 20" oben) · R6 TS `Theorem` erzwingt ausgefüllte
Wachenspalte ·
R7 jede Trägerzeile der Tabelle hat genau eine passende Referenz in
`Reformulation/Proemial/DefinitionLedger.lean` — und umgekehrt · R8 jede Zeilen-ID kommt in
beiden Dateien genau einmal vor.

R1 und R2 werden von `Reformulation/Proemial/DefinitionLedger.lean` beim Bau geprüft; R3 bis
R8 sind Textprüfungen in `doc_lint.sh`.

**Zur Lesart der Profile.** `[propext, Quot.sound]` ist bei omega-getragenen Beweisen
Eigenschaft der Taktikhülle. `[propext, Classical.choice, Quot.sound]` ist bei den
Bahnaussagen Eigenschaft des Bahnbegriffs, nicht des Satzes — gemessen an
`EC.isPeriodicPt_two`, das dieselbe Involutionsaussage ohne Bahnbegriff trägt und nur
`[Quot.sound]` zieht. Eine Wache ist Driftschutz, keine Ertragsmarke.

## Namensraum-Kürzel

Die Spalte „Art" nennt, woraus das Präfix besteht. Ihr Fehlen in Rev. 4 war die Ursache
beider Fehlexpansionen.

| Kürzel | Expansion | Art |
|---|---|---|
| `TCB.` | `Reformulation.Proemial.TransjunctionCloneBound.` | Namensraum |
| `NUCB.` | `Reformulation.Proemial.NonUniformCloneBound.` | Namensraum |
| `GCB.` | `Reformulation.Proemial.GeneralCloneBound.` | Namensraum |
| `RelInv.` | `Reformulation.Proemial.RelabelInvariance.` | Namensraum |
| `QCB.` | `Reformulation.Proemial.QuaternaryCloneBound.` | Namensraum |
| `SA.` | `Reformulation.Proemial.StageAggregation.` | Namensraum |
| `PC.` | `Reformulation.Proemial.PolicyCheck.` | Namensraum |
| `RA.` | `Reformulation.Proemial.RAGAuthority.` | Namensraum |
| `CO.` | `Reformulation.Proemial.ContextureOverlap.` | Namensraum |
| `CC.` | `Reformulation.Proemial.CompoundContexture.` | Namensraum |
| `PM.` | `Reformulation.Proemial.PairwiseMixture.` | Namensraum |
| `DS.` | `Reformulation.Proemial.Discontextural.DiscontexturalStratification.` | Namensraum **plus Struktur** |
| `CF.` | `Reformulation.Proemial.ContexturalFibration.` | Namensraum |
| `RT.` | `Reformulation.Proemial.RegimeThreshold.` | Namensraum |
| `IB.` | `Reformulation.Proemial.IntervalBackbone.` | Namensraum |
| `EC.` | `Reformulation.Proemial.ElementaryCycle.` | Namensraum |
| `K.` | `Reformulation.Kenogram.` | Namensraum |
| `KM.` | `Reformulation.Kenogram.Morphogram.` | Namensraum |
| `KF.` | `Reformulation.Kenogram.Fillability.` | Namensraum |
| `KFib.` | `Reformulation.Kenogram.Fiber.` | Namensraum |
| `KU.` | `Reformulation.Kenogram.Unbounded.` | Namensraum |
| `KOS.` | `Reformulation.Kenogram.OccupancySeparation.` | Namensraum |
| `KPS.` | `Reformulation.Kenogram.PairStageBound.` | Namensraum |
| `CEB.` | `Reformulation.Proemial.ContextureEscapeBound.` | Namensraum |
| `SAsc.` | `Reformulation.Proemial.StageAscent.` | Namensraum |
| `SPar.` | `Reformulation.Proemial.StageParity.` | Namensraum |
| `CV.` | `Reformulation.Proemial.ChoiceVectors.` | Namensraum |

## Die Tabelle

| ID | Begriff (§) | Träger | TS | ZS | Wache | Grenze |
|---|---|---|---|---|---|---|
| L01-1 | Kontextur (§1) | `TCB.S` | Definition | Operationalisierung | keine (def) | Substruktur `{0,2}`, signaturrelativ; kein Totalzusammenhang |
| L01-2 | Kontextur (§1) | `NUCB.PreservesPair` | Definition | Operationalisierung | keine (def) | Erhaltung eines Zweierbereichs, nicht Geschlossenheit im Quellsinn |
| L01-3 | Kontextur (§1) | `NUCB.ContextureFaithful` | Definition | Operationalisierung | keine (def) | Treue gegenüber allen drei Zweierbereichen auf `Fin 3` |
| L01-4 | Kontextur (§1) | `CF.fiber_emb_morphism` | Theorem | Deutung | ja, `[propext, Quot.sound]` | Faserung als Kontexturindex ist laut Modul-Doc selbst Deutung |
| L01-5 | Kontextur (§1) | — | Offen | Offen | — | `ContextureIndex` existiert nicht; Programm nach Plan §7 Ansatz D |
| L01-6 | Kontextur (§1) | — | Offen | Offen | — | `ContextureSite` existiert nicht; Programm nach Plan §7 Ansatz D |
| L01-7 | Kontextur (§1) | — | Offen | Offen | — | `ContextureComponent` existiert nicht; Programm nach Plan §7 Ansatz D |
| L02-1 | Elementarkontextur (§2) | `CO.IsElemContexture` | Definition | Operationalisierung | keine (abbrev) | Zweiermenge als `Finset`, Kardinalität 2 |
| L02-2 | Elementarkontextur (§2) | `CO.three_contextures_overlap` | Theorem | Operationalisierung | ja, `[propext]` | prädikativ, `Fin 3`; Überlappung in genau einem Wert |
| L02-3 | Elementarkontextur (§2) | `CO.elem_contexture_overlap_le_one` | Theorem | Operationalisierung | ja, `[propext, Quot.sound]` | allgemein über `Fin m`, nur obere Schranke |
| L02-4 | Elementarkontextur (§2) | `GCB.ActsAsMin` | Definition | Operationalisierung | keine (def) | generisch in `m`; `NUCB.ActsAsMin` ist eine andere Deklaration |
| L02-5 | Elementarkontextur (§2) | `GCB.ActsAsMax` | Definition | Operationalisierung | keine (def) | dito |
| L02-6 | Elementarkontextur (§2) | `EC.card_orb_le_two` | Theorem | **Benennung** | ja, `[propext, Classical.choice, Quot.sound]` | Bahn einer Involution hat höchstens zwei Elemente; Spezialisierung von Mathlibs `isPeriodicPt_iff_minimalPeriod_dvd` |
| L02-7 | Elementarkontextur (§2) | `EC.isElemContexture_orb_iff` | Theorem | Operationalisierung | ja, `[propext, Classical.choice, Quot.sound]` | Bahn ist Elementarkontextur genau dann, wenn `x` kein Fixpunkt ist |
| L02-8 | Elementarkontextur (§2) | `EC.exists_involutive_orb_eq` | Theorem | Operationalisierung | ja, `[propext, Classical.choice, Quot.sound]` | jede Elementarkontextur ist Zweierbahn einer Involution; Existenz, **nicht** Eindeutigkeit — siehe Grenznotiz C |
| L03-1 | Verbundkontextur (§3) | `GCB.locally_classical_in_clone_iff` | Theorem | Deutung | ja, `[propext, Quot.sound]` | trägt Nicht-Erzeugbarkeit, nicht Vermittlung |
| L03-2 | Verbundkontextur (§3) | `CC.overlap_or_third_touches` | Theorem | Operationalisierung | ja, `[propext, Classical.choice, Quot.sound]` | Zusammenschluss als Berührungsstruktur: überlappend oder über eine dritte Elementarkontextur. **Grenze:** Berührung, nicht Günthers Vermittlung — die zweite Negation ist nicht getragen. Existenz, nicht Eindeutigkeit |
| L03-3 | Verbundkontextur (§3) | `CC.zaehlungen_nirgends_gleich` | Theorem | Operationalisierung | ja, `[propext, Quot.sound]` | die zwei Zählungen der Grenznotiz A stimmen nirgends überein, richtungstreu. **Grenze:** strikte Ungleichung auf der Verbundfolge; der Stirling-Zusatz bleibt gerechnet |
| L03-4 | Verbundkontextur (§3) | `CC.two_elem_contextures_iff` | Theorem | Operationalisierung | ja, `[propext, Classical.choice, Quot.sound]` | Mindestdreiwertigkeit als Satz: mehrere Elementarkontexturen gibt es genau ab `m = 3`. **Grenze:** dass dies Günthers Begründung über den unvermittelten zweiten Wert ist, bleibt Deutung |
| L03-5 | Verbundkontextur (§3) | `CC.disjoint_elem_contextures_iff` | Theorem | Operationalisierung | ja, `[propext, Classical.choice, Quot.sound]` | die Schwelle: disjunkte Elementarkontexturen genau ab `m = 4`; gibt `RT.regime_threshold_at_four` seinen begrifflichen Rahmen, ohne gemeinsamen Satz |
| L03-6 | Verbundkontextur (§3) | `PM.w_differs_on_disjoint` | Theorem | Operationalisierung | ja, `[propext, Classical.choice, Quot.sound]` | am Bestandszeugen `w` liegt die Mischung auf zwei disjunkten Elementarkontexturen. **Grenze:** Verortung am gewählten Zeugen; die Disjunktheit ist Zeugen- und nicht Gattungseigenschaft — Gegenbeispiel in der Grenznotiz des Moduls |
| L04-1 | Diskontexturalität (§4) | `TCB.T_not_in_clone` | Theorem | Operationalisierung | ja, `[propext, Quot.sound]` | Nicht-Erzeugbarkeit im Termklon, `m = 3` |
| L04-2 | Diskontexturalität (§4) | `NUCB.W_not_in_clone` | Theorem | Operationalisierung | ja, `[propext, Quot.sound]` | Bruch ohne Verlassen einer Kontextur |
| L04-3 | Diskontexturalität (§4) | `GCB.locally_classical_in_clone_iff` | Theorem | Operationalisierung | ja, `[propext, Quot.sound]` | Charakterisierung für alle `m ≥ 4` |
| L04-4 | Diskontexturalität (§4) | `DS.discontextural_posited` | Setzung | Setzung | ja, axiomfrei | Projektion eines `True`-Feldes, technisch `thmInfo`; konstitutive Setzung; **anderer Begriff als L04-1 bis L04-3**, siehe Grenznotiz B |
| L04-5 | Diskontexturalität (§4) | `QCB.locally_classical_in_clone_iff4` | Theorem | Operationalisierung | ja, `[propext, Quot.sound]` | Charakterisierung bei `m = 4`, Vorstufe von L04-3 |
| L04-6 | Diskontexturalität (§4) | `QCB.mixed_not_in_constant_clone` | Theorem | Operationalisierung | ja, `[propext, Quot.sound]` | Schranke überlebt konstante Prüfer; Invariante `R_4` reflexiv |
| L05-1 | Transkontexturalität (§5) | `TCB.T_leaves_contextur` | Theorem | Operationalisierung | ja, `[propext]` | Verlassen der Kontextur an einem Punkt |
| L05-2 | Transkontexturalität (§5) | `NUCB.W_contexture_faithful` | Theorem | Operationalisierung | ja, `[propext]` | Grenzüberschreitung ohne Verlassen |
| L05-3 | Transkontexturalität (§5) | `SA.agg_nicht_erzeugbar` | Theorem | Operationalisierung | ja, `[propext, Quot.sound]` | Stufenaggregation, `Fin 4` |
| L05-4 | Transkontexturalität (§5) | — | Offen | Offen | — | Erzeugung des geschichtlich Neuen nicht formalisiert |
| L05-5 | Transkontexturalität (§5) | `PC.freigabe_nicht_erzeugbar` | Theorem | Operationalisierung | ja, `[propext, Quot.sound]` | zweiter Konsument von E3; kein neuer Satz |
| L05-6 | Transkontexturalität (§5) | `RA.autoritaet_nicht_erzeugbar` | Theorem | Operationalisierung | ja, `[propext, Quot.sound]` | dritter Konsument von E3; kein neuer Satz |
| L05-7 | Transkontexturalität (§5) | `PM.not_in_clone_pair_mixture` | Theorem | Operationalisierung | ja, `[propext, Classical.choice, Quot.sound]` | nicht im Klon heisst: wählt auf zwei verschiedenen Paaren verschieden. Tragendes Allgemeines: `PM.pair_mixture_of_ne_min_ne_max`. **Grenze:** Paar-Verschiedenheit, nicht Disjunktheit |
| L06-1 | Poly-Kontexturalität stark (§6) | — | Offen | Offen | — | verengt: ein gerichteter Stufenaufstieg ist als Probe getragen (L12-7, L12-8, L06-8); die weltbildhafte Totalität der Definition bleibt ohne Träger, Forschungsstrang Plan §8; der Stufenschritt selbst ist paritätsabhängig (L10-6, L12-9); kein endlicher Wertvorrat trägt einen unbeschränkten Strom (L06-9); der Reichtum wächst bei konstanter Erreichbarkeit (L06-10, L12-10) |
| L06-2 | Poly-Kontexturalität f.-o. (§6) | `NUCB.W_locally_classical` | Theorem | Deutung | ja, `[propext]` | lokale Klassizität, `Fin 3` |
| L06-3 | Poly-Kontexturalität f.-o. (§6) | `NUCB.W_not_in_clone` | Theorem | Deutung | ja, `[propext, Quot.sound]` | globaler Reduzierbarkeitsbruch |
| L06-4 | Poly-Kontexturalität f.-o. (§6) | `CO.three_contextures_overlap` | Theorem | Deutung | ja, `[propext]` | Kontexturpluralität mit Überlappung |
| L06-5 | Poly-Kontexturalität f.-o. (§6) | `SA.agg_nicht_erzeugbar_konstanten` | Theorem | Deutung | ja, `[propext, Quot.sound]` | Robustheit gegen konstante Prüfer |
| L06-6 | Poly-Kontexturalität f.-o. (§6) | `PC.freigabe_nicht_erzeugbar_konstanten` | Theorem | Deutung | ja, `[propext, Quot.sound]` | Robustheit gegen konstante Prüfer |
| L06-7 | Poly-Kontexturalität f.-o. (§6) | `RA.autoritaet_nicht_erzeugbar_konstanten` | Theorem | Deutung | ja, `[propext, Quot.sound]` | Robustheit gegen konstante Prüfer |
| L06-8 | Poly-Kontexturalität f.-o. (§6) | `SAsc.ascent_proper` | Theorem | Deutung | ja, axiomfrei | Wachstums-Lesart: das Bild der Vorstufe verfehlt das neue Element, jedes Paar mit ihm liegt ausserhalb — die Lesung „sich erweiternde Kontexturen" ist Deutung, nicht Satzwortlaut |
| L06-9 | Poly-Kontexturalität stark (§6) | `KU.idRGSStream_not_fillable` | Theorem | Operationalisierung | ja, `[propext, Classical.choice, Quot.sound]` | der Identitätsstrom wird von jedem endlichen Wertesystem überschritten; die bedingte Allform ist `KU.unbounded_not_fillable`, ohne eigene Zeile. **Deutungs-Sprung: Kenogramm ist nicht Kontextur** — die Lesung als „sich unendlich erweiternde Kontexturen" ist Deutung und trägt kein Satz; getragen ist die Wertseite über `KU.marksLt_iff_fillable` (L16-10) |
| L06-10 | Poly-Kontexturalität stark (§6) | `CV.card_locallyClassical` | Theorem | Operationalisierung | ja, `[propext, Classical.choice, Quot.sound]` | genau `2^C(m,2)` lokal klassische Operationen auf `Fin m`, als Korollar der Bijektion `CV.locallyClassicalEquiv`; die Erreichbarkeits-Seite ist `CV.clone_locallyClassical_eq` (Mengengleichheit, ab m ≥ 4 genau `min` und `max`), ohne eigene Zeile. **„Wachsender Reichtum bei konstanter Erreichbarkeit" ist Deutung des Paars**, kein Satzwortlaut |
| L07-1 | Erste Negation (§7) | `TCB.negFin` | Definition | Operationalisierung | keine (def) | Ordnungsumkehr auf `Fin 3`, Teil der Basissignatur |
| L07-2 | Zweite Negation (§7) | `TCB.T_not_in_clone` | Theorem | Deutung | ja, `[propext, Quot.sound]` | Proxy, kein globaler Operator |
| L07-3 | Zweite Negation (§7) | `GCB.locally_classical_in_clone_iff` | Theorem | Deutung | ja, `[propext, Quot.sound]` | dito, ohne feste Wertzahl |
| L07-4 | Zweite Negation (§7) | — | Offen | Offen | — | keine Definition `SecondNegation`; nicht als Permutation zu bauen |
| L08-1 | Transjunktion (§8) | `TCB.T` | Definition | Operationalisierung | keine (def) | `if a = 0 ∧ b = 2 then 1 else max a b` |
| L08-2 | Transjunktion (§8) | `TCB.T_rejective` | Theorem | Operationalisierung | ja, `[propext]` | rejektiver Kern `T 0 2 = 1` |
| L08-3 | Transjunktion (§8) | `TCB.T_crosses_exactly_one` | Theorem | Operationalisierung | ja, `[propext]` | Bruch genau einer von drei Invarianten |
| L08-4 | Transjunktion (§8) | — | Offen | Offen | — | Produktion des ontologisch Neuen nicht formalisiert |
| L08-5 | Transjunktion (§8) | `CEB.not_in_clone_of_escapes` | Theorem | Operationalisierung | ja, `[propext]` | **das Zeugnis mit Menge und Punkt**, allgemein über jeder Sprache, jeder Struktur und jeder Substruktur: verlässt eine Operation eine abgeschlossene Menge an einem angebbaren Punkt, so ist sie kein Term über der Signatur. Konsumiert Mathlibs `Term.realize_mem`. **Grenze:** hinreichend, nicht notwendig — das Fehlen eines Punktes ist kein Zeugnis für Erzeugbarkeit |
| L08-6 | Transjunktion (§8) | `CEB.contexture03` | Definition | Operationalisierung | keine (def) | die Randkontextur `{0,3}` als Substruktur über `L` bei `m = 4`; Gegenstück `CEB.contexture12` ohne eigene Zeile. Benannte Konsumenten: L08-7, `CEB.mem_contexture03`, `CEB.mem_contexture12`, `CEB.avgDown_escapes`. **Grenze:** exhaustiv über alle 16 Teilmengen gemessen sind genau diese zwei nichttrivial abgeschlossen; über andere Wertzahlen ist nichts gemessen |
| L08-7 | Transjunktion (§8) | `CEB.avgDown_not_in_clone` | Theorem | Operationalisierung | ja, `[propext, Quot.sound]` | der abgerundete Durchschnitt `CEB.avgDown` verlässt `{0,3}` am Punkt `(0,3)` (`CEB.avgDown_escapes`) und liegt darum nicht im Klon von `{min, max, ¬}`. Daneben ohne eigene Zeile — L05-7-Präzedenz: `CEB.locallyClassical_preserves_both`, das die zwei Zeugnisse des Bestandes gegeneinander abgrenzt. **Grenze:** eine Aussage über eine Operation, keine über eine Politik |
| L09-1 | Intra-kontexturell (§9) | `TCB.L` | Definition | Operationalisierung | keine (def) | Signatur `{¬, ∧, ∨}`, keine Konstante |
| L09-2 | Intra-kontexturell (§9) | `TCB.term_preserves_contextur` | Theorem | Operationalisierung | ja, `[propext, Quot.sound]` | konsumiert Mathlibs `Term.realize_mem` |
| L09-3 | Trans-kontexturell (§9) | `TCB.term_clone_localization` | Theorem | Operationalisierung | ja, `[propext, Quot.sound]` | Verortung auf Klon-Ebene, kein freies Prädikat |
| L10-1 | Isomorphie (§10) | `TCB.phi` | Definition | Operationalisierung | keine (def) | `{0,2} → Bool` |
| L10-2 | Isomorphie (§10) | `TCB.test1_injective` | Theorem | Operationalisierung | ja, `[propext]` | mit `TCB.test1_surjective` der Bijektionsbeleg |
| L10-3 | Isomorphie (§10) | `TCB.test1_min_max` | Theorem | Operationalisierung | ja, `[propext]` | Operationsverträglichkeit auf der Kontextur |
| L10-4 | Anisomorphie (§10) | `NUCB.conj` | Definition | Deutung | keine (def) | Negationskonjugation als Transport, keine Anisomorphie-These |
| L10-5 | Anisomorphie (§10) | — | Offen | Offen | — | PathC: **eingefroren** (29.07.2026); 27 betroffene Deklarationen mit `sorry` in 8 Dateien (Route: frische Elaboration je Modul, verschiedene Warnpositionen; `docs/build-targets.md`), 0 Wachen, ein Modul rot |
| L10-6 | Anisomorphie (§10) | `SPar.castSucc_negFin_ne` | Theorem | Deutung | ja, `[propext, Quot.sound]` | die Stufeneinbettung vertauscht an keiner Stelle mit der Negation; dass Nicht-Abbildbarkeit Anisomorphie-Material ist, ist Lesart und kein Satz |
| L11-1 | Vermittlung (§11) | `NUCB.W` | Definition | Deutung | keine (def) | Dateiname bewusst `NonUniformCloneBound`, nicht `Mediation` |
| L11-2 | Vermittlung (§11) | `SA.agg_lokal` | Theorem | Deutung | ja, `[propext]` | lokal klassisch bei globaler Nicht-Erzeugbarkeit |
| L11-3 | Unmittelbarkeit (§11) | — | Offen | Offen | — | kein Träger |
| L11-4 | Vermittlung (§11) | `PC.freigabe_lokal` | Theorem | Deutung | ja, `[propext]` | lokal klassisch bei globaler Nicht-Erzeugbarkeit |
| L11-5 | Vermittlung (§11) | `RA.autoritaet_lokal` | Theorem | Deutung | ja, `[propext]` | lokal klassisch bei globaler Nicht-Erzeugbarkeit |
| L12-1 | Stufengang (§12) | `GCB.locally_classical_in_clone_iff` | Theorem | Deutung | ja, `[propext, Quot.sound]` | Satz über Klonzugehörigkeit; Stufengang ist die Zuordnung |
| L12-2 | Stufengang (§12) | `SA.agg` | Definition | Deutung | keine (def) | vier lineare Autorisierungsstufen |
| L12-3 | Stufengang (§12) | `RT.regime_threshold_at_four` | Theorem | Deutung | ja, `[propext, Quot.sound]` | Ein-Satz-Modul; Übergang drei zu vier Werten |
| L12-4 | Stufengang (§12) | — | Offen | Offen | — | kein unendlicher Stufengang; gerichtetes System offen |
| L12-5 | Stufengang (§12) | `PC.freigabe` | Definition | Deutung | keine (def) | vier Freigabestufen; Mischstelle unten, Kontrast zu `SA.agg` |
| L12-6 | Stufengang (§12) | `RA.autoritaet` | Definition | Deutung | keine (def) | vier Autoritätsstufen; Mischstelle Mitte, dritter Zeuge |
| L12-7 | Stufengang (§12) | `SAsc.exists_locally_classical_not_in_clone` | Theorem | Operationalisierung | ja, `[propext, Quot.sound]` | für jedes m ≥ 4 ist die Lücke der Charakterisierung bewohnt; Klon-Ausschluss ist Konsum der E3-Iff, kein neuer Beweis |
| L12-8 | Stufengang (§12) | `SAsc.w_castSucc` | Theorem | Operationalisierung | ja, `[propext]` | Zielformel §12: auf dem eingebetteten Quadrat stimmt Stufe m+1 mit Stufe m überein; eine Regel auf allen Stufen, kein Grenzobjekt |
| L12-9 | Stufengang (§12) | `SPar.odd_no_neg_compatible` | Theorem | Operationalisierung | ja, `[propext, Quot.sound]` | bei ungeradem m ist keine Abbildung `Fin m → Fin (m+1)` negationsverträglich; nur der Schritt m → m+1, nichts über m+2, kein Kolimes-Satz |
| L12-10 | Stufengang (§12) | `CV.card_locallyClassical_lt` | Theorem | Operationalisierung | ja, `[propext, Classical.choice, Quot.sound]` | die Zahl der lokal klassischen Operationen wächst je Stufenschritt echt; Konsum von `SAsc.choose_two_succ`, Schranke `1 ≤ m` scharf. Wachstum je Schritt, **kein Grenzobjekt** und keine Aussage über einen Limes |
| L13-1 | Designation (§13) | `TCB.T_rejective` | Theorem | Deutung | ja, `[propext]` | Rejektionswert als operative Bruchstelle |
| L13-2 | Designation (§13) | — | Offen | Offen | — | keine ontologische Semantik von designierend/nicht-designierend |
| L14-1 | Zyklus, Selbstzyklus (§14) | — | Offen | Offen | — | Selbstzyklus ohne nicht-triviale Fassung; siehe Grenznotiz C |
| L15-1 | Kategorie des Neuen (§15) | — | Offen | Offen | — | nicht formalisiert; laut `TCB`-Doc-String so nicht formalisierbar |
| L16-1 | Morphogramm (§16) | `K.relabel` | Definition | Operationalisierung | ja, axiomfrei | Normalform einer Folge als RGS; Morphogramm-Bildung, kein Quotientstyp |
| L16-2 | Morphogramm (§16) | `K.rgs_unique_of_pattern` | Theorem | Operationalisierung | ja, `[propext, Quot.sound]` | gleiches Muster erzwingt gleiche Normalform |
| L16-3 | Morphogramm (§16) | `KM.SamePattern` | Definition | Operationalisierung | keine (def) | Muster-Gleichheit als Relation; kein Quotientstyp |
| L16-4 | Morphogramm (§16) | `KM.samePattern_iff_pattern` | Theorem | Operationalisierung | ja, `[propext, Classical.choice, Quot.sound]` | Charakterisierung am Positionsmuster, typübergreifend |
| L16-5 | Morphogramm (§16) | `KM.samePattern_iff_common_nf` | Theorem | Operationalisierung | ja, `[propext, Classical.choice, Quot.sound]` | Muster-Gleichheit = gemeinsame Reduktions-Normalform; nur `List ℕ` |
| L16-6 | Morphogramm (§16) | — | Offen | Offen | — | verengt: Zählung und Besetzbarkeit getragen (L16-7 ff.); offen bleiben die semantischen Fälle 1–3 aus §16 und die zeilenweise Identifikation mit Günthers Tafel VIII |
| L16-7 | Morphogramm (§16) | `KF.marksLeOne_iff_fillable` | Theorem | Operationalisierung | ja, `[propext, Classical.choice, Quot.sound]` | Marke ≤ 1 ⟺ Normalform einer zweiwertigen Wertfolge; die Lesung von `Fin n → Bool` als Wahrheitstafel setzt eine gewählte Zeilenordnung voraus |
| L16-8 | Morphogramm (§16) | `KF.card_rgs_four_fillable` | Theorem | Operationalisierung | ja, `[propext, Classical.choice, Quot.sound]` | acht der fünfzehn vierstelligen Morphogramme sind zweiwertig besetzbar; die Identifikation mit den acht klassisch markierten Zeilen Günthers ist Deutung, kein Satz |
| L16-9 | Morphogramm (§16) | `KF.fillable_card_lt_card` | Theorem | Operationalisierung | ja, `[propext, Classical.choice, Quot.sound]` | strikte Ungleichung als formale Lesung von „morphogrammatisch unvollständig"; der benannte Zeuge dazu ist `KF.exists_nonfillable` (`[0,1,2,0]`, axiomfrei), ohne eigene Zeile |
| L16-10 | Morphogramm (§16) | `KU.marksLt_iff_fillable` | Theorem | Operationalisierung | ja, `[propext, Classical.choice, Quot.sound]` | verallgemeinerte Wertbesetzung über `Fin k` für jedes k; **ersetzt die Bool-Fassung L16-7 nicht** — `Fin 2` ist nicht `Bool`, eine Übersetzung ist nicht gebaut; zusammen fällt nur die Prädikat-Seite (`KU.marksLeOne_iff_marksLt_two`, ohne eigene Zeile) |
| L16-11 | Morphogramm (§16) | `KF.MarksLeOne` | Definition | Operationalisierung | keine (def) | Wertseiten-Prädikat der Zweiwertigkeit; trägt L16-7 bis L16-9 |
| L16-12 | Morphogramm (§16) | `KFib.fiberEquiv` | Definition | Operationalisierung | ja, `[propext, Classical.choice, Quot.sound]` | die Faser der Kanonisierung ist zweielementig, als Äquivalenz zu `Bool`; dazu `KFib.card_bool_fun_eq_two_mul` als Gleichung 16 = 2·8 zwischen Korpus-Kardinalitäten. **Grenze:** Faser bei `n = 4`; allgemeines `n` bleibt aussen |
| L16-13 | Morphogramm (§16) | `KFib.witness_over_three` | Theorem | Operationalisierung | ja, axiomfrei | zweiter Zeuge `[0,1,2,3]`: von keinem dreiwertigen, wohl aber von einem vierwertigen System besetzbar; Gegenstück `KFib.witness_over_two`. **Grenze:** Stufentrennung am Zeugen; die Tafelnummern-Zuordnung bleibt Deutung |
| L16-14 | Morphogramm (§16) | `RelInv.relabel_map_negFin` | Theorem | Operationalisierung | ja, `[propext, Classical.choice, Quot.sound]` | die Kanonisierung ist gegen jede **injektive** Umbenennung der Werte invariant (`RelInv.relabel_map_of_injective`, heterogen); die Instanz an der ordnungsumkehrenden Negation `negFin` folgt daraus. **Grenze:** Invarianz der Kanonisierung gegen injektive Wertumbenennung; **keine** Nichtdarstellbarkeitsaussage |
| L16-15 | Morphogramm (§16) | `K.JointlyClosed` | Definition | Operationalisierung | ja, `[propext]` | Abgeschlossenheit einer Reihenmenge unter jedem Stellentausch **innerhalb der Reihe** und unter dem Abstieg; trägt L16-16. **Grenze:** die Indexschranke ist gemessen und nicht gewählt — ohne sie setzt `exchangeAt` bei einem Index ausserhalb eine Stelle auf `0`, statt zwei zu tauschen (Vorprobe im Dateikopf) |
| L16-16 | Morphogramm (§16) | `K.hull_le_of_jointlyClosed` | Theorem | Operationalisierung | ja, `[propext, Classical.choice, Quot.sound]` | jede gemeinsam abgeschlossene Menge, die eine RGS-Reihe der Länge ≥ 2 enthält, enthält `{[],[0],[0,0]}` oder `{[],[0],[0,1]}` **ganz** — ohne Längenschranke. Daneben `K.jointlyClosed_hull_pair` (beide Dreiermengen sind selbst gemeinsam abgeschlossen, `[propext, Quot.sound]`), ohne eigene Zeile — L05-7-Präzedenz. **Grenze:** eine ⊆-Untergrenze; keine Prioritätsaussage |
| L16-17 | Morphogramm (§16) | `KOS.canonicalize_eq_of_ne` | Theorem | Operationalisierung | ja, `[propext, Classical.choice, Quot.sound]` | über **zwei** Stellen haben je zwei Belegungen mit verschiedenen Werten dieselbe Normalform — heterogen über beliebigen Trägern mit entscheidbarer Gleichheit. Daneben `KOS.canonicalize_comp_swap` (der Stellentausch ist für die Normalform unsichtbar, ohne Voraussetzung an die Belegung), ohne eigene Zeile — L05-7-Präzedenz. **Grenze:** eine Blindheitsaussage über zwei Stellen; keine Aussage über die Proemialrelation |
| L16-18 | Morphogramm (§16) | `KOS.RisingOccupancy` | Definition | Operationalisierung | keine (def) | Wertbesetzung zweier Stellen: die Werte steigen längs der Stellen; Gegenstück `KOS.FallingOccupancy` ohne eigene Zeile. Trägt L16-19 sowie `KOS.occupancy_exclusive`, `KOS.occupancy_total`, `KOS.no_occupancy_of_eq`. **Grenze:** welcher der beiden Fälle Günthers symmetrisches Umtauschverhältnis und welcher seine Ordnung trägt, ist **nicht** zugeordnet — die Quelle sagt es an dieser Stelle nicht, und L16-19 zeigt, dass die Trennleistung es nicht bestimmt |
| L16-19 | Morphogramm (§16) | `KOS.separation_is_the_order` | Theorem | Operationalisierung | ja, `[propext, Quot.sound]` | jedes unter Ordnungseinbettungen stabile Kriterienpaar, das die verschiedenwertigen Belegungen zweier Stellen ausschliessend und vollständig teilt, **ist** das Ordnungspaar — in einer der beiden Benennungen und in keiner dritten Gestalt. **Grenze:** zwei Stellen und ein blosses `LinearOrder`; über mehr Stellen oder mehr Trägerstruktur sagt der Satz nichts |
| L16-20 | Morphogramm (§16) | `KPS.no_injective_pair_three` | Theorem | Operationalisierung | ja, `[propext, Classical.choice, Quot.sound]` | keine Abbildung der **geordneten** Paare von `RGS 3` in `RGS 4` ist injektiv (`25 > 15`). Daneben ohne eigene Zeile — L05-7-Präzedenz: `KPS.no_injective_pair_four` (`225 > 52`), `KPS.exists_injective_pair_two` (`4 ≤ 5`, die Schwelle ist scharf) und die drei benannten Stufenzahlen `KPS.card_rgs_two`, `KPS.card_rgs_three`, `KPS.card_rgs_five`, gerechnet aus dem Generator wie `KF.card_rgs_four`. **Grenze:** eine Kardinalitätsschranke zwischen zwei Stufen; die geordnete Paar-Lesart ist eine Setzung ausserhalb des Moduls, und dass die Vier-Relata-Bewegung diese Gestalt hat, ist Lesart und nicht Gegenstand des Satzes |
| L16-21 | Morphogramm (§16) | `K.concatWith` | Definition | Operationalisierung | keine (def) | Verkettung zweier Reihen unter einer **Identifikation** — einer injektiven Umbenennung der Symbole der hinteren Reihe; die Wohlgeformtheit wird durch die Kanonisierung erzeugt und nicht von den Argumenten verlangt. Benannte Konsumenten: L16-22 sowie `K.concatWith_take_left`, `K.concatWith_pattern_right`, `K.concatWith_dropLast`, `K.concatWith_ambiguous_nonempty`. **Grenze:** die Injektivität sitzt im Typ `ℕ ↪ ℕ`; dass jede auf den Symbolen der hinteren Reihe injektive Belegung sich dorthin fortsetzt, ist nicht bewiesen |
| L16-22 | Morphogramm (§16) | `K.concatWith_pair_not_injective` | Theorem | Operationalisierung | ja, `[propext]` | aus der verketteten Reihe ist die **Zerlegung** nicht zurückgewinnbar, und zwar für keine Identifikation. Daneben ohne eigene Zeile — L05-7-Präzedenz: `K.concatWith_ambiguous_nonempty` (derselbe Befund an vier nichtleeren wohlgeformten Reihen, axiomfrei), `K.concatWith_isRGS_length` (Z1) und `K.concatWith_dropLast` (Z2, der Abstieg wirkt auf dem hinteren Teil, Voraussetzung gemessen). **Grenze:** über die **Identifikation** sagt der Satz nichts — im gezählten Bereich wurde keine echte Freiheit gefunden, ausserhalb ist es ungemessen |
| L17-1 | Trans-klass. Mehrwertigkeit (§17) | `CO.three_contextures_overlap` | Theorem | Deutung | ja, `[propext]` | die drei Zweierkontexturen als Verkopplung 1↔2, 2↔3, 1↔3 |
| L18-1 | Ontologie vs. Logik (§18) | `IB.two_mul_intervalStart` | Theorem | Deutung | ja, `[propext, Quot.sound]` | Ontologien-Wertzahl `n(n+1)/2`; Profil ist omega-Hülle |
| L18-2 | Ontologie vs. Logik (§18) | `IB.intervalEnd_sub_start` | Theorem | Deutung | ja, `[propext, Quot.sound]` | Themenzahl gleich Intervallbreite; kein Designationsbegriff |
| L19-1 | Logisches Intervall (§19) | `IB.tafel_IV` | Theorem | Operationalisierung | ja, axiomfrei | beweist `(1,2),(3,5),(6,9),(10,14),…` — die Tafel aus §19 wörtlich |
| L19-2 | Logisches Intervall (§19) | `IB.intervalEnd_succ_start` | Theorem | Operationalisierung | ja, `[propext, Quot.sound]` | Intervalle schließen lückenlos und überlappungsfrei an |

## Grenznotiz A — Verbundkontextur, zwei Zählfunktionen

`Definitionen.md` §3 zählt Designationsthemen, also den Index n der Dreieckszahl; §17 und der
Korpus zählen Wert-Zweiermengen, C(m,2). Sie stimmen an keiner Stelle der Folge überein; die
Differenz wächst wie n⁴/8. Die Wertfolge der Verbundkontexturen ist n(n+1)/2 ab n = 2, also
3, 6, 10, 15; die 1 gehört zur Ontologien-Folge §18, nach Günthers eigenen Bedingungen — §3
verlangt mindestens drei Werte, §18 nennt das einwertige System notwendig eine Ontologie. Die
Zuordnung „n gleich Themenzahl" ist Deutung: die Koinzidenz ist definitorisch, weil beide
Größen der Index derselben Dreieckszahl sind.

Daraus die Rücknahme in L03-2. `IB.intervalStart` ist die Ontologien-Wertzahl; die
Verbundkontextur-Folge ist ihr Bild ab Index 2. Dieselbe Arithmetik trägt beide Folgen bei
verschobenem Index — und darum darf sie nicht unter beiden Paragraphen stehen.

**Nachtrag (Ledger Rev. 11): der Kern dieser Notiz ist satzförmig.** Was oben als Rechnung
stand — die beiden Zählungen stimmen an keiner Stelle überein —, trägt jetzt ein Theorem:
`CC.zaehlungen_nirgends_gleich` (L03-3) zeigt `guentherZaehlung k < korpusZaehlung k` für
alle `k`, also **strikt und richtungstreu**; die Korpuszählung liegt stets über Günthers.
Die Indexbrücke steht dabei nicht mehr still im Text, sondern ausgeschrieben in
`CC.verbundWertzahl := IB.intervalStart (k + 2)` — die Form, die die Rücknahme in L03-2
verlangt: dieselbe Arithmetik, sichtbar versetzt, statt unter zwei Paragraphen.

**Zusatz (computed, außerhalb des Korpus).** Die beiden Zählungen berühren sich an genau
einer Stelle: |s(m, m−1)| = C(m,2) für m = 2 bis 8 gerechnet, also bei den Permutationen mit
genau einer Transposition. Günthers Stirling-Zählung aus §14 und die Korpuszählung fallen
dort zusammen. Das ist ein gerechneter Vorbefund und **kein Satz des Korpus**; keine Zahl
davon ist in eine Lean-Datei eingegangen. **Auch der Nachtrag ändert daran nichts:** der
Satz oben trägt die Nichtübereinstimmung, nicht die Stirling-Koinzidenz.

## Grenznotiz B — zwei Begriffe, und die Aggregatregel

**Zwei Diskontexturalitätsbegriffe unter einem Paragraphen.** L04-1 bis L04-3 sowie L04-5 und
L04-6 tragen die Klon-Lesart: Nicht-Erzeugbarkeit einer Operation aus einer angegebenen
Signatur. L04-4 trägt die kategoriale Lesart: Nicht-Einholbarkeit eines Kontexturübergangs
durch Morphismen der Schema-Achse — gesetzt, mit der Begründung, ein intra-kontexturaler
Beweis der Nicht-Intra-Kontexturalität wäre ein Selbstwiderspruch. Wer beide unter einem
Namen liest, erhält den Widerspruch, Diskontexturalität sei bewiesen und zugleich prinzipiell
unbeweisbar. Die erste quantifiziert über Terme einer endlichen Signatur, die zweite über
Morphismen einer Kategorie; ihre Identifikation ist Deutung.

**Zur Aggregatregel.** `DS.discontextural_posited` ist eines von 32 `True`-Feldern im
Aggregat (korpusweit 33). `CLAUDE.md` §10 lautet seit `f5d5244`/`3dc2649`: **kein Satz des
Aggregats hängt an einer Setzung** — gemessen, weil genau zwei Aggregatkonstanten eine
`True`-Feld-Projektion referenzieren und beide selbst die Aussage `True` haben. Die 32 Felder
zerfallen in Platzhalter (30, verschobene Beweisschuld, Exit-Kriterium nötig) und
konstitutive Setzungen (2, Begründung statt Exit nötig). Von den Bestandsfeldern erfüllen 19
die Klassenpflicht noch nicht; sie gilt für neu angelegte Felder und ist Phase-2-Posten.

## Grenznotiz C — Zyklus, Selbstzyklus, Umtauschverhältnis

Der Zyklusbegriff ist seit `e69fb16` an **einer** Stelle angeschlossen: die Elementarkontextur
ist als Zweierbahn einer Involution darstellbar (L02-6 bis L02-8). Eine allgemeine
Zyklentheorie ist nicht gebaut und war nicht Auftrag.

**Der Selbstzyklus bleibt offen, und zwar begründet.** Drei Fassungen wurden geprüft: als
Minimalperiode 1 steht er wörtlich in Mathlib; als leerer Support verschwindet er; als
Nicht-Kontextur sagt er `1 ≠ 2`. Wörtlich aus dem Befund:

> Der Selbstzyklus trägt im Zielsatz mit — aber nur als der Fall, der keinen eigenen Satz
> hat. Er ist der Zweig, der die Dichotomie erschöpfend macht.

**Nachtrag (Ledger Rev. 15): eine vierte, gemessene Lage — auf der kenogrammatischen
Seite.** Die drei geprüften Fassungen oben liegen sämtlich auf der Wertseite. Seit
`K.JointlyClosed` (L16-15) und seinen beiden Konsumenten (L16-16) steht eine vierte
daneben, und sie ist von anderer Art: unter Abschluss gegen **Stellentausch und
Abstieg** zeichnet der Bestand genau zwei Reihen der Länge zwei aus — `[0,0]` und
`[0,1]`. Jede gemeinsam abgeschlossene Menge, die eine RGS-Reihe der Länge ≥ 2 enthält,
enthält die Hülle einer der beiden **ganz** (`K.hull_le_of_jointlyClosed`), und beide
Hüllen sind selbst gemeinsam abgeschlossen (`K.jointlyClosed_hull_pair`).

*Was daran Satz ist und was nicht, getrennt:* die **⊆-Untergrenze** und die
**Abgeschlossenheit beider Hüllen** sind Sätze, über alle Längen. Dass die beiden die
**einzigen** ⊆-minimalen sind, ist **gemessen** (Aufzählung der Längen 0–6,
`KorpusRev2/Kenogrammatischer_Invariantenschnitt_Befund.md`) und **kein Satz** — ein
„genau zwei"-Satz war freigestellt und ist nicht gebaut.

*Und die Zuordnung ist Deutung:* dass `[0,0]` **der Selbstzyklus** aus
`Definitionen.md` §2(a) und `[0,1]` **das Umtauschverhältnis** aus §2(b) sei, ist eine
Lesart und trägt kein Satz. **L14-1 bleibt darum offen:** ein wertseitiger
Selbstzyklus-Begriff ist weiterhin nicht gebaut, und die kenogrammatische Lage ersetzt
ihn nicht. Was der Nachtrag ändert, ist allein dies — der Selbstzyklus ist hier zum
ersten Mal nicht der Fall ohne eigenen Satz, sondern eine von zwei ausgezeichneten
Gestalten; und keine Zeile hat sich dafür bewegt.

**Die Eindeutigkeit des Umtauschverhältnisses ist nicht getragen.** `Definitionen.md` §2(b)
versteht die Elementarkontextur als *Umtauschverhältnis* zweier Werte, und dessen Pointe ist
Eindeutigkeit. L02-8 liefert Existenz, nicht Eindeutigkeit — und an dieser Signatur wäre
Eindeutigkeit nicht bloß unbewiesen, sondern falsch: der Satz quantifiziert über Involutionen
des ganzen Typs, und über `Fin 4` haben `swap 0 1` sowie `swap 0 1 ∘ swap 2 3` beide die Bahn
`{0,1}` durch `0` (in Lean gegengerechnet, außerhalb des Korpus). Die gemeinte Eindeutigkeit
betrifft die Einschränkung auf die Zweiermenge und bräuchte einen Begriff „Involution auf
`K`", den der Bestand nicht führt. Nicht gebaut: kein Satz des Korpus verlangt ihn.

## Vom Korpus gemessene Choice-Grenze

`EC.isPeriodicPt_two` trägt die Involutionsaussage `f^[2] x = x` vor jedem Bahnbegriff und
zieht nur `[Quot.sound]`. Erst `Function.minimalPeriod` — `noncomputable` — bringt
`Classical.choice` herein. Damit ist die Stelle des Übergangs nicht behauptet, sondern am
Term abgelesen, und die Profile der Zeilen L02-6 bis L02-8 sind Eigenschaft des
Bahnbegriffs, nicht der Kontexturaussage.
