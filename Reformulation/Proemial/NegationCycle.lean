import Mathlib.Data.List.Permutation
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Range

/-!
# Proemial.NegationCycle — Negationsfolgen, die jede Wertfolge genau einmal durchlaufen (Günthers Hamiltonkreise, Stufe 1)

**BENENNUNG mit Zeugen-Sätzen und drei Erträgen.** Gebaut auf Anordnung des
Architekten vom 21. September 2026 nach `KorpusRev2/Vorprobe_Hamiltonkreise_Impl.md`
(Stufe 1 der dortigen Empfehlung); am selben Tag auf seine zweite Anordnung ergänzt um die
Emendation als Satz, `full_length` und `triadic_unique'`
(`KorpusRev2/Antwort_Anmerkungen_NegationCycle_Impl.md`). Bis zu diesem Modul trug das Repo zum Gegenstand nichts;
die Grenznotiz C des Ledgers sagt: „Zyklentheorie ist nicht gebaut und war nicht Auftrag."

Der Träger ist der schmalste, der die Sache fasst: eine **Wertfolge** ist eine Liste über
`Fin (m + 1)`, ein **Negator** `N_{i+1}` tauscht in ihr die Werte `i` und `i + 1` (`sw`,
`negate`), eine **Negationsfolge** ist eine Liste von Negator-Indizes. `stations` führt die
durchlaufenen Wertfolgen, `endpoint` die erreichte. `IsFullCycle seq` sagt in vier Feldern,
was Günther einen *vollständigen Hamiltonkreis* nennt: die Folge kehrt zum Ausgang zurück,
keine Station kehrt wieder, jede Station ist eine Anordnung aller Werte, und jede Anordnung
aller Werte ist Station. Das Prädikat ist entscheidbar; die Zeugen-Sätze gehen durch `decide`.

Die Sätze:

* `sw_sw`, `negate_negate` — der Negator ist eine Involution (Günther: die Negation,
  „auf sich selbst angewendet, annulliert ihre Negationswirkung").
* `tafelVI4_full`, `tafelVI5_full`, `tafelVI5_eq_reverse` — dreiwertig: die zwei Folgen
  (4) und (5) sind Vollkreise, und die eine ist die andere rückwärts gelesen.
* `full_length` — **Ertrag**: jeder Vollkreis über `m + 1` Werten hat genau `(m + 1)!`
  Negatoren. Günther sagt es als Regel (1980 S. 20: „Ein n-wertiger Hamiltonkreis umfasst,
  wenn er vollständig ist n! Negationsschritte"); hier folgt es aus den vier Feldern. Dass
  es für jede Wertzahl ab zwei einen Vollkreis gibt, ist `NegationCycleSJT.full_exists`.
  Hilfssatz `stations_length`.
* `triadic_unique`, `triadic_unique'` — **Ertrag, der Beweis einer unbewiesenen
  Quellenaussage**: dreiwertig sind (4) und (5) die einzigen Vollkreise. Günther sagt es ohne
  Beweis (IGN S. 43: „Die triadische Wertordnung besaß nur einen einzigen solchen Kreis, der
  je nach der Wertordnung entweder im Uhrzeigersinn oder im Gegensinn durchlaufen werden
  konnte" — den Drehsinn nennt er also selbst; was hier hinzukommt, ist der Beweis).
  `triadic_unique` läuft über die 64 Folgen der Länge sechs; `triadic_unique'` lässt die
  Längenvoraussetzung fallen, über `full_length2` (Hilfssatz `perms2_nodup`). Beide sind
  choice-frei.
* `kreis1_full`, `kreis2_full`, `kreis3_full` — vierwertig: Günthers drei ausgeschriebene
  Beispielkreise sind Vollkreise; `kreis1_family` (10-9-5), `kreis2_family` (9-6-9),
  `kreis3_family` (6-12-6) — die Operatorhäufigkeiten, nach denen er die drei Familien
  unterscheidet. `kreis3` ist zugleich die Negatorfolge über **Tafel IV** des Aufsatzes von
  1980.
* `reverse_full` — **Ertrag, und die Schliessung einer benannten Lücke**: die Umkehrung
  *jedes* Vollkreises ist ein Vollkreis. Günther rechnet „Drehsinn und Gegen-Drehsinn als
  einen Kreis" (1980, S. 20) — bis zum 21. September stand das hier nur an den drei
  Beispielen. Der Beweis geht über `fullStations_reverse`: die umgekehrte Folge durchläuft
  dieselbe Stationenfolge rückwärts (Hilfssätze `endpoint_append`, `stations_append`,
  `fullStations_append`, `endpoint_reverse`). `kreis1_reverse_full`,
  `kreis2_reverse_full`, `kreis3_reverse_full` sind seither seine Folgerungen, nicht mehr
  `decide`-Läufe. `kreis1_mirror_full`, `kreis1_mirror_family` — die Spiegelung
  `N₁ ↔ N₃` führt 10-9-5 in 5-9-10 über; Günther rechnet beide zur selben Familie.
* `pseudo_closes`, `pseudo_family`, `pseudo_half`, `pseudo_not_full` — Günthers eigenes
  Gegenbeispiel, die Folge (23): `N₁·₂·₃` achtmal kehrt zurück und verteilt die Operatoren
  8-8-8, durchläuft aber in der zweiten Hälfte noch einmal die erste — eine
  „Pseudoäquivalenz", ein „partieller Hamiltonkreis mit einem Bestand von nur zwölf
  Wertkolonnen".
* `kreis2Gedruckt_not_closed`, `kreis2_emendation`, `kreis2_eq` — **Ertrag, die Emendation
  als Satz**: die zweite Beispielfolge, wie sie gedruckt steht, kehrt nicht zurück; unter
  allen neun Fortsetzungen um zwei Negatoren gibt **genau eine** einen Vollkreis, `·1·3`;
  und `kreis2` ist diese Fortsetzung. Siehe unten, Textbefund 1.
* `visits_every_arrangement` — der Anschluss an `List.Perm`: ein Vollkreis trifft jede
  Liste, die eine Permutation des Ausgangs ist.

* `track`, `sw_step`, `track_last`, `track_between`, `track_between_down`,
  `track_mediates` — **der vermittelnde Wert** (Teil 5, 25.9.2026): Unter jedem Negatorwort
  durchläuft ein Wert jeden Wert zwischen Anfang und Ende (HKN S. 25, Lesart „vermittelnd =
  durchlaufen").
* `sw_val`, `braid`, `comm_far`, `braid_fails_far_all`, `braid_fails_far`, `genese_resultat`,
  `genese_verschieden` — **die Genese** (Teil 5, 23.9.2026): Günthers zwei Wege zum
  selben Umtausch (HKN S. 25) als Eichung, und dahinter die Zopfrelation der Negatoren für
  jedes `m`. Siehe den Abschnitt „Die Genese" unten.

* `klassisch3`, `transklassisch3`, `transklassisch3_nodup`, `transklassisch3_disjoint`,
  `zone_exhausts`, `zone_count`, `transklassisch3_card` — **der kalkültheoretische Bereich
  der zweiten Negation bei drei Werten** (Teil 6, 25.9.2026): Günthers vier Spalten aus HKN
  S. 24 sind genau das Komplement der Doppelstrich-Zone in den sechs Anordnungen. Siehe den
  Abschnitt unten; **er löst V nicht ein.**

* `klassisch`, `transklassisch`, `transklassisch_card`, `transklassisch_eq_three`,
  `transklassisch_four`, `transklassisch_two` (Hilfssätze `sw_bij`, `negate_perm`,
  `klassisch_sub`, `klassisch_nodup`) — **der Bereich für jede Wertzahl** (Teil 7,
  25.9.2026): bei `m + 2` Werten `(m + 2)! − 2` Elemente; bei drei Werten dieselben vier wie
  in Teil 6. Siehe den Abschnitt unten.

**Warum überwiegend Benennung:** die Zeugen-Sätze rechnen nach, was Günther ausschreibt.
Neuen Satzgehalt tragen `full_length`, das Paar `triadic_unique` / `triadic_unique'` und
`kreis2_emendation`; die zwei letzten sind endliche Fallarbeit (64 Folgen, neun
Fortsetzungen). Die Skala FOLGERUNG / HEBUNG / ZUSAMMENSTELLUNG / UMBENENNUNG ist auf sie
**nicht anwendbar**: sie misst das Verhältnis zum Bestand und setzt Verbrauch voraus, und
diese Sätze verbrauchen keinen Bestandssatz. Was sie trägt, ist ihr Verhältnis zur Quelle.

## Quellenlage

Härte-Marke durchweg **GEMESSEN** (CLAUDE.md §6), gelesen an der Textschicht der PDF
(`pypdf`; die Seiten liessen sich nicht rendern — der Druck ist **nicht** eingesehen):

* **IGN** = *Identität, Gegenidentität und Negativsprache* (1979),
  `KorpusRev1/gunther_identitaet.pdf`, Seitenzahl = PDF-Seite.
  S. 18: die Folgen (4) `p ≡ N₁·₂·₁·₂·₁·₂ p` und (5) `p ≡ N₂·₁·₂·₁·₂·₁ p`, Tafel VI —
  „Wertpermutationen, die Hamilton-Kreise bilden". S. 41: N₃ als Umtausch zwischen drittem
  und viertem Wert. S. 43: die drei Familien nach Operatorhäufigkeit. S. 44: der erste und
  der zweite Beispielkreis, Tafel XI und XII. S. 45: der dritte, und die Folge (23) mit
  Tafel XIV. S. 46: „Pseudoäquivalenz", „partieller Hamiltonkreis".
* **Heidegger 1980** = *Martin Heidegger und die Weltgeschichte des Nichts*,
  `KorpusRev1/gg_heidegger-weltgeschichte-nichts.pdf`, S. 20: Tafel IV mit Negatorfolge
  und 25 Wertspalten; „alle überhaupt möglichen Permutationen einmal und nur einmal".

**Drei Textbefunde, gemeldet und nicht geheilt** (Hermeneutes) — **der erste ist eine
EMENDATION**, keine Lesart: eine Lesart wählt unter dem, was dasteht; eine Emendation setzt
ein, was nicht dasteht.

1. IGN S. 44 druckt den zweiten Kreis mit **22** Negatoren
   (`1·2·3·1·3·2·1·3·1·2·3·1·3·2·1·3·1·2·3·1·3·2`, hier `kreis2Gedruckt`); die Folge kehrt
   so nicht zurück und verteilt 8-6-8. `kreis2` ist die um `·1·3` **emendierte** Folge
   (dreimal `1·2·3·1·3·2·1·3`). Belege, in der Reihenfolge ihrer Stärke:
   * **Sie ist erzwungen** (`kreis2_emendation`): keine andere Fortsetzung um zwei
     Negatoren schliesst die gedruckte Folge zu einem Vollkreis. Ausserhalb gerechnet und
     hier kein Satz: Fortsetzungen um null, einen, drei oder vier Negatoren geben keinen
     Vollkreis, und das Einfügen zweier Negatoren an beliebiger Stelle gibt nur noch zwei
     weitere, die mit `1·3` bzw. `3·1` beginnen — Tafel XII beginnt `1·2`.
   * **Der Begriff verlangt `n! = 24`** (`full_length`; Günther 1980 S. 20, und IGN S. 41:
     „24 Stationen"). Die drei anderen ausgeschriebenen Folgen des Textes haben 24.
   * **Günthers Verteilung an der Stelle**, neun-sechs-neun — sie trägt die Länge schon in
     sich (`9 + 6 + 9 = 24`) und ist darum kein von ihr unabhängiger Zeuge.
   * **Tafel XII**: ihre 25 Wertspalten folgen der emendierten Folge in 24 von 25 Spalten.
2. Tafel XII, Spalte 18, lautet in der Textschicht `2 3 □ 2`; die Folge verlangt `2 3 □ 1`.
3. Tafel IV (1980), Spalte 17, lautet `1 4 2 1`; die Folge verlangt `1 4 2 3`.

**Quelle der Emendation (Hermeneutes / Custos, 22.9.).** Der emendierte Kreis 2 steht nicht
nur durch drei innere Zeugen (die 9-6-9-Verteilung, die Länge 24 aller übrigen Kreise,
Tafel XII), sondern durch Günthers eigenen Druck: im *Janusgesicht der Dialektik* (1974)
druckt er denselben Kreis vollständig, mit 24 Negatoren in der Verteilung 9-6-9. Diese
Folge — `janus1974` — ist ein Vollkreis (`janus1974_full`) und ist genau die emendierte
Folge, um einen Schritt rotiert (`janus1974_rotate`); die in IGN gedruckten 22 Negatoren
stehen darin als zusammenhängendes Stück (`janus1974_contains_printed`).
**„Emendation" ist damit das richtige Wort: die Fassung trägt einen Druckfehler, nicht
der Kreis.**

**Druckvorlage.** Die drei Textbefunde sind Druckfehler der *Fassung*, deren Vorlage die
*Hegeljahrbücher* 1979, S. 22–88, sind; ob schon der Originaldruck so aussah, ist am Bestand
nicht zu entscheiden, und die Extraktion ist nicht die Ursache. Befund 2 steht unabhängig
davon, wie man das strittige Kästchen liest.

## Lesart, im Kopf festgelegt und nicht stillschweigend

* **Der Negator wirkt auf WERTE** (`sw` tauscht die Werte `i` und `i + 1`, wo immer sie
  stehen), nicht auf Stellen. So liest Günther (S. 41: „Umtauschverhältnis zwischen dem
  dritten und vierten Wert"), und so reproduzieren seine Tafeln. Der Stellen-Tausch gäbe
  einen isomorphen Graphen und andere Tafeln.
* **Null-Indizierung.** Günthers Werte `1 … 4` sind hier `0 … 3`, seine Negatoren
  `N₁, N₂, N₃` die Indizes `0, 1, 2`.
* **„Hamiltonkreis" ist Günthers Wort** und steht darum im Titel. Den Graphenbegriff führt
  dieses Modul nicht. Dass `kreis1` ein `SimpleGraph.Walk.IsHamiltonianCycle` im Sinn von
  Mathlib ist, ist **gemessen und nicht im Repo**: die Probe steht mit Quelltext in der
  Vorprobe-Notiz (Anhang A). Sie liegt ausserhalb, weil die Graphenbibliothek eine
  Importhülle nachzieht, die das Aggregat sonst nicht trägt, und weil keines der
  bestehenden Targets sie ihrem Zweck nach aufnimmt — das ist eine Entscheidung des
  Architekten, keine des Baus.

## Was dieses Modul NICHT sagt

* **Nicht die 44 und nicht Tafel XX — hier.** Günthers Zahl der vierwertigen Vollkreise
  (IGN S. 41, 1980 S. 20) steht als Liste in `NegationCycleTable` (mindestens 44) und in
  Iff-Form in `NegationCycleSearch` (genau 44, `exactly_fortyfour`). Die Kreiszahlen je
  Umfang (IGN S. 50, Tafel XX) sind ausserhalb des Korpus nachgerechnet und nicht gebaut.
* **Nicht, dass kein Vollkreis 8-8-8 verteilt — hier.** Günther sagt „niemals" (IGN S. 43);
  dieses Modul zeigt an **einer** Folge, seiner eigenen, dass 8-8-8 scheitern *kann*. Die
  Unmöglichkeit für jeden Vollkreis ist `NegationCycleSymmetry.no_888_all`.
* **Nichts über Proemialrelation, Paragraph 20 oder die Zeit.** Günther selbst schreibt
  (IGN S. 58), wer sich mit der Rückkehr des Vollkreises zufriedengebe, habe „völlig das
  Zeitproblem ignoriert". Keine Ledger-Zeile; ob L14-1 (Zyklus) hier einen Träger findet,
  entscheidet Custos mit Hermeneutes.
* **Nichts über „Negativsprache", „Wörterbuch", „Totaläquivalenz".** Das sind Günthers
  Deutungen der Kreise; formalisiert sind die Kreise.
* **Die Spiegelung `N₁ ↔ N₃` hier nur am ersten Beispiel.** Dass sie *jeden* Vollkreis bei
  vier Werten in einen Vollkreis überführt, ist `NegationCycleSymmetry.mirror_all`; für mehr
  Werte ist es ungemessen. (Die Drehsinn-Aussage
  war bis zum 21. September ebenso beschränkt und ist es seit `reverse_full` nicht mehr.)

## Die Genese (Teil 5)

Gebaut auf Anordnung des Architekten vom 23.9.2026 (Sitzungsnachricht 13:15 +0200, mit der Spec
als Anhang) nach `KorpusRev2/Spec_V_O1_O3.md`
(Fassung 2, Mathematiker; Teil O3), begutachtet in
`KorpusRev2/Begutachtung_Spec_V_O1_O3_Impl.md`. Quelle: **HKN** = *Die historische
Kategorie des Neuen* (1970), `KorpusRev1/gg_category.pdf`, S. 25, Wortlaut nach
`KorpusRev1/HKN_1970_Volltext.txt`.

* **K1 — Günthers Doppeldeutigkeit.** Der Umtausch der Werte 1 und 3 „kann … durch den
  Operator N1.2.1, aber auch durch den Operator N2.1.2 aktiviert werden"; die Tafel „gibt das
  'abstrakte' Resultat, das in beiden Fällen gleich ist", aber es „muss uns die Genese dieses
  Resultats wichtig sein" — „die für die Dialektik erforderliche Doppeldeutigkeit einer
  logischen Funktion". `genese_resultat` und `genese_verschieden` sind sein Beispiel:
  dasselbe `endpoint`, verschiedene `stations`. Sie sind **Eichung**, nicht Folgerung —
  zwei `decide` über festen Listen verbrauchen keinen Satz.
  **Zweiter Anker: Metamorphose der Zahl, PDF-S. 9 (gedr. S. 8).** Dieselbe Figur — die
  Umwandlung von 1,2,3 in ihren Rücklauf, einmal „zuerst … die klassische Negation N1", einmal
  mit der Negation, „die vom dritten Wert zum zweiten zurückführt", und „weder Gewinn noch
  Verlust" — und Günther nennt, worum es geht: „die Frage des Primats des Begriffs über den
  Willen oder umgekehrt des Willens über den Begriff". Die Tafeln IIIa/IIIb (PDF-S. 6, gedr.
  S. 5) sind die zwei Wege hin und zurück. **Gemessen:** Tafel IIIa, `N1 N2 N1 N2 N1 N2`, ist
  Zeichen für Zeichen Günthers Folge (4) aus IGN S. 18 (`tafelVI4`), und sie zerfällt in die
  zwei Genesen, `[0,1,0] ++ [1,0,1] = tafelVI4` (definitionsgleich, `example` in Teil 5); ihr
  Vollkreis ist `tafelVI4_full`. Genese ↔ Primat-Frage ist **Günthers eigene Zuordnung**
  (Themensatz vor der Rechnung). *Marken: die Rechnung GEMESSEN; Wortlaut und Tafeln
  QUELLENFEST (am Bild, Hermeneutes 25.9.).*
* **K2 — formal die Zopfrelation.** `braid`: `N_i · N_(i+1) · N_i = N_(i+1) · N_i · N_(i+1)`
  für jedes `m`. Skala **FOLGERUNG**: verbraucht `sw_val` und sagt, was kein Satz des
  Bestandes sagt.
* **K3 — „Doppel-" ist der Fall von drei Werten.** Die Zahl der Genesen des längsten
  Elements (reduzierte Wörter) wächst: 2, 16, 768, 292 864 für 3, 4, 5, 6 Werte. Ausserhalb
  Lean gerechnet (Mathematiker und impl. Instanz, unabhängig); **kein Satz hier**. Die
  ersten zwei stehen seit dem 25.9. als Satz in `Proemial/NegationCycleLength.lean`: bei drei
  Werten sind `N1·2·1` und `N2·1·2` genau die kürzesten Wege zum Rücklauf
  (`genesen_kuerzeste`), bei vier Werten sind es 16 (`rueckwaerts_vier`, gerechnet).
* **K4 — genau dort, wo ein Wert geteilt wird.** Die Zopfrelation gilt für benachbarte
  Negatoren (`braid`); entfernte vertauschen nur (`comm_far`, einseitig notiert als
  `i + 2 ≤ j` — die andere Seite ist dieselbe Gleichung umgekehrt gelesen), und für sie
  gilt der Zopf für **jedes** Paar nicht (`braid_fails_far_all`, Zeuge stets der Wert `i`;
  nachgetragen am 25.9. nach der Abnahme — bis dahin stand das „jedes" nur an einem
  Beispiel, `braid_fails_far`, das jetzt seine Eichung ist). Das „genau" hängt an Z2 und Z3,
  allgemein; am Beispiel geeicht. Günther nennt an seinem Beispiel den Wert 2
  „vermittelnd zwischen 1 und 3" — dass das der **geteilte** Wert der Zopfrelation ist, ist
  **LESART**. Eine zweite Lesart, der Durchgang, ist als Satz gebaut (`track_mediates`, unten
  K-V1–K-V5).
* **K5 — kein §11-Träger.** Günther nennt den *Wert* vermittelnd, nicht die Genese. Die
  Genese ist hier Doppeldeutigkeit einer Funktion, nicht Vermittlung; den vermittelnden
  *Wert* trägt `track_mediates` (K-V1–K-V5); Buchung, wenn Custos
  bucht, an §7 (HKN S. 25). Die zweite Negation definiert dieses Modul nicht; L07-4 bleibt
  offen.
* **K6 — nicht geprüft:** ob die Zopfrelation dieselbe Vermittlung trägt wie das Kriterium
  (B) in `SharedPlaceGrowth`. Bis dahin Wortgleichheit, keine Sachgleichheit.

**Der vermittelnde Wert** (Teil 5, gebaut am 25.9.2026 nach
`KorpusRev2/Spec_Vermittlung_Durchgang.md`, Mathematiker; Probe in
`KorpusRev2/Vermittlung_Durchgang_Probe_Impl.md`):

* **K-V1 — die Quelle.** HKN S. 25: „In dieser ersten und einfachsten trans-klassischen
  Negationstafel spielt nun der Wert 2 eine vermittelnde Rolle zwischen 1 und 3." Der
  vermittelnde ist ein **Wert**, keine Operation. Günther nennt diese Wertbewegung auch in
  der *Metamorphose der Zahl* „Vermittlung": auf PDF-S. 9 (gedr. S. 8) als „dieser relativ
  einfache Fall von Wertbewegung, den Hegel ‹Vermittlung› nennt", und eine Seite früher
  selbst — „einen Vermittlungsvorgang" (PDF-S. 8, gedr. S. 7). Das stützt die Lesart
  „vermittelnd = durchlaufen"; ein neuer Anspruch ist es nicht (**LESART-VERSTÄRKUNG**, kein
  Träger, kein Beleg für §11).
* **K-V2 — der Satz.** `track_mediates`: Unter jedem Negatorwort durchläuft ein Wert jeden
  Wert zwischen Anfang und Ende, in beide Richtungen (`track_between`,
  `track_between_down`), für jedes `m`. Er folgt daraus, dass Günthers Negatoren benachbarte
  Werte tauschen (`sw_step`); einen Negator `1 ↔ 3` gibt es nicht. Bei drei Werten heisst
  das: Der Umtausch von 1 und 3 geht auf keinem Weg ohne die 2. Die drei `example`-Eichungen
  zeigen es an Günthers `N1.2.1` und `N2.1.2`.
* **K-V3 — Lesart.** „vermittelnd = durchlaufen" ist **LESART** an HKN S. 25. Die Fassung für
  `m ≥ 4` („alle Werte dazwischen vermitteln") setzt diese Lesart fort; Günthers Satz ist sie
  nicht.
* **K-V4 — zwei andere Lesarten** fallen bei drei Werten mit ihr zusammen: der geteilte Wert
  (K4 oben) und die geteilte Stelle (`SharedPlaceGrowth`, Kriterium (B), Lille S. 29, dort
  gesetzt; ein anderer Gegenstand: Tafelstellen, nicht Werte). Sie werden genannt, nicht
  entschieden. Bei drei Werten ist die 2 der durchlaufene, der geteilte und, dem Wort nach,
  der geteilte Tafelwert; danach gehen die drei auseinander.
* **K-V5 — nicht die Hegelsche Vermittlung**, kein §11-Anspruch; ob und wie an §11 gebucht
  wird, entscheidet Custos.

## Der kalkültheoretische Bereich der zweiten Negation (drei Werte) — Teil 6

Gebaut auf Anordnung des Architekten vom 25.9.2026 nach `KorpusRev2/Spec_V_O2.md`
(Fassung 2, Mathematiker), begutachtet in `KorpusRev2/Begutachtung_Spec_V_O2_Impl.md`;
Bedingungen (a)–(d) nach `KorpusRev2/Prompt_Custos_O2_und_L07-4.md` und Register §24.

* **(a) Nur der kalkültheoretische Schatten.** Günther: „was man unter dem Hegelschen
  Terminus zweite Negation kalkültheoretisch allein verstehen kann" (HKN S. 23). Kein
  Anspruch auf Hegels Vermittlung. **Dieser Teil löst V nicht ein** (Register §24): er baut
  den Bereich, den Günther bei drei Werten selbst abgrenzt, nicht die Negation, die er
  vermittelnd nennt. Keine Definition der zweiten Negation, kein Bezeichner dieses Namens;
  L07-4 bleibt offen.
* **(b) Günthers Auswahl, quellenfest.** HKN S. 24: die zweite Negation bezieht sich bei
  drei Werten „auf die gesamte Wertstruktur, die außerhalb des klassischen
  Negationsbereiches, der links oben durch Doppelstriche abgegrenzt ist, liegt". Seine vier
  Spalten sind die **Eichung** (`transklassisch3`, Kürzel von links nach rechts gelesen,
  Spalte für Spalte gemessen). Der Kern, der die Auswahl trägt, wörtlich: die N2-Tafel ist
  „mit der vorangehenden Tafel strukturell identisch" (HKN S. 23–24), und im Tafelkopf steht
  N2 unter „trans-klassisch" — strukturell wie die klassische Negation und doch
  trans-klassisch. Dass N2 „die klassische Negation seiner Elementarkontextur" sei, ist
  **ZUORDNUNG**, nicht Günthers Wort. Seine sechste Spalte, `N2.1.2`, fällt auf dieselbe
  Anordnung wie `N1.2.1` — das ist die Zopfrelation (`braid`, `genese_resultat`), und darum
  hat der Bereich vier Elemente und nicht fünf. Hier berühren sich Teil 5 und Teil 6.
* **(c) Nicht für mehr als drei Werte — in diesem Teil.** Für `m ≥ 4` spricht die Quelle:
  die hinzukommenden Werte sind trans-klassisch (HKN S. 24: „Fügt man dann noch einen
  vierten, fünften, sechsten usw. trans-klassischen Wert hinzu, dann erweitert sich jener
  trans-klassische Strukturbereich ganz enorm"), die klassischen bleiben die ersten zwei,
  und die Zone bleibt Ausgang und `N1` (**QUELLENNAH**). Dieser Teil baut nur drei Werte;
  für jedes `m` steht der Bereich in Teil 7 (`transklassisch_card`).
  *Berichtigt am 25.9.2026: die Fassung aus `d61d85d` sagte, die Quelle schweige für
  `m ≥ 4`; das war falsch.*
* **(d) Auf der Kenogramm-Ebene unsichtbar.** Die Negation ändert das Morphogramm nie
  (`Kenogram.PatternInvariance`, 3a5ef78): alle sechs Anordnungen haben dasselbe Kenogramm.
  Verweis, kein Satz dieses Teils.

Skala **ZUSAMMENSTELLUNG**: fünf entschiedene Aussagen über eine feste Sechsermenge, kein
Satz des Bestandes wird verbraucht. Der Wert liegt darin, dass es Günthers eigene Auswahl
ist.

## Der kalkültheoretische Bereich für jede Wertzahl — Teil 7

Gebaut auf Anordnung des Architekten vom 25.9.2026 nach
`KorpusRev2/Spec_Zug2_Bereich_jedes_m.md` (Fassung 2, Mathematiker), begutachtet in
`KorpusRev2/Begutachtung_Spec_Zug2_Impl.md`.

* **K1 — die Zahl.** `transklassisch_card`: bei `m + 2` Werten hat der Bereich
  `(m + 2)! − 2` Elemente. Das ist Definitionen §7 („bei `m` Werten also `m!` Permutationen
  abzüglich des klassischen Bereichs") als Satz, und die Zahl zu Günthers „Fügt man dann
  noch einen vierten, fünften, sechsten usw. trans-klassischen Wert hinzu, dann erweitert
  sich jener trans-klassische Strukturbereich ganz enorm" (HKN S. 24). Skala **FOLGERUNG**.
* **K2 — die Zone.** Sie bleibt Ausgang und `N1`, weil Günther die hinzukommenden Werte
  trans-klassisch nennt: die klassischen bleiben die ersten zwei. **QUELLENNAH**, nicht
  wörtlich für `m ≥ 4`.
* **K3 — das Choice.** `transklassisch_card` trägt `Classical.choice` aus zwei
  Mathlib-Bausteinen: `List.nodup_finRange` (über `negate_perm` in `klassisch_sub`) und
  `List.nodup_permutations`, derselbe Preis wie bei `full_length`. Das offene `simp` in
  `klassisch_nodup` ist eine dritte Quelle; es zu heilen änderte am Zielsatz nichts
  (gemessen, Spec §4). Bei festem `m` ist alles choice-frei entschieden
  (`transklassisch_eq_three`, `transklassisch_four`, `transklassisch_two`).
* **K4 — die Brücke.** `transklassisch_eq_three`: bei drei Werten liefert die allgemeine
  Definition genau Günthers vier aus Teil 6. Teil 7 ersetzt Teil 6 nicht: Teil 6 trägt
  Günthers Auswahl Spalte für Spalte, Teil 7 die Zahl für jedes `m`.
* **K4′ — zwei Werte.** `transklassisch_two`: bei zwei Werten ist der Bereich leer,
  `2! − 2 = 0`, denn die klassische Logik hat nur die erste Negation. Dass das Günthers
  Satz über die Verbundkontextur *ist*, sagt dieser Teil nicht: Verbundkontextur und
  Negationsbereich sind zwei Gegenstände, und die Gleichsetzung wäre eine **ZUORDNUNG**.
* **K5 — Bedingung (a) gilt.** Der kalkültheoretische Schatten, nicht die Hegelsche zweite
  Negation; V ist nicht eingelöst, L07-4 bleibt offen.
* **K6 — nicht konstruktiv, hier.** Dass jedes Element als Negatorwort gegeben ist, sagt
  dieser Teil nicht. Jedes Element ist eine Anordnung, und für jede Anordnung liefert
  `NegationCycleSJT.reach_all` ein Negatorwort, choice-frei; das ist M4 in der
  Listen-Fassung.

## Axiomprofil

Gemessen und am Dateiende gewacht. Die Zeugen-Sätze, `triadic_unique` und
`kreis2_emendation` tragen `[propext]` — **ohne `Classical.choice`**: der Listen-Träger
braucht `DecidableEq`, keine `Fintype`-Instanz. (Über `Equiv.Perm (Fin 4)` gemessen zieht
derselbe Inhalt das volle Profil, siehe Vorprobe §3.) `negate_negate` trägt zusätzlich
`Quot.sound` (`funext` unter `List.map`), `visits_every_arrangement` trägt, was
`List.mem_permutations'` trägt. **Ein Satz trägt das volle Profil: `full_length`**, und zu
Recht — er ist der allgemeine Satz für jedes `m`, und sein `Classical.choice` kommt aus
Mathlibs Sätzen über `List.permutations` (`nodup_permutations`,
`permutations_perm_permutations'`, `length_permutations`), nicht aus der Sache.

**Geheilt am 22.9.2026:** bis dahin trug auch `triadic_unique'` das volle Profil, weil es
`full_length` verbrauchte. Für `m = 2` ist die Nodup-Eigenschaft der sechs Anordnungen
**entscheidbar** (`perms2_nodup`, axiomfrei), und `full_length2` braucht den Mathlib-Baustein
nicht. Dasselbe Muster wie `full_length3` in `NegationCycleSearch` (Fallstrick 10, die
Baustein-Gattung); gemessen bei der Abnahme der dortigen Heilung.

`janus1974_full`, `janus1974_rotate` und `janus1974_contains_printed` tragen `[propext]`,
gemessen am 22.9. bzw. 23.9.2026.
`List.permutations` reduziert unter `decide` nicht; darum die strukturelle Fassung
`List.permutations'`. Die Umkehr-Sätze (`fullStations_reverse`, `reverse_full` und ihre
Hilfssätze) tragen `[propext, Quot.sound]` und sind damit die ersten Sätze des Moduls, die
**nicht** durch `decide` gehen.
Teil 5 (gemessen am 23.9.2026 nach grünem Bau): `sw_val` ist **axiomfrei**, `braid`
und `comm_far` tragen `[propext, Quot.sound]`, ebenso `braid_fails_far_all` (25.9.,
Schritt für Schritt über `sw_val`: ein `split_ifs` über alle sechs verschachtelten `sw`
läuft in den Heartbeat-Timeout und meldet sich dann als axiomfrei — Fallstrick 23);
`braid_fails_far`,
`genese_resultat` und `genese_verschieden` tragen `[propext]`. Der vermittelnde Wert
(25.9.): `sw_step`, `track_between`, `track_between_down` und `track_mediates` tragen
`[propext, Quot.sound]`, `track_last` trägt `[propext]`. Mit offenem
`simp` statt `rw [if_pos …]` in `sw_val` zöge die Kette `Classical.choice`
(Spec, Bau-Hinweis H1; Fallstrick 21) — die Taktik, nicht die Sache.
Teil 6 (gemessen am 25.9.2026 nach grünem Bau): `transklassisch3_nodup`,
`transklassisch3_disjoint`, `zone_exhausts`, `zone_count` und `transklassisch3_card`
tragen `[propext]`. Auf Mathlibs `Equiv.Perm (Fin 3)` trug derselbe Inhalt das volle
Profil (Optionen-Notiz vom 23.9., P2) — der Träger, nicht die Sache. Aus demselben Grund
steht die Erschöpfung als Inklusion plus Längen: als `List.Perm` formuliert zöge sie
`Classical.choice` (Spec, Bau-Hinweis; nachgemessen).
Teil 7 (gemessen am 25.9.2026 nach grünem Bau): `sw_bij`, `transklassisch_eq_three`,
`transklassisch_four` und `transklassisch_two` tragen `[propext]`, `negate_perm`
`[propext, Quot.sound]`; `klassisch_sub`, `klassisch_nodup` und `transklassisch_card` tragen
`[propext, Classical.choice, Quot.sound]` — die Herkunft steht oben unter K3.
-/

namespace Reformulation.Proemial.NegationCycle

-- ============================================================
-- Teil 1 — Negator, Negationsfolge, Vollkreis
-- ============================================================

/-- Der Umtausch der Werte `i` und `i + 1`; alle anderen Werte bleiben. -/
def sw {m : ℕ} (i : Fin m) (v : Fin (m + 1)) : Fin (m + 1) :=
  if v = i.castSucc then i.succ else if v = i.succ then i.castSucc else v

/-- Der Negator `N_{i+1}` auf einer Wertfolge: der Werte-Umtausch an jeder Stelle. -/
def negate {m : ℕ} (i : Fin m) (l : List (Fin (m + 1))) : List (Fin (m + 1)) := l.map (sw i)

/-- Die Stationen einer Negationsfolge vom Ausgang `l` an, ohne die zuletzt erreichte. -/
def stations {m : ℕ} : List (Fin m) → List (Fin (m + 1)) → List (List (Fin (m + 1)))
  | [], _ => []
  | i :: is, l => l :: stations is (negate i l)

/-- Die Wertfolge, die eine Negationsfolge vom Ausgang `l` aus erreicht. -/
def endpoint {m : ℕ} : List (Fin m) → List (Fin (m + 1)) → List (Fin (m + 1))
  | [], l => l
  | i :: is, l => endpoint is (negate i l)

/-- Der Ausgang: die Werte in ihrer Ordnung (Günthers `p`). -/
def origin (m : ℕ) : List (Fin (m + 1)) := List.finRange (m + 1)

/-- Eine Negationsfolge ist ein **Vollkreis**, wenn sie zum Ausgang zurückkehrt und dabei
jede Anordnung aller Werte einmal und nur einmal durchläuft.

*„Vollkreis" ist der Begriff des Bestandes.* Günther gebraucht „Kreis" in IGN in zwei
Bedeutungen (Definitionen §21, Abschnitt 8). Die eine ist der **Hamiltonkreis**: die Folgen
(4) und (5), die alle Anordnungen durchlaufen („die Permutationen unseres Hamiltonkreises",
S. 26). Die andere ist die **Kreisrelation** `K` des Katalogs zwischen zwei Stationen, mit
Links- und Rechtsdrall (S. 26 f., 27, 37). **Der Vollkreis ist der Hamiltonkreis** (*Marke:
ZUORDNUNG*). Die Kreisrelation ist etwas anderes. Sie steht als Einordnung einer
Wertabbildung (`Kl`, `Kr`) bei drei Werten in `NegationCycleCatalog` und als Dreierzyklus
(`IsThree`) für jede Wertzahl in `NegationCycleThreeCycle`; der Katalog steht auf dem
Hamiltonkreis (`NegationCycleCatalog.alt1_basis`).

Den Hamiltonkreis gibt es erst ab der zweiten Negation (IGN S. 29: „eine zweite Negation. Die
aber gestattet nur einen Kreis"; die Seite zählt Kreise und kennt weder Drall noch `K`), also
ab `2 ≤ m`. Bei zwei Werten (`m = 1`) ist der Vollkreis `N1·N1`
(`NegationCycleSJT.sjt1_full`), Günthers zweifacher Umtausch. Einen eigenen Namen für den
Hamiltonkreis gibt es nicht, weil er keinen Satz trüge; er würde die Aussage von S. 29 durch
Definition wahr machen. -/
structure IsFullCycle {m : ℕ} (seq : List (Fin m)) : Prop where
  /-- Die Folge kehrt zum Ausgang zurück. -/
  closes : endpoint seq (origin m) = origin m
  /-- Keine Station kehrt wieder. -/
  nodup : (stations seq (origin m)).Nodup
  /-- Jede Station ist eine Anordnung aller Werte. -/
  only_arrangements : ∀ l ∈ stations seq (origin m), l ∈ (origin m).permutations'
  /-- Jede Anordnung aller Werte ist Station. -/
  all_arrangements : ∀ l ∈ (origin m).permutations', l ∈ stations seq (origin m)

instance {m : ℕ} (seq : List (Fin m)) : Decidable (IsFullCycle seq) :=
  decidable_of_iff
    (endpoint seq (origin m) = origin m ∧ (stations seq (origin m)).Nodup ∧
      (∀ l ∈ stations seq (origin m), l ∈ (origin m).permutations') ∧
      (∀ l ∈ (origin m).permutations', l ∈ stations seq (origin m)))
    ⟨fun ⟨a, b, c, d⟩ => ⟨a, b, c, d⟩, fun ⟨a, b, c, d⟩ => ⟨a, b, c, d⟩⟩

/-- Der Werte-Umtausch ist eine Involution. -/
theorem sw_sw {m : ℕ} (i : Fin m) (v : Fin (m + 1)) : sw i (sw i v) = v := by
  unfold sw
  have h : i.castSucc ≠ i.succ := Fin.ne_of_lt Fin.castSucc_lt_succ
  by_cases h1 : v = i.castSucc
  · simp [h1, h.symm]
  · by_cases h2 : v = i.succ
    · simp [h2]
    · simp [h1, h2]

/-- Der Negator, auf sich selbst angewendet, hebt sich auf. -/
theorem negate_negate {m : ℕ} (i : Fin m) (l : List (Fin (m + 1))) :
    negate i (negate i l) = l := by
  simp [negate, List.map_map, Function.comp_def, sw_sw]

/-- Ein Vollkreis trifft jede Permutation des Ausgangs. -/
theorem visits_every_arrangement {m : ℕ} {seq : List (Fin m)} (h : IsFullCycle seq)
    {l : List (Fin (m + 1))} (hl : l.Perm (origin m)) : l ∈ stations seq (origin m) :=
  h.all_arrangements l (List.mem_permutations'.mpr hl)

/-- Eine Negationsfolge hat so viele Stationen wie Negatoren. -/
theorem stations_length {m : ℕ} (seq : List (Fin m)) (l : List (Fin (m + 1))) :
    (stations seq l).length = seq.length := by
  induction seq generalizing l with
  | nil => rfl
  | cons i is ih => simp [stations, ih]

open List in
/-- **Ein Vollkreis über `m + 1` Werten hat `(m + 1)!` Negatoren** — Günthers „n!
Negationsschritte" (1980, S. 20). -/
theorem full_length {m : ℕ} {seq : List (Fin m)} (h : IsFullCycle seq) :
    seq.length = (m + 1).factorial := by
  have hn : (origin m).permutations'.Nodup :=
    ((permutations_perm_permutations' _).nodup_iff).mp
      (nodup_permutations _ (nodup_finRange _))
  have hp : (stations seq (origin m)).Perm (origin m).permutations' :=
    (perm_ext_iff_of_nodup h.nodup hn).mpr fun l =>
      ⟨h.only_arrangements l, h.all_arrangements l⟩
  rw [← stations_length seq (origin m), hp.length_eq,
    ← (permutations_perm_permutations' _).length_eq, length_permutations]
  simp [origin]

-- ============================================================
-- Teil 1b — der Gegen-Drehsinn: die Umkehrung eines Vollkreises
-- ============================================================

theorem endpoint_append {m : ℕ} (seq : List (Fin m)) (i : Fin m) (l : List (Fin (m + 1))) :
    endpoint (seq ++ [i]) l = negate i (endpoint seq l) := by
  induction seq generalizing l with
  | nil => rfl
  | cons j js ih => simpa [endpoint] using ih (negate j l)

theorem stations_append {m : ℕ} (seq : List (Fin m)) (i : Fin m) (l : List (Fin (m + 1))) :
    stations (seq ++ [i]) l = stations seq l ++ [endpoint seq l] := by
  induction seq generalizing l with
  | nil => rfl
  | cons j js ih => simpa [stations, endpoint] using ih (negate j l)

/-- Die **volle** Stationenfolge: die Stationen samt der zuletzt erreichten Wertfolge. -/
def fullStations {m : ℕ} (seq : List (Fin m)) (l : List (Fin (m + 1))) :
    List (List (Fin (m + 1))) :=
  stations seq l ++ [endpoint seq l]

theorem fullStations_cons {m : ℕ} (j : Fin m) (js : List (Fin m)) (l : List (Fin (m + 1))) :
    fullStations (j :: js) l = l :: fullStations js (negate j l) := rfl

theorem fullStations_append {m : ℕ} (seq : List (Fin m)) (i : Fin m) (l : List (Fin (m + 1))) :
    fullStations (seq ++ [i]) l = fullStations seq l ++ [negate i (endpoint seq l)] := by
  simp [fullStations, stations_append, endpoint_append]

/-- Die umgekehrte Folge führt vom Ziel zum Ausgang zurück. -/
theorem endpoint_reverse {m : ℕ} (seq : List (Fin m)) (l : List (Fin (m + 1))) :
    endpoint seq.reverse (endpoint seq l) = l := by
  induction seq generalizing l with
  | nil => rfl
  | cons j js ih =>
    rw [List.reverse_cons, endpoint_append]
    show negate j (endpoint js.reverse (endpoint js (negate j l))) = l
    rw [ih (negate j l), negate_negate]

/-- **Die umgekehrte Folge durchläuft dieselbe Stationenfolge rückwärts.** -/
theorem fullStations_reverse {m : ℕ} (seq : List (Fin m)) (l : List (Fin (m + 1))) :
    fullStations seq.reverse (endpoint seq l) = (fullStations seq l).reverse := by
  induction seq generalizing l with
  | nil => rfl
  | cons j js ih =>
    rw [List.reverse_cons]
    show fullStations (js.reverse ++ [j]) (endpoint js (negate j l)) = _
    rw [fullStations_append, ih (negate j l), endpoint_reverse, negate_negate,
      fullStations_cons, List.reverse_cons]

/-- **Die Umkehrung eines Vollkreises ist ein Vollkreis** — Günthers „Drehsinn und
Gegen-Drehsinn", als Satz für jeden Kreis. -/
theorem reverse_full {m : ℕ} {seq : List (Fin m)} (h : IsFullCycle seq) :
    IsFullCycle seq.reverse := by
  cases seq with
  | nil => simpa using h
  | cons j js =>
    set seq := j :: js with hseq
    have hc : endpoint seq (origin m) = origin m := h.closes
    have hcl : endpoint seq.reverse (origin m) = origin m := by
      have := endpoint_reverse seq (origin m); rwa [hc] at this
    have hfs : fullStations seq.reverse (origin m) = (fullStations seq (origin m)).reverse := by
      have := fullStations_reverse seq (origin m); rwa [hc] at this
    obtain ⟨t, ht⟩ : ∃ t, stations seq (origin m) = origin m :: t :=
      ⟨stations js (negate j (origin m)), rfl⟩
    have key : stations seq.reverse (origin m) = origin m :: t.reverse := by
      have e1 : fullStations seq.reverse (origin m)
          = stations seq.reverse (origin m) ++ [origin m] := by rw [fullStations, hcl]
      have e2 : (fullStations seq (origin m)).reverse
          = (origin m :: t.reverse) ++ [origin m] := by rw [fullStations, hc, ht]; simp
      rw [e1, e2] at hfs
      exact List.append_cancel_right hfs
    have hperm : (stations seq.reverse (origin m)).Perm (stations seq (origin m)) := by
      rw [key, ht]; exact (List.perm_cons _).mpr (List.reverse_perm t)
    exact ⟨hcl, hperm.nodup_iff.mpr h.nodup,
      fun l hl => h.only_arrangements l (hperm.mem_iff.mp hl),
      fun l hl => hperm.mem_iff.mpr (h.all_arrangements l hl)⟩

-- ============================================================
-- Teil 2 — dreiwertig: Tafel VI (IGN S. 18)
-- ============================================================

/-- Folge (4): `p ≡ N₁·₂·₁·₂·₁·₂ p`. -/
def tafelVI4 : List (Fin 2) := [0, 1, 0, 1, 0, 1]

/-- Folge (5): `p ≡ N₂·₁·₂·₁·₂·₁ p`. -/
def tafelVI5 : List (Fin 2) := [1, 0, 1, 0, 1, 0]

theorem tafelVI4_full : IsFullCycle tafelVI4 := by decide

theorem tafelVI5_full : IsFullCycle tafelVI5 := by decide

/-- Die zwei Folgen sind ein Kreis in zwei Drehsinnen. -/
theorem tafelVI5_eq_reverse : tafelVI5 = tafelVI4.reverse := by decide

/-- **Dreiwertig gibt es nur diesen einen Kreis.** Unter allen Negationsfolgen der Länge
sechs sind (4) und (5) die einzigen Vollkreise. -/
theorem triadic_unique : ∀ a b c d e f : Fin 2, IsFullCycle [a, b, c, d, e, f] →
    [a, b, c, d, e, f] = tafelVI4 ∨ [a, b, c, d, e, f] = tafelVI5 := by decide

/-- Die sechs Anordnungen dreier Werte sind paarweise verschieden — entscheidbar, und darum
ohne den Mathlib-Baustein, der `full_length` das `Classical.choice` einträgt. -/
theorem perms2_nodup : (origin 2).permutations'.Nodup := by decide

/-- `full_length` für zwei Negatoren (drei Werte), ohne `Classical.choice`. -/
theorem full_length2 {seq : List (Fin 2)} (h : IsFullCycle seq) : seq.length = 6 := by
  have hp : (stations seq (origin 2)).Perm (origin 2).permutations' :=
    (List.perm_ext_iff_of_nodup h.nodup perms2_nodup).mpr fun l =>
      ⟨h.only_arrangements l, h.all_arrangements l⟩
  have h1 := stations_length seq (origin 2)
  have h2 : (origin 2).permutations'.length = 6 := by decide
  have h3 := hp.length_eq
  omega

/-- Dasselbe ohne Längenvoraussetzung: **jeder** dreiwertige Vollkreis ist (4) oder (5). -/
theorem triadic_unique' (seq : List (Fin 2)) (h : IsFullCycle seq) :
    seq = tafelVI4 ∨ seq = tafelVI5 := by
  have hl : seq.length = 6 := full_length2 h
  match seq, hl with
  | [a, b, c, d, e, f], _ => exact triadic_unique a b c d e f h

-- ============================================================
-- Teil 3 — vierwertig: die drei Beispielkreise (IGN S. 44–45; 1980 Tafel IV)
-- ============================================================

/-- IGN S. 44, „Unser erster Hamiltonkreis". -/
def kreis1 : List (Fin 3) :=
  [0, 1, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 2, 1, 0, 1, 0, 1, 2, 1, 0, 2]

/-- IGN S. 44, der zweite Kreis — **um `·1·3` emendiert**, siehe Kopf, Textbefund 1, und
`kreis2_emendation`. -/
def kreis2 : List (Fin 3) :=
  [0, 1, 2, 0, 2, 1, 0, 2, 0, 1, 2, 0, 2, 1, 0, 2, 0, 1, 2, 0, 2, 1, 0, 2]

/-- IGN S. 45, der dritte Kreis; zugleich die Negatorfolge über Tafel IV (1980, S. 20). -/
def kreis3 : List (Fin 3) :=
  [0, 1, 2, 1, 2, 1, 0, 1, 0, 1, 2, 1, 2, 1, 0, 1, 0, 1, 2, 1, 2, 1, 0, 1]

/-- Der zweite Kreis, **wie er IGN S. 44 gedruckt steht**: 22 Negatoren. -/
def kreis2Gedruckt : List (Fin 3) :=
  [0, 1, 2, 0, 2, 1, 0, 2, 0, 1, 2, 0, 2, 1, 0, 2, 0, 1, 2, 0, 2, 1]

set_option maxRecDepth 100000 in
theorem kreis1_full : IsFullCycle kreis1 := by decide

set_option maxRecDepth 100000 in
theorem kreis2_full : IsFullCycle kreis2 := by decide

set_option maxRecDepth 100000 in
theorem kreis3_full : IsFullCycle kreis3 := by decide

/-- Die gedruckte Folge kehrt nicht zum Ausgang zurück. -/
theorem kreis2Gedruckt_not_closed : endpoint kreis2Gedruckt (origin 3) ≠ origin 3 := by
  decide

set_option maxRecDepth 100000 in
/-- **Die Emendation ist erzwungen.** Unter allen Fortsetzungen der gedruckten Folge um
zwei Negatoren gibt genau `·1·3` einen Vollkreis. -/
theorem kreis2_emendation :
    ∀ a b : Fin 3, IsFullCycle (kreis2Gedruckt ++ [a, b]) ↔ (a = 0 ∧ b = 2) := by
  decide

/-- `kreis2` ist die emendierte Folge. -/
theorem kreis2_eq : kreis2 = kreis2Gedruckt ++ [0, 2] := by decide

/-- **Günthers eigener Druck desselben Kreises**: *Das Janusgesicht der Dialektik*
(Hegel-Jahrbuch 1974), S. 24 der vordenker-Fassung, `p ≡ N 3·1·2·3·1·3·2·1·3·…·3·2·1 p`,
24 Negatoren. Zeuge der Emendation — er tritt neben `kreis2`, nicht an seine Stelle. -/
def janus1974 : List (Fin 3) :=
  [2, 0, 1, 2, 0, 2, 1, 0, 2, 0, 1, 2, 0, 2, 1, 0, 2, 0, 1, 2, 0, 2, 1, 0]

set_option maxRecDepth 100000 in
/-- Der Druck von 1974 ist ein Vollkreis. -/
theorem janus1974_full : IsFullCycle janus1974 := by decide

/-- **Der Druck von 1974 ist die emendierte Folge, um einen Schritt rotiert** —
`List.rotate 23` stellt das letzte Glied an den Anfang. Dieselbe Folge, nicht nur eine
gleich lange. -/
theorem janus1974_rotate : janus1974 = kreis2.rotate 23 := by decide

/-- **Die 22 gedruckten Negatoren stehen im Druck von 1974 als zusammenhängendes Stück** —
umrahmt von dem einen Negator davor und dem einen danach. -/
theorem janus1974_contains_printed : janus1974 = [2] ++ kreis2Gedruckt ++ [0] := by decide

/-- Familie 10-9-5. -/
theorem kreis1_family : kreis1.count 0 = 10 ∧ kreis1.count 1 = 9 ∧ kreis1.count 2 = 5 := by
  decide

/-- Familie 9-6-9. -/
theorem kreis2_family : kreis2.count 0 = 9 ∧ kreis2.count 1 = 6 ∧ kreis2.count 2 = 9 := by
  decide

/-- Familie 6-12-6. -/
theorem kreis3_family : kreis3.count 0 = 6 ∧ kreis3.count 1 = 12 ∧ kreis3.count 2 = 6 := by
  decide

theorem kreis1_reverse_full : IsFullCycle kreis1.reverse := reverse_full kreis1_full

theorem kreis2_reverse_full : IsFullCycle kreis2.reverse := reverse_full kreis2_full

theorem kreis3_reverse_full : IsFullCycle kreis3.reverse := reverse_full kreis3_full

set_option maxRecDepth 100000 in
/-- Die Spiegelung `N₁ ↔ N₃` eines Vollkreises, am ersten Beispiel. -/
theorem kreis1_mirror_full : IsFullCycle (kreis1.map Fin.rev) := by decide

/-- Die Spiegelung führt 10-9-5 in 5-9-10 über. -/
theorem kreis1_mirror_family :
    (kreis1.map Fin.rev).count 0 = 5 ∧ (kreis1.map Fin.rev).count 1 = 9 ∧
      (kreis1.map Fin.rev).count 2 = 10 := by
  decide

-- ============================================================
-- Teil 4 — Günthers Gegenbeispiel: die Folge (23) (IGN S. 45–46)
-- ============================================================

/-- Folge (23): `N₁·₂·₃`, achtmal. -/
def pseudo : List (Fin 3) :=
  [0, 1, 2, 0, 1, 2, 0, 1, 2, 0, 1, 2, 0, 1, 2, 0, 1, 2, 0, 1, 2, 0, 1, 2]

/-- Die Folge kehrt zum Ausgang zurück … -/
theorem pseudo_closes : endpoint pseudo (origin 3) = origin 3 := by decide

/-- … verteilt die Operatoren gleich … -/
theorem pseudo_family : pseudo.count 0 = 8 ∧ pseudo.count 1 = 8 ∧ pseudo.count 2 = 8 := by
  decide

/-- … durchläuft aber in der zweiten Hälfte noch einmal die erste … -/
theorem pseudo_half :
    stations (pseudo.take 12) (origin 3) =
      stations (pseudo.drop 12) (endpoint (pseudo.take 12) (origin 3)) := by
  decide

set_option maxRecDepth 100000 in
/-- … und ist darum kein Vollkreis. -/
theorem pseudo_not_full : ¬ IsFullCycle pseudo := by decide

-- ============================================================
-- Teil 5 — die Genese: zwei Wege, ein Umtausch (HKN S. 25)
-- ============================================================

/-- Der Negator auf der Ebene der Werte. Werkzeug für `braid` und `comm_far`; mit
`rw [if_pos …]` / `rw [if_neg …]` bewiesen, nicht mit offenem `simp` (Fallstrick 21). -/
theorem sw_val {m : ℕ} (i : Fin m) (v : Fin (m + 1)) :
    (sw i v).val = if v.val = i.val then i.val + 1
                   else if v.val = i.val + 1 then i.val else v.val := by
  unfold sw
  have hc : i.castSucc.val = i.val := Fin.val_castSucc i
  have hs : i.succ.val = i.val + 1 := Fin.val_succ i
  by_cases h1 : v.val = i.val
  · have e1 : v = i.castSucc := Fin.ext (by rw [hc]; exact h1)
    rw [if_pos e1, if_pos h1, hs]
  · have e1 : v ≠ i.castSucc := fun h => h1 (by rw [h, hc])
    rw [if_neg e1, if_neg h1]
    by_cases h2 : v.val = i.val + 1
    · have e2 : v = i.succ := Fin.ext (by rw [hs]; exact h2)
      rw [if_pos e2, if_pos h2, hc]
    · have e2 : v ≠ i.succ := fun h => h2 (by rw [h, hs])
      rw [if_neg e2, if_neg h2]

/-- **Die Zopfrelation**: benachbarte Negatoren, die einen Wert teilen, erreichen auf zwei
Wegen dasselbe — `N_i · N_{i+1} · N_i = N_{i+1} · N_i · N_{i+1}`, für jedes `m`. -/
theorem braid {m : ℕ} (i j : Fin m) (hij : j.val = i.val + 1) (v : Fin (m + 1)) :
    sw i (sw j (sw i v)) = sw j (sw i (sw j v)) := by
  apply Fin.ext
  rw [sw_val, sw_val, sw_val, sw_val, sw_val, sw_val, hij]
  split_ifs <;> omega

/-- Entfernte Negatoren, die keinen Wert teilen, vertauschen nur. Einseitig notiert
(`i + 2 ≤ j`); die andere Seite ist dieselbe Gleichung umgekehrt gelesen. -/
theorem comm_far {m : ℕ} (i j : Fin m) (h : i.val + 2 ≤ j.val) (v : Fin (m + 1)) :
    sw i (sw j v) = sw j (sw i v) := by
  apply Fin.ext
  rw [sw_val, sw_val, sw_val, sw_val]
  split_ifs <;> omega

/-- Für entfernte Negatoren gilt die Zopfrelation **nicht**: `N₁ · N₃ · N₁ ≠ N₃ · N₁ · N₃`,
am Wert `0` von vier Werten — die Eichung von `braid_fails_far_all` an einem Fall. -/
theorem braid_fails_far :
    sw (0 : Fin 3) (sw 2 (sw 0 0)) ≠ sw (2 : Fin 3) (sw 0 (sw 2 0)) := by decide

/-- **Für jedes entfernte Paar** scheitert die Zopfrelation, für jedes `m`; Zeuge ist stets
der Wert `i`. Schritt für Schritt über `sw_val` bewiesen — ein `split_ifs` über alle sechs
verschachtelten `sw` läuft in den Heartbeat-Timeout (Fallstrick 23). -/
theorem braid_fails_far_all {m : ℕ} (i j : Fin m) (h : i.val + 2 ≤ j.val) :
    sw i (sw j (sw i i.castSucc)) ≠ sw j (sw i (sw j i.castSucc)) := by
  intro heq
  have hc : (i.castSucc).val = i.val := Fin.val_castSucc i
  have l1 : (sw i i.castSucc).val = i.val + 1 := by
    rw [sw_val]; split_ifs; omega
  have l2 : (sw j (sw i i.castSucc)).val = i.val + 1 := by
    rw [sw_val, l1]; split_ifs <;> omega
  have l3 : (sw i (sw j (sw i i.castSucc))).val = i.val := by
    rw [sw_val, l2]; split_ifs <;> omega
  have r1 : (sw j i.castSucc).val = i.val := by
    rw [sw_val, hc]; split_ifs <;> omega
  have r2 : (sw i (sw j i.castSucc)).val = i.val + 1 := by
    rw [sw_val, r1]; split_ifs <;> omega
  have r3 : (sw j (sw i (sw j i.castSucc))).val = i.val + 1 := by
    rw [sw_val, r2]; split_ifs <;> omega
  have := congrArg Fin.val heq
  omega

/-- Der Weg eines Wertes unter einer Negationsfolge: die Werte, die `v` nacheinander annimmt;
Anfang `v`, Ende das Bild von `v` unter dem ganzen Wort. -/
def track {m : ℕ} : List (Fin m) → Fin (m + 1) → List (Fin (m + 1))
  | [], v => [v]
  | i :: is, v => v :: track is (sw i v)

/-- Ein Negator bewegt einen Wert um höchstens eins: Günthers Negatoren tauschen benachbarte
Werte, einen Negator `1 ↔ 3` gibt es nicht. -/
theorem sw_step {m : ℕ} (i : Fin m) (v : Fin (m + 1)) :
    (sw i v).val ≤ v.val + 1 ∧ v.val ≤ (sw i v).val + 1 := by
  have h := sw_val i v
  constructor
  · rw [h]; split_ifs <;> omega
  · rw [h]; split_ifs <;> omega

/-- Der Weg endet am Bild von `v`. -/
theorem track_last {m : ℕ} (w : List (Fin m)) (v : Fin (m + 1)) :
    (track w v).getLast? = some (w.foldl (fun x i => sw i x) v) := by
  induction w generalizing v with
  | nil => rfl
  | cons i is ih =>
    simp only [track, List.foldl]
    rw [List.getLast?_cons, ih]; rfl

/-- Aufwärts: steigt ein Wert von `v` auf sein Bild, so nimmt er jeden Wert dazwischen an. -/
theorem track_between {m : ℕ} (w : List (Fin m)) (v c : Fin (m + 1))
    (h1 : v.val ≤ c.val) (h2 : c.val ≤ (w.foldl (fun x i => sw i x) v).val) :
    c ∈ track w v := by
  induction w generalizing v with
  | nil =>
    simp only [List.foldl] at h2
    have : c = v := Fin.ext (by omega)
    simp [track, this]
  | cons i is ih =>
    simp only [List.foldl] at h2
    by_cases hc : c = v
    · simp [track, hc]
    · have hlt : v.val < c.val := lt_of_le_of_ne h1 (fun e => hc (Fin.ext e.symm))
      have hs := (sw_step i v).1
      have : (sw i v).val ≤ c.val := by omega
      exact List.mem_cons_of_mem _ (ih (sw i v) this h2)

/-- Abwärts: fällt ein Wert von `v` auf sein Bild, so nimmt er jeden Wert dazwischen an. -/
theorem track_between_down {m : ℕ} (w : List (Fin m)) (v c : Fin (m + 1))
    (h1 : c.val ≤ v.val) (h2 : (w.foldl (fun x i => sw i x) v).val ≤ c.val) :
    c ∈ track w v := by
  induction w generalizing v with
  | nil =>
    simp only [List.foldl] at h2
    have : c = v := Fin.ext (by omega)
    simp [track, this]
  | cons i is ih =>
    simp only [List.foldl] at h2
    by_cases hc : c = v
    · simp [track, hc]
    · have hlt : c.val < v.val := lt_of_le_of_ne h1 (fun e => hc (Fin.ext e))
      have hs := (sw_step i v).2
      have : c.val ≤ (sw i v).val := by omega
      exact List.mem_cons_of_mem _ (ih (sw i v) this h2)

/-- **Der vermittelnde Wert wird durchlaufen** (HKN S. 25, Lesart „vermittelnd =
durchlaufen"): unter jedem Negatorwort nimmt ein Wert jeden Wert zwischen Anfang und Ende an,
in beide Richtungen, für jedes `m`. -/
theorem track_mediates {m : ℕ} (w : List (Fin m)) (v c : Fin (m + 1))
    (h : (v.val ≤ c.val ∧ c.val ≤ (w.foldl (fun x i => sw i x) v).val) ∨
         ((w.foldl (fun x i => sw i x) v).val ≤ c.val ∧ c.val ≤ v.val)) :
    c ∈ track w v := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact track_between w v c h1 h2
  · exact track_between_down w v c h2 h1

/-- Eichung, Günthers `N1.2.1`: der Wert 1 läuft `1 → 2 → 3 → 3` (0-basiert). -/
example : track ([0, 1, 0] : List (Fin 2)) 0 = [0, 1, 2, 2] := by decide

/-- Eichung, Günthers `N2.1.2`: der Wert 1 läuft `1 → 1 → 2 → 3`. -/
example : track ([1, 0, 1] : List (Fin 2)) 0 = [0, 0, 1, 2] := by decide

/-- Eichung, der Rückweg unter `N1.2.1`: der Wert 3 läuft `3 → 3 → 2 → 1`, über die 2. -/
example : track ([0, 1, 0] : List (Fin 2)) 2 = [2, 2, 1, 0] := by decide

/-- **Eichung an HKN S. 25**: `N1.2.1` und `N2.1.2` geben dasselbe „abstrakte Resultat",
den Umtausch der Werte 1 und 3 … -/
theorem genese_resultat :
    endpoint ([0, 1, 0] : List (Fin 2)) (origin 2) =
      endpoint ([1, 0, 1] : List (Fin 2)) (origin 2) := by decide

/-- … auf zwei verschiedenen Wegen: die Zwischenstände sind Günthers „beiden echten
zyklischen Wertfolgen 2, 3, 1 und 3, 1, 2". -/
theorem genese_verschieden :
    stations ([0, 1, 0] : List (Fin 2)) (origin 2) ≠
      stations ([1, 0, 1] : List (Fin 2)) (origin 2) := by decide

/-- Eichung an Metamorphose der Zahl, Tafel IIIa (PDF-S. 6, gedr. S. 5): die zwei Genesen
hintereinander, hin über `N1.2.1` und zurück über `N2.1.2`, sind Zeichen für Zeichen Günthers
Folge (4) aus IGN S. 18 — definitionsgleich; ihr Vollkreis ist `tafelVI4_full`. -/
example : ([0, 1, 0] ++ [1, 0, 1] : List (Fin 2)) = tafelVI4 := rfl

-- ============================================================
-- Teil 6 — der kalkültheoretische Bereich der zweiten Negation (drei Werte, HKN S. 24)
-- ============================================================

/-- Die Doppelstrich-Zone bei drei Werten: der Ausgang und die erste Negation `N1`
(HKN S. 24; tml Tafel II). -/
def klassisch3 : List (List (Fin 3)) := [origin 2, endpoint [0] (origin 2)]

/-- Günthers vier trans-klassische Spalten (HKN S. 24) als Negatorwörter, Kürzel von links
nach rechts gelesen: `N2`, `N2.1`, `N1.2`, `N1.2.1`. -/
def transklassisch3 : List (List (Fin 3)) :=
  [endpoint [1] (origin 2), endpoint [1, 0] (origin 2),
   endpoint [0, 1] (origin 2), endpoint [0, 1, 0] (origin 2)]

/-- Eichung: die Zone ist Günthers Ausgang `1 2 3` und seine Spalte `N1`, `2 1 3`. -/
example : klassisch3 = [[0, 1, 2], [1, 0, 2]] := by decide

/-- Eichung, Spalte für Spalte: `N2` = `1 3 2`, `N2.1` = `2 3 1`, `N1.2` = `3 1 2`,
`N1.2.1` = `3 2 1` (Günther 1-basiert, hier 0-basiert). -/
example : transklassisch3 = [[0, 2, 1], [1, 2, 0], [2, 0, 1], [2, 1, 0]] := by decide

/-- Die vier sind verschieden. -/
theorem transklassisch3_nodup : transklassisch3.Nodup := by decide

/-- Keine der vier liegt in der Doppelstrich-Zone. -/
theorem transklassisch3_disjoint : ∀ a ∈ transklassisch3, a ∉ klassisch3 := by decide

/-- Zone und Bereich erschöpfen die sechs Anordnungen. Als Inklusion formuliert, nicht als
`List.Perm`: dessen Entscheidung zöge `Classical.choice`. -/
theorem zone_exhausts :
    ∀ a ∈ (origin 2).permutations', a ∈ klassisch3 ∨ a ∈ transklassisch3 := by decide

/-- … und zählen zusammen genau so viele wie die Anordnungen. -/
theorem zone_count :
    (origin 2).permutations'.length = klassisch3.length + transklassisch3.length := by decide

/-- Definitionen §7 bei drei Werten: „`m!` Permutationen abzüglich des klassischen
Bereichs". -/
theorem transklassisch3_card :
    transklassisch3.length = Nat.factorial 3 - klassisch3.length := by decide

-- ============================================================
-- Teil 7 — der kalkültheoretische Bereich für jede Wertzahl (HKN S. 24, Definitionen §7)
-- ============================================================

/-- Die Doppelstrich-Zone bei `m + 2` Werten: der Ausgang und die erste Negation `N1`. Die
hinzukommenden Werte sind trans-klassisch (HKN S. 24); die Zone bleibt darum dieselbe. -/
def klassisch (m : ℕ) : List (List (Fin (m + 2))) :=
  [origin (m + 1), endpoint [0] (origin (m + 1))]

/-- Der trans-klassische Bereich bei `m + 2` Werten: die Anordnungen ausserhalb der Zone. -/
def transklassisch (m : ℕ) : List (List (Fin (m + 2))) :=
  (origin (m + 1)).permutations'.filter (fun a => a ∉ klassisch m)

/-- Der Werte-Umtausch ist bijektiv. -/
theorem sw_bij {m : ℕ} (i : Fin m) : Function.Bijective (sw i) :=
  Function.Involutive.bijective (sw_sw i)

/-- Ein Negator permutiert eine vollständige, duplikatfreie Liste. -/
theorem negate_perm {m : ℕ} (i : Fin m) (l : List (Fin (m + 1))) (hl : l.Nodup)
    (hall : ∀ v, v ∈ l) : (negate i l).Perm l := by
  apply (List.perm_ext_iff_of_nodup (hl.map (sw_bij i).1) hl).mpr
  intro v
  constructor
  · intro _; exact hall v
  · intro _
    exact List.mem_map.mpr ⟨sw i v, hall _, sw_sw i v⟩

/-- Die Zone liegt in den Anordnungen. -/
theorem klassisch_sub (m : ℕ) : ∀ a ∈ klassisch m, a ∈ (origin (m + 1)).permutations' := by
  intro a ha
  simp only [klassisch, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl
  · exact List.mem_permutations'.mpr (List.Perm.refl _)
  · exact List.mem_permutations'.mpr
      (negate_perm 0 _ (List.nodup_finRange _) (List.mem_finRange))

/-- Der Ausgang ist nicht sein `N1`-Bild. -/
theorem klassisch_nodup (m : ℕ) : (klassisch m).Nodup := by
  simp only [klassisch, List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    List.nodup_nil, and_true, not_false_eq_true]
  intro h
  have := congrArg List.head? h
  simp [origin, endpoint, negate, List.finRange_succ, sw] at this

/-- **Der trans-klassische Bereich hat bei `m + 2` Werten `(m + 2)! − 2` Elemente** —
Definitionen §7 („`m!` Permutationen abzüglich des klassischen Bereichs") als Satz, und die
Zahl zu Günthers „erweitert sich … ganz enorm" (HKN S. 24). -/
theorem transklassisch_card (m : ℕ) :
    (transklassisch m).length = (m + 2).factorial - 2 := by
  have hn : (origin (m + 1)).permutations'.Nodup :=
    ((List.permutations_perm_permutations' _).nodup_iff).mp
      (List.nodup_permutations _ (List.nodup_finRange _))
  have hlen : (origin (m + 1)).permutations'.length = (m + 2).factorial := by
    rw [← (List.permutations_perm_permutations' _).length_eq, List.length_permutations]
    simp [origin]
  have hK : ((origin (m + 1)).permutations'.filter (fun a => a ∈ klassisch m)).length = 2 := by
    have hp : ((origin (m + 1)).permutations'.filter (fun a => a ∈ klassisch m)).Perm
        (klassisch m) :=
      (List.perm_ext_iff_of_nodup (hn.filter _) (klassisch_nodup m)).mpr fun a => by
        simp only [List.mem_filter, decide_eq_true_eq]
        exact ⟨fun h => h.2, fun h => ⟨klassisch_sub m a h, h⟩⟩
    rw [hp.length_eq]; rfl
  have hsplit := List.length_eq_length_filter_add (l := (origin (m + 1)).permutations')
    (fun a => decide (a ∈ klassisch m))
  unfold transklassisch
  have : ((origin (m + 1)).permutations'.filter (fun a => a ∉ klassisch m)) =
      (origin (m + 1)).permutations'.filter (fun a => !decide (a ∈ klassisch m)) := by
    congr 1; funext a; simp
  rw [this]
  simp only [hK, hlen] at hsplit
  rw [hsplit, Nat.add_sub_cancel_left]

/-- **Die Brücke zu Teil 6**: bei drei Werten liefert die allgemeine Definition genau
Günthers vier Spalten aus HKN S. 24. -/
theorem transklassisch_eq_three : ∀ a, a ∈ transklassisch 1 ↔ a ∈ transklassisch3 := by
  intro a; constructor <;> intro h <;> revert a <;> decide

/-- Eichung bei vier Werten: `4! − 2 = 22`. -/
theorem transklassisch_four : (transklassisch 2).length = 22 := by decide

/-- Eichung bei zwei Werten: der Bereich ist leer, `2! − 2 = 0` — es gibt nur die erste
Negation. -/
theorem transklassisch_two : transklassisch 0 = [] := by decide

-- ============================================================
-- Wachen
-- ============================================================

/-- info: 'Reformulation.Proemial.NegationCycle.sw_sw' depends on axioms: [propext] -/
#guard_msgs in #print axioms sw_sw

/-- info: 'Reformulation.Proemial.NegationCycle.negate_negate' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms negate_negate

/-- info: 'Reformulation.Proemial.NegationCycle.visits_every_arrangement' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms visits_every_arrangement

/-- info: 'Reformulation.Proemial.NegationCycle.stations_length' depends on axioms: [propext] -/
#guard_msgs in #print axioms stations_length

/-- info: 'Reformulation.Proemial.NegationCycle.full_length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms full_length

/-- info: 'Reformulation.Proemial.NegationCycle.endpoint_append' does not depend on any axioms -/
#guard_msgs in #print axioms endpoint_append

/-- info: 'Reformulation.Proemial.NegationCycle.stations_append' depends on axioms: [propext] -/
#guard_msgs in #print axioms stations_append

/-- info: 'Reformulation.Proemial.NegationCycle.fullStations_cons' does not depend on any axioms -/
#guard_msgs in #print axioms fullStations_cons

/-- info: 'Reformulation.Proemial.NegationCycle.fullStations_append' depends on axioms: [propext] -/
#guard_msgs in #print axioms fullStations_append

/-- info: 'Reformulation.Proemial.NegationCycle.endpoint_reverse' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms endpoint_reverse

/-- info: 'Reformulation.Proemial.NegationCycle.fullStations_reverse' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms fullStations_reverse

/-- info: 'Reformulation.Proemial.NegationCycle.reverse_full' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms reverse_full

/-- info: 'Reformulation.Proemial.NegationCycle.tafelVI4_full' depends on axioms: [propext] -/
#guard_msgs in #print axioms tafelVI4_full

/-- info: 'Reformulation.Proemial.NegationCycle.tafelVI5_full' depends on axioms: [propext] -/
#guard_msgs in #print axioms tafelVI5_full

/-- info: 'Reformulation.Proemial.NegationCycle.tafelVI5_eq_reverse' depends on axioms: [propext] -/
#guard_msgs in #print axioms tafelVI5_eq_reverse

/-- info: 'Reformulation.Proemial.NegationCycle.triadic_unique' depends on axioms: [propext] -/
#guard_msgs in #print axioms triadic_unique

/-- info: 'Reformulation.Proemial.NegationCycle.perms2_nodup' does not depend on any axioms -/
#guard_msgs in #print axioms perms2_nodup

/-- info: 'Reformulation.Proemial.NegationCycle.full_length2' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms full_length2

/-- info: 'Reformulation.Proemial.NegationCycle.triadic_unique'' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms triadic_unique'

/-- info: 'Reformulation.Proemial.NegationCycle.kreis1_full' depends on axioms: [propext] -/
#guard_msgs in #print axioms kreis1_full

/-- info: 'Reformulation.Proemial.NegationCycle.kreis2_full' depends on axioms: [propext] -/
#guard_msgs in #print axioms kreis2_full

/-- info: 'Reformulation.Proemial.NegationCycle.kreis3_full' depends on axioms: [propext] -/
#guard_msgs in #print axioms kreis3_full

/-- info: 'Reformulation.Proemial.NegationCycle.kreis2Gedruckt_not_closed' depends on axioms: [propext] -/
#guard_msgs in #print axioms kreis2Gedruckt_not_closed

/-- info: 'Reformulation.Proemial.NegationCycle.kreis2_emendation' depends on axioms: [propext] -/
#guard_msgs in #print axioms kreis2_emendation

/-- info: 'Reformulation.Proemial.NegationCycle.kreis2_eq' depends on axioms: [propext] -/
#guard_msgs in #print axioms kreis2_eq

/-- info: 'Reformulation.Proemial.NegationCycle.kreis1_family' depends on axioms: [propext] -/
#guard_msgs in #print axioms kreis1_family

/-- info: 'Reformulation.Proemial.NegationCycle.kreis2_family' depends on axioms: [propext] -/
#guard_msgs in #print axioms kreis2_family

/-- info: 'Reformulation.Proemial.NegationCycle.kreis3_family' depends on axioms: [propext] -/
#guard_msgs in #print axioms kreis3_family

/-- info: 'Reformulation.Proemial.NegationCycle.kreis1_reverse_full' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms kreis1_reverse_full

/-- info: 'Reformulation.Proemial.NegationCycle.kreis2_reverse_full' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms kreis2_reverse_full

/-- info: 'Reformulation.Proemial.NegationCycle.kreis3_reverse_full' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms kreis3_reverse_full

/-- info: 'Reformulation.Proemial.NegationCycle.kreis1_mirror_full' depends on axioms: [propext] -/
#guard_msgs in #print axioms kreis1_mirror_full

/-- info: 'Reformulation.Proemial.NegationCycle.kreis1_mirror_family' depends on axioms: [propext] -/
#guard_msgs in #print axioms kreis1_mirror_family

/-- info: 'Reformulation.Proemial.NegationCycle.pseudo_closes' depends on axioms: [propext] -/
#guard_msgs in #print axioms pseudo_closes

/-- info: 'Reformulation.Proemial.NegationCycle.pseudo_family' depends on axioms: [propext] -/
#guard_msgs in #print axioms pseudo_family

/-- info: 'Reformulation.Proemial.NegationCycle.pseudo_half' depends on axioms: [propext] -/
#guard_msgs in #print axioms pseudo_half

/-- info: 'Reformulation.Proemial.NegationCycle.pseudo_not_full' depends on axioms: [propext] -/
#guard_msgs in #print axioms pseudo_not_full

/-- info: 'Reformulation.Proemial.NegationCycle.janus1974_full' depends on axioms: [propext] -/
#guard_msgs in #print axioms janus1974_full

/-- info: 'Reformulation.Proemial.NegationCycle.janus1974_rotate' depends on axioms: [propext] -/
#guard_msgs in #print axioms janus1974_rotate

/-- info: 'Reformulation.Proemial.NegationCycle.janus1974_contains_printed' depends on axioms: [propext] -/
#guard_msgs in #print axioms janus1974_contains_printed

/-- info: 'Reformulation.Proemial.NegationCycle.sw_val' does not depend on any axioms -/
#guard_msgs in #print axioms sw_val

/-- info: 'Reformulation.Proemial.NegationCycle.braid' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms braid

/-- info: 'Reformulation.Proemial.NegationCycle.comm_far' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms comm_far

/-- info: 'Reformulation.Proemial.NegationCycle.braid_fails_far' depends on axioms: [propext] -/
#guard_msgs in #print axioms braid_fails_far

/-- info: 'Reformulation.Proemial.NegationCycle.braid_fails_far_all' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms braid_fails_far_all

/-- info: 'Reformulation.Proemial.NegationCycle.genese_resultat' depends on axioms: [propext] -/
#guard_msgs in #print axioms genese_resultat

/-- info: 'Reformulation.Proemial.NegationCycle.genese_verschieden' depends on axioms: [propext] -/
#guard_msgs in #print axioms genese_verschieden

/-- info: 'Reformulation.Proemial.NegationCycle.transklassisch3_nodup' depends on axioms: [propext] -/
#guard_msgs in #print axioms transklassisch3_nodup

/-- info: 'Reformulation.Proemial.NegationCycle.transklassisch3_disjoint' depends on axioms: [propext] -/
#guard_msgs in #print axioms transklassisch3_disjoint

/-- info: 'Reformulation.Proemial.NegationCycle.zone_exhausts' depends on axioms: [propext] -/
#guard_msgs in #print axioms zone_exhausts

/-- info: 'Reformulation.Proemial.NegationCycle.zone_count' depends on axioms: [propext] -/
#guard_msgs in #print axioms zone_count

/-- info: 'Reformulation.Proemial.NegationCycle.transklassisch3_card' depends on axioms: [propext] -/
#guard_msgs in #print axioms transklassisch3_card

/-- info: 'Reformulation.Proemial.NegationCycle.sw_bij' depends on axioms: [propext] -/
#guard_msgs in #print axioms sw_bij

/-- info: 'Reformulation.Proemial.NegationCycle.negate_perm' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms negate_perm

/-- info: 'Reformulation.Proemial.NegationCycle.klassisch_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms klassisch_sub

/-- info: 'Reformulation.Proemial.NegationCycle.klassisch_nodup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms klassisch_nodup

/-- info: 'Reformulation.Proemial.NegationCycle.transklassisch_card' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms transklassisch_card

/-- info: 'Reformulation.Proemial.NegationCycle.transklassisch_eq_three' depends on axioms: [propext] -/
#guard_msgs in #print axioms transklassisch_eq_three

/-- info: 'Reformulation.Proemial.NegationCycle.transklassisch_four' depends on axioms: [propext] -/
#guard_msgs in #print axioms transklassisch_four

/-- info: 'Reformulation.Proemial.NegationCycle.transklassisch_two' depends on axioms: [propext] -/
#guard_msgs in #print axioms transklassisch_two

/-- info: 'Reformulation.Proemial.NegationCycle.sw_step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms sw_step

/-- info: 'Reformulation.Proemial.NegationCycle.track_last' depends on axioms: [propext] -/
#guard_msgs in #print axioms track_last

/-- info: 'Reformulation.Proemial.NegationCycle.track_between' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms track_between

/-- info: 'Reformulation.Proemial.NegationCycle.track_between_down' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms track_between_down

/-- info: 'Reformulation.Proemial.NegationCycle.track_mediates' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms track_mediates

end Reformulation.Proemial.NegationCycle
