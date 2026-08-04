# CLAUDE.md - Bau-Konventionen fuer dieses Repository

*PKL-Reformulierung Gotthard Guenthers in Lean 4 / Mathlib. Diese Datei bindet die
Implementations-Instanz. Projektgeschichte und Begruendungen stehen in den Niederlegungen
im iCloud-Korpus, nicht hier - hier steht nur, was beim Bauen zu tun und zu lassen ist.*

---

## 1 - Nach jedem geschlossenen Bau: Commit mit Eichwerten

Jeder abgeschlossene Bau endet mit einem Commit, dessen Nachricht die am **gruenen Build
gezaehlten** Kennzahlen fuehrt:

```
<Was gebaut wurde, eine Zeile>

Aggregat: <N> gepruefte Konstanten, <M> Axiom-Wachen ueber <D> Dateien,
AxiomGate <Stand>, Whitelist <W>, <J> Build-Jobs.
Neu: <Datei>, <k> Saetze, <w> Wachen, <s> Sorries.
```

Damit haengt jede Kennzahl an einem Commit-Hash statt an einer Uhrzeit. Ein Stichtag ohne
Zustand ist nicht nachpruefbar; ein Hash ist es.

**Wer eine Kennzahl aendert, fuehrt das README nach** - im selben Zug, auch ohne Auflage.
Eine Auflage sagt nur noch, was *nicht* nachzufuehren ist. Betroffen sind die
Kennzahlentafel, die Bereichstafel und die Struktur-Tafel; welche Zahl ueber welche Route
laeuft, steht in §3.

**Nicht committen ohne gruenen Build.** `git status` vor dem Commit leer pruefen.

### Die Papierfassungen: HTML ist Bestand, Markdown ist Entwurf

Die Papierfassungen `docs/de.html` und `docs/en.html` sind der **Bestand**, nicht ein
Erzeugnis. Textaenderungen laufen dort. Markdown ist Entwurfsmedium: eine kuenftige Ausgabe
darf in Markdown entworfen werden, der Entwurf wird nach dem Bau **datiert abgelegt und nicht
gepflegt**.

Wer eine Papierfassung aendert, aendert beide oder begruendet, warum nicht, und faehrt
`./docs/parity.sh`. Die Ausgabe gehoert in den Befund, auch wenn sie leer ist.

`./docs/figures.sh` gehoert ins Abschluss-Ritual, neben `lake build`,
`lake build ForeignPeresMermin` und `./doc_lint.sh`. **Es bricht** - eine zerschlagene Figur
ist kein Ermessen. `parity.sh` daneben meldet nur, wie Gruppe (A) des Lints: eine Abweichung
zwischen den Sprachfassungen kann eine begruendete Uebersetzungsentscheidung sein.

*Herkunft (2. August 2026, Vorgang 8 und 12):* zwei Darstellungen desselben Textes ohne Route
dazwischen haben acht Divergenzen erzeugt, drei davon unbemerkt ueber Wochen. Der Versuch,
sie durch eine Erzeugungsstrecke zu bewachen, hat die fuenf Figuren zerschlagen, ohne dass
eine von sechzehn Abnahmerouten es sah. Ausweg C beseitigt die Divergenz konstruktiv statt
sie zu bewachen: ohne zweite Darstellung gibt es nichts nachzufuehren. Was bleibt, ist die
Divergenz zwischen den Sprachfassungen - dagegen steht `parity.sh`. Der stehende Negativfall
fuer Darstellungsschaeden ist `a0fe668`; jede kuenftige Route dieser Art wird an ihm geeicht.

### Nach jedem Commit auf `rev2` wird `main` per Fast-Forward nachgezogen

```sh
git push origin rev2
git push origin rev2:main      # Ausgabe pruefen: alt..neu, zwei Punkte
```

`main` ist der Default des oeffentlichen Repositoriums; wer auf der Repo-Seite landet,
sieht `main` und sonst nichts. Ein Zug, der nur `rev2` bewegt, ist fuer jeden fremden
Leser unsichtbar - und **kein Bau meldet das.** Die beiden Zweige koennen beliebig weit
auseinanderlaufen, ohne dass eine Kennzahl sich ruehrt, ohne dass das AxiomGate anschlaegt
und ohne dass `doc_lint` etwas findet. Es ist die Sorte Bruch, gegen die keine Wache
gebaut ist, weil sie ausserhalb des Baums sitzt.

Sobald GitHub Pages laeuft, gilt dasselbe doppelt: die Quelle ist `main/docs`. Eine
Projektseite, die aus einem nicht nachgezogenen `main` ausgeliefert wird, beschreibt den
Bestand nicht mehr und sagt es niemandem.

**Die Ausgabe des zweiten Push ist zu lesen, nicht zu ueberfliegen.** Die Form `alt..neu`
mit zwei Punkten weist ihn als echten Fast-Forward aus. Steht dort ein `+` oder ein
Hinweis auf einen erzwungenen Push, ist etwas anderes geschehen als beabsichtigt - dann
nicht wiederholen, sondern nachsehen.

*Herkunft (1. August 2026, Vorgang 6):* `main` stand vierzig Zuege lang auf dem
Rev1-Abschluss, waehrend die Arbeit auf `rev2` lief. Beim Oeffentlichwerden waere damit
ein Stand sichtbar geworden, dem die Lizenzdateien fehlten und dessen Projektseite sich
selbst als nicht zur Veroeffentlichung bestimmt bezeichnet. Der Tag `rev1` haelt den
Rev1-Stand unabhaengig fest; ein Fast-Forward ruehrt Tags nicht an.

---

## 2 - Vor jeder Lieferung

- `lake build` laeuft durch, AxiomGate gruen.
- Fuer **jeden** neuen Satz `#print axioms` ausfuehren, das gemessene Profil verbatim in eine
  `#guard_msgs`-Wache einfrieren. Profile werden gemessen, nicht geschaetzt.
- **Keine** Whitelist-Eintraege im AxiomGate. Die Whitelist ist seit der
  Whitelist-Aufloesung (24. Juli 2026, Commit-Hash siehe git log) leer; jede
  `sorryAx`-Konstante im Aggregat ist ein Verstoss, kein Whitelist-Kandidat.
- `Classical.choice` ist kein Fehler, aber ein Befund: wo er auftritt, gehoert er in die
  Rueckgabe. Wo er vermeidbar war, gehoert der Weg dokumentiert (Fintype-Maschinerie ueber
  Funktionsraeumen zieht ihn regelmaessig; punktweise Brueckenlemmata vermeiden ihn).

---

## 3 - Wachen

Jeder **tragende** Satz traegt eine Wache. Hilfslemmata sind ausgenommen, sofern ihr Profil
ueber die Huelle eines gewachten Satzes mitgesichert ist - Axiom-Profile sind
Huell-Eigenschaften, ein konsumierender Satz faengt Aenderungen in seinen Voraussetzungen mit.

**Ausnahme, die keine ist:** Ein Hilfssatz, an dem eine *Eigenschaft der ganzen Datei* haengt
(etwa die Classical-Freiheit), wird gewacht, auch wenn er formal Hilfslemma ist. Beispiel:
`realize_eq_of_pointwise` in `Proemial/NonUniformCloneBound.lean`.

Wachen stehen in eigenen Bloecken am Dateiende, nicht vor den Deklarationen.

Geschriebene gegen erzwungene Wachen. Nicht jede geschriebene Wache laeuft mit. Eine Wache
in einem Modul, das von keinem Default-Target erfasst wird, erzeugt kein Bau-Ereignis; sie
sichert nichts und sieht in jeder Kennzahl wie Sicherung aus. Beide Zahlen sind darum
getrennt zu fuehren.

Route geschrieben: grep -rE '#guard_msgs.*in #print axioms' ueber Reformulation/ und
Foreign/. Die naive Route ohne den zweiten Teil zaehlt Doc-Prosa mit und liefert einen zu
hohen Wert.

Route erzwungen: dieselbe Route, eingeschraenkt auf die Import-Huelle der Default-Targets.
Die Anwesenheit einer .olean ist KEIN Nachweis, dass ein Modul vom Bau erfasst wird —
Waisen tragen .olean-Dateien aus frueheren Einzelbauten. Die Import-Huelle ist die tragende
Route.

Zaehlt man ueber mehrere Targets, gilt dasselbe in der anderen Richtung: ihre Import-Huellen
ueberlappen, und wer die Bauausgaben summiert, zaehlt Module doppelt. Siehe §12, Regel 4.

Die aktuellen Werte stehen im README, nicht hier. Eine Kennzahl gehoert in diese Datei nur
als Beleg fuer eine Regel, an einen Commit gebunden; nie als laufender Stand.

### Deklarationszahlen: Quell-Deklarationen zaehlen

Drei Routen liefern drei Zahlen — fuer den Kenogram-Zweig etwa 238, 132 und 128. Verbindlich
fuer README, Ledger und Befunde ist die dritte:

- **Umgebungskonstanten** — alles im `.olean`, inklusive `_proof_*`, `.match_*`, `._simp_*`.
- **user-facing** — davon ohne `Lean.Name.isInternalDetail`.
- **Quell-Deklarationen** (**verbindlich**) — user-facing minus die automatisch erzeugten
  Begleiter: `.eq_def`, `.congr_simp`, `.rec`, `.recOn`, `.casesOn`, `.noConfusion*`, `.mk*`,
  `.ctorIdx`, `._sizeOf_*`.

Gemessen wird per Umgebungsabfrage (`env.constants` plus `findDeclarationRanges?`), nicht per
`grep`. Die Satzzahl bleibt eine `grep`-Route, aber seit dem Satzrouten-Zug in geweiteter
Form:

    grep -rhE '^((private|protected|nonrec) +)?(@\[[^]]*\] +)?(theorem|lemma) '

*Grund (29. Juli 2026):* die fruehere Route `^(theorem|lemma) ` war in beide Richtungen
falsch. Sie verfehlte 13 `private`-Deklarationen und 6 Deklarationen mit Attribut auf der
Deklarationszeile, und sie zaehlte 3 Zitate entfernter Aussagen in Memorial-Bloecken mit.
Beleg am Commit dieses Zuges; die laufenden Werte stehen im README.

**Keine uneingerueckte Zeile beginnt mit einem Deklarationswort.** Die Satzroute zaehlt
Zeilenanfaenge; jede Zeile, die am linken Rand mit `theorem`, `lemma`, `def`, `abbrev` oder
`instance` beginnt, wird als Deklaration gezaehlt. Wo das keine ist, steht eine stille
Falschzaehlung. Heilung: zwei Leerzeichen davor, oder den Umbruch eine Silbe frueher.

Die Regel galt bis zum Scan-B-Zug nur fuer **Zitate in Memorial-Bloecken** und deckte damit
den haeufigeren Fall nicht: gewoehnliche Prosa im Doc-String, deren Umbruch ein
Deklarationswort an den Zeilenanfang schiebt. Gemessen am Stand `427b4b0`: die verbindliche
Satzroute liefert 802, dieselbe Route mit einer Deklarations-Verschaerfung (nach dem Namen
muss `(`, `{`, `[`, `⦃`, `:` oder Zeilenende folgen) liefert 801; die Differenz war genau
eine Zeile, `F1/D2/Rollups/Coalgebraic.lean` 21, wo `consistency theorem with four aspects`
umbrach. Die Verschaerfung taugt als Gegenprobe, nicht als Ersatz — sie kennt die
Binderformen des Baus nicht.

Fuer `def` gilt dieselbe Weitung:

    grep -rhE '^((private|protected|nonrec) +)?(@\[[^]]*\] +)?def '

*Beleg (29. Juli 2026):* alte Route 309, geweitete 315; die Differenz sind sechs
`private def`. Zitate in Memorial-Bloecken gibt es fuer `def` bisher keine; die
Einrueckungsregel oben gilt trotzdem.

Die rohe sorry-Zahl N1 ist eine selbstzaehlende Groesse. Sie zaehlt Wortvorkommen ueber den
ganzen verfolgten Bestand, und sie zaehlt Prosa mit Absicht - genau so findet ein fremder
grep sie. Wer den Wortlaut der Suche in ein Dokument schreibt, erhoeht sie; dreimal gemessen
(README-Absatz 121 -> 123, deutsche Papierfassung 123 -> 126, englische 126 -> 129), jedes
Mal ein Fixpunkt, weil das Einsetzen der Ziffer kein Wortvorkommen erzeugt.

Daraus folgt die Regel: eine Differenz zwischen zwei Staenden von N1 ist ohne Angabe, welche
Seite sich bewegt hat, keine Aussage ueber den Bestand. Wer N1 aendert, misst je Datei und
nennt die Rechnung. N2 und N3 sind davon nicht betroffen - sie laufen ueber .lean
beziehungsweise ueber betroffene Deklarationen.

**Und die Route laeuft ueber den verfolgten Bestand.** Eine Datei, die noch nicht verfolgt
wird, ist fuer sie nicht vorhanden: N1 bleibt dann unveraendert stehen, obwohl der Zug die
Zahl bewegt hat, und der Wert ist plausibel und falsch. **Regel: nach dem Hinzufuegen einer
Datei erst verfolgen, dann messen.** Gemessen am Morphogramm-Zug (Commit `d55158b`) - die
Messung vor dem Verfolgen lieferte den unveraenderten Vorwert, die Messung danach den um
eins hoeheren; beide Male stand dieselbe Datei im Arbeitsbaum. Es ist Fallstrick 8 in einer
weiteren Gestalt: nicht ein falsches Ergebnis, sondern ein unbewegtes, und ein unbewegtes
sieht aus wie eine gute Nachricht.

Verallgemeinerung. Eine Route, deren Suchwort in Prosa vorkommt, zaehlt ihre eigene
Dokumentation mit; wer die Route erklaert, veraendert ihren Wert. Das ist kein Fehler und
keine Ausnahme, sondern die Regel fuer einen Korpus, der seine Werkzeuge in derselben
Sprache dokumentiert, in der er misst. Drei Belege aus ein und demselben Zug: die rohe Zahl
oben, das Stichwort der Lint-Gruppe (B), das im Pruefbereich nur in der Zeile vorkommt, die
den Lint beschreibt, und zwei der drei eingefrorenen Treffer der Gruppe (A), die die
Musterliste aufzaehlen. Praktische Folge: wer eine solche Route dokumentiert, benennt sie,
statt das Kommando auszuschreiben, und misst nach dem Zug je Datei.

### Statement-Pins: maschinenlesbar markieren

Jeder Statement-Pin traegt unmittelbar davor die eigene Zeile

```
-- STATEMENT-PIN
```

**Zaehlroute:** `grep -rc '^-- STATEMENT-PIN' --include='*.lean' Reformulation/`.

*Grund (24. Juli 2026, nach einem Befund der Implementations-Instanz):* Die frueheren Routen
zaehlten `example`-Deklarationen in Dateien mit einer Pin-**Ueberschrift** in der Prosa. Das war
zweifach bruechig. Erstens haengt es an der Schreibweise - `## Statement pins` (englisch, ohne
Bindestrich) in `F1/D5/IBC/PullBack.lean` gegen `**Statement-Pins.**` in den uebrigen; je nach
Suchmuster fehlten vier Pins und eine Datei. Zweitens erfasste die weitere Route ab dem
E4-Doc-Eintrag `Proemial.lean` mit, weil dort der Begriff im Fliesstext vorkommt - eine Datei
mit null Pins. **Eine Zaehlroute, die Prosa als Kriterium nimmt, ist eine Zeitbombe.**

Zur Groessenordnung: korpusweit gibt es rund achtzig `example`-Deklarationen, die grosse Mehrheit
davon Sonden-Beispiele ohne Pin-Charakter. `example` allein ist darum kein brauchbares Kriterium.

---

## 4 - Im Dateikopf: Ertrag oder Benennung

Jedes neue Modul vermerkt im Doc-String, was es ist:

- **Ertrag** - liefert einen Satz, den Mathlib nicht schon hat und den man ohne den
  PKL-Begriff nicht formuliert haette.
- **Benennung** - uebersetzt einen Begriff in Lean-Syntax ohne neuen Satzgehalt. Legitim als
  Traeger, aber als solche zu kennzeichnen.

Beides ist zulaessig. Die Verwechslung ist es nicht.

---

## 5 - Nicht bauen

Drei Formalisierungen widersprechen dem Korpus oder der Quelle und sind zu vermeiden:

1. **`Disjoint K1 K2`** auf Kontextur-Traegermengen. Die Elementarkontexturen ueberlappen
   paarweise in genau einem Wert (`{0,1} ∩ {1,2} = {1}` usw.), und die Ueberlappung ist
   konstitutiv fuer die vorhandenen Schranken-Beweise.
2. **`¬ ∃ f : K1 → K2`** als Formalisierung von Diskontexturalitaet. Sein und Nichts sind bei
   Guenther isomorph und trotzdem diskontextural. Die tragfaehige Form ist
   `¬ ∃ t : L.Term, ...` - Nicht-Erzeugbarkeit im Termklon.
3. **Verbundkontextur-Folge beginnend bei 1.** Sie beginnt bei 3; die 1 gehoert zur
   Ontologien-Folge. `Definitionen.md` §3 fuehrt hier einen Off-by-one.

---

## 6 - Marken und Wortlaut-Grenzen

Deutungen werden als Deutungen gefuehrt, nicht als Saetze. Der **Dateiname** sagt, was bewiesen
ist, nicht was gedeutet wird - darum `NonUniformCloneBound` und nicht `Mediation`.

Zahlen, die ausserhalb des Korpus gerechnet wurden (Klon-Groessen, Aufzaehlungen ueber alle
Operationen), bleiben ausserhalb. In den Korpus gehoeren sie nur in Bijektions- oder
Iff-Form, nicht als Kardinalzahl-Behauptung.

Rang-Ansprueche ("erstmals", "die einzige Stelle") werden der Quelle zugeschrieben, die sie
erhebt, und nicht als Korpus-Aussage gefuehrt.

---

## 7 - Umgebung

- Lean `4.30.0-rc2`; `.lake/` ist 7,5 GB und per `.gitignore` ausgeschlossen.
- Der Quellbestand ist wenige hundert Dateien, zusammen unter 1 MB. Wer wesentlich mehr
  committet, hat die Ignore-Regel verletzt.
- `lake build` repliziert; ein vollstaendiger Neubau ist nicht noetig, um Profile zu pruefen -
  `lake env lean` auf einer generierten `#print axioms`-Datei genuegt.

### Aenderungen an der Maschine

Eine Aenderung an der Maschine traegt den vorherigen Zustand DESSELBEN Gegenstands, nicht nur
die Abwesenheit des Ziels. „pandoc nicht gefunden" ist nicht „pypandoc nicht installiert".
Vor einer Installation wird das Paket selbst abgefragt und die vorgefundene Fassung notiert;
sonst ist die Umkehr keine Umkehr, sondern eine Loeschung. Gemessen: eine Installation im
August hat eine im Oktober vorhandene Fassung ueberschrieben, und die Deinstallation hat sie
entfernt.

---

## 8 - Lean-Fallstricke (gemessen, nicht vermutet)

Jeder Eintrag ist an diesem Korpus aufgetreten und hat Zeit gekostet. Sie stehen hier, damit
sie nicht ein zweites Mal gefunden werden muessen. Der neunte ist kein Lean-Fallstrick,
sondern einer der Werkzeugkette; er steht hier, weil er dieselbe Sorte ist wie der achte.

*Ohne Gesamtzahl, mit Absicht.* Hier stand bis `e97fdbe` eine Ordnungszahl ("Alle zehn").
Sie war zweimal von Hand nachzuziehen und waere beim naechsten Eintrag ein drittes Mal
faellig gewesen - eine zweite Darstellung der Eintragszahl ohne Route dazwischen, also
genau der Fall aus §1 (Ausweg C). Die Eintraege bleiben durchnummeriert; eine Gesamtzahl
steht nirgends und muss darum auch nirgends nachgezogen werden.

Wer sie doch zaehlen will, zaehlt die fetten Eintragsnummern **innerhalb dieses
Paragraphen** - die naive Route ueber die ganze Datei liefert mehr, weil §12 gleich
ausgezeichnete Regeln fuehrt. Gegengerechnet am Stand dieses Zuges: §8 zwoelf, §12 fuenf,
Datei siebzehn; die Gleichung 12 + 5 = 17 geht auf. Es ist dieselbe Sorte Falle wie in §3:
eine Route unterscheidet nur, was sie zaehlt.

**Aufgetreten heisst nicht erklaert.** Ein Eintrag haelt fest, was gemessen wurde, und das
ist nicht immer die Ursache: der zehnte haelt eine Profildifferenz fest, deren Mechanismus
ungeprueft ist, und sagt das an seiner Stelle. Wer einen Eintrag ergaenzt, trennt beides.

**1 - `Fin n`-Subtraktion ist modular.** `|a - b| <= 1` ueber `Fin 4` ist **nicht** die
Nachbarschaftsrelation, sondern etwas anderes. Relationen dieser Art werden als explizite Tafel
ueber `.val` geschrieben oder ueber `Nat`-Ungleichungen an `.val`. (Aus der E2-Spezifikation.)

**2 - `abbrev` statt `def` fuer alles, was `decide` sehen soll.** Bei `def P ... : Prop := ...`
findet die Instanzensuche die `Decidable`-Instanz nicht und `decide` schlaegt fehl
(*failed to synthesize Decidable*). `abbrev` ist reducible und loest es. (Vorab-Probe zu E2.)

**3 - Quantifizierung ueber Funktionsraeume zieht `Classical.choice`.** Gemessen am selben Satz:
`forall c : Fin 6 -> Bool, ...` ergab `[propext, Classical.choice, Quot.sound]`, sechs explizite
`Bool`-Argumente ergaben `[propext]`. **Wo ein endlicher Funktionsraum quantifiziert wird, sind
explizite Argumente vorzuziehen** - der Unterschied ist nicht kosmetisch, er steht im Profil.

**4 - `decide` verweigert freie Variablen im Ziel** (*Expected type must not contain free
variables*). Die angebotene Option `+revert` **kaskadiert**: sie zieht ueber Hypothesen auch
Groessen ins Ziel, die es unentscheidbar machen. Heilung: die Abhaengigen vorher mit `clear`
entfernen, wenn das Ziel sie ohnehin nicht mehr braucht. (E2-Bau.)

**5 - `decide +revert` ueber grosse Fallzahlen laeuft in den `whnf`-Timeout.** Bei ~4096
Kombinationen gemessen (200 000 Heartbeats). **Die Heartbeat-Grenze nicht heraufsetzen** -
stattdessen pro Koordinate Fallzug und die Mischfaelle per `show`-defeq auf einen konkreten
Widerspruch reduzieren; die Auswertung geschieht dann in der Definitional-Pruefung. (E2-Bau.)

**6 - `rw [ht ![x, u], ...]` scheitert am Token `]]`.** Die Klammerform `ht (![x, u])`
funktioniert. (E1 und E2, beide Male.)

**7 - `omega` und Klassik: negierte Konjunktion als Hypothese UND Disjunktion im Ziel
ziehen `Classical.choice`.** Beide Seiten gemessen: `¬(x = 0 ∧ y = 1)` als *Hypothese*
zwingt `omega` auf `[propext, Classical.choice, Quot.sound]` (E3-Spezifikation §4);
`x ≠ 0 ∨ y ≠ 1` als *Ziel* ebenso (E3-Bau, Wegwerf-Probe). Harmlos sind Disjunktions-
*Hypothesen* und negierte Konjunktionen im *Ziel*. Heilung: Invarianten in
Disjunktionsform definieren (Hypothesen-Seite) und Disjunktions-Ziele vor `omega`
choice-frei zerlegen — `dite` über `Nat.decEq` nach dem Muster `ne_or_ne_of_imp` in
`Proemial/GeneralCloneBound.lean`; `omega` bekommt nur atomare Ziele. Ferner: `omega`
sieht `Fin`-`min`/`max` nicht — erst mit `simp only [Fin.coe_min, Fin.coe_max]` auf
`ℕ` bringen, dann versteht `omega` `min`/`max` nativ und die Fallarbeit über
`Nat.le_total` entfällt. (E3-Bau.)


**8 - `ConstantInfo.value?` sieht keinen Beweisterm.** Fuer `thmInfo` liefert das Feld
`none`; eine Route, die Konsumenten ueber `value?` sucht, ist fuer Saetze blind und meldet
zuverlaessig null. Gemessen an
`F1.D2.Ethereum.gasper_inter_layer_compatible`: `value?.isSome = false`, obwohl der
Quelltext den Beweis ausschreibt. Heilung: explizit mustern.

    match ci with
    | .thmInfo v => some v.value
    | .defnInfo v => some v.value
    | .opaqueInfo v => some v.value
    | _ => none

Der Fehler ist die gefaehrliche Sorte: er liefert kein falsches Ergebnis, sondern ein
leeres, und ein leeres Ergebnis sieht aus wie eine gute Nachricht. (Phase-2-Zuspitzung.)

**9 - `git grep` fuehrt `\b` nicht.** Die Regex-Maschine von `git grep` kennt die
Wortgrenze in dieser Betriebsart nicht; das Muster trifft nichts und die Suche meldet
null. Gemessen am verfolgten Bestand: `git grep -E '\bsorry\b'` liefert **0**, dieselbe
Suche ohne `\b` liefert **189** Zeilen ueber den ganzen verfolgten Bestand und **153**
ueber `*.lean`. Es ist die Sorte aus Fallstrick 8 in neuer Gestalt - kein falsches
Ergebnis, sondern ein leeres, und ein leeres sieht aus wie eine gute Nachricht.

*Gegenprobe, die ihn aufdeckt:* jede Wortgrenzen-Route einmal ohne `\b` fahren. Liefern
beide 0, ist die Route verdaechtig und nicht der Bestand.

*Heilung:* `git grep -w` traegt die Wortgrenze. Gegengerechnet nach `CLAUDE.md` §12
Regel 2 - `git grep -cw sorry` und eine Python-Route mit `re.compile(r'\bsorry\b')`
liefern beide **118** Zeilen; geprueft ist die Gleichheit, nicht der Wert.

*Nachtrag (Vorgang 10): die Heilung war eine halbe.* Sie traegt die Wortgrenze, aber sie
beantwortet eine andere Frage als `N1`. **Zwei Routen, zwei Fragen** - gemessen am Stand
`b6fda6b` und an diesen Stand gebunden:

    Zeilen mit mindestens einem Vorkommen   git grep -cw   127   (davon .lean 92)
    Wortvorkommen  =  N1                    Python re      130   (davon .lean 95)

Die Differenz sind drei Zeilen, die den Begriff zweimal tragen: zwei in
`Reformulation/PathC/Classifying/ModelFunctor.lean`, eine in `Reformulation/F3f.lean`.
**Wer `N1` meint und die Zeilenroute nimmt, misst zu niedrig und merkt es nicht**, weil
beide Zahlen plausibel sind und keine von beiden 0 ist. Das ist Fallstrick 8 in dritter
Gestalt: nicht ein leeres Ergebnis, sondern ein knapp falsches - und ein knapp falsches ist
schwerer zu bemerken als ein leeres.

Die Gleichheitsprobe oben bleibt richtig: beide Routen zaehlen Zeilen und stimmen ueberein.
Falsch war nur, sie als Route fuer `N1` zu lesen. Eine Route wird an ihrer Frage geprueft,
nicht an ihrer Uebereinstimmung mit einer zweiten Route derselben Frage.

*Gegengeprueft, ob eine stehende Route betroffen ist: nein.* `doc_lint.sh` nutzt weder
`git grep` noch `\b`; die verbindlichen Zaehlrouten in §3 laufen ueber `grep -rE` mit
expliziten Zeilenanfaengen. Der Eintrag ist Praevention. (Vorgang 6, Stufe 1.)

**10 - `deriving Fintype` kann `Classical.choice` in jedes `decide` tragen.** Gemessen an
`Proemial/M3CloneWitness.lean` (Bauzustand `54fa37c`): dieselbe Datei, nur die
`Fintype`-Instanz getauscht, ergab mit `deriving Fintype` dreizehn Saetze mit
`[propext, Classical.choice, Quot.sound]` und mit einer Handinstanz ueber die Elementliste
dieselben dreizehn mit `[propext, Quot.sound]`. Betroffen ist jeder Satz, der ueber
`forall x : T` quantifiziert; punktweise Saetze bleiben unberuehrt. Gemessen ist die
**Differenz der beiden Fassungen**, nicht der Weg des Axioms in den Term - die
naheliegende Erklaerung ueber die Aufzaehlungs-Maschinerie ist Vermutung und nicht
geprueft. Heilung: bei kleinen Aufzaehlungstypen die `Fintype`-Instanz von Hand schreiben.
Verwandt mit Fallstrick 3: nicht die Quantifikation selbst, sondern die Maschinerie hinter
der bequemen Instanz steht im Profil.

**11 - Ein nicht aufgeloester Typname wird zur autogebundenen Variablen.** Unter
`relaxedAutoImplicit` bindet der Elaborator einen Namen, den er nicht aufloest, still als
implizite Typvariable. Jede Folgemeldung spricht dann ueber diese Variable - und zeigt auf
Stellen, die in Ordnung sind. Gemessen beim Bau von `Kenogram/Unbounded.lean` (Commit
`e97fdbe`): `RGSStream` liegt in `Reformulation.Kenogram.Stream`, und `open
Reformulation.Kenogram` allein holt es nicht. Die Meldung lautete *"Invalid projection ...
`r` has type `RGSStream` which does not have the necessary form"* und wies damit auf die
Subtyp-Projektion `.1`, die in Ordnung war; der wahre Grund erschien erst weiter unten als
*"don't know how to synthesize implicit argument `RGSStream`"*.

Es ist die Sorte aus Fallstrick 8 in weiterer Gestalt: nicht ein leeres und nicht ein knapp
falsches Ergebnis, sondern ein **falsch adressiertes**. Wer der Meldung folgt, arbeitet an
einem gesunden Bauteil.

*Heilung:* die fehlenden `open`-Zeilen - hier `Reformulation.Kenogram.Stream` und
`Reformulation.Kenogram.Bridge` neben `Reformulation.Kenogram`. Danach lief die Vorprobe
ohne weitere Aenderung durch.

*Gegenprobe, die ihn aufdeckt:* bei einer Projektions- oder Instanzmeldung ueber einen
eigenen Typ zuerst `#check <Typname>` auf den blossen Namen. `#check` bindet **nicht**
automatisch und meldet darum, was der Elaborator verschweigt. Gegengerechnet in beide
Richtungen am selben Stand: ohne den passenden `open` liefert `#check RGSStream`
*"Unknown identifier"*, mit ihm `Reformulation.Kenogram.Stream.RGSStream : Type`.

**12 - Eine unquotierte Pfadliste in einer Variablen wird von `zsh` nicht wortgeteilt.**
`AREAS="dirA dirB"; grep -r muster $AREAS` uebergibt beides als **einen** Pfad; `grep` findet
ihn nicht, warnt nach stderr und liefert **0**. Mit `2>/dev/null` bleibt eine plausible Null.
Gemessen im Scan-B-Nachtrag: eine Uebersicht ueber neunundzwanzig Suchwoerter lieferte fuer
**jedes** den Wert 0 - auch fuer `placeholder`, von dem aus einer frueheren Messung bekannt
war, dass es in 24 Dateien steht. Heilung: Pfadlisten als Array fuehren (`AREAS=(dirA dirB)`),
in bash `"${AREAS[@]}"`.

*Die zweite Haelfte der Heilung ist die wertvollere, weil sie nicht an `zsh` haengt:* **eine
Route, die fuer jedes Suchwort denselben Wert liefert, ist zuerst an sich selbst zu
verdaechtigen und nicht am Bestand.** Aufgefallen ist der Fehler allein an einem Muss-Fall aus
einer frueheren Messung; ohne ihn waere „die englischen Bereiche tragen kein Statusvokabular"
ein plausibler und falscher Befund geworden. Damit gilt §12 Regel 1 (Muss- und
Darf-nicht-Fall) auch fuer Uebersichtsmessungen, nicht nur fuer Akzeptanzrouten. Es ist der
achte Fallstrick in weiterer Gestalt: kein falsches Ergebnis, sondern ein leeres.

### Was aus dem achten und neunten folgt - kein eigener Fallstrick, die Regel dahinter

Ein fehlender Treffer und ein anders geschriebener Treffer sehen in einer Trefferzaehlung
gleich aus. Ebenso ein intaktes und ein zertruemmertes Element. Zwei Belege aus einem Block:
eine Formel, die in der Quelle anders geschrieben stand als im Erzeugnis und wie eine
Fehlstelle aussah; und fuenf Figuren, deren Textknoten vollzaehlig und im richtigen
Elternelement lagen, waehrend die Darstellung zerstoert war. Daraus folgt: eine Route
unterscheidet nur, was sie zaehlt. Wer eine Eigenschaft pruefen will, die keine Zaehlung ist,
braucht eine Route, die sie prueft.

Der Commit a0fe668 ist der stehende Negativfall des Projekts. Jede Route gegen
Darstellungsschaeden wird an ihm geeicht: sie muss dort anschlagen und an b3681b3 schweigen.
Gemessen: `<p>` innerhalb `<figure>` liefert dort 20 und hier 0. Ein kaputtes Artefakt, das
man behalten kann, ist wertvoller als jede Beschreibung des Schadens.

---

## 9 - Schranken: Robustheit gegen Signatur-Erweiterung pruefen

Eine Nicht-Erzeugbarkeits-Schranke haengt an ihrer Invariante. Wird die Signatur um Konstanten
erweitert, faellt die Schranke genau dann nicht, wenn die Invariante jedes `(c,c)` enthaelt -
also **reflexiv** ist.

| Zeuge | Invariante | ueberlebt Konstanten |
|---|---|---|
| `TransjunctionCloneBound` | Elementarkontextur `{0,2}` | **nein** (`1` liegt nicht darin) |
| `QuaternaryCloneBound` | `R_4`, reflexiv | **ja** |

**Vor dem Bau einer neuen Schranke ist zu pruefen, ob ihre Invariante reflexiv ist**, und das
Ergebnis gehoert in den Doc-String. Eine Schranke, die an einer hinzugefuegten Konstante faellt,
behauptet weniger, als sie zu behaupten scheint - das ist kein Fehler, aber es muss dastehen.

---

## 10 - Kein Satz des Aggregats haengt an einer Setzung

Kein Satz des Aggregats haengt an einer Setzung.

Das ist die tragende Regel, nicht "das Aggregat enthaelt keine Setzung". Der Unterschied
ist gemessen: das Aggregat traegt 32 Strukturfelder vom Typ True, und genau zwei
Aggregatkonstanten referenzieren eine solche Feld-Projektion — beide mit der Aussage True.
Ein Feld vom Typ True kann in keinen Beweis eingehen; es verletzt das Schutzziel nicht.

Pruefbar ist die Regel am Axiomabschluss, also dort, wo das AxiomGate ohnehin misst.

Setzungen zerfallen in zwei Klassen, die nicht dasselbe sagen:

- Platzhalter: eine verschobene Beweisschuld. Der Doc-String sagt "placeholder" oder
  Gleichwertiges. Ein Platzhalter braucht ein Exit-Kriterium: was muesste vorliegen, damit
  er faellt. 30 der 32 Felder sind Platzhalter.
- Konstitutive Setzung: kein Beweis-Soll. Der Doc-String sagt es ausdruecklich. Eine
  konstitutive Setzung braucht keine Exit-Bedingung, wohl aber eine Begruendung, warum sie
  keine hat. Zwei der 32 Felder sind konstitutiv:
  Proemial.DiscontexturalStratification.discontextural_posited und
  Proemial.ContexturalTransjunction.CharacterizedPosit.contexturePartitionGenuine.

Wer ein neues Setzungsfeld anlegt, benennt seine Klasse im Feld-Doc. Ein Feld ohne
Klassenangabe ist ein Mangel, kein Sonderfall.

Warum Setzungen im Aggregat markiert und benannt sein muessen: nicht weil sie die Geltung
gefaehrden — ein Feld vom Typ True kann in keinen Beweis eingehen —, sondern wegen des
epistemischen Signals. Was im Aggregat steht, liest sich als zertifizierter Bestand; eine
Setzung darin wird als Anspruch gelesen statt als Markierung. Darum traegt der Feldname
seinen Status (discontextural_posited, nicht discontextural), und darum ist die
Klassenangabe im Feld-Doc Pflicht.

*Zaehlroute und Stand:* die 32 sind der Aggregat-Importbaum am Commit `284995b`, gemessen
per Umgebungsabfrage ueber `getStructureFields` und `env.getProjectionFnInfo?` mit
`forallBoundedTelescope` auf die Projektions-Stelligkeit — nicht per `grep`, und nicht
ueber `forallTelescopeReducing`, das `Set X = X → Prop` faelschlich als `Prop`-Feld zaehlt.
Am selben Stand: null Felder, deren Typ erst per `whnf` zu `True` reduziert, und null
Felder vom Typ `Prop`.

### Ablage: wo eine Datei hingehoert

Davon zu unterscheiden ist die **Ablagekonvention**. Sie regelt nicht, was gelten darf,
sondern wo eine Datei liegt:

- **setzungsfrei bedeutet Aggregat.** Beispiele: `ContextureOverlap`, `RegimeThreshold` -
  sie konsumieren nur Aggregat-Inhalt und arbeiten auf dem etablierten Kontexturbegriff.
- **setzungstragend bedeutet standalone**, mit Vermerk im Dateikopf und ausdruecklicher
  Anschlussbedingung. Beispiel: die Turm-Linie (`TowerAsymmetryProbe`,
  `AsymmetricDiscontexturalTransition`) mit `contextureCrossing : True`.

Der legitime Ausloeser fuer einen spaeteren Anschluss ist genau einer: ein Aggregat-Satz, der
die standalone Datei **konsumiert** - oder die Aufloesung der Setzung durch einen Satz.
Bis dahin ist die Standalone-Lage nicht ein Zwischenzustand vor der eigentlichen Aufnahme,
sondern die dem Status angemessene Verortung.

Die Konvention ist eine Ordnungsregel, keine Geltungsregel: dass das Aggregat an 32 Stellen
Setzungen traegt, verletzt sie nicht rueckwirkend. Neu angelegte setzungstragende Dateien
gehen standalone, solange kein Aggregat-Satz sie konsumiert.

---

## 11 - Ergebnisdokumente: Fund ja, Stand nein

Jeder Auftrag endet in einem Ergebnisdokument. Es berichtet, was der Zug getan und gemessen
hat - und nur das.

**Kein fremder Stand.** Ein Befund schreibt den Stand eines Dokuments, das er nicht geaendert
hat, nicht fort: nicht den Plan, nicht das README, nicht das Ledger, nicht das Register. Wer
einen Stand mitliest, liest ihn irgendwann veraltet ab. Das ist zweimal vorgekommen, beide
Male ohne Sachfolge und beide Male mit einer zweiten Quelle als Ergebnis.

**Aber jeder Fund.** Ein Widerspruch, den der Zug an einem fremden Dokument misst, gehoert in
den Befund, und zwar mit beiden Zahlen und beiden Routen: "dort steht 25, meine Route ergibt
34". Das ist ein Messergebnis und kein Stand.

Der Unterschied ist der ganze Punkt: berichtet wird, was gemessen wurde; nicht berichtet
wird, was anderswo geschrieben steht. Wer einen Stand fortfuehrt, steht im jeweiligen
Dokument selbst - fuer Plan und Erfolgskriterien ist es die Spezifikations-Instanz.

### Wortlaut: „kein Remote" heisst nicht „nicht gepusht"

Ein Remote ist seit Beginn konfiguriert (`origin`, mit Tracking fuer `main` und `rev2`).
Die Formel **„kein Remote"** stand in jedem Befund dieses Blocks und war jedes Mal
unrichtig; gemeint war der Ablagezustand, und der heisst **„nicht gepusht"**.

Der Unterschied ist keine Wortklauberei. „Kein Remote" sagt: der Bestand liegt nirgends
ausser hier. „Nicht gepusht" sagt: er liegt teilweise dort, und wie weit, sagt erst eine
Messung - `git fetch`, dann `git log --oneline origin/<branch>..<branch> | wc -l`. Wer den
Remote-Zeiger ohne `git fetch` abliest, misst den lokalen Stand und nicht den Server.

---

## 12 - Messen: was eine Route zu leisten hat

Vier Regeln, jede aus einem gemessenen Fehlgriff dieses Korpus. Sie gelten fuer jede Zahl,
die ein Dokument verlaesst.

**1 - Eine Route wird gegengerechnet, bevor ihr Ergebnis in ein Dokument geht.** Der
Gegenfall ist einer, dessen Antwort aus dem Quelltext bekannt ist - einer, der treffen muss,
und wo es geht einer, der nicht treffen darf. Eine Route ohne Gegenprobe ist eine Vermutung
mit Nachkommastellen.

**2 - Eine Messprobe prueft eine Gleichung, nicht eine Zahl.** Wo zwei Wege zur selben
Groesse fuehren - Tafelsumme gegen Gesamtzahl, geschriebene gegen erzwungene Wachen, Tabelle
gegen Referenzdatei -, wird die Gleichheit geprueft und nicht der Wert abgelesen. Eine
falsche Route faellt dann auf; eine Probe, die nur zaehlt, liefert eine plausible Zahl und
schweigt. Gemessen: eine Bereichsprobe fiel laut bei -80, weil sie eine Gleichung prueft.

**3 - Wertgleichheit zweier Routen ist kein Beleg fuer Mengengleichheit.** Gemessen: zwei
Routen lieferten beide 49 und hatten keine Zeile gemeinsam - 33 Feldzeilen, 3 Kopfzeilen,
9 Fortsetzungszeilen und 4 Prosazeilen gegen 33 Projektionen, 6 def und 10 Saetze. Wer zwei
Routen vergleicht, vergleicht ihre Mengen und nicht ihre Summen.

**4 - Bauausgaben mehrerer Targets werden nicht summiert.** Targets ueberlappen in ihren
Import-Huellen; ein Modul, das in zweien liegt, meldet zweimal. Gemessen: 27 betroffene
Deklarationen wurden auf diesem Weg zu 34. Wer ueber mehrere Targets zaehlt, gleicht die
Huellen ab oder misst je Modul mit `lake env lean`.

**5 - Ein erweitertes Nachschlagewerk wird als Menge geprueft, nicht als Zahl.** Wer Ledger,
Markenregister, Setzungsregister oder Statusregister erweitert, prueft die **Inklusion** des
alten Standes im neuen ueber die Eintrags-Schluessel - nicht, ob die Zahl gewachsen ist. Eine
wachsende Zahl belegt bei einer Erweiterung nichts; im schlimmeren Fall verdeckt sie einen
Verlust. Gemessen am Markenregister Rev. 2: der erste Anlauf verlor **neun** Eintraege des
alten Standes an die Aehnlichkeits-Entdopplung, darunter zwei Benennungs-Marken, und die
Gesamtzahl stieg dabei von 125 auf 281. Gefunden hat es die Mengenprobe, nicht der
Zahlenvergleich. Das ist Regel 3 in ihrer schaerfsten Gestalt: dort belegte Wertgleichheit
keine Mengengleichheit, hier belegt Wertzuwachs keine Mengeninklusion.

Die vierte Regel hat eine Schwester in §3: die Anwesenheit einer `.olean` ist kein Nachweis
der Targetzugehoerigkeit. Beide Male ist die Import-Huelle die tragende Groesse.
