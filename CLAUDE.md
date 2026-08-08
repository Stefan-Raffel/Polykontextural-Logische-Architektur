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

> **Die Zaehlrouten dieses Paragraphen fahren in `./kennzahlen.sh`** (§13). Wer eine
> Kennzahl braucht, ruft das Skript - es gibt jede Zahl mit ihrer Route aus und prueft
> Gleichungen zwischen ihnen mit. Die Prosa hier begruendet die Routen; sie ist **nicht**
> die Vorlage zum Abschreiben.

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
`grep`. **Die Satzzahl bleibt eine `grep`-Route, und das ist keine Bequemlichkeit** - die
Umgebung fuehrt Saetze, die niemand geschrieben hat, siehe Fallstrick 13. Seit dem
Satzrouten-Zug in geweiteter Form:

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

**Wer sie doch braucht, ruft `./kennzahlen.sh`** - es zaehlt §8, §12 und die ganze Datei
und prueft die Gleichung `§8 + §12 = Datei` mit. Von Hand wurde diese Zahl dreimal
nachgezogen; seit §13 wird sie nicht mehr nachgezogen, sondern gemessen.

*Warum die Route eine Abschnittsgrenze braucht.* Die naive Route ueber die ganze Datei
liefert mehr als §8, weil §12 gleich ausgezeichnete Eintraege fuehrt - und beim Nachzaehlen
in Zug A lieferte ein erster Lauf fuer §12 **null**, weil das Abbruchmuster fuer das
Dateiende auf jede Leerzeile passte. Die Gleichung fiel damals laut aus; eine Probe, die nur
eine Zahl abliest, haette geschwiegen. Beide Fehler sind der Grund, aus dem das Skript nicht
zaehlt, sondern eine Gleichung prueft.

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

*Zweite Heilung, kuerzer, und beide gemessen gleich (7. August 2026):* `value?` nimmt ein
optionales Argument, und **`ci.value? (allowOpaque := true)` sieht den Beweisterm eines
Satzes**. Gemessen an zwei Saetzen des Aggregats unter `v4.30.0-rc2`:

    ci.value?                        -> none  (thmInfo, beide)
    ci.value? (allowOpaque := true)  -> some  (thmInfo, beide)
    ci.value?                        -> some  (defnInfo — dort braucht es das Argument nicht)

Die Konsumentenmessung dieses Tages ist auf **beiden** Wegen gefahren worden, von zwei
Instanzen unabhaengig: Musterung nach `.thmInfo v => v.value` und `value?` mit dem
Argument. Beide liefern **dieselben sieben Namen**. Der Eintrag bleibt trotzdem stehen,
und zwar unveraendert in seinem Kern: **die Route ohne das Argument ist blind**, und wer
`value?` gedankenlos aufruft, misst null. Das Argument ist die Heilung, nicht die
Entwarnung.

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

**13 - Eine Satzmenge „aus der Umgebung" enthaelt Saetze, die niemand geschrieben hat.**
Eine Struktur mit einem `Prop`-Feld erzeugt eine Projektion, die die Umgebung als `thmInfo`
fuehrt und die im Quelltext keine `theorem`-Zeile hat. Der Filter auf Quell-Deklarationen
(§3) faengt sie nicht: sie tragen keinen der Begleiter-Suffixe. Gemessen an den neun
`Proemial.AlphaGamma*`-Modulen (Vorgang 15, Stand `3b2da94`): die Umgebungsroute liefert
**54**, die verbindliche `grep`-Satzroute **43**; die Differenz sind Prop-Feld-Projektionen
und drei Deklarationen, deren Bereichsangabe auf den Doc-Kommentar zeigt statt auf die
Deklarationszeile.

*Welche Route richtig ist, entscheidet die Frage und nicht die Bequemlichkeit.* Fuer die
**Wachenpflicht** ist es die `grep`-Route, weil die Pflicht an geschriebenen Saetzen haengt;
fuer eine Aussage darueber, was die Umgebung traegt, ist es die Umgebungsroute. Dieselbe
Lehre wie bei der `sorry`-Zahl und bei der Satzroute selbst, hier zum ersten Mal an der
**Umgebung** statt am Text - und darum ein eigener Eintrag: wer eine Menge dort bildet,
misst mehr und freut sich, statt nachzusehen.

*Heilung, falls beides gebraucht wird:* die Menge aus der `grep`-Route bilden und in der
Umgebung **aufloesen**, statt sie dort zu suchen. Die Aufloesungsprobe (alle gefunden?) ist
dann die Gegenprobe, die eine Suche nicht hat.

**14 - `#print axioms` bricht seine Ausgabe an der ZEILENLAENGE um, nicht an der
Namenslaenge.** Die gedruckte Zeile lautet `'<Name>' depends on axioms: <Profil>`; fuer das
Profil `[propext, Classical.choice, Quot.sound]` gilt

    Zeilenlaenge  =  len(Name) + 61

**Gemessen:** ohne Umbruch bei Zeilenlaenge 116 (`end_id_comm`, 55 Namenszeichen), mit
Umbruch bei 123 (`naturality_K_from_S`, 62 Namenszeichen). **Das Intervall ist in seiner
Mitte offen** - zwischen 55 und 62 Namenszeichen liegt am gemessenen Bestand kein Messpunkt.
Die pp-Breite 120 ist mit dem Intervall vertraeglich; sie stammt aus einer frueheren Messung
des Korpus und ist **nicht** hier am Werkzeug abgefragt. Bei einem anderen Profil verschiebt
sich die Schwelle um dessen Laengendifferenz.

*Die Folge fuer den Leser:* ein umgebrochener Erwartungstext ist die richtige Form und keine
Schlamperei. Er wird **nicht** „geheilt" - `#guard_msgs` vergleicht die Ausgabe verbatim, und
eine glattgezogene Erwartung bricht den Bau. Umgekehrt gilt dasselbe: wer alle Wachen einer
Reihe nach einer Schablone setzt, bricht die kurzen. Gemessen an den 17 Saetzen des
α+γ-Strangs (Stand `8e54889`); beim Setzen der dreizehn Wachen der Stufe 2 hat jede der
dreizehn Erwartungen beim ersten Lauf gehalten, elf in umgebrochener und zwei in einzeiliger
Form.

**15 - `#print axioms` hat ZWEI Wortlaute; wer nur einen sucht, misst zu klein.** Die
Ausgabe lautet

    '<Name>' depends on axioms: <Profil>          fuer jeden Satz mit Axiomen
    '<Name>' does not depend on any axioms        fuer jeden axiomfreien Satz

Wer die gewachten Namen aus den eingefrorenen Erwartungstexten zieht und nur den ersten
Wortlaut sucht, findet die axiomfreien Wachen nicht. **Gemessen am Stand `c3b28cb`:** die
Route ueber den ersten Wortlaut allein liefert **415** Namen, ueber beide **487** - 72
Wachen des Bestandes sind axiomfrei.

*Heilung:* beide Wortlaute suchen, und die gewonnene Namensmenge gegen die `grep`-Route der
Wachen eichen - Mengengroesse gegen Mengengroesse, §12 Regel 2.

*Warum der Eintrag hier steht:* das Ergebnis war **nicht leer, sondern knapp zu klein**.
Eine Huelle aus 415 Saatnamen laesst sich rechnen, sie sieht plausibel aus, und keine
Zwischenrechnung faellt dabei auf; gefunden hat es allein die Eichung. Das ist der achte
Fallstrick in weiterer Gestalt, und die unangenehmere: ein leeres Ergebnis stutzt, ein knapp
zu kleines nicht.

**16 - Ein blosses `#print axioms` sieht aus wie eine Sicherung und ist keine.** Ohne
`#guard_msgs` davor druckt es ein Profil in die Bauausgabe und sichert **nichts**: aendert
der Satz sein Profil, druckt es das neue und der Bau bleibt gruen. In einer Datei steht
dann ein Abschnitt, oft unter der Ueberschrift „Verifikation (kein `sorryAx`)", der wie
Sorgfalt aussieht. §3 unterscheidet *geschrieben* und *erzwungen*; hier liegt eine dritte
Stufe darunter - **gedruckt gegen gewacht.**

**Gemessen am Stand `4c263ee`** (die Zahlen bleiben an diesem Stand geankert, auch nachdem
Zug B sie geheilt hat - historische Messung wie „415 statt 487" im fuenfzehnten Eintrag):
**39** blosse Aufrufe in 9 Dateien, davon **28** auf einen Satz der **eigenen** Datei in
der Import-Huelle der Default-Targets. Nackt und gewacht kamen dabei in keiner Datei
zusammen vor.

*Zwei Klassen, die nicht zusammengeworfen werden duerfen.* In einem **Messwerkzeug** ist
der nackte Aufruf die **richtige Bauform** - ein Werkzeug, das Profile anzeigen soll, darf
sie nicht einfrieren; betroffen sind `Diagnostics/AxiomProbe.lean` und
`Diagnostics/SwapSatzProbe.lean` mit zusammen 11 Aufrufen. Nackt **neben einem Satz, den
man sichern koennte**, ist der Fallstrick. Eine Route, die beides zaehlt, erzeugt falsche
Treffer, und eine Pruefung mit falschen Treffern wird abgeschaltet.

*Route.* **Zuerst die Kommentare entfernen** - `--` bis Zeilenende und `/- -/`
verschachtelt, einschliesslich `/--` und `/-!`, Strings uebersprungen -, dann suchen. Eine
blosse `grep`-Differenz misst **zu hoch**: das Suchwort steht auch in Prosa, und seit den
Wachen zusaetzlich in Erwartungstexten. Gegengerechnet am selben Stand:
roh 551 = 501 Wachen + 39 nackt + 11 Prosa.

*Seit dem Lint-Zug ist der Fall bewacht.* **Gruppe (D) von `doc_lint.sh` faehrt diese
Route bei jedem Lauf und bricht** - Grundlinie null, Bereich `.lean`, Ausschluss ueber die
Marke `-- LINT-AUSNAHME (D):` im Dateikopf statt ueber eine Dateiliste. Wer ein neues
Messwerkzeug anlegt, setzt die Marke und begruendet sie; wer sie ohne Grund setzt, hat den
Fallstrick nicht geheilt, sondern verlegt.

### Ausgabeinterne Ziffern - der Gegenstand der Lint-Gruppe (E)

**Die Ziffern in eckigen Klammern, mit denen Teil A der Papierfassung auf die Traegertafel
in Teil B verweist, sind AUSGABEINTERN.** Sie werden je Ausgabe neu vergeben, wie
Fussnotennummern, und ausserhalb von Ausgabe und Entwurf nicht zitiert. Der Grund ist die
Lesereihenfolge: neue Saetze in den vorderen Kapiteln muessen eingefuegt werden, und dann
verschiebt sich alles Folgende. Wer eine Ziffer von aussen zitiert, zeigt nach der
naechsten Ausgabe auf einen anderen Satz - und **niemand merkt es**, weil kein Bau bricht.

**Ergebnisdokumente sind ausgenommen, und das ist keine Ausnahme, sondern eine Anwendung.**
Ein Ergebnisdokument haelt einen Stand seines Datums fest (§11: Fund ja, Stand nein); seine
Kennzahlen werden nicht nachgefuehrt, wenn sich der Bestand bewegt, und seine Ziffern sind
derselbe Fall - sie meinen die Traegertafel seines Datums. Der Schnitt laeuft darum ueber
`Papierausgabe_*.md`, als Glob und nicht als Dateiliste.

*Was der Schnitt kostet, gehoert dazu:* die Gruppe sieht gerade die Dokumente nicht, in
denen die Ziffern am dichtesten stehen - gemessen 25 Verweisungen in den drei
Rev4-Zugdokumenten. Sie bewacht den **laufenden** Bestand, und dort ist die Grundlinie
null.

*Und ein Fund, der die Festlegung erst noetig machte:* die Traegertafel ist eine Erfindung
der **vierten** Ausgabe. `docs/rev1|rev2|rev3` tragen je null Ziffern; vor Rev4 gab es
nichts zu bewachen.

**17 - Lean-Namen duerfen `?` und `!` enthalten; eine Zeichenklasse verliert sie still.**
Die Route `'([A-Za-z0-9_.']+)'` ueber die eingefrorenen Erwartungstexte lieferte **500**
Namen bei **501** Wachen. Die eine Differenz war
`Reformulation.Kenogram.relabel_getElem?_eq_iff`. Eine zweite Route,
`grep -oE '#print axioms [A-Za-z_0-9.]+'`, schnitt denselben Namen an derselben Stelle ab
und meldete eine Scheindifferenz - **zwei Routen, derselbe blinde Fleck.**

Das Ergebnis war nicht leer, sondern **um eins zu klein**; ohne Eichung waere die
Wachenhuelle um einen Saatnamen zu klein geworden, und ein Satz, den nur dieser Zweig
deckt, waere faelschlich als huellenfrei gemeldet worden.

*Heilung:* **den Namen nicht durch eine Zeichenklasse beschreiben, sondern durch das, was
ihn begrenzt** - hier die Anfuehrungszeichen und der folgende Literaltext, also `'(\S+)'`.
Lean-Namen enthalten keine Leerzeichen; der Anker macht das sicher. *Gegenprobe:* die
gewonnene Namensmenge gegen die verbindliche Wachenroute eichen, Mengengroesse gegen
Mengengroesse (§12 Regel 2).

**18 - Eine Route, deren Bereichsliste aelter ist als der Zug, misst den Vorstand und
meldet ihn als neuen Stand.** Gemessen im Stellen-Tausch-Zug: der erste Lauf der zweiten
Messung nahm die Modulliste der Aggregat-Huelle aus einem Stand **vor** dem Zug, in dem das
neue Modul `Kenogram/PlaceSwap.lean` naturgemaess fehlt.

*Was die Gestalt neu macht:* **das Ergebnis war richtig und die Route trotzdem blind.**
Dieselbe Zahl - wachenfreie Aggregat-Saetze, 66 in 22 Modulen - waere herausgekommen, weil
die Route das neue Modul **gar nicht angesehen** hat. Und **keine bestehende Gegenprobe
haette es gezeigt: sie alle sehen auf den Wert.**

Damit fuehrt der Korpus drei Gestalten des Messfehlers, und das ist die dritte: das
**leere** Ergebnis (Fallstrick 9), das **knapp zu kleine** (Fallstricke 15 und 17), und das
**richtige aus dem falschen Grund**. Die Reihe steht hier zusammen, weil ein Leser die
Gattung an ihr erkennt und nicht am Einzelfall.

*Heilung:* **die Bereichsliste nach dem Zug erzeugen, nicht vor ihm** - und die
**Modulzahl selbst als Gegenprobe lesen**: sie muss sich bewegt haben. Gemessen 112 -> 113
Module; die Bewegung trat erst nach der Heilung ein. Vor dem Zug erzeugte Listen sind fuer
den Regel-6-Lauf (§12) richtig und fuer die Nachmessung falsch; beide Laeufe brauchen ihre
eigene Liste.

**19 - Die Textextraktion aus PDF setzt an Zeilenumbruechen Trennstriche; ein
Zitatvergleich ohne Tilgung meldet Fehlalarm.** Gemessen an `KorpusRev1/e_und_w.pdf` ueber
`pypdf` (kein `pdftotext` auf dieser Maschine): von fuenf woertlich richtigen Zitaten
meldeten **zwei** Abweichung - `Um- tauschrelation` auf S. 27 und `Rangord- nung` auf
S. 29. Dieselbe Extraktion zerreisst ausserdem Woerter ohne Trennstrich
(`kenogrammatisch en`).

*Die Begruendung des Eintrags ist die Quote und nicht der Einzelfall.* **Eine Pruefung,
die bei zwei von fuenf richtigen Stellen anschlaegt, wird beim dritten Mal nicht mehr
gelesen** - und uebersieht dann die eine echte Abweichung, fuer die sie gebaut wurde. Es
ist dasselbe Argument, mit dem der Lint seinen Pfadausschluss bekam: eine Meldung, die man
gewohnheitsmaessig wegdrueckt, ist schlechter als keine.

*Heilung:* vor dem Vergleich Trennstriche **und** Leerraum tilgen; wer nur Leerraum tilgt,
faengt die zweite Haelfte der Faelle nicht.

*Und die Verschaerfung, die daran haengt.* Das Etikett **quellen-fest** heisst: an der
Quelle geprueft, mit Seitenangabe, und die Pruefung ist benannt. Keine neue Regel - ein
vorhandener Mechanismus, der eine Route hatte fuer alles ausser fuer sich selbst. *Anlass:*
eine Wiedergabe im Transkript hat als Quelle gedient, und eine Wendung darin war
abgewichen (`welche Schaerfe die Ordnung hat` gegen die *implikative* Schaerfe der Quelle).
Mitzupruefen ist der Seitenanker selbst: Druck- und PDF-Seite koennen auseinanderfallen.

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

**Die Regelform: die Commit-Nachricht ist der Bericht.** Ein Zug endet in einem Commit und
einer Zeile in `docs/journal.md`. Die Nachricht traegt, was der Zug getan und gemessen hat;
die Journalzeile traegt Datum, Hash, einen Satz und - wenn es einen gab - den Fund. Beides
liegt in der Geschichte, ist an den Stand gebunden und kostet keinen zweiten Ort.

**Ein eigenes Ergebnisdokument nur auf Verlangen** oder wenn der Zug etwas findet, das
laenger ist als eine Commit-Nachricht: eine Erhebung, eine Begutachtung, eine Messung mit
Tafel. **Die Faustregel: was in eine Commit-Nachricht passt, gehoert in eine
Commit-Nachricht.** Bis zu diesem Paragraphen endete jeder Zug in einem mehrhundertzeiligen
Befund; das war der groesste Einzelposten dieses Projekts und hat den Bau verdraengt, den er
berichten sollte (§13).

**Und kein Ergebnisdokument schreibt eine Kennzahl ab.** Sie stehen in `docs/kennzahlen.md`,
erzeugt von `./kennzahlen.sh --markdown`, mit Stand-Anker. Ein Bericht zeigt dorthin.

Was fuer beide Formen gilt - Nachricht wie Dokument:

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

Regeln, jede aus einem gemessenen Fehlgriff dieses Korpus. Sie gelten fuer jede Zahl,
die ein Dokument verlaesst - und, seit der neunten, auch fuer die Pruefungen, deren
Unterlassung sich nicht meldet.

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

**6 - Eine wiederholte Messung laeuft zuerst mit der Saatmenge des vorigen Zuges.** Wird
eine Messung nach einer Aenderung wiederholt, muss dieser erste Lauf die Zahlen des vorigen
Zuges **exakt** reproduzieren; erst dann gilt der neue Lauf. Anlass: die Wachenspitze
Stufe 2 - die Huellenmessung lief zweimal ueber dieselbe Umgebung, einmal mit den 474
Wachennamen des Vorstandes und einmal mit allen 487. Der erste Lauf bestaetigte den Stand
der Stufe 1 Zahl fuer Zahl (464 wirksam, Huelle 7585, 6 innen, 37 aussen), und erst damit
war der zweite mit ihm vergleichbar.

**Was die Regel leistet, und was nicht.** Die Regeln 1 bis 3 pruefen ein *Ergebnis* gegen
eine Erwartung oder gegen eine zweite Route desselben Standes. Diese hier prueft, ob die
Route **in zwei Zuegen dasselbe misst**. Eine Abweichung im ersten Lauf hiesse: die beiden
Messungen sind nicht vergleichbar - und das faellt sonst niemandem auf, weil beide fuer sich
plausibel sind. Sie ersetzt keine der uebrigen Regeln; sie kommt hinzu, wo ein Stand gegen
einen frueheren gestellt wird.

**7 - Wer einen Bestand aendert, prueft die Aussagen anderer Dateien ueber diesen
Bestand.** §11 regelt den fremden Stand, den man *mitliest*; hier geht es um den fremden
Stand, den die **eigene Aenderung entwertet**. Der Unterschied ist, dass niemand ihn meldet:
kein Bau bricht, kein Lint schlaegt an, und die falsch gewordene Aussage steht in einer
Datei, die der Zug gar nicht angefasst hat.

Gemessen: der K1-Zug wachte vier Sonden und machte damit den Kopfvermerk in
`Proemial/AsymmetricDiscontexturalityProbeRegister.lean` falsch - dort stand „die Sonden
selbst tragen nach Bestand keine Wachen". Er wurde im selben Zug nachgefuehrt. Zug A
benannte einen Satz um und machte damit drei Prosastellen in drei anderen Dateien falsch.

*Route:* vor dem Abschluss den geaenderten Namen oder Sachverhalt ueber `Reformulation/`
und `Foreign/` suchen, **auch in Prosa und Doc-Strings** - ein Term-Konsument bricht den
Bau, eine Prosa-Aussage nicht. Wer nur den Bau als Probe nimmt, findet die zweite Klasse
nie.

**Und der Suchbereich endet nicht am Lean-Bestand.** Seit dem Schaufenster-Zug stehen
Satznamen auch in `docs/index.html` und in `README.md` - beide ausserhalb jeder
Namensprobe: `profil_probe.sh` loest nur Traegertafel-Namen auf, und Lint-Gruppe (F)
prueft Anker, keine Namen. **Wer einen Satz umbenennt, der auf der Startseite oder im
README beim Namen steht, fuehrt beide nach.** Kein neues Werkzeug: eine stehende
Papier-gegen-Bestand-Lint ist mit der Rev6-Entscheidung abgelehnt, und der Ausfallmodus
ist derselbe wie bei der uebrigen Regel - kein Bau bricht, kein Lint schlaegt an.

**8 - Eine Gegenprobe wird gegen den Zug geprueft, der sie verwendet; ihr Anker liegt an
einer Stelle, die der Zug nicht beruehrt.** Ein Muss-Fall, der auf eine Fundstelle zeigt,
die der Zug beseitigt, wird durch den Zug selbst falsch - und er ist danach
**stillschweigend unbrauchbar** statt auffaellig kaputt.

Gemessen: der Muss-Fall der Nackt-Route zeigte auf drei Zeilen in
`Proemial/K4DiscontexturalityProbe.lean`, die Zug B geheilt hat; die Nachmessung meldete
fuer ihn `False`, ohne dass an der Route etwas falsch war.

*Die Sortierung, die hilft.* Muss-Faelle **aus dem Zielbereich** sind nach dem Zug
verbraucht; sie belegen den Vorstand und sind fuer die Nachmessung neu zu setzen. Muss-
Faelle **aus dem Ausschlussbereich** ueberleben - in Zug B waren das die
`Diagnostics`-Messwerkzeuge, die nach Vorgabe nackt bleiben. Die geheilten Stellen wechseln
die Seite und werden zu **Darf-nicht-Faellen**; dort sind sie wertvoller als vorher, weil
sie pruefen, dass der Zug gegriffen hat.

**9 - Vor der Vergabe eines Namens wird geprueft, ob er im Bestand oder im Umfeld besetzt
ist; ist er es, entscheidet die Bedeutung und nicht die Naehe.** Die Regel steht in diesem
Paragraphen, obwohl sie keine Zahl regelt: sie teilt mit den uebrigen den Ausfallmodus -
**die unterlassene Pruefung meldet sich nicht**, sie laesst den Bau gruen.

Zwei Anlaesse, beide gemessen:

- **Ein Buchstabe, der im selben Strang zwei verschiedene Dinge bezeichnete.** Im
  α+γ-Strang trug `γ` den **Tausch** `(L ⋙ R) ⟶ (R ⋙ L)` an einer Stelle und den
  **Kollaps** `L ⋙ R ≅ 𝟭 S` ueberall sonst. Zwei Saetze mit fast gleichem Namen und
  entgegengesetzter Substanzlage; die Doppeldeutigkeit war jahrelang unsichtbar, weil
  beide Lesarten fuer sich stimmig sind.
- **Ein Name, unter dem der Bestand bereits die Werte-Vertauschung fuehrt.** Fuer die
  Stellen-Vertauschung lag `swapVals` nahe - und ist in
  `Proemial/K3CouplingProbe.lean` fuer die **Werte**-Vertauschung besetzt. Die Folge, die
  ihn gefaehrlich macht, ist gemessen: **mit `Kenogram.swapVals` waeren zwei Saetze des
  Moduls trivial und der Bau gruen** (`relabel ∘ swapVals` ist auf Normalformen die
  Identitaet, die Kommutation gaelte geschenkt, die Charakterisierung waere falsch).

*Und der prophylaktische Fall, der zeigt, dass die Regel nicht bloss Vorsatz ist.* Im
Stellen-Tausch-Zug wurden drei Namen **vor** der Definition geprueft und zwei begruendet
verworfen: `swapVals` (im Bestand besetzt) und `swapAt` (`Array.swapAt`/`Vector.swapAt`
setzen einen Wert und geben den alten zurueck - im Umfeld anders bedeutend). Gebaut wurde
`swapPlaces`, 0 Vorkommen im Bestand, kein `List.swapPlaces`/`Array.swapPlaces` im Umfeld.
**Die Regel hat gegen ihren eigenen Vorschlagenden entschieden.**

*Route:* den Kandidaten vor der Definition ueber `Reformulation/` und `Foreign/` suchen
**und** im Umfeld (Mathlib, Lean-Kern) - und bei einem Treffer nicht die Naehe entscheiden
lassen, sondern die Bedeutung.

**10 - Fallen Wortlaut und Grund einer Vorgabe auseinander, gilt der Grund - und die
Divergenz wird gemeldet.** Auch diese Regel regelt keine Zahl; sie steht hier aus demselben
Grund wie die neunte und mit demselben Ausfallmodus in seiner schaerfsten Gestalt: **die
buchstabengetreue Befolgung meldet sich nicht als Fehler, sondern als Erfolg.** Wer den
Wortlaut erfuellt und die Sache verfehlt, hat einen gruenen Zug, eine erfuellte Auflage und
kein Warnzeichen.

Zwei Anlaesse, beide gemessen:

- **Ein Gegenstand, den die Vorgabe der Ablage zuwies und der in einer Lean-Datei lag.** Im
  Formulierungs-Zug verlangte §1 die Trennung von Ablage- und Bestands-Commit; Gegenstand 4
  war dort der Ablage zugeschlagen. Die Suche ueber `Reformulation/`, `Foreign/`, `docs/`,
  `README.md` und `CLAUDE.md` fand ihn an **einer** Stelle, und die war ein Dateikopf in
  `Kenogram/PlaceSwap.lean`. Nach dem Wortlaut haette eine Lean-Datei in den Ablage-Commit
  gehoert - und genau das haette aufgehoben, was die Trennung sichern soll: der
  Ablage-Commit haette einen Bau nach sich gezogen und die Kennzahlenmessung ihre Ursache
  verloren. Der Gegenstand ging in den Bestands-Commit.
- **Eine Pruefung, deren Bereich kleiner war als der Anspruch, den sie pruefen sollte.** Die
  Vorgabe zur fuenften Ausgabe knuepfte eine Aussage ueber **alle** vierzig Traeger des
  Papiers an die Profile von **dreien**. Keiner der drei fiel axiomfrei aus; nach dem
  Wortlaut haette die Rangaussage stehen duerfen. Gemessen wurden alle vierzig - und der
  vierte axiomfreie Traeger, `Proemial/StageAscent.lean` `ascent_proper`, stand in keiner
  der drei Marken. Die Rangaussage faellt und wird durch die gemessene Liste ersetzt.

*Route:* vor der Ausfuehrung einer Auflage den Bereich nennen, ueber den sie entscheidet,
und ihn gegen den Bereich der Aussage halten, die sie schuetzen soll. Sind die beiden
verschieden, wird der groessere gemessen und die Divergenz in den Befund geschrieben - die
Auflage wird dabei nicht stillschweigend geweitet, sondern ihr Fehlgriff benannt.

*Und die Grenze der Regel.* Sie erlaubt kein Auslegen nach Gutduenken: der Grund muss der
**genannte** Grund der Vorgabe sein, nicht ein unterstellter. Wo die Vorgabe ihren Grund
nicht nennt, gilt ihr Wortlaut, und die Nachfrage ist der Zug.

### Die Kontaktzahl: eine Messgroesse und ihr Bereich

Die Kontaktzahl misst, ob ein Beweisterm im Aggregat **beide Straenge** beruehrt - den
kenogrammatischen und den kategorialen.

Sie war ueber ein **Modul-Namensmuster** definiert (`Kenogram.*` gegen `AlphaGamma*`), mit
dem Muster als Stellvertreter des kategorialen Strangs. Seit dessen Haelfte in
`Proemial/ArrowAscent.lean` liegt, trifft der Stellvertreter seinen Gegenstand nicht mehr.
**Geaendert ist die Definition der Groesse, nicht ihr Wert:**

- sie nennt den **Strang** und nicht ein Namensmuster;
- die Modulliste wird **bei jeder Messung neu gebildet**, nicht fortgeschrieben - sonst
  altert sie beim naechsten Modul wieder (Fallstrick 18 ist derselbe Fehler an einer
  anderen Groesse);
- verbindlich ist der Stand **ein Kontakt**, mit `Proemial/RetractionBracket.lean`
  `both_strands_retract` als benannter Ursache;
- **beide Zahlen bleiben in den Befunden stehen, aus denen sie stammen**; die frueheren
  Nullen waren an ihrem Stand richtig.

*Gegen den Verdacht der Opportunitaet, und darum hier vermerkt:* haette man die Groesse
einen Zug frueher geweitet, stuende sie weiterhin bei **null** - die beiden kategorialen
Zeugen des Ordnungswechsel-Zuges beruehren weder `Kenogram.*` noch `AlphaGamma*`. **Die
Weitung erfindet keine rueckwirkende Bewegung.**

Die vierte Regel hat eine Schwester in §3: die Anwesenheit einer `.olean` ist kein Nachweis
der Targetzugehoerigkeit. Beide Male ist die Import-Huelle die tragende Groesse.

---

## 13 - Rueckbau: wann eine Regel entfaellt

Bis zu diesem Paragraphen wuchs diese Datei **monoton**. Jeder Fehlgriff wurde zu einer
Regel, jede Regel prueft seither jeden Zug, und keine ist je entfallen - neunundzwanzig
Eintraege, null Ausserkraftsetzungen. Der Apparat sollte Zahlen schuetzen; er hat angefangen,
die Arbeit zu verdraengen, die er schuetzt. **Das ist kein Vorwurf an die Regeln, sondern ein
fehlendes Gegenstueck**: eine Ablage ohne Verfall ist kein Werkzeug, sondern ein Archiv.

**§13.1 - Was ein Skript fahren kann, steht nicht als Handlungsanweisung.** Eine Regel, deren
Route maschinell laeuft, wird zur Zeile im Skript; in dieser Datei bleibt der **Grund** und
ein Zeiger, nicht das Kommando. Ein Grund altert nicht, ein Kommando altert bei jedem Zug.

**§13.2 - Eine Regel, die zwei Ausgaben lang nicht gefeuert hat, wird gestrichen oder
maschinell.** Gefeuert heisst: sie hat einen Zug angehalten oder korrigiert, nachweisbar an
einem Befund oder einem Commit. Wer sie behalten will, nennt den Fall. **Eine Regel ohne
Fall ist eine Vermutung mit Nummer.**

**§13.3 - Wer eine Regel setzt, sagt, wie sie wieder verschwindet.** Zu jedem neuen Eintrag
gehoert ein Satz: was sie maschinell machen wuerde, oder woran man merkt, dass sie sich
erledigt hat. Ohne diesen Satz ist der Eintrag unvollstaendig.

**§13.4 - Der Rueckbau ist ein eigener Zug und braucht keine Vorgabe.** Er darf Regeln
streichen, zusammenlegen und in Skripte verschieben; er darf keine setzen. Was er streicht,
nennt er mit Nummer und Grund in der Commit-Nachricht - **die Geschichte behaelt, was die
Datei verliert.**

*Erster Vollzug, `kennzahlen.sh`.* Die Zaehlrouten aus §3 fahren jetzt in einem Skript, mit
vier mitlaufenden Gleichungen. Die Prosa in §3 begruendet sie weiterhin und **ersetzt sie
nicht mehr**: wer eine Kennzahl braucht, ruft `./kennzahlen.sh` und schreibt keine `grep`
Zeile von Hand ab. Damit sind §12 Regel 1, 2 und 4 an dieser Stelle **ausgefuehrt statt
befolgt** - die Gegenrechnung, die Gleichungspruefung und die Nicht-Summierung der Targets
stehen im Skript und nicht mehr in der Sorgfalt des Zuges.
