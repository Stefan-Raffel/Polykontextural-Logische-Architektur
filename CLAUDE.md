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

**Zitate in Memorial-Bloecken werden um zwei Leerzeichen eingerueckt.** Die Satzroute
zaehlt Zeilenanfaenge; ein uneingeruecktes Zitat wird als Deklaration gezaehlt und ist
damit eine stille Falschzaehlung. Die Regel gilt fuer `theorem`, `lemma`, `def`, `abbrev`
und `instance` gleichermassen.

Fuer `def` gilt dieselbe Weitung:

    grep -rhE '^((private|protected|nonrec) +)?(@\[[^]]*\] +)?def '

*Beleg (29. Juli 2026):* alte Route 309, geweitete 315; die Differenz sind sechs
`private def`. Zitate in Memorial-Bloecken gibt es fuer `def` bisher keine; die
Einrueckungsregel oben gilt trotzdem.

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

---

## 8 - Lean-Fallstricke (gemessen, nicht vermutet)

Alle neun sind an diesem Korpus aufgetreten und haben Zeit gekostet. Sie stehen hier, damit
sie nicht ein zweites Mal gefunden werden muessen. Der neunte ist kein Lean-Fallstrick,
sondern einer der Werkzeugkette; er steht hier, weil er dieselbe Sorte ist wie der achte.

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

*Gegengeprueft, ob eine stehende Route betroffen ist: nein.* `doc_lint.sh` nutzt weder
`git grep` noch `\b`; die verbindlichen Zaehlrouten in §3 laufen ueber `grep -rE` mit
expliziten Zeilenanfaengen. Der Eintrag ist Praevention. (Vorgang 6, Stufe 1.)

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

Die vierte Regel hat eine Schwester in §3: die Anwesenheit einer `.olean` ist kein Nachweis
der Targetzugehoerigkeit. Beide Male ist die Import-Huelle die tragende Groesse.
