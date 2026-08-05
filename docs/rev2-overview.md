# PKL Rev2 - was Rev2 gegenueber Rev1 ergaenzt

*Repo-Dokument, keine Seite. `docs/` traegt `.nojekyll`; ausgeliefert werden nur die
HTML-Dateien der Projektseite. Diese Datei richtet sich an Mitarbeitende am Repo.*

Stand: 29. Juli 2026, Lean-Bestand `a66514f`. Grundlage ist der Implementierungsplan zu PKLrev2 in
seiner Fassung Rev. 2. Bei Widerspruch gilt der Plan, nicht diese Uebersicht: der Plan
traegt das Vorhaben, diese Datei erklaert die Repo-Form.

---

## 1 - Was Rev2 ist

Rev2 ist **keine neue Fassung des Korpus**, sondern eine additive Schicht ueber Rev1.
Die beweistragenden Kerne - Nicht-Erzeugbarkeit, Invarianten, Termklone, Stufenarithmetik,
Kenogramm-Normalformen - werden nicht refaktoriert. Rev2 **konsumiert** sie.

Vier Selbstbindungen:

- keine neue globale Theorie, die mehr behauptet als Rev1 beweist;
- keine Gleichsetzung von philosophischer Deutung und Lean-Satz;
- keine neue Setzung im Aggregat ohne ausdruecklichen Status;
- keine Anwendung ohne benannten konsumierten Satz.

Daraus folgt die Repo-Form: **ein Baum, ein Aggregat, ein AxiomGate.** Rev1 und Rev2 sind
nicht zwei Verzeichnisse, sondern zwei Zustaende desselben Baums, unterschieden durch Tags.
Eine Kopie haette den Korpus verdoppelt und damit genau die Auditierbarkeit zerstoert, die
Rev2 herstellen soll: zwei Baeume tragen zwei Eichwerte, und keiner ist mehr der gemeinte.

---

## 2 - Bezugsstand Rev1

Tag `rev1`, annotiert, auf Commit `59541bd`.

| Kennzahl | Wert |
|---|---:|
| geprueft (AxiomGate) | 2984 Konstanten |
| Axiom-Wachen | 299 ueber 35 Dateien |
| Statement-Pins | 36 |
| Saetze gesamt | 698 |
| Build-Jobs | 1267 |
| ausgewiesene Luecken | 0 (Whitelist leer) |

*Nachtrag 29. Juli 2026:* die Satzzahl dieser Tabelle steht auf der frueheren Route
`^(theorem|lemma) `. Seit dem Satzrouten-Zug fuehrt das README eine geweitete Route; die
beiden Zahlen sind Messpunkte verschiedener Routen und nicht gegeneinander zu lesen.

Die Zahlen der ersten und der letzten Zeile sind am gruenen Build auf `59541bd` gemessen,
Wachen und Pins ueber die Zaehlrouten aus `CLAUDE.md` §3 nachgezaehlt. `59541bd` selbst
aendert nur `docs/` und drei Zeilen `README.md`; der Lean-Bestand steht seit `c576b57`.

Entwicklung laeuft auf Branch `rev2`. `main` bleibt auf `59541bd`, bis ein Rev2-Zug gruen ist.

*Nachtrag 1. August 2026 (Vorgang 6, Stufe 1):* die Bedingung ist eingetreten und der
Fast-Forward vollzogen - `git push origin rev2:main` fuehrt `59541bd..cf5beba`, ein echter
Fast-Forward ohne Ueberschreiben. `main` und `rev2` stehen seither auf demselben Commit;
Default am Remote bleibt `main`, ohne dass eine Einstellung geaendert wurde. Der Satz oben
gilt rueckblickend und beschreibt nicht mehr den heutigen Stand.

Der Anlass war nicht Ordnungsliebe. Pages wird nach `docs/README.md` aus Branch `main`,
Ordner `/docs` ausgeliefert; am Stand `59541bd` trugen die drei HTML-Dateien fuenfmal den
Vermerk „nicht zur Veroeffentlichung", und `LICENSE`, `docs/LICENSE` und `CITATION.cff`
lagen dort nicht. Eine Umstellung auf oeffentlich vor dem Fast-Forward haette also eine
Projektseite ausgeliefert, die sich selbst als unveroeffentlicht bezeichnet, an einem
Repositorium ohne Lizenz. Kein Bau meldet das.

Rev1 ist davon nicht beruehrt: der annotierte Tag `rev1` zeigt weiterhin auf `59541bd`,
lokal wie am Remote, und `59541bd` bleibt Vorfahr von `main`. Ein Fast-Forward ruehrt Tags
nicht an.

---

## 3 - Namenslage

Drei Namen, die absichtlich auseinanderfallen:

| Ort | Name | Grund |
|---|---|---|
| Arbeitsverzeichnis | `PKL/Reformulation` | versionsfrei; die Version tragen die Tags |
| Lake-Paket und Lean-Bibliothek | `reformulation` / `Reformulation` | war schon immer versionsfrei |
| GitHub-Repo | `PKLrev1` | der Remote-Name bleibt; eine Umbenennung kauft nichts |

Der Remote-Name bleibt, aber nicht aus dem Grund, der hier frueher stand. Die Annahme, die
Adresse <https://stefan-raffel.github.io/PKLrev1/> sei publiziert und darum zu schonen, ist
gemessen falsch: am 29. Juli 2026 liefert sie ohne Anmeldung HTTP 404, ebenso die
Repo-Seite selbst. Das Repository ist privat, es gibt keine Leser ausser dem
Projektinhaber. Damit ist der Grund, nicht umzubenennen, ein anderer und ein schwaecherer:
eine Umbenennung kauft nichts und kostet einen Eingriff. Das Arbeitspapier liegt unter
`docs/`. Der lokale Verzeichnisname weicht vom Remote-Namen ab - fuer Git ohne Belang, hier
vermerkt, damit es spaeter niemanden irritiert.

**Nachtrag vom 1. August 2026 (Vorgang 6, Stufe 1):** der Remote-Name ist inzwischen
geaendert - `PKLrev1` heisst jetzt `Polykontextural-Logische-Architektur`. Gemessen an der
Antwort des Servers beim Push, nicht an der lokalen Konfiguration; `origin` zeigt weiter
auf den alten Namen und laeuft ueber die Weiterleitung. Die Tafelzeile oben und der Absatz
davor bleiben stehen: sie halten den frueheren Stand samt seiner Begruendung fest, und die
Messung vom 29. Juli gilt fuer die damalige Adresse. **Die Pages-Adresse folgt dem
Repo-Namen**; ob GitHub sie ebenso weiterleitet wie die Repo-URL, ist nicht gemessen und
vor der Umstellung auf oeffentlich auch nicht messbar.

*Nachtrag vom 1. August 2026 (Vorgang 6, Stufe 3):* jetzt gemessen, und die Antwort ist
**nein**. Anmeldungsfreier Abruf nach der Umstellung und nach dem Einschalten von Pages:

| Adresse | Statuscode |
|---|---:|
| `github.com/Stefan-Raffel/Polykontextural-Logische-Architektur` | 200 |
| `github.com/Stefan-Raffel/PKLrev1` | **301** auf den neuen Namen |
| `stefan-raffel.github.io/Polykontextural-Logische-Architektur/` | **200** |
| `stefan-raffel.github.io/PKLrev1/` | **404**, ohne Weiterleitung |

**Repository-URLs leitet GitHub weiter, Pages-Adressen nicht.** Die Messung traegt, weil
sie beide Seiten zugleich sieht: die neue Pages-Adresse liefert aus, waehrend die alte
404 gibt - es ist also nicht der Fall, dass nichts ausgeliefert wuerde. Der Satz oben
bleibt stehen und beschreibt den damaligen Kenntnisstand.

Das AxiomGate prueft ueber das Modulpraefix `Reformulation`, nicht ueber Verzeichnisnamen.
Kein Rename beruehrt es.

---

## 4 - Statusvokabular

Jeder neue Begriff bekommt zuerst einen Status, dann erst eine Abstraktion:

| Status | Bedeutung |
|---|---|
| `Theorem` | traegt einen maschinellen Satz |
| `Operationalisierung` | modelliert einen Begriff ueber vorhandene Beweismittel |
| `Benennung` | gibt einer vorhandenen Struktur einen PKL-Namen |
| `Deutung` | erklaert eine Lesart ohne Satzanspruch |
| `Setzung` | markiert ein bewusst nicht bewiesenes Strukturdatum |
| `Offen` | braucht noch Beweis oder Gegenmodell |

Das ergaenzt die Kopfmarke aus `CLAUDE.md` §4 (*Ertrag* oder *Benennung*), es ersetzt sie
nicht: die Kopfmarke sagt, was eine Datei ist, das Statusvokabular sagt es pro Begriff.

---

## 5 - Die Schichten

Was jede Schicht ist, steht hier; **wie weit sie gediehen ist, steht in §8** und sonst
nirgends. Gebaut sind die ersten beiden (Definition-Ledger, Setzungsregister); die uebrigen
sind offen.

### 5.1 Definition-Ledger - `docs/definition-ledger.md`

Verbindet `Definitionen.md` mit dem Lean-Bestand: je Begriff der Rev1-Ort, der Status, der
tragende Satz und die Grenze. Kein Eintrag darf mehr behaupten als der genannte Satz traegt.
Der Off-by-one zur Verbundkontextur-Folge (`CLAUDE.md` §5.3) wird ausdruecklich markiert.

### 5.2 Setzungsregister - `docs/status-register.md`

Fuehrt jede Setzung des Korpus mit Klasse, Reichweite und Exit-Kriterium beziehungsweise
Begruendung, warum sie keines hat. Die Zweiklassigkeit - Platzhalter gegen konstitutive
Setzung - steht in `CLAUDE.md` §10; das Register schreibt sie nur auf, samt der
Ablagekonvention: setzungsfrei bedeutet Aggregat, setzungstragend bedeutet standalone.

**Bau- und Targetstatus gehoeren nicht hierher.** Welches Modul in welchem Target liegt,
welche Module gar keines hatten und was ein gruener Bau je Target zusichert, steht seit dem
Buildabdeckungs-Zug in `docs/build-targets.md`.

### 5.3 Anwendungsdemonstratoren - `Reformulation/Proemial/Applications/`

`PolicyCheck` (Toolfreigabe), `RAGAuthority` (Quellenautoritaet), dazu Cybersecurity-Stufen
und Normenhierarchie. Jeder Demonstrator besitzt eine lineare Skala mit mindestens vier
Stufen und modelliert eine lokal klassische, aber nicht global uniforme Politik - ohne diese
Stufenachse darf keine Anwendung die starke Schranke beanspruchen.

Jeder Demonstrator **konsumiert** `GeneralCloneBound` beziehungsweise `StageAggregation`
und kopiert keinen Beweis. Was die Demonstratoren nicht sind: Sicherheits-, Rechts- oder
Medizingarantien. Bewiesen wird Nicht-Komponierbarkeit, sonst nichts.

### 5.4 Kenogramm-Morphogramm-Bruecke - `Reformulation/Kenogram/Morphogram.lean`

Mustersemantik normalformbasiert, ueber `relabel` und RGS, konsumierend aus `Basic` und
`Bridge`. **Kein Quotientstyp zu Beginn** - er kommt erst nach stabilen Normalform- und
Muster-Theoremen, wenn ueberhaupt.

### 5.5 Doku-Ordnung und Lint

Continuous Integration ist **Nicht-Ziel mit Ausloesebedingung**: sie kommt, sobald ein
zweiter Beitragender committet oder zum ersten Mal ein Commit ohne gruenen Bau vorkommt.
Der Grund steht im Plan §11 und wird hier nicht wiederholt.

`lake build` bleibt der harte Aggregatcheck, `lake build ForeignPeresMermin` der separate
Kalibrierungscheck. Standalone-Dateien werden gelistet, aber nicht mit dem Aggregatstatus
vermischt. README-Kennzahlen werden nachgefuehrt, sobald ein Modul ins Aggregat kommt.

`doc_lint.sh` liegt in der Repo-Wurzel. Ohne Argument laeuft er ueber das Repo, mit
Pfadargument ueber Aussentexte. Seine Gruppen zerfallen in zwei Arten, und die Art
entscheidet ueber den Exit-Code:

- **meldende Gruppen** - Rang-Ansprueche ohne Ist-Pruefung und ZFC-Rueckfaelle. Sie setzen
  keinen Exit-Code: ein Rang-Anspruch ist Ermessenssache, und ein brechender Lint wird
  umgangen, waehrend ein meldender gelesen wird. Die Beurteilung eines Treffers bleibt
  ausserhalb - das Skript nennt das Muster, nicht das Urteil.
- **brechende Gruppen** - dort, wo nichts zu ermessen ist und die Grundlinie null:
  Ledger-Regeln, gedruckte statt gewachte Axiomprofile, ausgabeinterne Ziffern von aussen
  zitiert. Ein Treffer setzt Exit 1.

*Welche Gruppen es heute gibt, sagt der Report des Laufs und nicht diese Datei; hier stand
bis zum Ziffern-Zug die Zahl zwei und der Satz „meldet und bricht nicht". Beides war seit
den brechenden Gruppen falsch und ist beim Anlegen der naechsten aufgefallen - eine
Gruppenzahl in Prosa ist eine Liste, und Listen altern.*

---

## 6 - Nicht-Ziele

- keine zentrale `Contexture`-Superklasse; Kontextur bleibt mehrdeutig operational
  (Substruktur, Zweierbereich, Stufentraeger, Indexobjekt, Setzungsrand);
- keine Diskontexturalitaet als `Disjoint` und keine als `¬ ∃ f`, gemaess `CLAUDE.md` §5;
- keine zweite Negation als blosse Permutation;
- kein Quotientstyp fuer Morphogramme zu Beginn;
- keine Sicherheits-, Rechts- oder Medizingarantie aus Nicht-Erzeugbarkeit;
- kein neues `True`-Feld im Aggregat ohne Status und Exit-Kriterium.

---

## 7 - Erfolgskriterien

Die Erfolgskriterien stehen im Implementierungsplan §13, mit Stand je Kriterium. Sie stehen
dort und nicht hier: eine zweite Liste laeuft von der ersten weg, und im Verlauf dieses
Projekts ist das zweimal geschehen.

Ein Kriterium sei dennoch hervorgehoben, weil es keine Aufgabe ist, sondern eine
Erhaltungsbedingung: das Aggregat bleibt `sorryAx`-frei, das AxiomGate gruen, die Whitelist
leer. Das gilt heute und darf durch keinen Rev2-Zug fallen.

---

## 8 - Vollzug

| Datum | Schritt | Stand |
|---|---|---|
| 25.07.2026 | Verzeichnis `PKLrev1` -> `Reformulation` umbenannt | erledigt |
| 25.07.2026 | Kontrollbau nach Rename: 1267 Jobs, AxiomGate gruen | erledigt |
| 25.07.2026 | Tag `rev1` auf `59541bd`, Branch `rev2` angelegt | erledigt |
| 26.07.2026 | Wachenluecke: 66 Axiom-Wachen im Kenogram-Zweig (`284995b`) | erledigt |
| 26.07.2026 | `CLAUDE.md` §10: Regel auf das Schutzziel (`f5d5244`, `3dc2649`) | erledigt |
| 26.07.2026 | `ElementaryCycle`: Elementarkontextur als Zweierbahn (`e69fb16`) | erledigt |
| 26.07.2026 | Definition-Ledger, Tabelle und Referenzdatei (`c61ca78`, `e3675d7`) | erledigt |
| 26.07.2026 | Kennzahl-Konsistenz, vier Posten (`f2aac24`) | erledigt |
| 28.07.2026 | Buildabdeckung: sechs Targets, `docs/build-targets.md` (`cfa9058`) | erledigt |
| 29.07.2026 | Dokumentationsabgleich README und diese Datei (`96fb0b7`) | erledigt |
| 29.07.2026 | Phase-2-Zuspitzung: 15 `True`-Deklarationen gestrichen (`4e5bbf7`) | erledigt |
| 29.07.2026 | Klassenmarken an allen 33 `True`-Feldern (`a66514f`) | erledigt |
| 29.07.2026 | Setzungsregister, `docs/status-register.md` | dieser Zug |
| | PolicyCheck-Demonstrator | offen |
| | RAGAuthority-Demonstrator | offen |
| | Cybersecurity- und Normenhierarchie-Demos | offen |
| | Morphogramm-Bruecke | offen |
| | Continuous Integration | Nicht-Ziel, Plan §11 |
