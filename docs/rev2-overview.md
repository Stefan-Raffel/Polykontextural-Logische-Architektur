# PKL Rev2 - was Rev2 gegenueber Rev1 ergaenzt

*Repo-Dokument, keine Seite. `docs/` traegt `.nojekyll`; ausgeliefert werden nur die
HTML-Dateien der Projektseite. Diese Datei richtet sich an Mitarbeitende am Repo.*

Stand: 25. Juli 2026. Grundlage ist der Implementierungsplan zu PKLrev2.

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

Die Zahlen der ersten und der letzten Zeile sind am gruenen Build auf `59541bd` gemessen,
Wachen und Pins ueber die Zaehlrouten aus `CLAUDE.md` §3 nachgezaehlt. `59541bd` selbst
aendert nur `docs/` und drei Zeilen `README.md`; der Lean-Bestand steht seit `c576b57`.

Entwicklung laeuft auf Branch `rev2`. `main` bleibt auf `59541bd`, bis ein Rev2-Zug gruen ist.

---

## 3 - Namenslage

Drei Namen, die absichtlich auseinanderfallen:

| Ort | Name | Grund |
|---|---|---|
| Arbeitsverzeichnis | `PKL/Reformulation` | versionsfrei; die Version tragen die Tags |
| Lake-Paket und Lean-Bibliothek | `reformulation` / `Reformulation` | war schon immer versionsfrei |
| GitHub-Repo und Pages | `PKLrev1` | die publizierte Adresse bleibt gueltig |

Das Arbeitspapier zur Fassung Rev1 ist unter <https://stefan-raffel.github.io/PKLrev1/>
veroeffentlicht und zitiert diese Adresse. Eine Repo-Umbenennung wuerde die Erreichbarkeit
an einen Redirect haengen; das ist einer publizierten Adresse nicht zuzumuten. Der lokale
Verzeichnisname weicht darum vom Remote-Namen ab - fuer Git ohne Belang, hier vermerkt,
damit es spaeter niemanden irritiert.

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

Alle sechs sind **geplant, keine ist gebaut**. Der Stand wird hier nachgefuehrt.

### 5.1 Definition-Ledger - `docs/definition-ledger.md`

Verbindet `Definitionen.md` mit dem Lean-Bestand: je Begriff der Rev1-Ort, der Status, der
tragende Satz und die Grenze. Kein Eintrag darf mehr behaupten als der genannte Satz traegt.
Der Off-by-one zur Verbundkontextur-Folge (`CLAUDE.md` §5.3) wird ausdruecklich markiert.

### 5.2 Statusregister - `docs/status-register.md`

Trennt Aggregat, standalone, Foreign und historisch/offen. Die Rohliste liegt vor: von
155 `.lean`-Dateien sind 19 nicht importiert - das AxiomGate selbst, `Foreign/PeresMermin`,
drei `Diagnostics/`, sieben Proemial-Sonden, zwei `PathC/Classifying/`, zwei
`MathlibExtensions/Sites/`, `PathC/ModalTwoCategoryNegation` und
`F1/D2/Rollups/Coalgebraic/SubstantialRev2`. Je Eintrag: Grund des Status, etwaige
`True`-Felder, etwaige `sorry`-Stellen, Konsumenten, Exit-Kriterium.

Die Trennung ist der Sache nach die aus `CLAUDE.md` §10: **setzungsfrei bedeutet Aggregat,
setzungstragend bedeutet standalone.** Das Register schreibt sie nur auf.

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
`Bridge`. **Kein Quotientstyp als erster Schritt** - er kommt erst nach stabilen Normalform-
und Muster-Theoremen, wenn ueberhaupt.

### 5.5 Doku- und CI-Ordnung

`lake build` bleibt der harte Aggregatcheck, `lake build ForeignPeresMermin` der separate
Kalibrierungscheck. Standalone-Dateien werden gelistet, aber nicht mit dem Aggregatstatus
vermischt. README-Kennzahlen werden nachgefuehrt, sobald ein Modul ins Aggregat kommt.

---

## 6 - Nicht-Ziele

- keine zentrale `Contexture`-Superklasse; Kontextur bleibt mehrdeutig operational
  (Substruktur, Zweierbereich, Stufentraeger, Indexobjekt, Setzungsrand);
- keine Diskontexturalitaet als `Disjoint` und keine als `¬ ∃ f`, gemaess `CLAUDE.md` §5;
- keine zweite Negation als blosse Permutation;
- kein Quotientstyp fuer Morphogramme als erster Schritt;
- keine Sicherheits-, Rechts- oder Medizingarantie aus Nicht-Erzeugbarkeit;
- kein neues `True`-Feld im Aggregat ohne Status und Exit-Kriterium.

---

## 7 - Erfolgskriterien

Rev2 ist erreicht, wenn:

1. jeder Begriff aus `Definitionen.md` einen dokumentierten Rev1/Rev2-Status hat;
2. mindestens zwei Anwendungsmodule `GeneralCloneBound` oder `StageAggregation`
   konsumieren, statt Beweise zu kopieren;
3. mindestens eine Anwendung eine Konstanten-Robustheits-Aussage besitzt - also eine
   reflexive Invariante nach `CLAUDE.md` §9;
4. das Aggregat `sorryAx`-frei und das AxiomGate gruen bleibt, Whitelist leer;
5. jede Setzung registriert ist und ein Exit-Kriterium hat;
6. morphogrammatische Muster normalformbasiert nutzbar sind;
7. die Dokumentation ausdruecklich sagt, wo Lean endet und Deutung beginnt.

Kriterium 4 ist keine Aufgabe, sondern eine Erhaltungsbedingung: es gilt heute und darf
durch keinen Rev2-Zug fallen.

---

## 8 - Vollzug

| Datum | Schritt | Stand |
|---|---|---|
| 25.07.2026 | Verzeichnis `PKLrev1` -> `Reformulation` umbenannt | erledigt |
| 25.07.2026 | Kontrollbau nach Rename: 1267 Jobs, AxiomGate gruen | erledigt |
| 25.07.2026 | Tag `rev1` auf `59541bd`, Branch `rev2` angelegt | erledigt |
| | Definition-Ledger | offen |
| | Statusregister | offen |
| | PolicyCheck-Demonstrator | offen |
| | RAGAuthority-Demonstrator | offen |
| | Cybersecurity- und Normenhierarchie-Demos | offen |
| | Morphogramm-Bruecke | offen |
| | CI-Ausbau | offen |
