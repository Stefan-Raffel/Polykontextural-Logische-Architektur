# Kennzahlen

**Erzeugt von `kennzahlen.sh --markdown`. Nicht von Hand aendern.**

Kennzahlen des Korpus stehen als **Werte** hier und sonst nirgends.
Papier, README und Ergebnisdokumente zeigen hierher und schreiben keine Zahl ab.
Der Grund steht in `CLAUDE.md` §13: eine Zahl, die an zwei Orten steht, hat
einen Ort zu viel, und der zweite altert unbemerkt.

Stand: Commit `2c075aa` (sauber).
Alle mitlaufenden Gleichungen halten.

| Kennzahl | Wert | Route |
|---|---:|---|
|  |  |  |
| **BESTAND** |  |  |
| Module (.lean, verfolgt) | 191 | git ls-files '*.lean' — schliesst die Wurzeldatei Reformulation.lean ein |
| Saetze gesamt | 967 | geweitete grep-Satzroute ueber Reformulation/ allein (CLAUDE.md §3) |
| Saetze, verschaerfte Route | 967 | Gegenprobe: nach dem Namen muss ( { [ ⦃ : oder Zeilenende folgen |
| def-Deklarationen | 404 | geweitete def-Route ueber Reformulation/ |
| Statement-Pins | 107 | grep '^-- STATEMENT-PIN' (Prosa-Kriterien sind eine Zeitbombe, §3) |
|  |  |  |
| **WACHEN** |  |  |
| Wachen geschrieben | 689 | grep '#guard_msgs.*in #print axioms' ueber Reformulation/ UND Foreign/ |
| davon Dateien | 96 | dieselbe Route, -l |
| nackte #print axioms | 11 | gedruckt ist nicht gewacht (§8 Fallstrick 16); Lint-Gruppe (D) bricht darauf |
|  |  |  |
| **IMPORT-HUELLEN** |  |  |
| Aggregat | 137 | Huelle der Wurzel Reformulation.lean |
| mitgebaut | 19 | ueber ein Default-Target erreicht, ausserhalb der Aggregathuelle |
| nur auf Ruf | 34 | nur ueber ein eigenes Target gebaut |
| kein Target | 1 | Reformulation.PathC.Classifying.Universal |
| Gate-Huelle | 138 | Huelle von Reformulation/AxiomGate.lean |
| Saetze im Aggregat | 786 | Satzroute, auf die Aggregathuelle eingeschraenkt |
| Wachen erzwungen | 679 | Wachenroute, auf die Huelle der Default-Targets eingeschraenkt |
| Wachen ausserhalb | 10 | geschrieben, aber von keinem Default-Target erfasst — sichern nichts; in: Foreign/PeresMermin.lean |
| wachenfreie Aggregat-Module | 22 | Aggregat-Module mit Saetzen und ohne jede Wache (Einheit: Modul) |
|   darin Saetze | 66 | nachrichtlich; die tragende Zahl ist die Modulzahl darueber |
| Gleichung *Partition* | ✓ | 191 gegen 191 |
| Gleichung *Gate=Aggregat+1* | ✓ | 138 gegen 138 |
| Gleichung *Wachen* | ✓ | 689 gegen 689 |
| Gleichung *Satzroute* | ✓ | ok gegen ok |
|  |  |  |
| **LUECKEN (selbstzaehlend — Prosa zaehlt mit, mit Absicht)** |  |  |
| N1 roh | 162 | WORTvorkommen (\bsorry\b) ueber den verfolgten Bestand; zaehlt die eigene Dokumentation mit — eine Huelle, die seit dem Grundlinien-Zug auch ihr Messwerkzeug einschliesst; tragend ist die Zahl darunter |
|   davon .lean | 115 | dieselbe Route, auf *.lean eingeschraenkt — die TRAGENDE der beiden |
| Zeilen mit Vorkommen | 159 | ANDERE FRAGE als N1 (git grep -cw); nie als N1 lesen (§8 Fallstrick 9) |
| Code-Vorkommen | 25 | das Token im Code, Kommentare und Strings entfernt, ueber alle verfolgten .lean — NICHT selbstzaehlend |
|   in Dateien | 8 | dieselbe Route, je Datei |
| betroffene Deklarationen (N3) | 27 | je Datei mit Code-Vorkommen: lake env lean, VERSCHIEDENE Positionen der Warnung |
|   rohe Warnungen | 31 | nachrichtlich — eine Deklaration kann mehrfach melden; nie als N3 lesen |
| Gleichung *Luecken-Dateien* | ✓ | 8 gegen 8 |
|  |  |  |
| **ABLAGEN (CLAUDE.md — selbstzaehlend)** |  |  |
| Fallstricke (§8) | 20 | fett nummerierte Eintraege INNERHALB von §8 |
| Messregeln (§12) | 10 | dieselbe Route in §12 |
| fett nummeriert, ganze Datei | 30 | die naive Route — sie mischt beide Ablagen |
| Gleichung *Ablagen* | ✓ | 30 gegen 30 |
|  |  |  |
| **DEFINITION-LEDGER** |  |  |
| Ledger-Zeilen | 111 | Zeilen-IDs in docs/definition-ledger.md |
| Referenzen im Bau | 97 | jedes #ledger_*-Kommando in DefinitionLedger.lean (auch #ledger_setzung) |
|  |  |  |
| **BAU (lake build)** |  |  |
| Build-Jobs | 1339 | lake build ueber die Default-Targets |
| geprueft (AxiomGate) | 3808 | Konstanten aus dem Importbaum, namensgefiltert auf Reformulation.* |
|  |  |  |
| **DOC-LINT** |  |  |
| (A.1) laufender Bestand | 74 | Superlativ, meldend |
| (A.2) eingefrorene Fassungen | 79 | duerfen nicht geheilt werden |
| (B) ZFC-Rueckfall | 0 | meldend |
| doc_lint Exit | 0 | 0 heisst: (C), (D) und (E) ohne Verstoss |

**Was hier nicht steht.** Zahlen, die ein Satz des Korpus *behauptet*, sind keine
Kennzahlen — sie stehen in der Traegertafel des Papiers, mit dem Satz, der sie
traegt. Und Zahlen, die ausserhalb des Korpus gerechnet wurden, tragen dort den
Vermerk *gerechnet* und keine Route in diese Datei.
