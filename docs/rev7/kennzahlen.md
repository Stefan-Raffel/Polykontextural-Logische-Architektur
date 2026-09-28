# Kennzahlen

**Erzeugt von `kennzahlen.sh --markdown`. Nicht von Hand aendern.**

Kennzahlen des Korpus stehen als **Werte** hier und sonst nirgends.
Papier, README und Ergebnisdokumente zeigen hierher und schreiben keine Zahl ab.
Der Grund steht in `CLAUDE.md` §13: eine Zahl, die an zwei Orten steht, hat
einen Ort zu viel, und der zweite altert unbemerkt.

Stand: Commit `5e1f30e` (sauber).
Alle mitlaufenden Gleichungen halten.

| Kennzahl | Wert | Route |
|---|---:|---|
|  |  |  |
| **BESTAND** |  |  |
| Module (.lean, verfolgt) | 180 | git ls-files '*.lean' — schliesst die Wurzeldatei Reformulation.lean ein |
| Saetze gesamt | 883 | geweitete grep-Satzroute ueber Reformulation/ allein (CLAUDE.md §3) |
| Saetze, verschaerfte Route | 883 | Gegenprobe: nach dem Namen muss ( { [ ⦃ : oder Zeilenende folgen |
| def-Deklarationen | 361 | geweitete def-Route ueber Reformulation/ |
| Statement-Pins | 94 | grep '^-- STATEMENT-PIN' (Prosa-Kriterien sind eine Zeitbombe, §3) |
|  |  |  |
| **WACHEN** |  |  |
| Wachen geschrieben | 614 | grep '#guard_msgs.*in #print axioms' ueber Reformulation/ UND Foreign/ |
| davon Dateien | 85 | dieselbe Route, -l |
| nackte #print axioms | 11 | gedruckt ist nicht gewacht (§8 Fallstrick 16); Lint-Gruppe (D) bricht darauf |
|  |  |  |
| **IMPORT-HUELLEN** |  |  |
| Aggregat | 125 | Huelle der Wurzel Reformulation.lean |
| mitgebaut | 20 | ueber ein Default-Target erreicht, ausserhalb der Aggregathuelle |
| nur auf Ruf | 34 | nur ueber ein eigenes Target gebaut |
| kein Target | 1 | Reformulation.PathC.Classifying.Universal |
| Gate-Huelle | 126 | Huelle von Reformulation/AxiomGate.lean |
| Saetze im Aggregat | 699 | Satzroute, auf die Aggregathuelle eingeschraenkt |
| Wachen erzwungen | 604 | Wachenroute, auf die Huelle der Default-Targets eingeschraenkt |
| Wachen ausserhalb | 10 | geschrieben, aber von keinem Default-Target erfasst — sichern nichts |
| wachenfreie Aggregat-Module | 22 | Aggregat-Module mit Saetzen und ohne jede Wache (Einheit: Modul) |
|   darin Saetze | 66 | nachrichtlich; die tragende Zahl ist die Modulzahl darueber |
| Gleichung *Partition* | ✓ | 180 gegen 180 |
| Gleichung *Gate=Aggregat+1* | ✓ | 126 gegen 126 |
| Gleichung *Wachen* | ✓ | 614 gegen 614 |
| Gleichung *Satzroute* | ✓ | ok gegen ok |
|  |  |  |
| **LUECKEN (selbstzaehlend — Prosa zaehlt mit, mit Absicht)** |  |  |
| N1 roh | 153 | WORTvorkommen (\bsorry\b) ueber den verfolgten Bestand; zaehlt die eigene Dokumentation mit |
|   davon .lean | 110 | dieselbe Route, auf *.lean eingeschraenkt |
| Zeilen mit Vorkommen | 150 | ANDERE FRAGE als N1 (git grep -cw); nie als N1 lesen (§8 Fallstrick 9) |
|  |  |  |
| **ABLAGEN (CLAUDE.md — selbstzaehlend)** |  |  |
| Fallstricke (§8) | 19 | fett nummerierte Eintraege INNERHALB von §8 |
| Messregeln (§12) | 10 | dieselbe Route in §12 |
| fett nummeriert, ganze Datei | 29 | die naive Route — sie mischt beide Ablagen |
| Gleichung *Ablagen* | ✓ | 29 gegen 29 |
|  |  |  |
| **DEFINITION-LEDGER** |  |  |
| Ledger-Zeilen | 110 | Zeilen-IDs in docs/definition-ledger.md |
| Referenzen im Bau | 96 | jedes #ledger_*-Kommando in DefinitionLedger.lean (auch #ledger_setzung) |
|  |  |  |
| **BAU (lake build)** |  |  |
| Build-Jobs | 1320 | lake build ueber die Default-Targets |
| geprueft (AxiomGate) | 3527 | Konstanten aus dem Importbaum, namensgefiltert auf Reformulation.* |
|  |  |  |
| **DOC-LINT** |  |  |
| (A.1) laufender Bestand | 74 | Superlativ, meldend |
| (A.2) eingefrorene Fassungen | 41 | duerfen nicht geheilt werden |
| (B) ZFC-Rueckfall | 0 | meldend |
| doc_lint Exit | 0 | 0 heisst: (C), (D) und (E) ohne Verstoss |

**Was hier nicht steht.** Zahlen, die ein Satz des Korpus *behauptet*, sind keine
Kennzahlen — sie stehen in der Traegertafel des Papiers, mit dem Satz, der sie
traegt. Und Zahlen, die ausserhalb des Korpus gerechnet wurden, tragen dort den
Vermerk *gerechnet* und keine Route in diese Datei.
