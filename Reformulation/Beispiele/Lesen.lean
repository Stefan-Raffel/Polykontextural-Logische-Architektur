import Reformulation.Beispiele.KaehrPfalzgraf

/-!
# Reformulation.Beispiele.Lesen — die Antworten zum Ansehen

Diese Datei definiert nichts. Sie zeigt die Antworten, die `Beispiele/KaehrPfalzgraf.lean` definiert und beim Bau
mit `#guard` prüft (Custos BQ1, Bedingung 1). Öffnen im Editor, oder bauen mit `lake build Beispiele`; sie liegt
ausserhalb der Default-Ziele, damit ihre Ausgaben die Bauausgabe nicht füllen.

Eine eigene Formel: eine `#eval`-Zeile ändern, etwa `freiAntwort (p₀ ∧∧∧ N₂ p₁)`. Die Schreibweise steht im Kopf von
`Beispiele/KaehrPfalzgraf.lean` (K2). Was hier unverändert steht, ist dort mit `#guard` geprüft; eine geänderte Zeile
ist es nicht.
-/

open Reformulation.Beispiele.KaehrPfalzgraf
open Reformulation.Kaehr.Tableau (H1 K beweisbar beweisbarGedruckt)

-- B1  Kaehrs H1 (1981, S. 16)
#eval freiAntwort H1
-- B2  der Trennfall:  Kaehrs zwei offene Äste;  im Quotienten der Wert für p = 1, 2, 3
#eval freiAntwort trennfall
#eval quotAntwort trennfall
#eval [1, 2, 3].map (wertBei trennfall)
-- B3  Kaehrs K:  gedruckte Beweisbarkeit gegen die Fassung von H1
#eval (beweisbarGedruckt K, beweisbar K)
-- B4  G:  gültig unter der Designation {1, 2}, für p = 3 der Wert 2
#eval freiAntwort G
#eval quotAntwort G
#eval wertBei G 3
-- B5  die Vorlage zum Ändern
#eval freiAntwort eigene
#eval quotAntwort eigene
-- B6  ein unzulässiger Junktor
#eval freiAntwort unzulaessig
#eval quotAntwort unzulaessig
-- zwei Variablen
#eval freiAntwort zweiVariablen
