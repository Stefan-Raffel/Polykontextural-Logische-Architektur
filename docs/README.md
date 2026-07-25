# docs/ - die Projektseite

Statische Seite fuer GitHub Pages. Kein Generator, kein Build-Schritt, keine externen
Ressourcen (keine CDN-Skripte, keine Web-Fonts, kein Tracking) - was hier liegt, wird
unveraendert ausgeliefert.

| Datei | Inhalt |
|---|---|
| `index.html` | Landing-Seite, zweisprachig, mit dem Stand der Kennzahlen |
| `de.html` | *Die mathematische Gestalt der Architektur* - Fassung PKL Rev1, deutsch |
| `en.html` | *The Mathematical Shape of the Architecture* - edition PKL Rev1, English |
| `assets/style.css` | gemeinsames Stylesheet, hell und dunkel ueber `prefers-color-scheme` |
| `.nojekyll` | schaltet die Jekyll-Verarbeitung ab; die Dateien werden roh ausgeliefert |

## Einschalten

Repo-Settings -> Pages -> Source: *Deploy from a branch*, Branch `main`, Ordner `/docs`.
Danach liegt die Seite unter <https://stefan-raffel.github.io/PKLrev1/>.

## Konventionen

- **Die zehn Figuren sind Inline-SVG**, aus den TikZ-Bildern des Arbeitspapiers nachgebaut.
  Farben laufen ueber CSS-Variablen (`--f03` .. `--f35`, `--stroke`), damit sie im dunklen
  Modus mitgehen; darum nicht als externe Datei einbinden - `<img>` erbt die Variablen nicht.
- **Beide Sprachfassungen fuehren dieselben Figuren** mit uebersetzter Beschriftung. Wer eine
  Geometrie aendert, aendert sie in beiden Dateien.
- **Die Kennzahlen stehen an drei Stellen**: `index.html`, `de.html` §VII, `en.html` §VII -
  und zusaetzlich in der `README.md` des Repos. Ein Bau-Zug macht sie still veraltet; sie
  tragen darum ihren Commit-Stand (derzeit `e89ab47`) im Kopf und im Anhang.
- Figuren stehen in `.wide` und brechen aus der Satzbreite aus; die Regel muss im Stylesheet
  **nach** `figure.fig` stehen, sonst gewinnt deren `margin`-Kurzform und das Transform
  schiebt die Figur aus dem Fenster.
