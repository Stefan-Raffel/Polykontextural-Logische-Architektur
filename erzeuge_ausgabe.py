#!/usr/bin/env python3
"""erzeuge_ausgabe.py — die Papierausgabe aus den beiden Entwuerfen einer Sprache.

    ./erzeuge_ausgabe.py de docs/de.html
    ./erzeuge_ausgabe.py en docs/en.html

Abgenommen als Erzeugungsstrecke am 6. August 2026, nachdem sie Teil A und
Teil B gegen ihre Entwuerfe in allen acht Groessen gehalten hat. Bis dahin galt
*benutzen ist nicht aufnehmen*; mit der fuenften Ausgabe stellt sie den Bestand
her und steht darum hier, neben `figures.sh` und `ausgabe_probe.sh`.

DIE FIGUREN KOMMEN JE SPRACHE AUS DER GLEICHSPRACHIGEN VORIGEN AUSGABE. Gemessen:
de und en teilen keine einzige Figur, weil die Beschriftungen als <text> IM SVG
stehen. Es ist die Art Fehler, die genau einmal passiert und dann acht Figuren
auf einmal betrifft.

Die Naht, die `ausgabe_probe.sh` ueberwacht:
  1. Entwurfs-Vorspann vor der ersten Trennlinie faellt weg
  2. ⟦Marken⟧ werden durch die Figur der GLEICHSPRACHIGEN vorigen Ausgabe
     ersetzt — das SVG eingesetzt, die BILDUNTERSCHRIFT AUS DER MARKE
  3. der Rest geht durch den Wandler
  4. Raenge nach fester Abbildung; Anker; Ziffern zu Sprungzielen
  5. Moebel — Kopf, Inhaltsverzeichnis, Fusszeile — hier, von Hand gefuehrt

Die Fusszeile traegt Ausgabe, Datum und die Verweise auf die Archive und SONST
NICHTS: die Quellenangaben stehen im Fliesstext am Ende von Teil A, und zweimal
dieselbe Auskunft hiesse, dass die zweite von keiner Probe gesehen wird.
"""
import re, sys, os
import mistune

REPO = os.path.dirname(os.path.abspath(__file__))
K = os.path.join(os.path.dirname(REPO), 'KorpusRev2')

SPRACHEN = {
    'de': dict(
        titel='Die mathematische Gestalt der Architektur',
        untertitel='Polykontexturale Logik in Lean 4 und Mathlib — Fassung PKL Rev5, in zwei Teilen',
        datum='6. August 2026',
        teile=[f'{K}/Entwurf_2026-08-05_Rev4_TeilA_Gestalt_de.md',
               f'{K}/Entwurf_2026-08-05_Rev4_TeilB_Apparat_de.md'],
        quelle_figuren=f'{REPO}/docs/rev4/de.html',
        inhalt='Inhalt', teilA='Teil A · Die Gestalt', teilB='Teil B · Der Apparat',
        andere='en.html', andere_wort='English version', uebersicht='Übersicht',
        archiv='Fassung Rev', caption='Bildunterschrift',
        kennzahlen='Kennzahlen des Prüfapparats',
        stand='Kennzahlen des Prüfapparats: <a href="kennzahlen.md">kennzahlen.md</a>, mit Stand-Anker',
        lang='de',
    ),
    'en': dict(
        titel='The Mathematical Shape of the Architecture',
        untertitel='Polycontextural logic in Lean 4 and Mathlib — Edition PKL Rev5, in two parts',
        datum='6 August 2026',
        teile=[f'{K}/Entwurf_2026-08-05_Rev4_TeilA_Shape_en.md',
               f'{K}/Entwurf_2026-08-05_Rev4_TeilB_Apparatus_en.md'],
        quelle_figuren=f'{REPO}/docs/rev4/en.html',
        inhalt='Contents', teilA='Part A · The Shape', teilB='Part B · The Apparatus',
        andere='de.html', andere_wort='Deutsche Fassung', uebersicht='Overview',
        archiv='Edition Rev', caption='Caption',
        kennzahlen='Figures of the checking apparatus',
        stand='Figures of the checking apparatus: <a href="kennzahlen.md">kennzahlen.md</a>, with a state anchor',
        lang='en',
    ),
}


def figuren_aus(pfad):
    s = open(pfad, encoding='utf-8').read()
    return re.findall(r'(?is)<figure class="fig.*?</figure>', s)


# --- Formeln -----------------------------------------------------------------
# Die Entwuerfe fuehren seit Rev5 Anzeigeformeln in LaTeX ($$…$$). Der Bestand
# hat KEINEN Formelsetzer, und die vierte Ausgabe hatte keine Formel: sie schrieb
# `2^C(m,2)` als Code-Spanne im Fliesstext. Roh durchgereicht steht die
# LaTeX-Quelle sichtbar auf der Seite — gemeldet nach der fuenften Ausgabe, und
# von keiner Groesse gefangen.
#
# Darum: die Formel wird in den Zeichenvorrat uebersetzt, den das Papier ohnehin
# fuehrt (∧ ∨ ¬ stehen seit Rev4 darin), UND die LaTeX-Quelle bleibt im Artefakt,
# als data-tex. Damit ist der Vergleich Entwurf gegen Ausgabe exakt: die neunte
# Groesse haelt `$$…$$` gegen data-tex und sieht keine Uebersetzung, sondern die
# Quelle. Was uebersetzt wird, ist die DARSTELLUNG; was verglichen wird, die QUELLE.
TEX_ZEICHEN = [
    (r'\\wedge', '∧'), (r'\\vee', '∨'), (r'\\lnot', '¬'), (r'\\neg', '¬'),
    (r'\\times', '×'), (r'\\le\b', '≤'), (r'\\ge\b', '≥'), (r'\\ne\b', '≠'),
    (r'\\to\b', '→'), (r'\\cdot', '·'), (r'\\emptyset', '∅'),
]


def tex_zu_text(tex):
    t = tex.strip()
    t = re.sub(r'\\binom\{([^{}]*)\}\{([^{}]*)\}', r'C(\1,\2)', t)
    t = re.sub(r'\\(bigl|bigr|Bigl|Bigr|left|right)\b', '', t)
    for muster, zeichen in TEX_ZEICHEN:
        t = re.sub(muster, zeichen, t)
    t = re.sub(r'\^\{([^{}]*)\}', r'^\1', t)
    t = re.sub(r'_\{([^{}]*)\}', r'_\1', t)
    t = re.sub(r'\s+', ' ', t)
    t = re.sub(r'([∧∨¬])\s+', lambda m: m.group(1) + ('' if m.group(1) == '¬' else ' '), t)
    t = re.sub(r'\(\s+', '(', t)
    t = re.sub(r'\s+\)', ')', t)
    return t.strip()


def formeln_setzen(text):
    """$$…$$ vor dem Wandler herausnehmen; der Wandler kennt kein LaTeX."""
    aus = []

    def d(m):
        tex = re.sub(r'\s+', ' ', m.group(1).strip())
        sicht = tex_zu_text(tex)
        aus.append(f'<p class="formel" data-tex="{tex}">{sicht}</p>')
        return f'\n\nFORMELPLATZ{len(aus) - 1}ENDE\n\n'

    text = re.sub(r'\$\$(.+?)\$\$', d, text, flags=re.S)
    return text, aus


def wandle_teil(md_text, figuren, caption_wort):
    zeilen = md_text.split('\n')
    trenn = next((i for i, z in enumerate(zeilen) if z.strip() == '---'), 0)
    kopf = [z for z in zeilen[:trenn]
            if not z.startswith('>') and 'fortlaufender ENTWURF' not in z
            and 'rolling DRAFT' not in z]
    rest = [z for z in zeilen[trenn + 1:] if z.strip() != '---']
    text = '\n'.join(kopf + rest)

    platz = []

    def marke(m):
        inhalt = re.sub(r'[ \t]*\n[ \t]*', ' ', m.group(1))
        k = re.match(r'\s*\**\s*(?:Figur|Figure|Abbildung)\s+(\d+)', inhalt)
        if not k:
            return ''
        fig = figuren[int(k.group(1)) - 1]
        u = re.search(rf'(?:{caption_wort}):\s*\**\s*(.*)$', inhalt)
        if u:
            neu = u.group(1).strip().rstrip('*').strip()
            neu = mistune.create_markdown(escape=False)(neu)
            neu = re.sub(r'(?is)^\s*<p>|</p>\s*$', '', neu).strip()
            nummer = re.search(r'(?is)<span class="fignum">(.*?)</span>', fig)
            cap = (f'<figcaption><span class="fignum">{nummer.group(1)}</span> — {neu}</figcaption>'
                   if nummer else f'<figcaption>{neu}</figcaption>')
            fig = re.sub(r'(?is)<figcaption.*?</figcaption>', lambda _: cap, fig)
        platz.append(fig)
        return f'\n\nFIGURPLATZ{len(platz) - 1}ENDE\n\n'

    text = re.sub(r'⟦(.*?)⟧', marke, text, flags=re.S)
    text, formeln = formeln_setzen(text)
    html = mistune.create_markdown(escape=False, plugins=['table'])(text)

    # Raenge: erstes h1 bleibt, jedes weitere h1 -> h2, h2 -> h3, h3 -> h4.
    for hoch, tief in ((5, 6), (4, 5), (3, 4), (2, 3)):
        html = re.sub(rf'(?is)<(/?)h{hoch}\b', rf'<\g<1>h{tief}', html)
    erstes = [True]

    def h1(m):
        if erstes[0]:
            erstes[0] = False
            return m.group(0)
        return re.sub(r'(?i)h1', 'h2', m.group(0))

    html = re.sub(r'(?is)<h1\b[^>]*>.*?</h1>', h1, html)

    # Traegertafel: Zeilen mit einer Ziffer bekommen ihren Anker.
    def zeile(m):
        inhalt = m.group(0)
        k = re.match(r'(?is)<tr[^>]*>\s*<td[^>]*>\s*\[(\d+)\]', inhalt)
        return inhalt.replace('<tr>', f'<tr id="t{k.group(1)}">', 1) if k else inhalt

    html = re.sub(r'(?is)<tr\b.*?</tr>', zeile, html)

    # Ziffern zu Sprungzielen — nicht in Tafeln, nicht in Code.
    def ziffer(m):
        return f'<a href="#t{m.group(1)}">[{m.group(1)}]</a>'

    stuecke = re.split(r'(?is)(<table\b.*?</table>|<code\b.*?</code>|<pre\b.*?</pre>)', html)
    html = ''.join(t if re.match(r'(?i)<(table|code|pre)\b', t)
                   else re.sub(r'(?<!#)\[(\d+)\](?!\()', ziffer, t)
                   for t in stuecke)

    for i, f in enumerate(platz):
        html = html.replace(f'<p>FIGURPLATZ{i}ENDE</p>', f).replace(f'FIGURPLATZ{i}ENDE', f)
    for i, f in enumerate(formeln):
        html = html.replace(f'<p>FORMELPLATZ{i}ENDE</p>', f).replace(f'FORMELPLATZ{i}ENDE', f)
    return html


def anker_setzen(html, praefix):
    """Das erste h3 eines Teils bekommt <praefix>0, jedes h2 der Reihe nach."""
    zaehler = [0]
    erstes_h3 = [True]

    def h(m):
        tag, attr = m.group(1), m.group(2) or ''
        if tag == 'h3' and erstes_h3[0]:
            erstes_h3[0] = False
            return f'<h3 id="{praefix}0"{attr}>'
        if tag == 'h2':
            zaehler[0] += 1
            return f'<h2 id="{praefix}{zaehler[0]}"{attr}>'
        return m.group(0)

    return re.sub(r'(?is)<(h2|h3)(\s[^>]*)?>', h, html)


def titel_und_kapitel(html):
    """(Titel des Teils, [Kapitelueberschriften]) fuer das Inhaltsverzeichnis."""
    t = re.search(r'(?is)<h1[^>]*>(.*?)</h1>', html)
    kap = re.findall(r'(?is)<h2[^>]*>(.*?)</h2>', html)
    ers = re.search(r'(?is)<h3[^>]*>(.*?)</h3>', html)
    return (re.sub(r'<[^>]+>', '', t.group(1)) if t else '',
            re.sub(r'<[^>]+>', '', ers.group(1)) if ers else '',
            [re.sub(r'<[^>]+>', '', k) for k in kap])


def baue(sprache):
    c = SPRACHEN[sprache]
    figs = figuren_aus(c['quelle_figuren'])
    teile = []
    for i, pfad in enumerate(c['teile']):
        h = wandle_teil(open(pfad, encoding='utf-8').read(), figs, c['caption'])
        h = anker_setzen(h, 'a' if i == 0 else 'b')
        teile.append(h)

    tocs = []
    for i, h in enumerate(teile):
        _, ers, kap = titel_und_kapitel(h)
        p = 'a' if i == 0 else 'b'
        zeilen = [f'    <li><a href="#{p}0">{ers}</a></li>']
        zeilen += [f'    <li><a href="#{p}{n}">{k}</a></li>' for n, k in enumerate(kap, 1)]
        tocs.append('\n'.join(zeilen))

    archive = ' · '.join(f'<a href="rev{n}/{sprache}.html">{c["archiv"]}{n}</a>'
                         for n in (4, 3, 2, 1))
    return f"""<!doctype html>
<html lang="{c['lang']}">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>{c['titel']} — PKL Rev5</title>
<meta name="description" content="{c['untertitel']}">
<link rel="stylesheet" href="assets/style.css">
</head>
<body>

<div class="topbar">
  <div class="topbar-inner">
    <a class="home" href="./">PKL Rev5</a>
    <div class="langswitch">
      <span aria-current="page">{sprache.upper()}</span>
      <span class="sep">·</span>
      <a href="{c['andere']}" hreflang="{'en' if sprache == 'de' else 'de'}">{'EN' if sprache == 'de' else 'DE'}</a>
      <span class="sep">·</span>
      <a href="https://github.com/Stefan-Raffel/Polykontextural-Logische-Architektur">Repository</a>
    </div>
  </div>
</div>

<main>

<header class="doctitle">
  <p class="subtitle">{c['untertitel']}</p>
  <p class="dateline">{c['datum']} · {c['stand']}</p>
</header>

<nav class="toc" aria-label="{c['inhalt']}">
  <p class="toc-title"><strong>{c['inhalt']}</strong></p>
  <p><strong>{c['teilA']}</strong></p>
  <ol>
{tocs[0]}
  </ol>
  <p><strong>{c['teilB']}</strong></p>
  <ol>
{tocs[1]}
  </ol>
</nav>

{teile[0]}

{teile[1]}

</main>

<footer class="pagefoot">
  <p>PKL Rev5 · {c['datum']}</p>
  <p><a href="./">{c['uebersicht']}</a> · <a href="{c['andere']}">{c['andere_wort']}</a> · {archive} ·
  <a href="https://github.com/Stefan-Raffel/Polykontextural-Logische-Architektur">Stefan-Raffel/Polykontextural-Logische-Architektur</a></p>
</footer>

</body>
</html>
"""


if __name__ == '__main__':
    sp = sys.argv[1]
    ziel = sys.argv[2]
    open(ziel, 'w', encoding='utf-8').write(baue(sp))
    print(f"  {ziel}: {os.path.getsize(ziel)} Bytes")
