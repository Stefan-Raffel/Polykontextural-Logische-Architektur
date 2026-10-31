#!/usr/bin/env python3
"""Erzeugt docs/mathematik/index.html aus Entwurf_2026-10-31_Mathematik_de.md (Janus; abgenommen Signum 31.10.).

Gedruckt wird nur der Text zwischen der ersten Linie und der Linie vor "Für die Gegenlesung"; die Raender und Zeilen in
⟨…⟩ nicht. AUSGABE ist die feste Adresse ../rev11/de.html, nie die laufende de.html: Mit dem ersten Rev12-Commit zeigte die
auf einen anderen Text. Figur 4 kommt samt Unterschrift unveraendert aus docs/rev11/de.html.
Aufruf aus der Repo-Wurzel, wie erzeuge_ausgabe.py:  /usr/bin/python3 ./erzeuge_mathematik.py docs/mathematik/index.html
"""
import hashlib, html, os, re, sys

import mistune

REPO = os.path.dirname(os.path.abspath(__file__))
K = os.path.join(os.path.dirname(REPO), 'KorpusRev2')
QUELLE = os.path.join(K, 'Entwurf_2026-10-31_Mathematik_de.md')
MD5 = '25b3c62a'
AUSGABE = '../rev11/de.html'
GITHUB = 'https://github.com/Stefan-Raffel/Polykontextural-Logische-Architektur'


def figur4():
    s = open(os.path.join(REPO, 'docs', 'rev11', 'de.html'), encoding='utf-8').read()
    return re.findall(r'(?is)<figure class="fig.*?</figure>', s)[3]


def baue():
    roh = open(QUELLE, encoding='utf-8').read()
    assert hashlib.md5(roh.encode()).hexdigest().startswith(MD5), 'Entwurf geaendert'
    z = roh.split('\n')
    titel = z[0].lstrip('# ').strip()
    linien = [i for i, l in enumerate(z) if l.strip() == '---']
    gegen = z.index('## Für die Gegenlesung (nicht gedruckt)')
    ende = max(i for i in linien if i < gegen)
    text = '\n'.join(z[linien[0] + 1:ende])
    text = re.sub(r'(?m)^⟨Rand:.*⟩\s*$', '', text)
    text = re.sub(r'\s*⟨[^⟩]*⟩', '', text)

    # Bild und Unterschrift: eine Einheit aus der Ausgabe.  Der Entwurf muss denselben Wortlaut tragen.
    fig = figur4()
    m = re.search(r'(?m)^!\[Figur 4 der Ausgabe\]\(AUSGABE-abb/Figur4\)\n\n\*(Figur 4 — .*?)\* — \[in der Ausgabe\]\(AUSGABE#a3\)$', text)
    assert m, 'Bild und Unterschrift nicht wie erwartet'
    sicht = html.unescape(re.sub(r'<[^>]+>', '', re.search(r'(?is)<figcaption>(.*?)</figcaption>', fig).group(1)))
    assert ' '.join(sicht.split()) == ' '.join(m.group(1).split()), 'Unterschrift weicht von der Ausgabe ab'
    fig = fig.replace('</figcaption>', f' — <a href="{AUSGABE}#a3">in der Ausgabe</a></figcaption>')
    text = text.replace(m.group(0), 'FIGURPLATZ')

    text = text.replace('AUSGABE', AUSGABE)
    text = re.sub(r'(?<![\w#])\[(\d+)\](?!\()', lambda q: f'<a href="{AUSGABE}#t{q.group(1)}">[{q.group(1)}]</a>', text)

    inhalt = mistune.create_markdown(escape=False, plugins=['table'])(text)
    inhalt = inhalt.replace('<p>FIGURPLATZ</p>', fig)
    inhalt = re.sub(r'(?is)(<table\b.*?</table>)', r'<div class="tablewrap">\1</div>', inhalt)
    return f"""<!doctype html>
<html lang="de">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>{titel}</title>
<meta name="description" content="{titel}">
<link rel="stylesheet" href="../assets/style.css">
</head>
<body>

<div class="topbar">
  <div class="topbar-inner">
    <a class="home" href="../">PKL Rev11</a>
    <div class="langswitch">
      <a href="{AUSGABE}">Ausgabe Rev11</a>
      <span class="sep">·</span>
      <a href="{GITHUB}">Repository</a>
    </div>
  </div>
</div>

<main>

<header class="doctitle">
  <h1>{titel}</h1>
</header>

{inhalt}
</main>

<footer class="pagefoot">
  <p><a href="../">Übersicht</a> · <a href="{AUSGABE}">Ausgabe Rev11</a> · <a href="{GITHUB}">Stefan-Raffel/Polykontextural-Logische-Architektur</a></p>
</footer>

</body>
</html>
"""


if __name__ == '__main__':
    ziel = sys.argv[1]
    os.makedirs(os.path.dirname(ziel), exist_ok=True)
    open(ziel, 'w', encoding='utf-8').write(baue())
    print(f'  {ziel}: {os.path.getsize(ziel)} Bytes')
