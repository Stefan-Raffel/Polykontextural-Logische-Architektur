#!/usr/bin/env python3
"""Erzeugt /mathematik, Blatt 1, je Sprache aus dem Entwurf (de: Janus, abgenommen Signum 31.10.; en: Janus 1.11.).

Gedruckt wird nur der Text zwischen der ersten Linie und der Linie vor "Für die Gegenlesung"; die Raender und Zeilen in
⟨…⟩ nicht. Die Verweise zielen auf die feste Adresse ../rev11/<sprache>.html, nie auf die laufende Seite: Mit dem ersten
Rev12-Commit zeigte die auf einen anderen Text. Figur 4 kommt samt Unterschrift unveraendert aus dem Archiv derselben Sprache.
Deutsch stehen Kopfzeile, Querverweis und Tafel-Ids hier (Mathematiker 1.11. 10:32, §2), englisch im Entwurf.
Das Stylesheet traegt eine Fassungskennung, damit Seite und Stil zusammen wechseln (Mathematiker 1.11. 11:45).
Aufruf aus der Repo-Wurzel, wie erzeuge_ausgabe.py:  /usr/bin/python3 ./erzeuge_mathematik.py de docs/mathematik/index.html
                                                     /usr/bin/python3 ./erzeuge_mathematik.py en docs/mathematik/en.html
"""
import hashlib, html, os, re, sys

import mistune

REPO = os.path.dirname(os.path.abspath(__file__))
K = os.path.join(os.path.dirname(REPO), 'KorpusRev2')
GITHUB = 'https://github.com/Stefan-Raffel/Polykontextural-Logische-Architektur'
SPRACHEN = {
    'de': dict(quelle='Entwurf_2026-10-31_Mathematik_de.md', md5='25b3c62a', ausgabe='../rev11/de.html', archiv='rev11/de.html',
               ausgabe_wort='Ausgabe Rev11', uebersicht='Übersicht', schwester='en.html'),
    'en': dict(quelle='Entwurf_2026-11-01_Mathematik_en.md', md5='26327e9d', ausgabe='../rev11/en.html', archiv='rev11/en.html',
               ausgabe_wort='Edition Rev11', uebersicht='Overview', schwester='./'),
}
KOPFZEILE = 'Hinführung · Blatt 1 · Stand 1. November 2026 · zur Ausgabe Rev11 (Tag rev11, 24fa57a)'
QUERVERWEIS = 'Was Günther zu diesen Gegenständen schreibt, und wo die Ausgabe es offen lässt, steht auf der Seite [Philosophie](../philosophie/).'
# Das Wort der ersten Spalte entscheidet;  "Umkehrung" ist Günthers Wort, die Marke heisst wie die Sache.
TAFEL_IDS = (('Anordnung', 'anordnung'), ('Negator', 'negator'), ('Kreis', 'kreis'), ('Vollkreis', 'vollkreis'), ('Drehsinn', 'drehsinn'),
             ('Umkehrung', 'umkehr'), ('Elementarkontextur', 'elementarkontextur'), ('Kenogramm', 'kenogramm'))


def stil_kennung():
    return hashlib.sha256(open(os.path.join(REPO, 'docs', 'assets', 'style.css'), 'rb').read()).hexdigest()[:8]


def seite(sp, titel, kopfzeile, inhalt):
    c = SPRACHEN[sp]
    de = '<span aria-current="page">DE</span>' if sp == 'de' else f'<a href="{c["schwester"]}" hreflang="de">DE</a>'
    en = '<span aria-current="page">EN</span>' if sp == 'en' else f'<a href="{c["schwester"]}" hreflang="en">EN</a>'
    return f"""<!doctype html>
<html lang="{sp}">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>{titel}</title>
<meta name="description" content="{titel}">
<link rel="stylesheet" href="../assets/style.css?v={stil_kennung()}">
</head>
<body>

<div class="topbar">
  <div class="topbar-inner">
    <a class="home" href="../">PKL Rev11</a>
    <div class="langswitch">
      {de}
      <span class="sep">·</span>
      {en}
      <span class="sep">·</span>
      <a href="{c['ausgabe']}">{c['ausgabe_wort']}</a>
      <span class="sep">·</span>
      <a href="{GITHUB}">Repository</a>
    </div>
  </div>
</div>

<main>

<header class="doctitle">
  <h1>{titel}</h1>
  <p class="dateline">{kopfzeile}</p>
</header>

{inhalt}
</main>

<footer class="pagefoot">
  <p><a href="../">{c['uebersicht']}</a> · <a href="{c['ausgabe']}">{c['ausgabe_wort']}</a> · <a href="{GITHUB}">Stefan-Raffel/Polykontextural-Logische-Architektur</a></p>
</footer>

</body>
</html>
"""


def figur4(sp):
    s = open(os.path.join(REPO, 'docs', SPRACHEN[sp]['archiv']), encoding='utf-8').read()
    return re.findall(r'(?is)<figure class="fig.*?</figure>', s)[3]


# Der Koerper der vier Werte, bis 14.11. die Portalgrafik (Prompt Mathematiker 14.11. 16:43, F1-F3):  nach dem Absatz zu [144], ohne
# Nummer (Figur 4 der Seite ist Figur 4 der Ausgabe), mit id.  Bildzeile wortlich, abgenommen vom Architekten 14.11. 16:41.
KOERPER = {
    'de': ('Günthers zweiter Kreis auf dem abgestumpften Oktaeder, räumlich: die Ecken und Kanten von Figur 4, die Negatoren in deren '
           'Farben. Kräftig und mit Richtungszeichen der Kreis, um zwei Schritte ergänzt, als Vollkreis (<code>kreis2</code>; bewiesen '
           '{t144}); er beginnt am weißen Punkt, dem Ausgang. Sieben seiner 24 Schritte liegen auf der Rückseite.',
           'Das abgestumpfte Oktaeder: 24 Ecken, die Anordnungen von vier Werten, verbunden durch die Negatoren; darauf Günthers zweiter '
           'Kreis, um zwei Schritte ergänzt, als geschlossener Weg durch alle Ecken.'),
    'en': ("Günther's second circle on the truncated octahedron, as a solid: the vertices and edges of Figure 4, the negators in the "
           'colours of Figure 4. Bold and with direction marks, the circle extended by two steps, as a full cycle (<code>kreis2</code>; '
           'proved {t144}); it begins at the white dot, the start. Seven of its 24 steps lie on the far side.',
           "The truncated octahedron: 24 vertices, the arrangements of four values, joined by the negators; on it Günther's second "
           'circle, extended by two steps, as a closed path through all vertices.'),
}


def koerper(sp):
    """Die SVG aus docs/abb (erzeugt von figuren/Portal_Koerper_Vier_Werte_mpl.py), eingebettet wie der Ring:  eigenes Id-Praefix."""
    unter, alt = KOERPER[sp]
    s = open(os.path.join(REPO, 'docs', 'abb', 'Portal_Koerper_Vier_Werte_mpl.svg'), encoding='utf-8').read()
    s = s[s.index('<svg'):]
    s = re.sub(r'(?is)<metadata>.*?</metadata>\s*', '', s)
    s = re.sub(r'(?is)<style[^>]*>.*?</style>\s*', '', s)
    s = re.sub(r'(?is)<defs>\s*</defs>\s*', '', s)
    s = re.sub(r'\bid="([^"]+)"', r'id="koerper-\1"', s)
    s = re.sub(r'(href=")#([^"]+)"', r'\1#koerper-\2"', s)
    s = re.sub(r'url\(#([^)]+)\)', r'url(#koerper-\1)', s)
    kopf = re.match(r'(?is)<svg\b[^>]*>', s).group(0)
    neu = re.sub(r'\s(width|height)="[^"]*"', '', kopf)
    neu = neu[:-1].rstrip() + f' role="img" aria-label="{alt}" stroke-linejoin="round" stroke-linecap="butt">'
    svg = neu + s[len(kopf):].strip()
    t144 = f'<a href="{SPRACHEN[sp]["ausgabe"]}#t144">[144]</a>'
    return f'<figure class="fig koerper" id="koerper">\n{svg}\n<figcaption>{unter.format(t144=t144)}</figcaption>\n</figure>\n'


def schluss_de(text):
    """Deutsche Anfuehrung „…" -> „…“ (Entscheid Architekt 14.11. 17:05, E2):  NUR das schliessende Zeichen einer mit „ geoeffneten
    Anfuehrung;  gerade Anfuehrungen IM Zitat (innere, "…") bleiben.  Nicht in Codespannen, Codebloecken, Tafelzeilen.  Gezaehlt je
    Zeile (ein Absatz ist eine Zeile);  eine Zeile, deren „ nicht schliesst, wird gemeldet.
    Regel fuer ein gerades " innerhalb von „…:  nach Leerraum, „, (, [ oeffnet es ein inneres Zitat, das naechste " schliesst dieses;
    sonst schliesst es die deutsche Anfuehrung und wird “.  Ein “ nach einem Wortzeichen schliesst ebenfalls (schon richtig gesetzt)."""
    aus, n, offen = [], 0, []
    zaun = False
    for zeile in text.split('\n'):
        if zeile.startswith('```'):
            zaun = not zaun
        if zaun or zeile.startswith('```') or zeile.lstrip().startswith('|'):
            aus.append(zeile)
            continue
        tiefe, innen, neu = 0, False, []
        for teil in re.split(r'(`[^`]*`)', zeile):
            if teil.startswith('`'):
                neu.append(teil)
                continue
            z = list(teil)
            for i, c in enumerate(z):
                vor = z[i - 1] if i else (neu[-1][-1] if neu and neu[-1] else '')
                if c == '„':
                    tiefe += 1
                    innen = False
                elif c == '“' and tiefe and vor not in ' \t(„[':
                    tiefe -= 1
                elif c == '"' and tiefe:
                    if innen:
                        innen = False
                    elif vor in ('', ' ', '\t', '„', '(', '[', ' '):
                        innen = True
                    else:
                        z[i] = '“'
                        tiefe -= 1
                        n += 1
            neu.append(''.join(z))
        if tiefe:
            offen.append(zeile[:90])
        aus.append(''.join(neu))
    return '\n'.join(aus), n, offen


def gedruckt(roh):
    "Der Text zwischen der ersten Linie und der letzten Linie vor dem Gegenlese-Block."
    z = roh.split('\n')
    linien = [i for i, l in enumerate(z) if l.strip() == '---']
    gegen = next(i for i, l in enumerate(z) if l.startswith('## Für die Gegenlesung'))
    return z, '\n'.join(z[linien[0] + 1:max(i for i in linien if i < gegen)])


def baue(sp):
    c = SPRACHEN[sp]
    roh = open(os.path.join(K, c['quelle']), encoding='utf-8').read()
    assert hashlib.md5(roh.encode()).hexdigest().startswith(c['md5']), 'Entwurf geaendert'
    z, text = gedruckt(roh)
    text = re.sub(r'(?m)^⟨Rand:.*⟩\s*$', '', text)
    text = re.sub(r'\s*⟨[^⟩]*⟩', '', text)
    if sp == 'de':
        titel, kopfzeile = z[0].lstrip('# ').strip(), KOPFZEILE
    else:
        m = re.match(r'\s*# (.+)\n\n\*(.+)\*\n', text)
        assert m, 'Kopf und Kopfzeile nicht wie erwartet'
        titel, kopfzeile = m.group(1), m.group(2)
        text = text[m.end():]

    # Bild und Unterschrift: eine Einheit aus der Ausgabe.  Der Entwurf muss denselben Wortlaut tragen.
    fig = figur4(sp)
    m = re.search(r'(?m)^!\[[^\]]*\]\((?:AUSGABE-abb/Figur4|abb/Figur4_EN\.svg)\)\n\n\*((?:Figur|Figure) 4 — .*?)\* — \[([^\]]+)\]\((?:AUSGABE|\.\./rev11/en\.html)#a3\)$', text)
    assert m, 'Bild und Unterschrift nicht wie erwartet'
    sicht = html.unescape(re.sub(r'<[^>]+>', '', re.search(r'(?is)<figcaption>(.*?)</figcaption>', fig).group(1)))
    assert ' '.join(sicht.split()) == ' '.join(m.group(1).split()), 'Unterschrift weicht von der Ausgabe ab'
    fig = fig.replace('</figcaption>', f' — <a href="{c["ausgabe"]}#a3">{m.group(2)}</a></figcaption>')
    text = text.replace(m.group(0), 'FIGURPLATZ')
    if sp == 'de':
        text, n, offen = schluss_de(text)
        print(f'  schluss_de: {n} gesetzt, offen {offen}', file=sys.stderr)

    if sp == 'de':
        letzter = 'wo die Ausgabe selbst das Wort gebraucht, steht es als ihr Wortlaut.'
        assert text.count(letzter) == 1
        text = text.replace(letzter, letzter + ' ' + QUERVERWEIS)
        ids = dict(TAFEL_IDS)
    else:
        ids = {}
        text = re.sub(r'(?m)^\| ([^|]+?) \|(.*)\| \{#([a-z]+)\}$', lambda q: (ids.__setitem__(q.group(1).strip(), q.group(3)), f'| {q.group(1)} |{q.group(2)}|')[1], text)
    text = text.replace('AUSGABE', c['ausgabe'])
    text = re.sub(r'(?<![\w#\[])\[(\d+)\](?![\(\]])', lambda q: f'<a href="{c["ausgabe"]}#t{q.group(1)}">[{q.group(1)}]</a>', text)

    inhalt = mistune.create_markdown(escape=False, plugins=['table'])(text)
    inhalt = inhalt.replace('<p>FIGURPLATZ</p>', fig)
    gesetzt = []
    def zeile(q):
        erste = q.group(1)
        if sp == 'de':
            for wort, tid in TAFEL_IDS:
                if re.search(r'(^|[ ;,])' + wort + r'\b', erste) and not (wort == 'Kreis' and 'Hamilton' in erste):
                    gesetzt.append(tid)
                    return f'<tr id="{tid}">\n  <td>{erste}</td>'
        elif erste.strip() in ids:
            gesetzt.append(ids[erste.strip()])
            return f'<tr id="{ids[erste.strip()]}">\n  <td>{erste}</td>'
        return q.group(0)
    inhalt = re.sub(r'<tr>\n  <td>(.*?)</td>', zeile, inhalt)
    assert sorted(gesetzt) == sorted(t for _, t in TAFEL_IDS), gesetzt
    inhalt = re.sub(r'(?is)(<table\b.*?</table>)', r'<div class="tablewrap">\1</div>', inhalt)
    # Der Koerper:  unmittelbar nach dem Absatz zu [144] im Abschnitt "Vier Werte" / "Four values"
    h2 = '<h2>Vier Werte</h2>' if sp == 'de' else '<h2>Four values</h2>'
    assert inhalt.count(h2) == 1
    a = inhalt.index(h2)
    e = inhalt.find('<h2', a + 1)
    abschnitt = inhalt[a:e]
    ps = [m for m in re.finditer(r'<p>.*?</p>\n', abschnitt, re.S) if f'#t144">[144]</a>' in m.group(0)]
    assert len(ps) == 1, 'Absatz zu [144] nicht eindeutig'
    inhalt = inhalt[:a + ps[0].end()] + koerper(sp) + inhalt[a + ps[0].end():]
    return seite(sp, titel, kopfzeile, inhalt)


if __name__ == '__main__':
    sp, ziel = sys.argv[1], sys.argv[2]
    os.makedirs(os.path.dirname(ziel), exist_ok=True)
    open(ziel, 'w', encoding='utf-8').write(baue(sp))
    print(f'  {ziel}: {os.path.getsize(ziel)} Bytes')
