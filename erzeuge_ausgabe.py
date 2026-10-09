#!/usr/bin/env python3
"""erzeuge_ausgabe.py — die Papierausgabe aus den Entwuerfen einer Sprache (Teil A, B und C).

    ./erzeuge_ausgabe.py de docs/de.html
    ./erzeuge_ausgabe.py en docs/en.html

Abgenommen als Erzeugungsstrecke am 6. August 2026, nachdem sie Teil A und
Teil B gegen ihre Entwuerfe in allen acht Groessen gehalten hat, die
`ausgabe_probe.sh` DAMALS fuehrte; wie viele es inzwischen sind, sagt ihr Kopf, und
ihre Schlussmeldung zaehlt sie. Die Zahl steht dort und nicht hier. Bis dahin galt
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

# Die Fassungsbezeichnung steht an EINER Stelle. Bis zur siebten Ausgabe stand sie
# an vier — Titel, Kopfleiste, Fusszeile, Untertitel —, und drei davon blieben beim
# Rev6-Zug auf der sechsten stehen, ohne dass eine der neun brechenden Groessen,
# `parity`, `figures` oder `doc_lint` es meldete. Keine Probe fuehrt die
# Fassungsbezeichnung; die Heilung ist darum die Aufhebung der Mehrfachnennung und
# nicht eine zehnte Groesse.
FASSUNG = 'Rev10'

SPRACHEN = {
    'de': dict(
        titel='Die mathematische Gestalt der Architektur',
        untertitel=f'Polykontexturale Logik in Lean 4 und Mathlib — Fassung PKL {FASSUNG}, in vier Teilen',
        datum='9. Oktober 2026',
        teile=[f'{K}/Entwurf_2026-10-09_Rev10_TeilA_Gestalt_de.md',
               f'{K}/Entwurf_2026-10-09_Rev10_Bericht_de.md',
               f'{K}/Entwurf_2026-10-09_Rev10_TeilB_Apparat_de.md',
               f'{K}/Entwurf_2026-10-09_Rev10_TeilC_Grenze_de.md'],
        quelle_figuren=f'{REPO}/docs/rev9/de.html',
        abb_suffix='',
        inhalt='Inhalt', teilA='Teil A · Die Gestalt',
        teilR='Der Bericht · Was operationsfähig geworden ist', teilB='Teil B · Der Apparat',
        teilC='Teil C · Die Grenze',
        andere='en.html', andere_wort='English version', uebersicht='Übersicht',
        archiv='Fassung Rev', caption='Bildunterschrift',
        kennzahlen='Kennzahlen des Prüfapparats',
        stand='Kennzahlen des Prüfapparats: <a href="kennzahlen.md">kennzahlen.md</a>, mit Stand-Anker',
        lang='de',
    ),
    'en': dict(
        titel='The Mathematical Shape of the Architecture',
        untertitel=f'Polycontextural logic in Lean 4 and Mathlib — Edition PKL {FASSUNG}, in four parts',
        datum='9 October 2026',
        teile=[f'{K}/Entwurf_2026-10-09_Rev10_TeilA_Shape_en.md',
               f'{K}/Entwurf_2026-10-09_Rev10_Report_en.md',
               f'{K}/Entwurf_2026-10-09_Rev10_TeilB_Apparatus_en.md',
               f'{K}/Entwurf_2026-10-09_Rev10_TeilC_Limit_en.md'],
        quelle_figuren=f'{REPO}/docs/rev9/en.html',
        abb_suffix='_EN',
        inhalt='Contents', teilA='Part A · The Shape',
        teilR='The report · What has become operational', teilB='Part B · The Apparatus',
        teilC='Part C · The Limit',
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


# DIE FIGUREN DER ZEHNTEN AUSGABE, in Lesereihenfolge (die Nummer ist die Stelle in
# dieser Liste). ('abb', Name) ist eine neue Figur aus docs/abb/, von den Skripten in
# figuren/ erzeugt; ('alt', n) ist Figur n der vorigen Ausgabe derselben Sprache. Die
# Nummer, die die Seite zeigt, kommt aus der MARKE des Entwurfs und nicht aus der
# Quellfigur: bis Rev8 wurde die Nummer der Quellfigur uebernommen, und das ging nur,
# solange keine Figur vor eine bestehende trat.
# Seit der zehnten Ausgabe kommen die elf Figuren der neunten aus docs/rev9/ (dort 1-11, schon mit
# ihren Praefixen); neu ist Figur 12 im Bericht (O7).
FIGUREN = [('alt', n) for n in range(1, 12)] + [('abb', 'Abb_Sechseck_Halbe_Drehung')]

# Die Alt-Texte der neuen Figuren, wortgleich aus der Uebergabe des Verfassers (§2).
ALT = {
    ('Abb_Achse_Zwei_Konstruktionen', 'de'): 'Links eine Treppe aus Blöcken, eine Reihe je Designationstyp mit 1 bis 4 Blöcken, daneben die Summen 1, 3, 6, 10. Rechts vollständige Graphen mit 3, 4 und 5 Punkten und 3, 6, 10 Paaren. Darunter die Identität und die zwei Folgen nebeneinander; die Folge der Verbundkontexturen beginnt erst bei 3.',
    ('Abb_Achse_Zwei_Konstruktionen', 'en'): 'Left, a staircase of blocks, one row per designation type with 1 to 4 blocks, with the sums 1, 3, 6, 10. Right, complete graphs on 3, 4 and 5 points with 3, 6, 10 pairs. Below, the identity and the two sequences side by side; the sequence of compound contextures starts only at 3.',
    ('Abb_Sechseck_Drei_Werte', 'de'): 'Ein Sechseck, oben die Anordnung 1 2 3, unten 3 2 1. Die Kanten wechseln zwischen zwei Farben für N₁ und N₂. Pfeile laufen rechts herum über 2 1 3 und 3 1 2 und links herum über 1 3 2 und 2 3 1 nach unten. Rechts Günthers Notation: ein N mit hochgestelltem 2.1.2 und tiefgestelltem 1.2.1, dahinter p, darunter die Spalte 3, 2, 1.',
    ('Abb_Sechseck_Drei_Werte', 'en'): 'A hexagon, the arrangement 1 2 3 at the top, 3 2 1 at the bottom. The edges alternate between two colours for N₁ and N₂. Arrows run down the right side via 2 1 3 and 3 1 2 and down the left via 1 3 2 and 2 3 1. On the right, Günther\'s notation: an N with 2.1.2 as superscript and 1.2.1 as subscript, followed by p, above the column 3, 2, 1.',
    ('Abb_Negationssystem_Oktaeder', 'de'): 'Links ein abgestumpftes Oktaeder aus Quadraten und Sechsecken, die Kanten in drei Farben für N₁, N₂, N₃, der Ausgang p markiert. Rechts dasselbe Netz flach ausgebreitet, darauf ein geschlossener Weg über alle 24 Ecken; die letzten zwei Schritte gestrichelt.',
    ('Abb_Sechseck_Halbe_Drehung', 'de'): 'Ein Sechseck, oben die Anordnung 1 2 3, im Uhrzeigersinn 2 1 3, 3 1 2, 3 2 1, 2 3 1, 1 3 2. Die Kanten wechseln zwischen zwei Farben für N₁ und N₂. Drei gestrichelte Durchmesser verbinden jede Station mit der gegenüberliegenden: dem Bild unter dem Tausch der Werte 1 und 3.',
    ('Abb_Sechseck_Halbe_Drehung', 'en'): 'A hexagon, the arrangement 1 2 3 at the top, clockwise 2 1 3, 3 1 2, 3 2 1, 2 3 1, 1 3 2. The edges alternate between two colours for N₁ and N₂. Three dashed diameters join each station to the opposite one: its image under the exchange of the values 1 and 3.',
    ('Abb_Negationssystem_Oktaeder', 'en'): 'Left, a truncated octahedron of squares and hexagons, the edges in three colours for N₁, N₂, N₃, the starting point p marked. Right, the same network laid out flat, with a closed path through all 24 vertices; the last two steps dashed.',
}


def neue_figur(name, sprache, suffix):
    """Eine Matplotlib-SVG aus docs/abb/ als Figur der Seite. Die Datei ist ein
    eigenes Dokument; eingebettet waere dreierlei falsch: (1) der Kopf (XML-
    Deklaration, DOCTYPE, Metadaten mit Zeitstempel), (2) der <style>-Block mit dem
    Selektor `*` — er traefe die ganze Seite —, (3) die IDs `figure_1`, `axes_1` …,
    die in JEDER solchen Datei gleich lauten und auf einer Seite doppelt staenden.
    Die zwei Strichregeln des Blocks gehen als erbende Attribute an die Wurzel; die
    IDs bekommen ein Praefix je Figur, mitsamt allen Verweisen darauf."""
    s = open(os.path.join(REPO, 'docs', 'abb', name + suffix + '.svg'), encoding='utf-8').read()
    s = s[s.index('<svg'):]
    s = re.sub(r'(?is)<metadata>.*?</metadata>\s*', '', s)
    s = re.sub(r'(?is)<style[^>]*>.*?</style>\s*', '', s)
    s = re.sub(r'(?is)<defs>\s*</defs>\s*', '', s)
    # Praefix aus dem ganzen Namen: 'sechseck-' allein waere seit Figur 12 doppelt vergeben.
    px = name[4:].lower().replace('_', '-') + '-'
    s = re.sub(r'\bid="([^"]+)"', lambda m: f'id="{px}{m.group(1)}"', s)
    s = re.sub(r'(href=")#([^"]+)"', lambda m: f'{m.group(1)}#{px}{m.group(2)}"', s)
    s = re.sub(r'url\(#([^)]+)\)', lambda m: f'url(#{px}{m.group(1)})', s)
    kopf = re.match(r'(?is)<svg\b[^>]*>', s).group(0)
    neu = re.sub(r'\s(width|height)="[^"]*"', '', kopf)
    neu = neu.replace('xmlns:c2pa="http://c2pa.org/manifest"', '')
    alt = ALT[(name, sprache)].replace('"', '&quot;')
    neu = neu[:-1].rstrip() + (f' role="img" aria-label="{alt}"'
                               ' stroke-linejoin="round" stroke-linecap="butt">')
    s = neu + s[len(kopf):]
    return (f'<figure class="fig wide">\n<div class="fig-scroll">\n{s.strip()}\n</div>\n'
            f'<figcaption></figcaption>\n</figure>')


def figuren_der_ausgabe(c, sprache):
    alt = figuren_aus(c['quelle_figuren'])
    return [neue_figur(q, sprache, c['abb_suffix']) if art == 'abb' else alt[q - 1]
            for art, q in FIGUREN]


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
            # BIS REV5 STAND HIER `return ''` — und das war eine stille Loeschung.
            # Gemessen an der fuenften Ausgabe: der Entwurf zu Teil A trug eine
            # offene Klaerungs-Marke, und der Absatz in Teil B, der das
            # Markenzeichen ERKLAERT, trug es als Beispiel. Beide verschwanden;
            # der Erklaerungsabsatz stand danach in BEIDEN Sprachfassungen ohne
            # Satzgegenstand („Marken. bezeichnete in den frueheren Fassungen").
            # Keine der neun Groessen sah es, weil die Probe die Marken auf der
            # Entwurfsseite ebenso entfernt — sie spiegelt diese Route, statt sie
            # zu pruefen. Eine begruendete Ausnahme auf beiden Seiten ist kein
            # Vergleich mehr.
            raise SystemExit(
                'FEHLER: Marke ohne Figur-Kopf — die Strecke loescht nicht mehr '
                'stillschweigend.\n         ⟦' + inhalt[:120] + '⟧\n'
                '         Entweder als Figur schreiben, oder aus dem Entwurf '
                'nehmen; ein Klaerungsvermerk gehoert nicht in die Ausgabe.')
        fig = figuren[int(k.group(1)) - 1]
        u = re.search(rf'(?:{caption_wort}):\s*\**\s*(.*)$', inhalt)
        if u:
            neu = u.group(1).strip().rstrip('*').strip()
            neu = mistune.create_markdown(escape=False)(neu)
            neu = re.sub(r'(?is)^\s*<p>|</p>\s*$', '', neu).strip()
            wort = 'Figure' if caption_wort == 'Caption' else 'Figur'
            cap = f'<figcaption><span class="fignum">{wort} {k.group(1)}</span> — {neu}</figcaption>'
            fig = re.sub(r'(?is)<figcaption.*?</figcaption>', lambda _: cap, fig)
        platz.append(fig)
        return f'\n\nFIGURPLATZ{len(platz) - 1}ENDE\n\n'

    text = re.sub(r'⟦(.*?)⟧', marke, text, flags=re.S)
    text, formeln = formeln_setzen(text)
    html = mistune.create_markdown(escape=False, plugins=['table'])(text)
    # Ausdruecklicher Anker an einer Ueberschrift: `## Titel {#id}` (seit dem C.3-Folgezug, 27.9.;
    # erster Fall #buridan). [^<]* statt .*?: der Anker darf keine Tag-Grenze ueberspringen -
    # der erste Probelauf mit .*? setzte die id auf eine fruehere Ueberschrift und verlor #a0.
    html = re.sub(r'(?i)<(h[1-6])>([^<]*?)\s*\{#([A-Za-z][\w-]*)\}\s*</\1>', r'<\1 id="\3">\2</\1>', html)

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
        if 'id=' in attr:          # ausdruecklicher Anker {#id}: nicht ueberschreiben, nicht zaehlen
            return m.group(0)
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
    figs = figuren_der_ausgabe(c, sprache)
    praefixe = 'aobc'    # Teil A, der Bericht (O0 = o0, O1 ... O7 = o1 ... o7), Teil B, Teil C
    teile = []
    for i, pfad in enumerate(c['teile']):
        h = wandle_teil(open(pfad, encoding='utf-8').read(), figs, c['caption'])
        h = anker_setzen(h, praefixe[i])
        teile.append(h)

    tocs = []
    for i, h in enumerate(teile):
        _, ers, kap = titel_und_kapitel(h)
        p = praefixe[i]
        zeilen = [f'    <li><a href="#{p}0">{ers}</a></li>']
        zeilen += [f'    <li><a href="#{p}{n}">{k}</a></li>' for n, k in enumerate(kap, 1)]
        tocs.append('\n'.join(zeilen))

    archive = ' · '.join(f'<a href="rev{n}/{sprache}.html">{c["archiv"]}{n}</a>'
                         for n in (9, 8, 7, 6, 5, 4, 3, 2, 1))
    return f"""<!doctype html>
<html lang="{c['lang']}">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>{c['titel']} — PKL {FASSUNG}</title>
<meta name="description" content="{c['untertitel']}">
<link rel="stylesheet" href="assets/style.css">
</head>
<body>

<div class="topbar">
  <div class="topbar-inner">
    <a class="home" href="./">PKL {FASSUNG}</a>
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
  <p><strong>{c['teilR']}</strong></p>
  <ol>
{tocs[1]}
  </ol>
  <p><strong>{c['teilB']}</strong></p>
  <ol>
{tocs[2]}
  </ol>
  <p><strong>{c['teilC']}</strong></p>
  <ol>
{tocs[3]}
  </ol>
</nav>

{teile[0]}

{teile[1]}

{teile[2]}

{teile[3]}

</main>

<footer class="pagefoot">
  <p>PKL {FASSUNG} · {c['datum']}</p>
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
