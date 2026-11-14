#!/usr/bin/env python3
"""Erzeugt die Blaetter der Hinfuehrung, die nach Blatt 1 kamen, je Sprache aus dem Entwurf (Prompt Mathematiker 14.11. 16:43):
/physik, /philosophie/axiome (Blatt 2, Goedel und Guenther) und dessen Anhaenge A und B.

Gedruckt wird alles unter der ersten Linie "---" des Entwurfs; der Kopf darueber (Stand, Vorlage, OFFEN ...) nicht. Der Wortlaut wird
nicht angefasst: kein Zeichen, keine Anfuehrung, keine Kursive.  Was der Generator am Satz tut, steht hier und sonst nirgends:
  - die erste Zeile "# ..." wird Titel, eine oder zwei ganz kursive Zeilen danach Untertitel und Kopfzeile;
  - Verweise auf die Wurzel (/rev11/..., /physik/, /philosophie/axiome, /mathematik/, anhang-a, anhang-b) werden relativ, und
    jede Sprache bleibt in ihrer Sprache (englisch -> en.html);
  - nummerierte Zeilen in Zitaten ("> 1. ...") bleiben Text (Signum S2:  die Zahlen gehoeren zum Wortlaut, kein <ol>);
  - Guenthers zwei Tafeln in Anhang A (Codebloecke im Entwurf, "Arbeitsform") werden Tafeln nach Signum S2 und dem Kopf des
    Entwurfs; "Tafel I" mittig darueber kommt aus diesen Vorgaben, nicht aus dem gedruckten Teil;
  - in der Formeltafel von Anhang A stehen die Variablen kursiv (Signum S2);
  - die Marke ⟪FIGUR ...⟫ im Goedel-Blatt wird Tafel III, mit den zwei folgenden Absaetzen als Bildunterschrift.
Ein geaenderter Entwurf bricht den Lauf (md5).
Aufruf aus der Repo-Wurzel:  /usr/bin/python3 ./erzeuge_blaetter.py            (alle acht Seiten)
"""
import hashlib, html, os, re, sys

import mistune

from erzeuge_mathematik import K, REPO, GITHUB, stil_kennung

# Name: (Quelle, md5, Ziel unter docs/, Tiefe unter docs/)
SEITEN = {
    ('physik', 'de'): ('Entwurf_2026-11-14_Physik_de_Janus_Fassung24.md', 'b4c77cc0', 'physik/index.html'),
    ('physik', 'en'): ('Entwurf_2026-11-14_Physik_en_Fassung3.md', '9d54b5e0', 'physik/en.html'),
    ('axiome', 'de'): ('Entwurf_2026-11-14_Goedel_Guenther_de_Fassung10.md', '70d1f1cd', 'philosophie/axiome/index.html'),
    ('axiome', 'en'): ('Entwurf_2026-11-14_Goedel_Guenther_en_Fassung2.md', 'ac2f0b62', 'philosophie/axiome/en.html'),
    # Dateinamen mit dem ALTEN Buchstaben (E62):  massgeblich ist der Titel in der Datei, geprueft unten.
    ('anhang-a', 'de'): ('Entwurf_2026-11-14_Goedel_Guenther_AnhangB_de_Fassung9.md', '3633f04a', 'philosophie/axiome/anhang-a/index.html'),
    ('anhang-a', 'en'): ('Entwurf_2026-11-14_Goedel_Guenther_AnhangA_Sein_en_Fassung3.md', 'ddc86058', 'philosophie/axiome/anhang-a/en.html'),
    ('anhang-b', 'de'): ('Entwurf_2026-11-14_Goedel_Guenther_AnhangA_de_Fassung7.md', '78fb5735', 'philosophie/axiome/anhang-b/index.html'),
    ('anhang-b', 'en'): ('Entwurf_2026-11-14_Goedel_Guenther_AnhangB_Maschinen_en_Fassung2.md', '175106c7', 'philosophie/axiome/anhang-b/en.html'),
}
TITELANFANG = {('anhang-a', 'de'): 'Anhang A · ', ('anhang-a', 'en'): 'Appendix A · ',
               ('anhang-b', 'de'): 'Anhang B · ', ('anhang-b', 'en'): 'Appendix B · '}
TAFEL3 = ('Figur_Tafel_III_IZM_S248_Signum.svg', '5b8ef0c1')
WORT = {'de': dict(ausgabe='Ausgabe Rev11', uebersicht='Übersicht'), 'en': dict(ausgabe='Edition Rev11', uebersicht='Overview')}


def md5_pruefen(pfad, kurz):
    roh = open(pfad, 'rb').read()
    assert hashlib.md5(roh).hexdigest().startswith(kurz), f'{os.path.basename(pfad)}:  md5 weicht ab (Soll {kurz})'
    return roh.decode('utf-8')


def ziel_von(name, sp):
    return SEITEN[(name, sp)][2]


def wurzel(ziel):
    return '../' * ziel.count('/')


def verweis(url, sp, ziel):
    """Ein Verweis des Entwurfs, relativ zur Seite.  Jede Sprache bleibt in ihrer."""
    w = wurzel(ziel)
    m = re.fullmatch(r'/rev11/(de|en)\.html(#[\w-]+)?', url)
    if m:
        assert m.group(1) == sp, f'{url} auf einer Seite der Sprache {sp}'
        return f'{w}rev11/{sp}.html{m.group(2) or ""}'
    m = re.fullmatch(r'/(physik|philosophie/axiome|mathematik)/?(en\.html)?(#[\w-]+)?', url)
    if m:
        assert (m.group(2) is not None) == (sp == 'en'), f'{url} auf einer Seite der Sprache {sp}'
        return f'{w}{m.group(1)}/{"en.html" if sp == "en" else ""}{m.group(3) or ""}'
    if url in ('anhang-a', 'anhang-b'):
        assert ziel.startswith('philosophie/axiome/') and ziel.count('/') == 2, (url, ziel)
        return f'{url}/{"en.html" if sp == "en" else ""}'
    raise AssertionError(f'unbekanntes Linkziel {url!r}')


def tafel_1957(zeilen):
    """Guenthers Tafel 1957 (Signum S2, 2):  Ueberschrift ueber beiden Spalten, Koepfe kursiv, eine Linie ueber dem Kopf, eine unter
    der Tafel, keine senkrechte;  jede Zeile endet mit Punkt wie im Entwurf."""
    z = [l for l in zeilen if l.strip()]
    titel = z[0].strip()
    kopf = re.split(r'\s{2,}', z[1].strip())
    reihen = [re.split(r'\s{2,}', l.strip()) for l in z[2:]]
    assert len(kopf) == 2 and all(len(r) == 2 for r in reihen) and len(reihen) == 4, (kopf, reihen)
    t = ['<div class="tablewrap"><table class="tafel tafel-1957">',
         f'<thead><tr class="titel"><th colspan="2"><em>{titel}</em></th></tr>',
         f'<tr class="kopf"><th><em>{kopf[0]}</em></th><th><em>{kopf[1]}</em></th></tr></thead>', '<tbody>']
    t += [f'<tr><td>{a}</td><td>{b}</td></tr>' for a, b in reihen]
    t += ['</tbody></table></div>']
    return '\n'.join(t)


def tafel_i(zeilen):
    """Tafel I 1978 (Signum S2, 3):  "Tafel I" mittig darueber, Linie unter dem Kopf, senkrechte Linie zwischen den Spalten, kein
    Rahmen, zentriert."""
    z = [re.split(r'\s{2,}', l.strip()) for l in zeilen if l.strip()]
    assert len(z) == 3 and all(len(r) == 2 for r in z), z
    t = ['<div class="tablewrap"><table class="tafel tafel-i">', '<caption>Tafel I</caption>',
         f'<thead><tr><th>{z[0][0]}</th><th>{z[0][1]}</th></tr></thead>', '<tbody>']
    t += [f'<tr><td>{a}</td><td>{b}</td></tr>' for a, b in z[1:]]
    t += ['</tbody></table></div>']
    return '\n'.join(t)


def tafel_iii(alt_bleibt=True):
    s = md5_pruefen(os.path.join(K, TAFEL3[0]), TAFEL3[1])
    s = s[s.index('<svg'):].strip()
    assert ' id=' not in s, 'Tafel III traegt ids — dann Praefix setzen'
    return s


def zitatnummern(text):
    """'> 1. ...' bleibt Text:  die Ziffer wird maskiert;  folgt eine weitere nummerierte Zeile, bricht die Zeile hart um."""
    z = text.split('\n')
    nr = [bool(re.match(r'> \d+\. ', l)) for l in z]
    for i, l in enumerate(z):
        if nr[i]:
            l = re.sub(r'^> (\d+)\. ', r'> \1\\. ', l)
            if i + 1 < len(z) and nr[i + 1]:
                l += '  '
            z[i] = l
    return '\n'.join(z), sum(nr)


def inline(md, s):
    h = md(s).strip()
    assert h.startswith('<p>') and h.endswith('</p>') and h.count('<p>') == 1, h
    return h[3:-4]


def seite(sp, ziel, titel, untertitel, kopfzeile, inhalt, fuss_vorn=''):
    w = wurzel(ziel)
    schwester = 'en.html' if sp == 'de' else './'
    de = '<span aria-current="page">DE</span>' if sp == 'de' else f'<a href="{schwester}" hreflang="de">DE</a>'
    en = '<span aria-current="page">EN</span>' if sp == 'en' else f'<a href="{schwester}" hreflang="en">EN</a>'
    ausgabe = f'{w}rev11/{sp}.html'
    kopf = [f'  <h1>{titel}</h1>']
    if untertitel:
        kopf.append(f'  <p class="subtitle">{untertitel}</p>')
    if kopfzeile:
        kopf.append(f'  <p class="dateline">{kopfzeile}</p>')
    kopf = '\n'.join(kopf)
    return f"""<!doctype html>
<html lang="{sp}">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>{re.sub(r'<[^>]+>', '', titel)}</title>
<meta name="description" content="{re.sub(r'<[^>]+>', '', untertitel or titel)}">
<link rel="stylesheet" href="{w}assets/style.css?v={stil_kennung()}">
</head>
<body>

<div class="topbar">
  <div class="topbar-inner">
    <a class="home" href="{w}">PKL Rev11</a>
    <div class="langswitch">
      {de}
      <span class="sep">·</span>
      {en}
      <span class="sep">·</span>
      <a href="{ausgabe}">{WORT[sp]['ausgabe']}</a>
      <span class="sep">·</span>
      <a href="{GITHUB}">Repository</a>
    </div>
  </div>
</div>

<main>

<header class="doctitle">
{kopf}
</header>

{inhalt}
</main>

<footer class="pagefoot">
  <p>{fuss_vorn}<a href="{w}">{WORT[sp]['uebersicht']}</a> · <a href="{ausgabe}">{WORT[sp]['ausgabe']}</a> · <a href="{GITHUB}">Stefan-Raffel/Polykontextural-Logische-Architektur</a></p>
</footer>

</body>
</html>
"""


def baue(name, sp, bericht):
    quelle, kurz, ziel = SEITEN[(name, sp)]
    roh = md5_pruefen(os.path.join(K, quelle), kurz)
    z = roh.split('\n')
    erste = next(i for i, l in enumerate(z) if l.strip() == '---')
    text = '\n'.join(z[erste + 1:]).strip('\n') + '\n'
    md = mistune.create_markdown(escape=False, plugins=['table'])

    m = re.match(r'# (.+)\n\n(?:\*([^*\n]+)\*\n\n)?(?:\*([^*\n]+)\*\n\n)?', text)
    assert m, 'Kopf nicht wie erwartet'
    titel, untertitel, kopfzeile = m.group(1), m.group(2), m.group(3)
    if (name, sp) in TITELANFANG:
        assert titel.startswith(TITELANFANG[(name, sp)]) and not untertitel, (titel, untertitel)
    else:
        assert untertitel and kopfzeile, 'Blatt ohne Untertitel oder Kopfzeile'
    text = text[m.end():]
    assert '⟦' not in text and '⟨' not in text, 'Randzeichen im gedruckten Teil'

    # Tafeln aus Codebloecken (nur Anhang A)
    platz = {}
    def codeblock(q):
        zeilen = q.group(1).split('\n')
        key = f'TAFELPLATZ{len(platz)}'
        platz[key] = tafel_1957(zeilen) if len([l for l in zeilen if l.strip()]) == 6 else tafel_i(zeilen)
        return key
    text = re.sub(r'(?m)^```text\n(.*?)\n```$', codeblock, text, flags=re.S)
    assert name == 'anhang-a' and len(platz) == 2 or name != 'anhang-a' and not platz, (name, len(platz))

    # Figur Tafel III (nur Goedel-Blatt):  die Marke und die zwei folgenden Absaetze
    if name == 'axiome':
        fm = re.search(r'(?m)^⟪FIGUR: Figur_Tafel_III_IZM_S248_Signum\.svg[^⟫]*⟫\n\n(.+)\n\n(.+)\n', text)
        assert fm, 'Figurmarke nicht wie erwartet'
        cap = f'<figcaption><blockquote><p>{inline(md, fm.group(1))}</p></blockquote><p>{inline(md, fm.group(2))}</p></figcaption>'
        platz['FIGURPLATZ'] = f'<figure class="fig tafel" id="tafel-iii">\n{tafel_iii()}\n{cap}\n</figure>'
        text = text[:fm.start()] + 'FIGURPLATZ\n' + text[fm.end():]
    assert '⟪' not in text

    text, n_nr = zitatnummern(text)

    # Verweise
    links = []
    def link(q):
        neu = verweis(q.group(2), sp, ziel)
        links.append((q.group(2), neu))
        return f'[{q.group(1)}]({neu})'
    text = re.sub(r'\[(\[\d+\]|[^\[\]]+)\]\(([^)\s]+)\)', link, text)

    inhalt = md(text)
    for key, h in platz.items():
        assert inhalt.count(f'<p>{key}</p>') == 1, key
        inhalt = inhalt.replace(f'<p>{key}</p>', h)
    if name == 'anhang-a':   # Formeltafel:  Variablen kursiv (Signum S2)
        for alt, neu in (('∀x (x = x)', '∀<em>x</em> (<em>x</em> = <em>x</em>)'), ('¬(p ∧ ¬p)', '¬(<em>p</em> ∧ ¬<em>p</em>)'),
                         ('<td>p ∨ ¬p</td>', '<td><em>p</em> ∨ ¬<em>p</em></td>')):
            assert inhalt.count(alt) == 1, alt
            inhalt = inhalt.replace(alt, neu)
    inhalt = re.sub(r'(?is)(?<!<div class="tablewrap">)(<table>.*?</table>)', r'<div class="tablewrap">\1</div>', inhalt)
    if name == 'anhang-a':   # die Formeltafel:  zwei kurze Spalten, ohne die Mindestbreite der Tafeln der Ausgabe
        assert inhalt.count('<div class="tablewrap"><table>') == 1
        inhalt = inhalt.replace('<div class="tablewrap"><table>', '<div class="tablewrap"><table class="formeln">')

    fuss_vorn = ''
    if name.startswith('anhang'):
        blatt = SEITEN[('axiome', sp)]
        btitel = re.search(r'(?m)^# (.+)$', md5_pruefen(os.path.join(K, blatt[0]), blatt[1]).split('\n---\n', 1)[1]).group(1)
        fuss_vorn = f'<a href="../{"en.html" if sp == "en" else ""}">{btitel}</a> · '
    bericht.append((ziel, quelle, len(links), n_nr, len(platz)))
    return ziel, seite(sp, ziel, titel, untertitel, kopfzeile, inhalt, fuss_vorn)


if __name__ == '__main__':
    bericht = []
    for (name, sp) in SEITEN:
        ziel, s = baue(name, sp, bericht)
        pfad = os.path.join(REPO, 'docs', ziel)
        os.makedirs(os.path.dirname(pfad), exist_ok=True)
        open(pfad, 'w', encoding='utf-8').write(s)
        print(f'  docs/{ziel}: {os.path.getsize(pfad)} Bytes')
    for ziel, quelle, nl, nn, np_ in bericht:
        print(f'  {ziel:45} {nl:3} Verweise, {nn} nummerierte Zitatzeilen, {np_} Einsetzungen  <- {quelle}')
