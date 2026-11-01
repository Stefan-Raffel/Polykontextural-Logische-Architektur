#!/usr/bin/env python3
"""Erzeugt /philosophie, Blatt 1, je Sprache aus dem Entwurf des Mathematikers (Prompts 1.11. 10:32, 12:10).

Gedruckt wird der Text zwischen der ersten Linie und "Für die Gegenlesung", ohne die Randzeichen ⟨…⟩. Ein offenes ⟦BILD⟧ bricht
den Lauf ab; --vorprobe laesst es zu und ist nicht fuer die Auslieferung. Der Ring wird eingebettet wie die Figuren der Ausgabe.
Aufruf aus der Repo-Wurzel:  /usr/bin/python3 ./erzeuge_philosophie.py de docs/philosophie/index.html [--vorprobe]
                             /usr/bin/python3 ./erzeuge_philosophie.py en docs/philosophie/en.html [--vorprobe]
"""
import hashlib, os, re, sys

import mistune

from erzeuge_mathematik import K, REPO, gedruckt, seite, SPRACHEN

QUELLEN = {'de': ('Entwurf_2026-10-31_Philosophie_de.md', '393dd8b9', 'Günthers zweiter Kreis als Ring'),
           'en': ('Entwurf_2026-11-01_Philosophie_en.md', '34ad85f3', "Günther's second circle as a ring")}


def ring(alt):
    """Wie neue_figur in erzeuge_ausgabe.py:  ohne Kopf, Metadaten und <style>, mit eigenem Id-Praefix."""
    s = open(os.path.join(REPO, 'docs', 'abb', 'Lethe_Ring_Kreis2_3d.svg'), encoding='utf-8').read()
    s = s[s.index('<svg'):]
    s = re.sub(r'(?is)<metadata>.*?</metadata>\s*', '', s)
    s = re.sub(r'(?is)<style[^>]*>.*?</style>\s*', '', s)
    s = re.sub(r'(?is)<defs>\s*</defs>\s*', '', s)
    s = re.sub(r'\bid="([^"]+)"', r'id="ring-\1"', s)
    s = re.sub(r'(href=")#([^"]+)"', r'\1#ring-\2"', s)
    s = re.sub(r'url\(#([^)]+)\)', r'url(#ring-\1)', s)
    kopf = re.match(r'(?is)<svg\b[^>]*>', s).group(0)
    neu = re.sub(r'\s(width|height)="[^"]*"', '', kopf)
    neu = neu[:-1].rstrip() + f' role="img" aria-label="{alt}" stroke-linejoin="round" stroke-linecap="butt">'
    return neu + s[len(kopf):].strip()


def baue(sp, vorprobe=False):
    datei, md5, alt = QUELLEN[sp]
    ausgabe = SPRACHEN[sp]['ausgabe']
    roh = open(os.path.join(K, datei), encoding='utf-8').read()
    assert vorprobe or hashlib.md5(roh.encode()).hexdigest().startswith(md5), 'Entwurf geaendert'
    text = gedruckt(roh)[1].strip('\n')
    assert vorprobe or '⟦' not in text, 'offenes ⟦BILD⟧ im gedruckten Teil'
    text = re.sub(r'\s*⟦[^⟧]*⟧', '', text)
    # Die Stationen tragen je Sprache dieselbe id (Portal, Motto zeigt auf p3):  aus dem Randzeichen ⟨P n⟩.
    stationen = [(m.group(1), f'p{m.group(2)}') for m in re.finditer(r'(?m)^## (.+?) ⟨P(\d)⟩$', text)]
    assert [i for _, i in stationen] == [f'p{n}' for n in range(1, 7)], stationen
    text = re.sub(r'\s*⟨[^⟩]*⟩', '', text)

    m = re.match(r'# (.+)\n\n\*(.+)\*\n\n!\[([^\]]*)\]\(Lethe_Ring_Kreis2_3d\.svg\)\n\n\*(.+)\*\n', text)
    assert m and m.group(3) == alt, 'Kopf, Kopfzeile, Ring und Unterschrift nicht wie erwartet'
    titel, kopfzeile, unter = m.group(1), m.group(2), m.group(4)
    text = text[m.end():]
    wort, ziel = ('Umkehr', '/mathematik/') if sp == 'de' else ('reversal', '/mathematik/en.html')
    assert text.count(f'[{wort}]({ziel})') == 1
    text = text.replace(f'[{wort}]({ziel})', f'[{wort}](..{ziel}#umkehr)').replace(f'({ziel})', f'(..{ziel})')
    text = text.replace(f'(/rev11/{sp}.html', f'({ausgabe}')
    # Die Unterschrift steht ganz kursiv;  Guenthers Kursive darin aufrecht.  Im Entwurf:  Sternchen geschlossen und wieder geoeffnet.
    teile = unter.split('*')
    assert len(teile) % 2 == 1
    satz = ''.join(f'<em>{t}</em>' if i % 2 == 0 else t for i, t in enumerate(teile))
    satz = re.sub(r'</em>(\s+)(.*?)(\s+)<em>', r'\1</em>\2<em>\3', satz)
    fig = f'<figure class="fig wide ring">\n{ring(alt)}\n<figcaption>{satz}</figcaption>\n</figure>\n'
    inhalt = mistune.create_markdown(escape=False, plugins=['table'])(text)
    for kopf, sid in stationen:
        assert inhalt.count(f'<h2>{kopf}</h2>') == 1, kopf
        inhalt = inhalt.replace(f'<h2>{kopf}</h2>', f'<h2 id="{sid}">{kopf}</h2>')
    return seite(sp, titel, kopfzeile, fig + '\n' + inhalt)


if __name__ == '__main__':
    sp, ziel = sys.argv[1], sys.argv[2]
    os.makedirs(os.path.dirname(ziel), exist_ok=True)
    open(ziel, 'w', encoding='utf-8').write(baue(sp, '--vorprobe' in sys.argv))
    print(f'  {ziel}: {os.path.getsize(ziel)} Bytes')
