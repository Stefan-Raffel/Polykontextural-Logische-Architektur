#!/usr/bin/env python3
"""Erzeugt docs/philosophie/index.html aus Entwurf_2026-10-31_Philosophie_de.md (Mathematiker; Prompt 1.11. 10:32).

Gedruckt wird der Text zwischen der ersten Linie und "Für die Gegenlesung", ohne die Randzeichen ⟨…⟩. Ein offenes ⟦BILD⟧ bricht
den Lauf ab; --vorprobe laesst es zu und ist nicht fuer die Auslieferung. Der Ring wird eingebettet wie die Figuren der Ausgabe.
Aufruf aus der Repo-Wurzel:  /usr/bin/python3 ./erzeuge_philosophie.py docs/philosophie/index.html [--vorprobe]
"""
import hashlib, os, re, sys

import mistune

from erzeuge_mathematik import AUSGABE, K, REPO, seite

QUELLE = os.path.join(K, 'Entwurf_2026-10-31_Philosophie_de.md')
MD5 = '279df610'
ALT = 'Günthers zweiter Kreis als Ring'


def ring():
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
    neu = neu[:-1].rstrip() + f' role="img" aria-label="{ALT}" stroke-linejoin="round" stroke-linecap="butt">'
    return neu + s[len(kopf):].strip()


def baue(vorprobe=False):
    roh = open(QUELLE, encoding='utf-8').read()
    assert vorprobe or hashlib.md5(roh.encode()).hexdigest().startswith(MD5), 'Entwurf geaendert'
    z = roh.split('\n')
    linien = [i for i, l in enumerate(z) if l.strip() == '---']
    gegen = next(i for i, l in enumerate(z) if l.startswith('## Für die Gegenlesung'))
    ende = max(i for i in linien if i < gegen)
    text = '\n'.join(z[linien[0] + 1:ende]).strip('\n')
    assert vorprobe or '⟦' not in text, 'offenes ⟦BILD⟧ im gedruckten Teil'
    text = re.sub(r'\s*⟦[^⟧]*⟧', '', text)
    text = re.sub(r'\s*⟨[^⟩]*⟩', '', text)

    m = re.match(r'# (.+)\n\n\*(.+)\*\n\n!\[([^\]]*)\]\(Lethe_Ring_Kreis2_3d\.svg\)\n\n\*(.+)\*\n', text)
    assert m and m.group(3) == ALT, 'Kopf, Kopfzeile, Ring und Unterschrift nicht wie erwartet'
    titel, kopfzeile, unter = m.group(1), m.group(2), m.group(4)
    text = text[m.end():]
    assert text.count('[Umkehr](/mathematik/)') == 1
    text = text.replace('[Umkehr](/mathematik/)', '[Umkehr](../mathematik/#umkehr)').replace('(/mathematik/)', '(../mathematik/)')
    text = text.replace('(/rev11/de.html', f'({AUSGABE}')
    # Die Unterschrift steht ganz kursiv;  Guenthers Kursive darin aufrecht.  Im Entwurf:  Sternchen geschlossen und wieder geoeffnet.
    teile = unter.split('*')
    assert len(teile) % 2 == 1
    satz = ''.join(f'<em>{t}</em>' if i % 2 == 0 else t for i, t in enumerate(teile))
    satz = re.sub(r'</em>(\s+)(.*?)(\s+)<em>', r'\1</em>\2<em>\3', satz)
    fig = f'<figure class="fig wide">\n<div class="fig-scroll">\n{ring()}\n</div>\n<figcaption>{satz}</figcaption>\n</figure>\n'
    inhalt = mistune.create_markdown(escape=False, plugins=['table'])(text)
    return seite(titel, kopfzeile, fig + '\n' + inhalt)


if __name__ == '__main__':
    ziel = sys.argv[1]
    os.makedirs(os.path.dirname(ziel), exist_ok=True)
    open(ziel, 'w', encoding='utf-8').write(baue('--vorprobe' in sys.argv))
    print(f'  {ziel}: {os.path.getsize(ziel)} Bytes')
