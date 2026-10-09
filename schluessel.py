#!/usr/bin/env python3
"""schluessel.py — Schlüssel der Bericht-Fassung in Trägerziffern umsetzen (Rev10, Zug 1).

Der Text der zehnten Ausgabe führt an jeder Stelle "bewiesen" einen vorläufigen
Schlüssel in eckigen Klammern: [O2.1], [A.3], [B.1], [C1.1]. Gedruckt wird an
seiner Stelle eine Ziffer, die auf eine Zeile der Trägertafel zeigt, wie die
Ziffern [1] … [100] der neunten Ausgabe. Dieses Modul vergibt die Ziffern.

Die Regeln (Übergabe des Verfassers, §2):
  - Ziffern in Lesereihenfolge des ganzen Papiers (die Teile in Druckfolge),
    fortgezählt ab der letzten Ziffer der bestehenden Trägertafel;
  - in beiden Sprachen dieselbe Zuordnung — sonst bricht der Zug;
  - ein Schlüssel ohne Tafelzeile oder eine Tafelzeile ohne Schlüssel bricht den Zug;
  - in Code (`…` und ``` … ```) wird nichts ersetzt: Pfalzgrafs `[16]` bleibt.

    ./schluessel.py --probe        Muss- und Darf-nicht-Fall an einer Probeseite
"""
import re, sys

SCHLUESSEL = re.compile(r'\[((?:O\d|A|B|C\d)\.\d+)\]')
CODE = re.compile(r'(```.*?```|`[^`\n]*`)', re.S)


def _ausser_code(text):
    """Die Stücke des Texts ausserhalb von Code, in Folge."""
    return [t for i, t in enumerate(CODE.split(text)) if i % 2 == 0]


def reihenfolge(texte):
    """Die Schlüssel nach ihrem ersten Vorkommen, über die Texte in der gegebenen Folge."""
    folge = []
    for text in texte:
        for stueck in _ausser_code(text):
            for k in SCHLUESSEL.findall(stueck):
                if k not in folge:
                    folge.append(k)
    return folge


def zuordnung(texte, start, tafel):
    """{Schlüssel: Ziffer}. `tafel` ist die Menge der Schlüssel, die eine Tafelzeile haben."""
    folge = reihenfolge(texte)
    ohne_zeile = [k for k in folge if k not in tafel]
    ohne_text = sorted(set(tafel) - set(folge))
    if ohne_zeile or ohne_text:
        raise SystemExit(f'FEHLER: Schlüssel ohne Tafelzeile {ohne_zeile}; '
                         f'Tafelzeile ohne Schlüssel {ohne_text}')
    return {k: start + i for i, k in enumerate(folge)}


def ersetze(text, z):
    """Jeden Schlüssel ausserhalb von Code durch seine Ziffer ersetzen."""
    teile = CODE.split(text)
    for i in range(0, len(teile), 2):
        teile[i] = SCHLUESSEL.sub(lambda m: f'[{z[m.group(1)]}]', teile[i])
    rest = [k for i in range(0, len(teile), 2) for k in SCHLUESSEL.findall(teile[i])]
    if rest:
        raise SystemExit(f'FEHLER: unersetzte Schlüssel {rest}')
    return ''.join(teile)


def gleich_in_beiden(z_de, z_en):
    if z_de != z_en:
        abw = {k: (z_de.get(k), z_en.get(k)) for k in set(z_de) | set(z_en)
               if z_de.get(k) != z_en.get(k)}
        raise SystemExit(f'FEHLER: die Sprachen ordnen verschieden zu: {abw}')


def _probe():
    # Muss-Faelle (Signums Vorgabe, Zug 1): je ein Schluessel jeder Art, [O5.0] zeigt auf eine Kette,
    # die zwei Schluessel der Bildunterschrift. Darf-nicht-Faelle: [16] im Zitat (Code), die Profile
    # der Tafel, [T6] und die Rev9-Ziffern [97] [99] [11] [58] [66], ein Literaturkuerzel, ein Codeblock.
    seite = ('Bewiesen ist das [O1.1], die Kette [O5.0], und hier [A.1], [B.1], [C1.1]. '
             'Pfalzgraf: „we refer to `[16]`." Profil [propext] und [propext, Quot.sound]; '
             'Rev9: [T6], [97], [99], [11], [58], [66]; [Pfa91a]. '
             'Zweimal derselbe [O1.1]; Bildunterschrift [O7.2] [O7.3].\n\n```\n[O9.9] im Code\n```\n')
    z = zuordnung([seite], 101, {'O1.1', 'O5.0', 'A.1', 'B.1', 'C1.1', 'O7.2', 'O7.3'})
    aus = ersetze(seite, z)
    muss = aus.startswith('Bewiesen ist das [101], die Kette [102], und hier [103], [104], [105].') \
        and '[106] [107]' in aus and aus.count('[101]') == 2
    darf_nicht = all(x in aus for x in ('`[16]`', '[propext]', '[propext, Quot.sound]', '[T6]', '[97]',
                                         '[99]', '[11]', '[58]', '[66]', '[Pfa91a]', '[O9.9] im Code'))
    fehlt = False
    try:
        zuordnung([seite], 101, {'O1.1', 'O5.0', 'A.1', 'B.1', 'C1.1', 'O7.2'})
    except SystemExit:
        fehlt = True
    print(f'  Muss-Faelle (O1.1, O5.0, A.1, B.1, C1.1, Bildunterschrift; Folge, Wiederholung): {"ok" if muss else "FEHLT"}')
    print(f'  Darf-nicht-Faelle (`[16]`, Profile, [T6], Rev9-Ziffern, Kuerzel, Code):       {"ok" if darf_nicht else "FEHLT"}')
    print(f'  Bruch bei fehlender Tafelzeile:                                {"ok" if fehlt else "FEHLT"}')
    return muss and darf_nicht and fehlt


if __name__ == '__main__':
    if sys.argv[1:] == ['--probe']:
        sys.exit(0 if _probe() else 1)
    print(__doc__)
