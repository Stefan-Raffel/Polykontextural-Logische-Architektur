#!/usr/bin/env bash
# =============================================================================
# deixis.sh — relative Zeitwoerter ohne Anker in den laufenden Fassungen
# -----------------------------------------------------------------------------
#   ./docs/deixis.sh            meldet ueber docs/de.html, docs/en.html, docs/index.html
#   ./docs/deixis.sh --probe    faehrt die Eichung am Anlass (braucht die Geschichte)
#
# DIESE PROBE MELDET NUR, wie parity.sh. Nicht jedes relative Zeitwort ist ein
# Fehler: "bisher war von Werten keine Rede" verweist innerhalb des Texts und altert
# nicht. Was sie zeigt, wird gelesen; ein Treffer ist ein Kandidat, kein Befund.
#
# ANLASS (Rev10-Register, Merkliste M2; Custos-Empfehlung 9.10.2026, Entscheid des
# Architekten): "In der juengsten Arbeitsphase" stand seit der vierten Ausgabe in
# Teil A und meinte die Phase vor ihr. d248dc0 (27.9.) datierte drei gleichartige
# Stellen in Teil B; die in Teil A blieb und ging mit Rev9 und Rev10 hinaus. Custos
# zaehlt zwei ausgelieferte Faelle (Register M2); CLAUDE.md §13.2: eine Probe braucht
# ihren Fall.
#
# ROUTE: Absaetze (p, li, td, figcaption) als Text. Gemeldet wird ein Absatz, der
# ein relatives Zeitwort traegt und KEINEN Anker: eine benannte Ausgabe ("vierten
# Fassung", "Rev9", "ninth edition"), ein Jahr, ein Datum oder einen Commit-Hash.
# Das blosse Wort "Fassung" ist KEIN Anker — "zwei Fassungen" einer Messung liess
# im ersten Lauf (9.10.) genau den Anlass durchfallen.
#
# EICHUNG (--probe), am Anlass:
#   Muss        d248dc0^  die "juengste Arbeitsphase" trifft (vier Absaetze)
#   Darf-nicht  d248dc0   die drei dort datierten Stellen in Teil B treffen nicht
#   Muss        d248dc0   die undatierte Stelle in Teil A trifft weiter
#
# SPRACHEN: die Wortlisten sind je Sprache eigene Listen und nicht Uebersetzungen
# voneinander; "seit kurzem" und "since recently" stehen beide, "bisher" und
# "so far" ebenso. Locale: Python liest UTF-8 und ist davon unabhaengig.
# =============================================================================
set -u
cd "$(dirname "$0")/.." || exit 2
MODUS="${1:-}"
MODUS="$MODUS" python3 - <<'PY'
import re, html, os, subprocess, collections

DEIX = {
 'de': re.compile(r'\b(jüngst\w*|ältest\w*|seit kurzem|neuerdings|inzwischen|neu|neue[nmrs]?|bisher\w*|seither|'
                  r'derzeit|zurzeit|mittlerweile|kürzlich|unlängst|jetzt)\b', re.I),
 'en': re.compile(r'\b(youngest|oldest|since recently|by now|latest|recent\w*|meanwhile|new|newly|so far|'
                  r'until now|hitherto|currently|now|lately)\b', re.I),
}
MON = (r'(Januar|Februar|März|April|Mai|Juni|Juli|August|September|Oktober|November|Dezember|'
       r'January|February|March|May|June|July|October|December)')
ANKER = re.compile(r'\bRev\d+\b|(erste|zweite|dritte|vierte|fünfte|sechste|siebte|achte|neunte|zehnte)[nrs]?\s+'
                   r'(Ausgabe|Fassung)|(first|second|third|fourth|fifth|sixth|seventh|eighth|ninth|tenth)\s+edition|'
                   r'\b(19|20)\d\d\b|\d{1,2}\.\s*' + MON + r'|' + MON + r'\s+\d{1,2}|\b\d{1,2}\.\d{1,2}\.|\b[0-9a-f]{7}\b',
                   re.I)

def absaetze(s):
    for m in re.finditer(r'<(p|li|td|figcaption)\b[^>]*>(.*?)</\1>', s, re.S):
        t = re.sub(r'\s+', ' ', html.unescape(re.sub(r'<[^>]+>', ' ', m.group(2)))).strip()
        if t:
            yield t

def lauf(s, sp):
    out = []
    for t in absaetze(s):
        w = [x if isinstance(x, str) else x[0] for x in DEIX[sp].findall(t)]
        if w and not ANKER.search(t):
            out.append((w, t))
    return out

if os.environ.get('MODUS') == '--probe':
    show = lambda r: subprocess.run(['git', 'show', f'{r}:docs/de.html'], capture_output=True, text=True).stdout
    vor = [t for _, t in lauf(show('d248dc0^'), 'de') if 'Arbeitsphase' in t]
    nach = [t for _, t in lauf(show('d248dc0'), 'de') if 'Arbeitsphase' in t]
    f = [('Muss       d248dc0^, "juengste Arbeitsphase" trifft', bool(vor)),
         ('Darf-nicht d248dc0, die drei datierten Stellen treffen nicht', not any('vierten Fassung' in t for t in nach)),
         ('Muss       d248dc0, die undatierte Stelle in Teil A trifft', any('ist es zweimal' in t for t in nach))]
    for n, ok in f:
        print(f"  {n:66s} {'ok' if ok else 'FEHLT'}")
    raise SystemExit(0 if all(ok for _, ok in f) else 1)

print("── deixis.sh — relative Zeitwoerter ohne Anker (meldet nur)")
for datei, sp in (('docs/de.html', 'de'), ('docs/en.html', 'en'), ('docs/index.html', 'de')):
    tr = lauf(open(datei, encoding='utf-8').read(), sp)
    c = collections.Counter(x.lower() for w, _ in tr for x in w)
    print(f"\n  {datei}: {len(tr)} Absaetze;  {', '.join(f'{k} {v}' for k, v in c.most_common())}")
    for w, t in tr:
        print(f"    - {'/'.join(sorted(set(x.lower() for x in w)))}: {t[:140]}")
print("\n   Ein Treffer ist ein Kandidat: verweist das Wort innerhalb des Texts, altert es nicht;")
print("   verweist es auf einen Stand des Vorhabens, braucht der Absatz seine Ausgabe oder sein Datum.")
PY
