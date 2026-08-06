#!/usr/bin/env bash
# =============================================================================
# profil_probe.sh — die Profilspalte der Traegertafel messen statt tippen
# -----------------------------------------------------------------------------
# Liest die Traegertafel eines Papier-Entwurfs, loest jeden zitierten Namen am
# Bestand auf, misst sein Axiomprofil mit `#print axioms` und haelt das Ergebnis
# gegen die Spalte *Profil*.
#
#   ./profil_probe.sh <entwurf.md>              nur berichten
#   ./profil_probe.sh <entwurf.md> --schreiben  Marken und Abweichungen fuellen
#
# Warum ueberhaupt: ein Profil, das von Hand in ein Papier getippt wird, steht an
# zwei Orten und altert am zweiten unbemerkt (CLAUDE.md §13). Die Profile der
# uebrigen Kennzahlen sind seit `kennzahlen.sh` erzeugt; dies ist dieselbe
# Bewegung fuer die Spalte, die je Satz spricht.
#
# Namensaufloesung, in dieser Reihenfolge:
#   1. voller Punktpfad als Suffix eines Bestandsnamens  (`Proemial.NoUniformSwap.no_uniform_swap`)
#   2. letzte Komponente allein, wenn sie im Bestand eindeutig ist
#   3. das Papier-Kuerzel vor dem Punkt als Initialen einer Namensraum-Komponente
#      (`AA.` -> `ArrowAscent`, `SAsc.` -> `StageAscent`)
# Bleibt danach mehr als ein Treffer, wird NICHT geraten, sondern gemeldet.
# Die Kuerzel des Papiers sind KEINE Lean-Namensraeume — Schritt 1 allein findet
# nichts; das ist der Grund fuer die drei Stufen.
#
# Was die Probe NICHT kann: sie prueft, ob der genannte Name das genannte Profil
# hat. Ob es der richtige Name fuer die Behauptung ist, prueft ein Mensch.
# =============================================================================
set -u
cd "$(dirname "$0")" || exit 2

ENTWURF="${1:-}"
SCHREIBEN=0
[ "${2:-}" = "--schreiben" ] && SCHREIBEN=1
if [ -z "$ENTWURF" ] || [ ! -f "$ENTWURF" ]; then
  sed -n '2,26p' "$0"
  exit 2
fi

TMP=$(mktemp -d)
trap 'rm -rf "$TMP"' EXIT

export PP_ENTWURF="$ENTWURF" PP_TMP="$TMP" PP_SCHREIBEN="$SCHREIBEN"

# --- 1. Tafel lesen, Namen aufloesen, Lean-Datei schreiben -------------------
python3 - <<'PY' || exit 2
import os, re, json, subprocess, collections

entwurf = os.environ['PP_ENTWURF']; tmp = os.environ['PP_TMP']

# Index der Bestandsnamen: Namensraum-Stapel plus Deklarationszeile.
decl = re.compile(r'^((?:private|protected|nonrec)\s+)?(?:@\[[^\]]*\]\s*)?'
                  r'(theorem|lemma|def|abbrev|structure|inductive|instance)\s+([^\s({\[:⦃]+)')
paths = subprocess.run(['git', 'ls-files', '*.lean'], capture_output=True, text=True).stdout.split()
idx = {}
for p in paths:
    stack = []
    for line in open(p, encoding='utf-8'):
        m = re.match(r'^namespace\s+(\S+)', line)
        if m:
            stack.append(('ns', m.group(1))); continue
        m = re.match(r'^section\s*(\S*)\s*$', line)
        if m:
            stack.append(('sec', m.group(1) or None)); continue
        m = re.match(r'^end\s*(\S*)\s*$', line)
        if m:
            nm = m.group(1) or None
            for i in range(len(stack) - 1, -1, -1):
                if stack[i][1] == nm:
                    del stack[i]; break
            continue
        d = decl.match(line)
        if d:
            pre = '.'.join(x[1] for x in stack if x[0] == 'ns')
            idx.setdefault((pre + '.' + d.group(3)) if pre else d.group(3), p[:-5].replace('/', '.'))

def initiale(abk, komp):
    if komp.lower().startswith(abk.lower()):
        return True
    gross = ''.join(c for c in komp if c.isupper())
    return gross.lower().startswith(abk.lower())

def loese(kurz):
    t = kurz.split('.')
    tr = [f for f in idx if f.split('.')[-len(t):] == t]
    if len(tr) == 1:
        return tr[0], 'voll', []
    tr = [f for f in idx if f.split('.')[-1] == t[-1]]
    if len(tr) == 1:
        return tr[0], 'einfach', []
    if len(t) > 1 and tr:
        eng = [f for f in tr if any(initiale(t[-2], k) for k in f.split('.')[:-1])]
        if len(eng) == 1:
            return eng[0], 'kuerzel', []
        if eng:
            return None, 'mehrdeutig', eng
    return (None, 'mehrdeutig', tr) if tr else (None, 'fehlt', [])

zeilen = []
for nr, line in enumerate(open(entwurf, encoding='utf-8')):
    if not re.match(r'^\| (\[\d+\]|—) \|', line):
        continue
    sp = [x.strip() for x in line.strip().strip('|').split('|')]
    if len(sp) < 4:
        continue
    namen = re.findall(r'`([A-Za-z][\w.\'!?]*)`', sp[1])
    eintraege = []
    for n in namen:
        voll, art, kand = loese(n)
        eintraege.append({'kurz': n, 'voll': voll, 'art': art, 'kandidaten': kand,
                          'modul': idx.get(voll) if voll else None})
    zeilen.append({'zeile': nr + 1, 'ziffer': sp[0], 'spalte': sp[3], 'namen': eintraege})

module = sorted({e['modul'] for z in zeilen for e in z['namen'] if e['modul']})
namen = [e['voll'] for z in zeilen for e in z['namen'] if e['voll']]
with open(f'{tmp}/probe.lean', 'w', encoding='utf-8') as f:
    for m in module:
        f.write(f'import {m}\n')
    f.write('set_option maxHeartbeats 1000000\n')
    for n in dict.fromkeys(namen):
        f.write(f'#print axioms {n}\n')
json.dump(zeilen, open(f'{tmp}/tafel.json', 'w'), ensure_ascii=False)
print(f"  Tafelzeilen {len(zeilen)} · zitierte Namen {len(namen)} · Module {len(module)}")
PY

# --- 2. Messen ---------------------------------------------------------------
echo "  messe …"
lake env lean "$TMP/probe.lean" > "$TMP/roh.txt" 2> "$TMP/fehler.txt"
if [ -s "$TMP/fehler.txt" ]; then
  echo "  FEHLER beim Messen:"; sed 's/^/    /' "$TMP/fehler.txt"; exit 2
fi

# --- 3. Vergleichen, berichten, ggf. schreiben -------------------------------
python3 - <<'PY'
import os, re, json

tmp = os.environ['PP_TMP']; entwurf = os.environ['PP_ENTWURF']
schreiben = os.environ['PP_SCHREIBEN'] == '1'
zeilen = json.load(open(f'{tmp}/tafel.json'))

# `#print axioms` bricht an der ZEILENLAENGE um (CLAUDE.md §8 Fallstrick 14) und
# hat ZWEI Wortlaute (Fallstrick 15) — beides hier gefasst.
roh = open(f'{tmp}/roh.txt', encoding='utf-8').read()
roh = re.sub(r'\n(?!\')', ' ', roh)
gemessen = {}
for m in re.finditer(r"'([^']+)' (does not depend on any axioms|depends on axioms: \[([^\]]*)\])", roh):
    name, art, liste = m.group(1), m.group(2), m.group(3)
    gemessen[name] = 'axiomfrei' if art.startswith('does not') else \
        '[' + ', '.join(x.strip() for x in liste.split(',')) + ']'

def norm(p):
    if p == 'axiomfrei':
        return 'axiomfrei'
    return '[' + ', '.join(sorted(x.strip() for x in p[1:-1].split(','))) + ']'

def anspruch(s):
    """Was die Spalte MASCHINENLESBAR behauptet. Prosa ist kein Anspruch."""
    if '⟦' in s:
        return 'marke', None
    a = {'[' + ', '.join(sorted(x.strip() for x in g.split(','))) + ']'
         for g in re.findall(r'`\[([^\]]*)\]`', s)}
    if re.search(r'\baxiomfrei\b|\baxiom-free\b', s):
        a.add('axiomfrei')
    choicefrei = bool(re.search(r'choice-frei|choice-free', s))
    if not a and not choicefrei:
        return 'prosa', None
    return 'anspruch', (a, choicefrei)

marken = abweichungen = treffer = prosa = ungeloest = 0
ersatz = {}
print()
print("  Ziffer   Traeger                                  gemessen")
print("  " + "─" * 96)
for z in zeilen:
    profile, unaufgeloest = [], []
    for e in z['namen']:
        if not e['voll']:
            unaufgeloest.append(e); continue
        p = gemessen.get(e['voll'])
        if p:
            profile.append((e['kurz'], p, norm(p)))
    for e in unaufgeloest:
        ungeloest += 1
        print(f"  {z['ziffer']:8s} {e['kurz']:40s} NICHT AUFGELOEST ({e['art']})")
        for k in e['kandidaten'][:4]:
            print(f"           … Kandidat: {k}")
    if not profile:
        continue
    # roh = die Reihenfolge, die Lean druckt (so steht es im Papier);
    # norm = alphabetisch, nur zum Vergleichen.
    roh_liste = list(dict.fromkeys(r for _, r, _ in profile))
    ist = list(dict.fromkeys(n for _, _, n in profile))
    art, inhalt = anspruch(z['spalte'])
    if art == 'marke':
        marken += 1
        urteil = "MARKE — wird gefuellt" if schreiben else "MARKE offen"
        ersatz[z['zeile']] = ' · '.join('**axiomfrei**' if p == 'axiomfrei' else f'`{p}`'
                                        for p in roh_liste)
    elif art == 'prosa':
        prosa += 1
        urteil = "Prosa — kein maschinenlesbarer Anspruch"
    else:
        behauptet, choicefrei = inhalt
        fehlend = behauptet - set(ist)
        traeger = profile[0][2]
        choicebruch = choicefrei and 'Classical.choice' in traeger
        if not fehlend and not choicebruch:
            treffer += 1; urteil = "✓"
        else:
            abweichungen += 1
            teile = []
            if fehlend:
                teile.append("Entwurf behauptet " + ' · '.join(sorted(fehlend)))
            if choicebruch:
                teile.append("Entwurf sagt choice-frei, gemessen " + traeger)
            urteil = "ABWEICHUNG — " + "; ".join(teile)
    kopf = profile[0][0] + (f" (+{len(profile)-1})" if len(profile) > 1 else "")
    print(f"  {z['ziffer']:8s} {kopf:40s} {' · '.join(roh_liste):40s} {urteil}")

print("  " + "─" * 96)
print(f"  {treffer} bestaetigt · {marken} Marken · {abweichungen} Abweichungen · "
      f"{prosa} Prosa · {ungeloest} nicht aufgeloest")

if prosa:
    print("  Prosa heisst: die Spalte sagt etwas, das keine Profilangabe ist "
          "(\"siehe 1.7\"). Das ist kein Fehler und wird nicht gefuellt.")

if schreiben and ersatz:
    lines = open(entwurf, encoding='utf-8').read().split('\n')
    for nr, neu in ersatz.items():
        sp = lines[nr - 1].rstrip().rstrip('|').split('|')
        sp[-1] = f' {neu} '
        lines[nr - 1] = '|'.join(sp) + '|'
    open(entwurf, 'w', encoding='utf-8').write('\n'.join(lines))
    print(f"  {len(ersatz)} Zeilen in {entwurf} geschrieben.")
elif schreiben:
    print("  Nichts zu schreiben.")

raise SystemExit(1 if (ungeloest or (abweichungen and not schreiben)) else 0)
PY
