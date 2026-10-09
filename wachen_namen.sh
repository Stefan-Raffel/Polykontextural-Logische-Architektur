#!/usr/bin/env bash
# =============================================================================
# wachen_namen.sh — aus einer Namensliste eine Wachen-Datei erzeugen
# -----------------------------------------------------------------------------
# ZWECK.  Fallstrick 12 beenden.  Wer Wachen fuer viele Saetze schreibt, baut
# die Liste der `#print axioms`-Aufrufe;  in `zsh` wird eine Variable NICHT
# wortgeteilt, und `for n in $NAMES` laeuft genau einmal — mit allen Namen in
# einem Aufruf.  Das ist in diesem Strang ZWEIMAL aufgetreten (C2-Bau,
# PatternInvariance-Bau), beide Male mit derselben Heilung:  die Datei per
# Python erzeugen.  Dieses Skript ist die Heilung als Werkzeug.
#
# REICHWEITE — ausdruecklich klein gehalten (O4-Abnahme §5, Custos-Vorgabe):
#   Es erzeugt die MESSDATEI aus einer NAMENSLISTE.  Es holt KEINE Profile und
#   schreibt KEINE Wachen.  Ein Skript, das auch misst, muesste `lake env lean`
#   fahren und waere ein anderes Werkzeug.
#
# GEBRAUCH
#   ./wachen_namen.sh <Modul> [Datei]       > messdatei.lean
#     <Modul>  voller Modulname, z. B. Reformulation.Proemial.PatternInvariance
#     [Datei]  Lean-Quelle;  fehlt sie, wird sie aus dem Modulnamen abgeleitet
#   Die Namen sind VOLL, aus dem Namensraum-Stapel der Datei (Weg-A-Zug, 9.10.2026).
#
#   Dann:   lake env lean messdatei.lean
#   und die Ausgabe ist der Doc-String-Text der Wachen, Zeile fuer Zeile.
#
# WARUM `python3` UND NICHT DIE SHELL:  genau wegen Fallstrick 12.  Die Namen
# durchlaufen keine Wortteilung.
# =============================================================================
set -euo pipefail

MODUL="${1:-}"
if [ -z "$MODUL" ]; then
  echo "Gebrauch: $0 <Modulname> [Datei.lean]" >&2
  exit 2
fi
DATEI="${2:-$(echo "$MODUL" | tr '.' '/').lean}"

if [ ! -f "$DATEI" ]; then
  echo "wachen_namen.sh: Datei nicht gefunden: $DATEI" >&2
  exit 3
fi

MODUL="$MODUL" DATEI="$DATEI" python3 - <<'PY'
import os, re, sys
modul = os.environ['MODUL']
datei = os.environ['DATEI']
quelle = open(datei, encoding='utf-8').read()

# Der VOLLE Name kommt aus dem Namensraum-Stapel, nicht aus dem Modulnamen.
# Bis zum Weg-A-Zug (9.10.2026) stand hier `<Modul>.<Satz>`; das lag bei 123 der 210
# damals ungewachten Saetze falsch (F3c/Operators.lean legt seine Saetze in
# F3c.ModalOperators ab) und meldete es nicht — erst `lake env lean` brach.
# Dieselbe Route wie doc_lint.sh Gruppe (G); dort gegen die Umgebung geeicht.
def code_lines(src):
    out, depth = [], 0
    for line in src.split('\n'):
        o, i, n = [], 0, len(line)
        while i < n:
            c, two = line[i], line[i:i + 2]
            if depth == 0 and c == '"':
                j = i + 1
                while j < n and line[j] != '"':
                    j += 2 if line[j] == '\\' else 1
                o.append(line[i:j + 1]); i = j + 1; continue
            if two == '/-': depth += 1; i += 2; continue
            if two == '-/' and depth > 0: depth -= 1; i += 2; continue
            if depth == 0 and two == '--': break
            if depth == 0: o.append(c)
            i += 1
        out.append(''.join(o))
    return out

# dieselbe Satzroute wie kennzahlen.sh (CLAUDE.md §3)
SATZ = re.compile(r'^(?:@\[[^\]]*\]\s+)?((?:private|protected|nonrec)\s+)?(?:@\[[^\]]*\]\s+)?'
                  r'(?:theorem|lemma)\s+([^\s({\[⦃:]+)')
NS = re.compile(r'^namespace\s+(\S+)')
SEC = re.compile(r'^(?:noncomputable\s+)?section\b')
MUT = re.compile(r'^mutual\b')
END = re.compile(r'^end\b(?:\s+(\S+))?\s*$')
stack, namen, privat = [], [], 0
for l in code_lines(quelle):
    if m := NS.match(l): stack.append(m.group(1).split('.')); continue
    if SEC.match(l) or MUT.match(l): stack.append([]); continue
    if END.match(l):
        if stack: stack.pop()
        continue
    if m := SATZ.match(l):
        if (m.group(1) or '').strip() == 'private':
            privat += 1; continue      # privat: von aussen nicht ueber den Namen erreichbar
        n = m.group(2)
        namen.append(n[7:] if n.startswith('_root_.') else '.'.join([c for cs in stack for c in cs] + [n]))
if not namen:
    sys.stderr.write(f"wachen_namen.sh: kein oeffentlicher Satz in {datei}\n")
    sys.exit(4)
print(f"import {modul}")
for n in namen:
    print(f"#print axioms {n}")
sys.stderr.write(f"wachen_namen.sh: {len(namen)} Saetze aus {datei}"
                 + (f" ({privat} private ausgelassen)" if privat else "") + "\n")
PY
