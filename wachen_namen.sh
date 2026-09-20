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
# dieselbe Satzroute wie kennzahlen.sh (CLAUDE.md §3), auf Namen verkuerzt
SATZ = re.compile(
    r'^(@\[[^\]]*\] +)?((private|protected|nonrec) +)?(@\[[^\]]*\] +)?'
    r'(theorem|lemma) ([^\s({\[⦃:]+)', re.M)
namen = [m.group(6) for m in SATZ.finditer(quelle)]
if not namen:
    sys.stderr.write(f"wachen_namen.sh: kein Satz in {datei}\n")
    sys.exit(4)
print(f"import {modul}")
for n in namen:
    print(f"#print axioms {modul}.{n}")
sys.stderr.write(f"wachen_namen.sh: {len(namen)} Saetze aus {datei}\n")
PY
