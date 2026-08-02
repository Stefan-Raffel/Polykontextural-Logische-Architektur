#!/usr/bin/env bash
# =============================================================================
# figures.sh — Strukturprobe an den Figuren einer HTML-Fassung  (Vorgang 12, C)
# -----------------------------------------------------------------------------
#   ./docs/figures.sh                 prueft docs/de.html und docs/en.html
#   ./docs/figures.sh <datei> [...]   prueft die genannten Dateien
#   ./docs/figures.sh -               liest eine Fassung von der Standardeingabe
#                                     (fuer `git show <commit>:docs/de.html | …`)
#
# DIESE PROBE BRICHT. Eine zerschlagene Figur ist kein Ermessen — anders als ein
# Rang-Anspruch, den Gruppe (A) des Doc-Lints nur meldet.
#
# ANLASS, damit die Probe nicht als Zierat gestrichen wird: in `a0fe668` waren
# alle fuenf Figuren der deutschen Fassung zerschlagen, und KEINE der sechzehn
# damaligen Abnahmerouten konnte es sehen. pandoc beendet einen rohen HTML-Block
# an der ersten Leerzeile; die SVG-Kinder dahinter wurden als Markdown gelesen
# und in <p> gehuellt — INNERHALB des <svg>. Ein <svg> mit <p> ist ungueltig:
# der Browser wirft die Kinder aus dem SVG-Namensraum, die Grafikflaeche bleibt
# leer, die Beschriftungen stehen als Fliesstext darunter.
#
# WARUM ZAEHLEN ALLEIN BLIND IST: am Schadensfall sind <svg> 5 = 5, <figure>
# 5 = 5 und die <text>-Zahlen JE GLEICH (25, 27, 11, 9, 13). Die Knoten sind
# vollzaehlig — sie stecken nur in einer Huelle, die sie unwirksam macht.
# Ein intaktes und ein zertruemmertes Element sehen in einer Zaehlung gleich aus.
# Darum zaehlt C-3 DIREKTE Kinder und nicht Nachfahren.
#
# EICHUNG (Vorbedingung, nicht Nachweis):
#     git show a0fe668:docs/de.html | ./docs/figures.sh -    -> muss ANSCHLAGEN
#     git show b3681b3:docs/de.html | ./docs/figures.sh -    -> muss SCHWEIGEN
# `a0fe668` ist der stehende Negativfall des Projekts. Ein kaputtes Artefakt,
# das man behalten kann, ist wertvoller als jede Beschreibung des Schadens.
# =============================================================================

set -uo pipefail

DOCS="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

TARGETS=()
if [ "$#" -eq 0 ]; then
  TARGETS=("${DOCS}/de.html" "${DOCS}/en.html")
else
  TARGETS=("$@")
fi

TMP="$(mktemp -d)"
trap 'rm -rf "${TMP}"' EXIT

rc=0
for t in "${TARGETS[@]}"; do
  if [ "$t" = "-" ]; then
    cat > "${TMP}/stdin.html"
    t="${TMP}/stdin.html"; label="(Standardeingabe)"
  else
    label="$t"
  fi
  if [ ! -f "$t" ]; then
    echo "figures: Datei nicht gefunden: $t" >&2
    rc=1; continue
  fi

  python3 - "$t" "$label" <<'PY'
import re, sys
pfad, label = sys.argv[1], sys.argv[2]
t = open(pfad, encoding='utf-8', errors='replace').read()

figs = re.findall(r'<figure\b.*?</figure>', t, re.S)
svgs = re.findall(r'<svg\b.*?</svg>', t, re.S)

def direkte_kinder(svg_block):
    """Elementnamen der DIREKTEN Kinder des <svg> — Nachfahren zaehlen nicht,
       weil sie am Schadensfall unveraendert sind."""
    innen = re.sub(r'^<svg\b[^>]*>', '', svg_block, count=1)
    innen = re.sub(r'</svg>$', '', innen)
    kinder, tiefe = [], 0
    for m in re.finditer(r'<(/?)([a-zA-Z][a-zA-Z0-9]*)\b([^>]*?)(/?)>', innen):
        schliessend, name, rest, selbst = m.group(1), m.group(2).lower(), m.group(3), m.group(4)
        if schliessend:
            tiefe -= 1
            continue
        if tiefe == 0:
            kinder.append(name)
        if not selbst:
            tiefe += 1
    return kinder

VERBOTEN = {'p', 'div', 'blockquote', 'ul', 'ol', 'li', 'pre', 'table'}
befunde = []

# --- C-1  <p> innerhalb <svg> ------------------------------------------------
c1 = sum(len(re.findall(r'<p[\s>]', s)) for s in svgs)
if c1: befunde.append(f"C-1  {c1} <p> innerhalb <svg>  (Soll 0)")

# --- C-2  <p> in <figure>, das nicht die Bildunterschrift ist ----------------
c2 = 0
for f in figs:
    ohne_cap = re.sub(r'<figcaption\b.*?</figcaption>', '', f, flags=re.S)
    c2 += len(re.findall(r'<p[\s>]', ohne_cap))
if c2: befunde.append(f"C-2  {c2} <p> innerhalb <figure> ausserhalb der Bildunterschrift  (Soll 0)")

# --- C-3  direkte Kinder des <svg> ------------------------------------------
for i, s in enumerate(svgs, 1):
    schlecht = [k for k in direkte_kinder(s) if k in VERBOTEN]
    if schlecht:
        befunde.append(f"C-3  svg {i}: Fliesstext-Element als direktes Kind: {sorted(set(schlecht))}")

# --- C-4  je <figure> genau eine Bildunterschrift ----------------------------
falsch = [i for i, f in enumerate(figs, 1) if len(re.findall(r'<figcaption\b', f)) != 1]
if falsch: befunde.append(f"C-4  <figure> ohne genau eine Bildunterschrift: {falsch}  (Soll keine)")

kopf = f"  {label}: {len(figs)} <figure>, {len(svgs)} <svg>"
if befunde:
    print(kopf + "   BEFUND")
    for b in befunde: print("      " + b)
    sys.exit(1)
print(kopf + "   in Ordnung")
PY
  [ "$?" -ne 0 ] && rc=1
done

if [ "$rc" -ne 0 ]; then
  echo "figures: Exit 1. Mindestens eine Figur ist strukturell zerschlagen." >&2
  exit 1
fi
echo "figures: Exit 0."
exit 0
