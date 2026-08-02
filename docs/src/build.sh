#!/usr/bin/env bash
# =============================================================================
# build.sh — Erzeugungsstrecke Markdown -> HTML fuer die beiden Papierfassungen
#            (Vorgang 8, Ausweg A)
# -----------------------------------------------------------------------------
# Eingang   genau docs/src/de.md und docs/src/en.md
# Ausgang   genau docs/de.html und docs/en.html
# Werkzeug  pandoc, Fassung festgeschrieben (siehe PANDOC_VERSION)
#
#   ./build.sh            erzeugt beide Fassungen
#   ./build.sh --check    erzeugt in ein temporaeres Verzeichnis und vergleicht
#                         byteweise; Abweichung setzt Exit 1
#
# DIE ERZEUGNISSE WERDEN NICHT VON HAND GEAENDERT. Wer den Text aendert, aendert
# die Quelle und erzeugt neu. `--check` faengt einen Handgriff am Erzeugnis erst
# beim naechsten Lauf — es ist eine Wache mit Verzoegerung, keine mit
# Verhinderung. Siehe CLAUDE.md §1.
#
# Die Fassungspruefung ist keine Formalie: ohne sie waere der Vergleich eine
# Route, die still bricht, sobald ein anderer Wandler dasselbe Markdown anders
# schreibt (dieselbe Figur wie `git grep -cw` in CLAUDE.md §8, Fallstrick 9).
# Ein Fassungswechsel ist zulaessig und kostet eine Neueichung: Fassung hier
# festschreiben, erzeugen, die entstehenden Unterschiede einzeln beurteilen,
# die Erzeugnisse neu ablegen. Eigener Zug, kein Nebenbei.
# =============================================================================

set -euo pipefail

PANDOC_VERSION="3.9"

SRC="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
DOCS="$(cd "${SRC}/.." && pwd)"

# --- Wandler finden ---------------------------------------------------------
# Erst im Pfad, dann im gebuendelten pypandoc-Rad (so liegt er auf der
# Baumaschine; siehe Vorgang8_Erzeugungsstrecke_Probe_Befund.md §3).
if command -v pandoc >/dev/null 2>&1; then
  PANDOC="$(command -v pandoc)"
else
  PANDOC="$(python3 -c 'import os,pypandoc;print(os.path.join(os.path.dirname(pypandoc.__file__),"files","pandoc"))' 2>/dev/null || true)"
fi

if [ -z "${PANDOC}" ] || [ ! -x "${PANDOC}" ]; then
  echo "build: kein pandoc gefunden." >&2
  echo "  erwartet: pandoc ${PANDOC_VERSION} im Pfad oder als pypandoc_binary" >&2
  exit 1
fi

# --- Fassung pruefen, nicht voraussetzen -------------------------------------
IST="$("${PANDOC}" --version | head -1 | awk '{print $2}')"
if [ "${IST}" != "${PANDOC_VERSION}" ]; then
  echo "build: falsche pandoc-Fassung." >&2
  echo "  festgeschrieben: ${PANDOC_VERSION}" >&2
  echo "  vorgefunden:     ${IST}   (${PANDOC})" >&2
  echo "  Ein Fassungswechsel ist ein eigener Zug mit Neueichung, kein Nebenbei." >&2
  exit 1
fi

# --- Erzeugen ----------------------------------------------------------------
render() {  # $1 = de|en   $2 = Zieldatei
  local lang="$1" out="$2" isen=()
  [ "${lang}" = "en" ] && isen=(--variable=is-en)
  "${PANDOC}" \
    --from=markdown-smart \
    --to=html5 \
    --standalone \
    --toc \
    --toc-depth=2 \
    --template="${SRC}/paper.html" \
    --lua-filter="${SRC}/classes.lua" \
    "${isen[@]}" \
    --output="${out}" \
    "${SRC}/${lang}.md"
}

MODE="${1:-}"

if [ "${MODE}" = "--check" ]; then
  TMP="$(mktemp -d)"
  trap 'rm -rf "${TMP}"' EXIT
  rc=0
  for lang in de en; do
    [ -f "${SRC}/${lang}.md" ] || { echo "  ${lang}: keine Quelle — uebersprungen"; continue; }
    render "${lang}" "${TMP}/${lang}.html"
    if cmp -s "${TMP}/${lang}.html" "${DOCS}/${lang}.html"; then
      echo "  ${lang}.html  byteweise identisch"
    else
      echo "  ${lang}.html  ABWEICHUNG — das Erzeugnis folgt nicht aus der Quelle"
      diff "${DOCS}/${lang}.html" "${TMP}/${lang}.html" | head -20
      rc=1
    fi
  done
  if [ "${rc}" -ne 0 ]; then
    echo "build --check: Exit 1. Quelle aendern und neu erzeugen, nicht das Erzeugnis." >&2
    exit 1
  fi
  echo "build --check: Exit 0. Beide Erzeugnisse folgen aus ihrer Quelle."
  exit 0
fi

for lang in de en; do
  [ -f "${SRC}/${lang}.md" ] || { echo "  ${lang}: keine Quelle — uebersprungen"; continue; }
  render "${lang}" "${DOCS}/${lang}.html"
  echo "  ${lang}.html  erzeugt  ($(wc -c < "${DOCS}/${lang}.html" | tr -d ' ') Bytes)"
done
