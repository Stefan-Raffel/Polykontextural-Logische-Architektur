#!/usr/bin/env bash
# =============================================================================
# doc_lint.sh — Doc-Lint für den PKL-Korpus (Prüfzug 4, Doc-Korrektur, Teil 2)
# -----------------------------------------------------------------------------
# Zwei Wortgruppen, getrennt ausgewiesen:
#   (A) SUPERLATIV      — Rang-Ansprüche ohne Ist-Prüfung
#                         (Hausregel: keine „erstmals/einzige/seit F-1" o. Ä.)
#   (B) ZFC-RÜCKFALL    — „unabhängig/Unabhängigkeit/independent/independence",
#                         NUR gemeldet bei Nähe (±1 Zeile) zu einem der
#                         ZFC-Trigger (ZFC, Zermelo).  [Nachtrag (2a);
#                         Nachschlag Teil 3: Trigger auf ZFC|Zermelo verengt —
#                         Axiom(e)/axiomatisch/ableitbar sind in diesem Korpus
#                         Leitthema (15/62/70 benigne Treffer) und erzeugten nur
#                         Rauschen.]
#
#   Ausschluss-Liste [Nachschlag Teil 3]: Dateien, die die Rückfall-Regel
#   *definieren*, schlagen nicht auf ihrer eigenen Definition an (Namens-Muster,
#   keine starre Liste) — siehe EXCLUDE_GLOBS unten.
#
# Lauf-Bereich  [Nachtrag (2b)]:
#   - ohne Argument      → Default = das Repo (Verzeichnis dieses Skripts).
#   - mit Argument       → doc_lint.sh <pfad>  läuft über <pfad> (Außentexte).
#
# Exit-Code  [Nachtrag (2c)]:
#   - IMMER 0. Der Lint MELDET, er BRICHT nicht. (Ein brechender Lint wird
#     umgangen; ein meldender wird gelesen.)
#
# Hinweis zur Herkunft: es lag keine Basis-`doc_lint.sh` vor; Gruppe (A) ist
# aus der dokumentierten Hausregel rekonstruiert und bewusst konservativ
# (Rang-Phrasen, nicht das blanke Adjektiv „erste"). Neu und maßgeblich für
# die Rückgabe ist allein Gruppe (B).
# =============================================================================

set -u

# --- Ziel-Verzeichnis -------------------------------------------------------
ROOT="${1:-}"
if [ -z "${ROOT}" ]; then
  # Default: das Repo = Verzeichnis, in dem dieses Skript liegt.
  ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
  SCOPE_LABEL="Repo (Default) — ${ROOT}"
else
  # Erreichbarkeit ehrlich prüfen: existiert UND lesbar (iCloud liefert bei
  # fehlender Freigabe „Operation not permitted" — das gilt als NICHT erreichbar).
  exists="nein"; [ -d "${ROOT}" ] && exists="ja"
  if [ "${exists}" = "nein" ] || ! ls -A "${ROOT}" >/dev/null 2>&1; then
    echo "doc_lint: Pfad nicht erreichbar: ${ROOT}" >&2
    echo "  existiert-als-Verzeichnis: ${exists}; lesbar: nein"
    echo "  (z. B. macOS 'Operation not permitted' bei nicht freigegebenem iCloud)"
    echo "  -> kein Ersatz-Lauf, keine geschaetzte Aussage. Erreichbarkeit = NEIN."
    exit 0
  fi
  ROOT="$(cd "${ROOT}" && pwd)"
  SCOPE_LABEL="Argument-Pfad (Außentexte) — ${ROOT}"
fi

# --- Wortlisten -------------------------------------------------------------
# (B) ZFC-Rückfall-Wörter (Stämme, case-insensitiv; fangen Flexionen mit):
#     unabhängig → unabhängig(e/er/keit ...);  independen → independent/independence
RUECKFALL_RE='unabhängig|independen'
# (B) ZFC-Trigger im Nähe-Fenster ±1 Zeile [Nachschlag Teil 3: verengt]:
TRIGGER_RE='ZFC|Zermelo'
# (A) Superlativ-/Rang-Phrasen (konservativ):
SUPERLATIV_RE='erstmals|erstmalig|zum ersten Mal|als erste[rs]?|einzige[rns]?|seit F-1|seit F1'

# --- Dateiliste -------------------------------------------------------------
# Markdown + Lean-Modul-Docs; vendored/Meta-Verzeichnisse ausgeschlossen.
# (bash-3.2-kompatibel: kein mapfile; NUL-getrennt einlesen)
#
# Ausschluss-Muster [Nachschlag Teil 3]: Regel-DEFINIERENDE Dokumente sollen
# nicht auf ihrer eigenen Definition anschlagen. Namens-Muster (Globs), damit
# Folge-Revisionen automatisch mitgefasst sind.
EXCLUDE_GLOBS=(
  'Janus_*_ZFC_Formel.md'                 # Janus_Nachtraege_/Janus_Wortheilung_…
  'Pruefzug4_Doc_Korrektur_*PI*.md'       # …_PI_Nachtrag / …_Nachschlag_PI (+ Final-PI)
  'Implementierungsplan_Phase_Design_Rev*.md'  # Rev20 und Folge-Revisionen
  'doc_lint_*_Report.md'                  # Lint-Reports zitieren Treffer → nicht auf sich selbst anschlagen
)
is_excluded() {  # $1 = voller Pfad; prüft nur den Basename gegen die Muster
  local base; base="$(basename -- "$1")"
  local g
  for g in "${EXCLUDE_GLOBS[@]}"; do
    case "$base" in ($g) return 0;; esac
  done
  return 1
}
FILES=()
while IFS= read -r -d '' f; do
  is_excluded "$f" && continue
  FILES+=("$f")
done < <(
  find "${ROOT}" \
    \( -name '.lake' -o -name '.git' -o -name '.claude' -o -name 'node_modules' \) -prune -o \
    \( -name '*.md' -o -name '*.lean' \) -type f -print0 \
    | sort -z
)

# --- Kern-Scanner (awk) -----------------------------------------------------
# Emittiert je Treffer eine Report-Zeile, getaggt nach Gruppe.
scan_file() {
  local f="$1"
  awk -v FN="$f" \
      -v RUECK="$RUECKFALL_RE" \
      -v TRIG="$TRIGGER_RE" \
      -v SUP="$SUPERLATIV_RE" '
    { lines[NR] = $0 }
    END {
      for (i = 1; i <= NR; i++) {
        L = lines[i]
        # ---- (B) ZFC-Rückfall: Wort + Trigger im Fenster ±1 -------------
        if (L ~ RUECK) {
          ctx = lines[i-1] "\n" L "\n" lines[i+1]
          if (ctx ~ TRIG) {
            # Welche Trigger-Zeile? (für den Report vermerken)
            where = "diese Zeile"
            if (lines[i-1] ~ TRIG) where = "Zeile davor"
            else if (lines[i+1] ~ TRIG && L !~ TRIG) where = "Zeile danach"
            printf "B\t%s\t%d\t%s\t%s\n", FN, i, where, L
          }
        }
        # ---- (A) Superlativ: reiner Wort-Match ---------------------------
        if (L ~ SUP) {
          printf "A\t%s\t%d\t%s\t%s\n", FN, i, "-", L
        }
      }
    }
  ' "$f"
}

# --- Lauf -------------------------------------------------------------------
RAW="$(
  for f in "${FILES[@]}"; do
    scan_file "$f"
  done
)"

BLOCK_A="$(printf '%s\n' "$RAW" | awk -F'\t' '$1=="A"')"
BLOCK_B="$(printf '%s\n' "$RAW" | awk -F'\t' '$1=="B"')"

fmt() {
  # Eingabe: getaggte TSV-Zeilen; Ausgabe: lesbarer Report.
  awk -F'\t' -v root="${ROOT}/" '
    NF < 5 { next }
    {
      path = $2; sub("^" root, "", path)
      printf "  %s:%d  [%s]\n      %s\n", path, $3, $4, $5
      n++
    }
    END { if (n == 0) print "  (keine Treffer)"; printf "  ── %d Treffer\n", n+0 }
  '
}

echo "=============================================================================="
echo "  doc_lint — Prüfzug 4 / Doc-Korrektur / Teil 2"
echo "  Bereich: ${SCOPE_LABEL}"
echo "  Dateien gescannt: ${#FILES[@]}  (*.md, *.lean; ohne .lake/.git/.claude)"
echo "=============================================================================="
echo
echo "── Gruppe (A) SUPERLATIV — Rang-Ansprüche ────────────────────────────────────"
printf '%s\n' "$BLOCK_A" | fmt
echo
echo "── Gruppe (B) ZFC-RÜCKFALL — Wort + ZFC-Trigger im Fenster ±1 ────────────────"
echo "     Wörter:   unabhängig | Unabhängigkeit | independent | independence"
echo "     Trigger:  ZFC | Zermelo   (verengt — Nachschlag Teil 3)"
printf '%s\n' "$BLOCK_B" | fmt
echo
echo "── Ende Report.  Exit 0 (Report, kein Bruch). ────────────────────────────────"

exit 0
