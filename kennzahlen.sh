#!/usr/bin/env bash
# =============================================================================
# kennzahlen.sh — alle Kennzahlen des Korpus in EINEM Lauf, jede mit ihrer Route
# -----------------------------------------------------------------------------
# Zweck: die Handmessungen ersetzen, die bisher je Zug einzeln gefahren wurden.
# Jede Zahl steht neben der Route, die sie erzeugt hat — wer sie nachrechnen
# will, liest die Route hier und muss sie nicht aus CLAUDE.md rekonstruieren.
#
# GEPRUEFT WIRD IN GLEICHUNGEN, NICHT IN ZAHLEN (CLAUDE.md §12 Regel 2). Vier
# Gleichungen laufen mit; faellt eine, ist der Exit-Code 1 und die Zahlen sind
# nicht zu verwenden.
#
# Die Wachen-Gleichung ist zugleich die eingebaute Gegenprobe auf eine
# UNVERFOLGTE Datei: die grep-Routen sehen den Arbeitsbaum, die Huellenrechnung
# laeuft ueber `git ls-files`. Eine neue .lean-Datei ohne `git add` laesst die
# Gleichung darum sofort fallen. Mit eingesetztem Treffer geprueft: ein temporaeres
# Modul mit einem Satz und einer Wache ergab unverfolgt 569 gegen 568 (Exit 1),
# verfolgt 569 gegen 569, nach dem Entfernen wieder 568 gegen 568.
#
# Aufruf:
#   ./kennzahlen.sh            schnell — alles ausser Bau und Lint
#   ./kennzahlen.sh --bau      zusaetzlich lake build (Jobs, Gate-Konstanten)
#   ./kennzahlen.sh --lint     zusaetzlich doc_lint.sh (Gruppensummen)
#   ./kennzahlen.sh --alles    beides
#   ./kennzahlen.sh --tsv      nur Name<TAB>Wert, fuer Weiterverarbeitung
#
# Die Werte gelten am ausgewiesenen Commit. Kennzahlen gehoeren NICHT in diese
# Datei und nicht in CLAUDE.md — hier stehen nur die Routen.
# =============================================================================
set -u
cd "$(dirname "$0")" || exit 2

BAU=0; LINT=0; TSV=0
for a in "$@"; do
  case "$a" in
    --bau) BAU=1 ;;
    --lint) LINT=1 ;;
    --alles) BAU=1; LINT=1 ;;
    --tsv) TSV=1 ;;
    -h|--help) sed -n '2,21p' "$0"; exit 0 ;;
    *) echo "unbekanntes Argument: $a" >&2; exit 2 ;;
  esac
done

FEHLER=0
declare -a TSVZEILEN=()

k() { # k NAME WERT ROUTE
  TSVZEILEN+=("$1	$2")
  [ "$TSV" = 1 ] && return
  printf '  %-34s %10s   %s\n' "$1" "$2" "$3"
}
ueberschrift() { [ "$TSV" = 1 ] || printf '\n── %s %s\n' "$1" "$(printf '─%.0s' $(seq 1 $((72 - ${#1}))))"; }
gleichung() { # gleichung TEXT LINKS RECHTS
  local ok="✓"
  if [ "$2" != "$3" ]; then ok="✗ FAELLT"; FEHLER=1; fi
  TSVZEILEN+=("gleichung.$1	$2=$3")
  [ "$TSV" = 1 ] && return
  printf '  %-34s %10s   %s\n' "Gleichung $1" "$ok" "$2 gegen $3"
}

# --- Stand ------------------------------------------------------------------
COMMIT=$(git rev-parse --short HEAD 2>/dev/null || echo '—')
DIRTY=$(git status --porcelain 2>/dev/null | wc -l | tr -d ' ')
[ "$DIRTY" = 0 ] && SAUBER="sauber" || SAUBER="$DIRTY geaenderte Dateien — Werte gelten NICHT am Commit"

if [ "$TSV" = 0 ]; then
  echo "=============================================================================="
  echo "  kennzahlen.sh — Stand $COMMIT ($SAUBER)"
  echo "  $(date '+%Y-%m-%d %H:%M')"
  echo "=============================================================================="
fi

# --- Bestand ----------------------------------------------------------------
ueberschrift "BESTAND"

MODULE=$(git ls-files '*.lean' | wc -l | tr -d ' ')
UNTRACKED=$(git ls-files --others --exclude-standard '*.lean' | wc -l | tr -d ' ')
k "Module (.lean, verfolgt)" "$MODULE" "git ls-files '*.lean' — schliesst die Wurzeldatei Reformulation.lean ein"
[ "$UNTRACKED" != 0 ] && k "Module unverfolgt" "$UNTRACKED" "WARNUNG: erst verfolgen, dann messen (CLAUDE.md §3)"

SAETZE=$(grep -rhE '^((private|protected|nonrec) +)?(@\[[^]]*\] +)?(theorem|lemma) ' --include='*.lean' Reformulation/ | wc -l | tr -d ' ')
SAETZE_SCHARF=$(grep -rhE '^((private|protected|nonrec) +)?(@\[[^]]*\] +)?(theorem|lemma) [^ ]+( *[({[⦃:]|$)' --include='*.lean' Reformulation/ | wc -l | tr -d ' ')
k "Saetze gesamt" "$SAETZE" "geweitete grep-Satzroute ueber Reformulation/ allein (CLAUDE.md §3)"
k "Saetze, verschaerfte Route" "$SAETZE_SCHARF" "Gegenprobe: nach dem Namen muss ( { [ ⦃ : oder Zeilenende folgen"

DEFS=$(grep -rhE '^((private|protected|nonrec) +)?(@\[[^]]*\] +)?def ' --include='*.lean' Reformulation/ | wc -l | tr -d ' ')
k "def-Deklarationen" "$DEFS" "geweitete def-Route ueber Reformulation/"

PINS=$(grep -rh '^-- STATEMENT-PIN' --include='*.lean' Reformulation/ | wc -l | tr -d ' ')
k "Statement-Pins" "$PINS" "grep '^-- STATEMENT-PIN' (Prosa-Kriterien sind eine Zeitbombe, §3)"

# --- Wachen -----------------------------------------------------------------
ueberschrift "WACHEN"

WACHEN_GESCHRIEBEN=$(grep -rhE '#guard_msgs.*in #print axioms' --include='*.lean' Reformulation/ Foreign/ | wc -l | tr -d ' ')
WACHEN_DATEIEN=$(grep -rlE '#guard_msgs.*in #print axioms' --include='*.lean' Reformulation/ Foreign/ | wc -l | tr -d ' ')
k "Wachen geschrieben" "$WACHEN_GESCHRIEBEN" "grep '#guard_msgs.*in #print axioms' ueber Reformulation/ UND Foreign/"
k "davon Dateien" "$WACHEN_DATEIEN" "dieselbe Route, -l"

NACKT=$(grep -rh '^#print axioms' --include='*.lean' Reformulation/ Foreign/ | wc -l | tr -d ' ')
k "nackte #print axioms" "$NACKT" "gedruckt ist nicht gewacht (§8 Fallstrick 16); Lint-Gruppe (D) bricht darauf"

# --- Huellen, Partition, erzwungene Wachen ----------------------------------
ueberschrift "IMPORT-HUELLEN"

HUELLEN=$(python3 - <<'PY'
import os, re, subprocess, sys

root = os.getcwd()
paths = subprocess.run(['git','ls-files','*.lean'], capture_output=True, text=True).stdout.split()
mods = {}
for rel in paths:
    name = rel[:-5].replace('/', '.')
    mods[name] = rel

imp = {}
for n, p in mods.items():
    try:
        s = open(p, encoding='utf-8').read()
    except OSError:
        s = ''
    imp[n] = [m for m in re.findall(r'^import\s+(\S+)', s, re.M) if m in mods]

def hull(rs):
    seen, st = set(), list(rs)
    while st:
        x = st.pop()
        if x in seen or x not in mods:
            continue
        seen.add(x); st += imp[x]
    return seen

# Targets aus lakefile.toml — roots je lean_lib; ohne roots ist der Name die Wurzel.
cfg = open('lakefile.toml', encoding='utf-8').read()
cfg = re.sub(r'(?m)^\s*#.*$', '', cfg)
defaults = re.findall(r'defaultTargets\s*=\s*\[(.*?)\]', cfg, re.S)
defaults = re.findall(r'"([^"]+)"', defaults[0]) if defaults else []
libs = {}
for blk in cfg.split('[[lean_lib]]')[1:]:
    nm = re.search(r'name\s*=\s*"([^"]+)"', blk)
    if not nm:
        continue
    nm = nm.group(1)
    rts = re.search(r'roots\s*=\s*\[(.*?)\]', blk, re.S)
    libs[nm] = re.findall(r'"([^"]+)"', rts.group(1)) if rts else [nm]

agg   = hull(libs.get('Reformulation', []))
gate  = hull(libs.get('AxiomGate', []))
dflt  = set()
for n in defaults:
    dflt |= hull(libs.get(n, []))
frz   = hull(libs.get('PathC', []))
ruf   = set()
for n, r in libs.items():
    if n in defaults:
        continue
    ruf |= hull(r)
A = agg
B = dflt - agg
C = ruf - dflt
D = set(mods) - dflt - ruf

wache = re.compile(r'#guard_msgs.*in #print axioms')
satz  = re.compile(r'^((private|protected|nonrec) +)?(@\[[^]]*\] +)?(theorem|lemma) ', re.M)

def zaehl(menge, rx):
    n = 0
    for m in menge:
        try:
            n += len(rx.findall(open(mods[m], encoding='utf-8').read()))
        except OSError:
            pass
    return n

# wachenfreie Aggregat-Module: Einheit ist das Modul (nicht der Satz)
frei_mod, frei_satz = 0, 0
for m in A:
    try:
        s = open(mods[m], encoding='utf-8').read()
    except OSError:
        continue
    ns = len(satz.findall(s))
    if ns and not wache.search(s):
        frei_mod += 1
        frei_satz += ns

print('\n'.join([
    f"module\t{len(mods)}",
    f"aggregat\t{len(A)}",
    f"mitgebaut\t{len(B)}",
    f"nurruf\t{len(C)}",
    f"keintarget\t{len(D)}",
    f"gate\t{len(gate)}",
    f"eingefroren\t{len(frz - dflt)}",
    f"wachen_erzwungen\t{zaehl(dflt, wache)}",
    f"wachen_aussen\t{zaehl(set(mods) - dflt, wache)}",
    f"saetze_aggregat\t{zaehl(A, satz)}",
    f"frei_module\t{frei_mod}",
    f"frei_saetze\t{frei_satz}",
    f"keintarget_namen\t{','.join(sorted(D)) if D else '—'}",
]))
PY
)
[ -z "$HUELLEN" ] && { echo "  FEHLER: Huellenrechnung lieferte nichts" >&2; exit 2; }
g() { echo "$HUELLEN" | awk -F'\t' -v k="$1" '$1==k{print $2}'; }

M_GES=$(g module); M_AGG=$(g aggregat); M_MIT=$(g mitgebaut); M_RUF=$(g nurruf); M_KEIN=$(g keintarget)
M_GATE=$(g gate); W_ERZ=$(g wachen_erzwungen); W_AUS=$(g wachen_aussen)
S_AGG=$(g saetze_aggregat); F_MOD=$(g frei_module); F_SATZ=$(g frei_saetze)

k "Aggregat" "$M_AGG" "Huelle der Wurzel Reformulation.lean"
k "mitgebaut" "$M_MIT" "ueber ein Default-Target erreicht, ausserhalb der Aggregathuelle"
k "nur auf Ruf" "$M_RUF" "nur ueber ein eigenes Target gebaut"
k "kein Target" "$M_KEIN" "$(g keintarget_namen)"
k "Gate-Huelle" "$M_GATE" "Huelle von Reformulation/AxiomGate.lean"
k "Saetze im Aggregat" "$S_AGG" "Satzroute, auf die Aggregathuelle eingeschraenkt"
k "Wachen erzwungen" "$W_ERZ" "Wachenroute, auf die Huelle der Default-Targets eingeschraenkt"
k "Wachen ausserhalb" "$W_AUS" "geschrieben, aber von keinem Default-Target erfasst — sichern nichts"
k "wachenfreie Aggregat-Module" "$F_MOD" "Aggregat-Module mit Saetzen und ohne jede Wache (Einheit: Modul)"
k "  darin Saetze" "$F_SATZ" "nachrichtlich; die tragende Zahl ist die Modulzahl darueber"

gleichung "Partition" "$M_GES" "$((M_AGG + M_MIT + M_RUF + M_KEIN))"
gleichung "Gate=Aggregat+1" "$M_GATE" "$((M_AGG + 1))"
gleichung "Wachen" "$WACHEN_GESCHRIEBEN" "$((W_ERZ + W_AUS))"

if [ "$SAETZE" -lt "$SAETZE_SCHARF" ]; then
  gleichung "Satzroute" "weit<scharf" "unmoeglich"
else
  gleichung "Satzroute" "ok" "ok"
  [ "$TSV" = 0 ] && [ "$SAETZE" != "$SAETZE_SCHARF" ] && \
    printf '  %-34s %10s   %s\n' "  Differenz weit/scharf" "$((SAETZE - SAETZE_SCHARF))" "Umbruch schiebt ein Deklarationswort an den Zeilenanfang (§3)"
fi

# --- Luecken ----------------------------------------------------------------
ueberschrift "LUECKEN (selbstzaehlend — Prosa zaehlt mit, mit Absicht)"

LUECKEN=$(python3 - <<'PY'
import re, subprocess
rx = re.compile(r'\bsorry\b')
alle = subprocess.run(['git','ls-files'], capture_output=True, text=True).stdout.split()
n1 = n1lean = z1 = 0
for f in alle:
    try:
        s = open(f, encoding='utf-8', errors='ignore').read()
    except OSError:
        continue
    t = len(rx.findall(s))
    if not t:
        continue
    n1 += t
    z1 += sum(1 for zeile in s.split('\n') if rx.search(zeile))
    if f.endswith('.lean'):
        n1lean += t
print(f"n1\t{n1}\nn1lean\t{n1lean}\nzeilen\t{z1}")
PY
)
N1=$(echo "$LUECKEN" | awk -F'\t' '$1=="n1"{print $2}')
N1LEAN=$(echo "$LUECKEN" | awk -F'\t' '$1=="n1lean"{print $2}')
N1ZEILEN=$(echo "$LUECKEN" | awk -F'\t' '$1=="zeilen"{print $2}')
k "N1 roh" "$N1" "WORTvorkommen (\\bsorry\\b) ueber den verfolgten Bestand; zaehlt die eigene Dokumentation mit"
k "  davon .lean" "$N1LEAN" "dieselbe Route, auf *.lean eingeschraenkt"
k "Zeilen mit Vorkommen" "$N1ZEILEN" "ANDERE FRAGE als N1 (git grep -cw); nie als N1 lesen (§8 Fallstrick 9)"

# --- Ledger -----------------------------------------------------------------
if [ -f docs/definition-ledger.md ] && [ -f Reformulation/Proemial/DefinitionLedger.lean ]; then
  ueberschrift "DEFINITION-LEDGER"
  L_ZEILEN=$(grep -cE '^\| *L[0-9]' docs/definition-ledger.md)
  L_REFS=$(grep -cE '^#ledger_[a-zA-Z]+' Reformulation/Proemial/DefinitionLedger.lean)
  k "Ledger-Zeilen" "$L_ZEILEN" "Zeilen-IDs in docs/definition-ledger.md"
  k "Referenzen im Bau" "$L_REFS" "jedes #ledger_*-Kommando in DefinitionLedger.lean (auch #ledger_setzung)"
fi

# --- Optional: Bau ----------------------------------------------------------
if [ "$BAU" = 1 ]; then
  ueberschrift "BAU (lake build)"
  OUT=$(lake build 2>&1)
  JOBS=$(echo "$OUT" | grep -oE 'Build completed successfully \([0-9]+ jobs\)' | grep -oE '[0-9]+' | head -1)
  GATEK=$(echo "$OUT" | grep -oE '\([0-9]+ geprüfte' | grep -oE '[0-9]+' | head -1)
  if [ -n "$JOBS" ]; then
    k "Build-Jobs" "$JOBS" "lake build ueber die Default-Targets"
  else
    k "Build-Jobs" "ROT" "lake build ist nicht gruen durchgelaufen"; FEHLER=1
  fi
  [ -n "$GATEK" ] && k "geprueft (AxiomGate)" "$GATEK" "Konstanten aus dem Importbaum, namensgefiltert auf Reformulation.*"
fi

# --- Optional: Lint ---------------------------------------------------------
if [ "$LINT" = 1 ] && [ -x ./doc_lint.sh ]; then
  ueberschrift "DOC-LINT"
  LOUT=$(./doc_lint.sh 2>&1); LRC=$?
  i=0
  while IFS= read -r z; do
    i=$((i+1))
    case $i in
      1) k "(A.1) laufender Bestand" "$(echo "$z" | grep -oE '[0-9]+')" "Superlativ, meldend" ;;
      2) k "(A.2) eingefrorene Fassungen" "$(echo "$z" | grep -oE '[0-9]+')" "duerfen nicht geheilt werden" ;;
      3) k "(B) ZFC-Rueckfall" "$(echo "$z" | grep -oE '[0-9]+')" "meldend" ;;
    esac
  done < <(echo "$LOUT" | grep -E '^  ── [0-9]+ Treffer')
  k "doc_lint Exit" "$LRC" "0 heisst: (C), (D) und (E) ohne Verstoss"
  [ "$LRC" != 0 ] && FEHLER=1
fi

# --- Abschluss --------------------------------------------------------------
if [ "$TSV" = 1 ]; then
  printf '%s\n' "${TSVZEILEN[@]}"
  exit $FEHLER
fi

echo
if [ "$FEHLER" = 0 ]; then
  echo "── Alle Gleichungen halten. Werte gelten am Commit $COMMIT."
else
  echo "── MINDESTENS EINE GLEICHUNG FAELLT. Die Zahlen oben sind nicht zu verwenden."
fi
[ "$DIRTY" != 0 ] && echo "   Arbeitsbaum nicht sauber — kein Wert ist an $COMMIT verankert."
exit $FEHLER
