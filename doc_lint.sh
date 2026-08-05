#!/usr/bin/env bash
# =============================================================================
# doc_lint.sh — Doc-Lint für den PKL-Korpus (Prüfzug 4, Doc-Korrektur, Teil 2)
# -----------------------------------------------------------------------------
# Zwei Wortgruppen, getrennt ausgewiesen:
#   (A) SUPERLATIV      — Rang-Ansprüche ohne Ist-Prüfung
#                         (Hausregel: keine „erstmals/einzige/seit F-1" o. Ä.)
#                         [Vorgang 9] deutsche UND englische Muster in derselben
#                         Gruppe — siehe SUPERLATIV_RE unten.
#                         [Vorgang 10] (A) wird in ZWEI Zeilen ausgewiesen:
#                         laufender Bestand und eingefrorene Fassungen
#                         (docs/rev1/**, seit der Rev3-Ausgabe auch
#                         docs/rev2/**). Grund: die eingefrorenen Treffer
#                         dürfen nicht geheilt werden — Vorgang 7 sichert deren
#                         Byte-Gleichheit zu. Liefen sie in derselben Zahl mit,
#                         wüchse ein Wert, den niemand senken darf, und ein
#                         unsenkbarer Wert wird bald nicht mehr gelesen.
#                         Das ersetzt die Vorgang-9-Zusage „genau eine
#                         Trefferzahl"; sie galt, solange es keine
#                         eingefrorenen Dateien im Prüfbereich gab.
#   (B) ZFC-RÜCKFALL    — „unabhängig/Unabhängigkeit/independent/independence",
#                         NUR gemeldet bei Nähe (±1 Zeile) zu einem der
#                         ZFC-Trigger (ZFC, Zermelo).  [Nachtrag (2a);
#                         Nachschlag Teil 3: Trigger auf ZFC|Zermelo verengt —
#                         Axiom(e)/axiomatisch/ableitbar sind in diesem Korpus
#                         Leitthema (15/62/70 benigne Treffer) und erzeugten nur
#                         Rauschen.]
#
#   [Vorgang 10] Beide Gruppen laufen FALLUNEMPFINDLICH. Bis dahin traf weder
#   „Unabhängigkeit" noch „Independence" — zwei der vier oben ausgewiesenen
#   (B)-Wörter —, weil sie in der Praxis groß beginnen; und (A) verfehlte jede
#   satzinitiale Form. Jede vor Vorgang 10 berichtete (A)- und (B)-Zahl ist
#   darum eine untere Schranke und keine Zählung.
#
#   Ausschluss-Liste [Nachschlag Teil 3]: Dateien, die die Rückfall-Regel
#   *definieren*, schlagen nicht auf ihrer eigenen Definition an (Namens-Muster,
#   keine starre Liste) — siehe EXCLUDE_GLOBS unten.
#
# Lauf-Bereich  [Nachtrag (2b)]:
#   - ohne Argument      → Default = das Repo (Verzeichnis dieses Skripts).
#   - mit Argument       → doc_lint.sh <pfad>  läuft über <pfad> (Außentexte).
#
# Exit-Code  [Nachtrag (2c); geändert mit dem Kennzahl-Konsistenz-Zug]:
#   - Gruppen (A) und (B) MELDEN und beeinflussen den Exit-Code nicht. Ein
#     Rang-Anspruch ist Ermessenssache und will gelesen, nicht erzwungen werden;
#     ein brechender Lint wird umgangen, ein meldender wird gelesen.
#   - Gruppe (C) BRICHT: mindestens ein Verstoß gegen R3 bis R8 setzt Exit 1.
#     Dort ist nichts zu ermessen — ein Widerspruch zwischen der Ledger-Tabelle
#     und der Referenzdatei, eine fehlende Referenz, eine doppelte Zeilen-ID
#     sind objektiv falsch, und wer sie stehen lässt, veröffentlicht eine
#     ungeprüfte Tabelle.
#   - Der Report sagt am Ende, welcher Code aus welchem Grund gesetzt wird.
#
# Hinweis zur Herkunft: es lag keine Basis-`doc_lint.sh` vor; Gruppe (A) ist
# aus der dokumentierten Hausregel rekonstruiert und bewusst konservativ
# (Rang-Phrasen, nicht das blanke Adjektiv „erste").
#
# [Vorgang 10] Hier stand ein Satz, der Gruppe (B) als „maßgeblich für die
# Rückgabe" auswies. Er stammte aus einer Fassung vor dem Kennzahl-Konsistenz-Zug
# und widersprach dem Abschnitt „Exit-Code" sechs Zeilen weiter oben; der Code
# folgte stets dem Abschnitt und nie diesem Satz. Gestrichen und nicht
# umgeschrieben — er beschrieb keinen Zustand mehr, den es gibt.
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
# BETRIEBSART [Vorgang 10]: alle drei Muster werden gegen `tolower($0)` geprüft
# und sind darum DURCHGEHEND KLEIN zu schreiben. Ein Großbuchstabe in einem
# Muster kann nach der Umstellung nie mehr treffen — das gilt besonders für den
# Trigger, der vorher `ZFC|Zermelo` hieß und gegen eine kleingeschriebene Zeile
# stumm geblieben wäre. Gruppe (B) wäre still auf 0 gefallen.
#
# `tolower` ist LOCALE-ABHÄNGIG, nicht byteweise. Gemessen an derselben Zeile,
# BWK-awk 20200816:
#     LANG=C.UTF-8   UNABHÄNGIGKEIT -> unabhängigkeit   (trifft)
#     LC_ALL=C       UNABHÄNGIGKEIT -> unabhÄngigkeit   (trifft NICHT)
# Unter einer C-Locale entkäme also jede durchgehend groß geschriebene deutsche
# Form still der Gruppe. Am Bestand ist das heute FOLGENLOS — es gibt keine
# solche Form, und der Lint liefert unter beiden Locales dieselben Zahlen (an
# diesem Commit gemessen). Es ist Vorsorge und keine offene Lücke.
#
# Wer den Lint in eine fremde Umgebung stellt (CI, Container, fremde Shell),
# prüft `locale` mit: eine C-Locale macht die deutsche Hälfte von (B) für
# Versalien blind. Die Muster werden deswegen NICHT um Versalienvarianten
# erweitert — das verlegte eine Umgebungseigenschaft in die Wortliste, wo
# niemand sie sucht.
#
# (B) ZFC-Rückfall-Wörter (Stämme; fangen Flexionen mit):
#     unabhängig → unabhängig(e/er/keit ...);  independen → independent/independence
#     [Vorgang 10] `unabh(ä|ae)ngig` fängt auch die ASCII-transliterierte
#     Schreibweise. Der Bestand führt beide Konventionen: `README.md` und
#     `CLAUDE.md` sind transliteriert, die Lean-Doc-Strings tragen Umlaute.
#     Vorher war die deutsche Hälfte der Gruppe für jede transliterierte Datei
#     blind. BEWUSST minimal: keine allgemeine Transliterationsnormalisierung —
#     die erzeugte Fehlalarme, wo `ae`/`oe`/`ue` regulär vorkommen, und trüge
#     mehr Annahmen, als sie prüft.
RUECKFALL_RE='unabh(ä|ae)ngig|independen'
# (B) ZFC-Trigger im Nähe-Fenster ±1 Zeile [Nachschlag Teil 3: verengt]:
#     Klein geschrieben, siehe BETRIEBSART.
TRIGGER_RE='zfc|zermelo'
# (A) Superlativ-/Rang-Phrasen (konservativ), deutsch und englisch in EINER Gruppe:
#     Eine getrennte Gruppe erzeugte zwei Zaehlstaende fuer dieselbe Frage; (A) gibt
#     weiterhin genau eine Trefferzahl aus.
#
#     Englische Muster [Vorgang 9]: an `docs/rev1/en.html` gemessen, bevor sie hier
#     standen — der einzigen umfangreichen englischen Prosa im Baum. Treffer dort:
#       for the first time 0 · the first to 1 · the only 0 · never before 0 · no other 0
#     Der eine Treffer ist eine ERWAEHNUNG (der Satz, der diese Musterliste beschreibt),
#     keine Verwendung — genau die Klasse von Fehlalarm, derentwegen (A) meldet und nicht
#     bricht. Geprueft und verworfen: `the first` (gewoehnliche Prosa: "the first half",
#     "the first mark"), `unique` (mathematische Aussage: "retraction is unique"),
#     `sole(ly)` ("classified solely by which places repeat which"), `uniquely` (ohne
#     Beleg im Bestand — nicht auf Verdacht aufgenommen).
#
#     KEIN `\b`: die awk-Regex-Maschine fuehrt keine Wortgrenze (CLAUDE.md §8,
#     Fallstrick 9). Die Muster sind darum mehrwortig und tragen ihre Abgrenzung selbst.
#     [Vorgang 10] Das bleibt richtig und wird durch die Fallunempfindlichkeit
#     WICHTIGER: `the only` trifft fallunempfindlich auch in „The Only Way Is Up".
#     Mehrwortige Muster tragen ihre Abgrenzung selbst; einwortige täten es nicht.
#
#     Klein geschrieben, siehe BETRIEBSART oben — `zum ersten mal`, `seit f-1`,
#     `seit f1` sind KEINE Tippfehler.
SUPERLATIV_RE='erstmals|erstmalig|zum ersten mal|als erste[rs]?|einzige[rns]?|seit f-1|seit f1|for the first time|the first to|the only|never before|no other'

# --- Dateiliste -------------------------------------------------------------
# Markdown + Lean-Modul-Docs + HTML; vendored/Meta-Verzeichnisse ausgeschlossen.
# (bash-3.2-kompatibel: kein mapfile; NUL-getrennt einlesen)
#
# [Vorgang 10] `*.html` ist aufgenommen. Bis dahin standen die fünf
# veröffentlichten Fassungen (docs/de.html, docs/en.html, docs/index.html,
# docs/rev1/de.html, docs/rev1/en.html) in KEINER Gruppe — also gerade das,
# was ein fremder Leser zuerst sieht.
#
# SCHWÄCHE DER ROUTE, benannt und nicht versteckt: HTML wird ROH gelesen, ohne
# Markup zu entfernen. Daraus folgt gemessen zweierlei (Route: roh gegen
# markup-entfernt an docs/rev1/en.html):
#   - Treffer INNERHALB einer Auszeichnung werden mitgezählt — `unique` liefert
#     roh 4 und markup-entfernt 3. Ein Fehlalarm; für eine MELDENDE Gruppe ist
#     die Richtung unschädlich.
#   - Treffer, die ÜBER eine Auszeichnungsgrenze hinweglaufen, würden fehlen —
#     `the <em>only</em> carrier` trifft nicht. In der Probe kam kein solcher
#     Fall vor (`the first`: roh 11 = markup-entfernt 11).
# Eine Route mit benannter Schwäche ist etwas anderes als eine mit unbenannter.
# Wer sie schließen will, braucht einen Markup-Entferner — und damit eine
# zweite Route, die selbst gegengerechnet werden müsste.
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
    \( -name '*.md' -o -name '*.lean' -o -name '*.html' \) -type f -print0 \
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
    # [Vorgang 10] Zwei Felder je Zeile: `low` wird geprüft, `orig` berichtet.
    # Der Report muss die Zeile zeigen, wie sie dasteht — nicht kleingeschrieben.
    { orig[NR] = $0; low[NR] = tolower($0) }
    END {
      for (i = 1; i <= NR; i++) {
        L = low[i]
        # ---- (B) ZFC-Rückfall: Wort + Trigger im Fenster ±1 -------------
        if (L ~ RUECK) {
          ctx = low[i-1] "\n" L "\n" low[i+1]
          if (ctx ~ TRIG) {
            # Welche Trigger-Zeile? (für den Report vermerken)
            where = "diese Zeile"
            if (low[i-1] ~ TRIG) where = "Zeile davor"
            else if (low[i+1] ~ TRIG && L !~ TRIG) where = "Zeile danach"
            printf "B\t%s\t%d\t%s\t%s\n", FN, i, where, orig[i]
          }
        }
        # ---- (A) Superlativ: reiner Wort-Match ---------------------------
        if (L ~ SUP) {
          printf "A\t%s\t%d\t%s\t%s\n", FN, i, "-", orig[i]
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

# [Vorgang 10] (A) zerfällt in zwei Zeilen. Die Trennung geschieht am
# PFADPRÄFIX `docs/rev<n>/` und nicht an einer Liste einzelner Dateien — eine
# Liste veraltete beim nächsten Einfrieren. (B) bleibt einzeilig: dort gibt es
# bisher keinen Treffer, und eine Trennung ohne Gegenstand wäre Zierat.
#
# [Papierausgabe Rev3] Das Präfix ist von `docs/rev1/` auf `docs/rev<Ziffer>/`
# geweitet, weil die Rev2-Fassungen mit dieser Ausgabe nach `docs/rev2/`
# archiviert und dort ebenso NICHT mehr nachgeführt werden. Ohne die Weitung
# wäre die Zahl der zu heilenden Treffer beim Archivieren gestiegen, ohne dass
# ein Satz sich bewegt hat — und ein unsenkbarer Wert wird bald nicht mehr
# gelesen. Die Ziffernform trägt die nächste Archivierung mit.
BLOCK_A_LAUF="$(printf '%s\n' "$RAW" | awk -F'\t' -v root="${ROOT}/" \
  '$1=="A" { p=$2; sub("^" root, "", p); if (p !~ /^docs\/rev[0-9]+\//) print }')"
BLOCK_A_FROZ="$(printf '%s\n' "$RAW" | awk -F'\t' -v root="${ROOT}/" \
  '$1=="A" { p=$2; sub("^" root, "", p); if (p ~ /^docs\/rev[0-9]+\//) print }')"
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

# --- (C) Ledger-Regeln R3 bis R6 --------------------------------------------
# Textprüfungen auf der abgelegten Ledger-Tabelle. R1 (Träger löst auf) und R2
# (Trägerstatus gleich Deklarationsart) prüft der Bau über
# Reformulation/Proemial/DefinitionLedger.lean; eine Textprüfung kann die
# Deklarationsart nicht kennen und versucht es hier auch nicht.
# Spaltenordnung: | ID | Begriff | Träger | TS | ZS | Wache | Grenze |
LEDGER="${ROOT}/docs/definition-ledger.md"
ledger_report() {
  if [ ! -f "${LEDGER}" ]; then
    echo "  (docs/definition-ledger.md liegt nicht in diesem Bereich — nicht geprüft)"
    return 0
  fi
  awk -F'|' '
    function trim(s) { gsub(/^[ \t]+|[ \t]+$/, "", s); return s }
    /^\| L[0-9][0-9]-[0-9]+ \|/ {
      id = trim($2); traeger = trim($4); ts = trim($5); zs = trim($6); wache = trim($7)
      par[substr(id, 1, 3)] = 1
      n++
      if (zs == "Theorem") {
        printf "  %s  [R3] Zuordnungsstatus \"Theorem\" ist nicht zulässig\n", id; r3++
      }
      if (ts == "Offen" && traeger != "—" && traeger != "") {
        printf "  %s  [R4] Trägerstatus \"Offen\", aber Trägerspalte gefüllt: %s\n", id, traeger; r4++
      }
      if (ts == "Theorem" && (wache == "—" || wache == "")) {
        printf "  %s  [R6] Trägerstatus \"Theorem\" ohne Wachenangabe\n", id; r6++
      }
    }
    END {
      k = 0
      for (i = 1; i <= 19; i++) {
        p = sprintf("L%02d", i)
        if (p in par) { k++ } else { printf "  §%d  [R5] Paragraph nicht vertreten\n", i; r5++ }
      }
      if (r3 + r4 + r5 + r6 == 0) print "  (keine Verstöße in R3–R6)"
      printf "  ── %d Zeilen geprüft; R3 %d, R4 %d, R5 %d, R6 %d; Paragraphen %d von 19\n", \
             n + 0, r3 + 0, r4 + 0, r5 + 0, r6 + 0, k
      if (r3 + r4 + r5 + r6 > 0) exit 1
    }
  ' "${LEDGER}"
}

# --- (C) Regel R7: Tabelle gegen Referenzdatei ------------------------------
# Die Naht, die der Bau nicht schließt: er prüft die Lean-Datei gegen die
# Umgebung, nicht die Tabelle gegen die Lean-Datei. R7 gleicht beide ab —
# Zeilen-ID, voll expandierter Trägername und Kommando gegen Trägerstatus, in
# beiden Richtungen. Eine verwaiste Referenz ist ebenso ein Verstoß wie eine
# fehlende. Löst ein Kürzel nicht auf, ist das ein eigener Verstoß.
LEDGER_LEAN="${ROOT}/Reformulation/Proemial/DefinitionLedger.lean"
ledger7_report() {
  if [ ! -f "${LEDGER}" ] || [ ! -f "${LEDGER_LEAN}" ]; then
    echo "  (Tabelle oder Referenzdatei liegt nicht in diesem Bereich — R7 nicht geprüft)"
    return 0
  fi
  awk '
    function trim(s) { gsub(/^[ \t]+|[ \t]+$/, "", s); return s }
    function bare(s) { gsub(/`/, "", s); return trim(s) }
    # ---- Datei 1: die Tabelle ------------------------------------------------
    NR == FNR {
      if ($0 ~ /^\| `[A-Za-z]+\.` \|/) {          # Kürzeltafel
        split($0, k, "|")
        kz[bare(k[2])] = bare(k[3])
      }
      if ($0 ~ /^\| L[0-9][0-9]-[0-9]+ \|/) {      # Tabellenzeile
        split($0, c, "|")
        id = bare(c[2]); traeger = bare(c[4]); ts = bare(c[5])
        if (ts != "Offen") {
          mdOrd[++mdN] = id; mdTS[id] = ts
          p = index(traeger, ".")
          pre = (p > 0) ? substr(traeger, 1, p) : ""
          if (pre == "" || !(pre in kz)) {
            printf "  %s  [R7] Kürzel \"%s\" steht nicht in der Kürzeltafel\n", id, pre
            v++; mdName[id] = "?"
          } else {
            mdName[id] = kz[pre] substr(traeger, p + 1)
          }
        }
      }
      next
    }
    # ---- Datei 2: die Referenzdatei ------------------------------------------
    /^#ledger_(theorem|def|setzung) / {
      id = $2; gsub(/"/, "", id)
      if (!(id in leanCmd)) { leanOrd[++leanN] = id }   # Doppelte meldet R8
      leanCmd[id] = $1; leanName[id] = $3
    }
    END {
      erw["Theorem"] = "#ledger_theorem"
      erw["Definition"] = "#ledger_def"
      erw["Setzung"] = "#ledger_setzung"
      for (i = 1; i <= mdN; i++) {
        id = mdOrd[i]
        if (!(id in leanCmd)) {
          printf "  %s  [R7] Tabellenzeile mit Träger, aber keine Referenz in der Referenzdatei\n", id
          v++; continue
        }
        ok = 1
        if (mdName[id] != "?" && leanName[id] != mdName[id]) {
          printf "  %s  [R7] Trägername verschieden — Tabelle: %s, Referenzdatei: %s\n", \
                 id, mdName[id], leanName[id]
          v++; ok = 0
        }
        if (leanCmd[id] != erw[mdTS[id]]) {
          printf "  %s  [R7] Trägerstatus \"%s\" erwartet %s, in der Referenzdatei steht %s\n", \
                 id, mdTS[id], erw[mdTS[id]], leanCmd[id]
          v++; ok = 0
        }
        if (ok && mdName[id] != "?") paare++
      }
      for (i = 1; i <= leanN; i++) {
        id = leanOrd[i]
        if (!(id in mdTS)) {
          printf "  %s  [R7] Referenz ohne Tabellenzeile mit Träger (verwaist)\n", id
          v++
        }
      }
      if (v + 0 == 0) print "  (keine Verstöße in R7)"
      printf "  ── R7 %d Verstöße; %d abgeglichene Paare (Tabelle %d, Referenzdatei %d)\n", \
             v + 0, paare + 0, mdN + 0, leanN + 0
      if (v + 0 > 0) exit 1
    }
  ' "${LEDGER}" "${LEDGER_LEAN}"
}

# --- (C) Regel R8: Eindeutigkeit der Zeilen-IDs -----------------------------
# Eine doppelte ID entsteht beim Einfügen einer Zeile leicht, und sie ist
# tückisch: R7 hält je ID einen Eintrag, die zweite überschreibt die erste, und
# eine Zeile bliebe still ungeprüft. R8 zählt darum jede ID in beiden Dateien
# und nennt bei einer Doppelung beide Fundstellen.
ledger8_report() {
  if [ ! -f "${LEDGER}" ] || [ ! -f "${LEDGER_LEAN}" ]; then
    echo "  (Tabelle oder Referenzdatei liegt nicht in diesem Bereich — R8 nicht geprüft)"
    return 0
  fi
  awk '
    function trim(s) { gsub(/^[ \t]+|[ \t]+$/, "", s); return s }
    NR == FNR {
      if ($0 ~ /^\| L[0-9][0-9]-[0-9]+ \|/) {
        split($0, c, "|"); id = trim(c[2])
        if (id in mdLine) {
          printf "  %s  [R8] Zeilen-ID doppelt in der Tabelle — Zeile %d und Zeile %d\n", \
                 id, mdLine[id], FNR
          v++
        } else { mdLine[id] = FNR; mdN++ }
      }
      next
    }
    /^#ledger_(theorem|def|setzung) / {
      id = $2; gsub(/"/, "", id)
      if (id in lnLine) {
        printf "  %s  [R8] Referenz doppelt in der Referenzdatei — Zeile %d und Zeile %d\n", \
               id, lnLine[id], FNR
        v++
      } else { lnLine[id] = FNR; lnN++ }
    }
    END {
      if (v + 0 == 0) print "  (keine Verstöße in R8)"
      printf "  ── R8 %d Verstöße; %d eindeutige IDs in der Tabelle, %d in der Referenzdatei\n", \
             v + 0, mdN + 0, lnN + 0
      if (v + 0 > 0) exit 1
    }
  ' "${LEDGER}" "${LEDGER_LEAN}"
}

# Gruppe (C) vorab fahren: ihre Rückgabecodes bestimmen den Exit-Code des Laufs.
C_RC=0
BLOCK_C1="$(ledger_report)"  || C_RC=1
BLOCK_C2="$(ledger7_report)" || C_RC=1
BLOCK_C3="$(ledger8_report)" || C_RC=1

echo "=============================================================================="
echo "  doc_lint — Prüfzug 4 / Doc-Korrektur / Teil 2"
echo "  Bereich: ${SCOPE_LABEL}"
echo "  Dateien gescannt: ${#FILES[@]}  (*.md, *.lean, *.html; ohne .lake/.git/.claude)"
# [Vorgang 11] Die Locale wird BERICHTET, nicht gesetzt. Die Fallunempfindlichkeit
# ist locale-abhaengig gemessen (Befund Vorgang 10 §5); eine Messung, deren Ergebnis
# von der Umgebung abhaengt, traegt ihre Bedingung mit — wie jede andere Zahl dieses
# Korpus. KEIN `export LC_ALL=C.UTF-8`: ob diese Locale auf der Zielmaschine
# existiert, ist ungemessen, und ein export, der ins Leere greift, ersetzte eine
# gemeldete Abhaengigkeit durch eine stille. Wer es dennoch will, misst zuerst
# `locale -a`.
echo "  Locale: ${LC_ALL:-${LANG:-nicht gesetzt}}"
echo "    (unter LC_ALL=C entkaemen Versalienformen der Stichwoerter der Gruppe B)"
echo "=============================================================================="
echo
echo "── Gruppe (A) SUPERLATIV — Rang-Ansprüche ────────────────────────────────────"
echo "     deutsch:   erstmals | erstmalig | zum ersten Mal | als erste(r/s) | einzige(r/n/s)"
echo "                seit F-1 | seit F1"
echo "     englisch:  for the first time | the first to | the only | never before | no other"
echo "     Fallbehandlung: UNEMPFINDLICH (tolower; locale-abhaengig, siehe Kopf)"
echo
echo "   (A.1) laufender Bestand — hier wird geheilt:"
printf '%s\n' "$BLOCK_A_LAUF" | fmt
echo
echo "   (A.2) eingefrorene Fassungen unter docs/rev<Ziffer>/ — NICHT zu heilen:"
echo "         Die Route ist das Präfix, nicht eine Liste der Revisionen: jede"
echo "         archivierte Fassung faellt automatisch hierher. Vorgang 7 sichert die"
echo "         Byte-Gleichheit der ersten Fassung zu; jede weitere ist mit ihrer"
echo "         Nachfolge-Ausgabe ebenso stillgelegt. Die Beurteilung dieser Treffer"
echo "         ist einmal erfolgt und festgeschrieben (Befund Vorgang 10); kuenftige"
echo "         Befunde nennen nur die Zahl und verweisen."
printf '%s\n' "$BLOCK_A_FROZ" | fmt
echo
echo "── Gruppe (B) ZFC-RÜCKFALL — Wort + ZFC-Trigger im Fenster ±1 ────────────────"
echo "     Wörter:   unabhängig | Unabhängigkeit | unabhaengig | independent | independence"
echo "     Trigger:  ZFC | Zermelo   (verengt — Nachschlag Teil 3)"
echo "     Fallbehandlung: UNEMPFINDLICH (tolower; locale-abhaengig, siehe Kopf); Transliteration mitgefasst"
printf '%s\n' "$BLOCK_B" | fmt
echo
echo "── Gruppe (C) LEDGER-REGELN R3–R8 — docs/definition-ledger.md ────────────────"
echo "     R3 kein Zuordnungsstatus \"Theorem\" · R4 Trägerstatus \"Offen\" erzwingt leere"
echo "     Trägerspalte · R5 alle 19 Paragraphen vertreten · R6 Trägerstatus \"Theorem\""
echo "     erzwingt ausgefüllte Wachenspalte.  (R1/R2 prüft der Bau, nicht der Lint.)"
echo "     R7 jede Trägerzeile der Tabelle hat genau eine passende Referenz in"
echo "     Reformulation/Proemial/DefinitionLedger.lean — und umgekehrt."
echo "     R8 jede Zeilen-ID kommt in beiden Dateien genau einmal vor."
printf '%s\n' "$BLOCK_C1"
printf '%s\n' "$BLOCK_C2"
printf '%s\n' "$BLOCK_C3"
echo

if [ "${C_RC}" -ne 0 ]; then
  echo "── Ende Report.  Exit 1: Gruppe (C) meldet mindestens einen Verstoß. ─────────"
  echo "   (A) und (B) beeinflussen den Exit-Code nicht — sie melden."
  exit 1
fi
echo "── Ende Report.  Exit 0: Gruppe (C) ohne Verstoß. ───────────────────────────"
echo "   (A) und (B) melden nur; ihre Treffer setzen keinen Exit-Code."

exit 0
