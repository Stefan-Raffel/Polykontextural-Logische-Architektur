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

# --- (D) Gedruckt gegen gewacht ---------------------------------------------
# Ein `#print axioms` ohne `#guard_msgs` in derselben Anweisung druckt ein Profil
# in die Bauausgabe und sichert NICHTS: aendert der Satz sein Profil, druckt es
# das neue und der Bau bleibt gruen. In einer Datei sieht das aus wie eine
# Sicherung. CLAUDE.md §3 unterscheidet *geschrieben* und *erzwungen*; hier liegt
# eine dritte Stufe darunter — *gedruckt gegen gewacht* (Fallstrick 16).
#
# BRECHEND, anders als (A) und (B). Der Befund ist nicht auslegungsbeduerftig:
# entweder steht eine Wache dabei oder nicht. Und die Grundlinie ist null — wer
# einen neuen nackten Aufruf schreibt, hat entweder eine Wache vergessen oder ein
# Werkzeug gebaut; im zweiten Fall traegt die Datei die Marke aus AUSNAHME_RE,
# und das ist eine bewusste Handlung.
#
# ROUTE: Kommentare ZUERST entfernen, dann suchen. Eine grep-Zeile taugt nicht —
# das Suchwort steht in Prosa und seit den Wachen auch in den eingefrorenen
# Erwartungstexten; die naive Differenz misst zu hoch. Entfernt werden `--` bis
# Zeilenende und `/- … -/` VERSCHACHTELT (einschliesslich `/--` und `/-!`);
# Strings werden uebersprungen. Was danach bleibt, ist Kommando-Text.
#
# PRUEFBEREICH: `.lean` allein — dieselben Dateien wie die Satz- und Wachenrouten.
# Markdown ist NICHT im Bereich; das ist gemessen (Zug-A-Befund §5.6) und der
# Grund, warum der Fallstricktext in CLAUDE.md seine eigene Route nicht bewegt.
#
# AUSSCHLUSS als Marke im Dateikopf und nicht als Dateiliste: die Praezedenz ist
# der Archiv-Ausschluss, der auf `docs/rev<n>/` geweitet wurde, statt Revisionen
# aufzuzaehlen. Ein Verzeichnis-Ausschluss traegt hier NICHT — `Diagnostics/`
# enthaelt neben den zwei Werkzeugen auch `HeteroreferenzProbe.lean`, eine Sonde,
# deren sieben Saetze in Zug B gewacht wurden; ein Verzeichnisschnitt naehme sie
# still mit heraus. Die Marke waechst dagegen mit: ein drittes Werkzeug traegt
# sie und braucht keine Aenderung an diesem Skript.
#
# Die Marke wird am ROHEN Text gesucht, vor dem Entfernen der Kommentare — sie
# steht in einem `--`-Kommentar und waere danach fort. Sie fuehrt den Suchbegriff
# absichtlich NICHT, damit sie sich nicht selbst meldet.
AUSNAHME_RE='^-- LINT-AUSNAHME \(D\):'

# Der Kern-Scanner. Gibt je Fundstelle eine Zeile `KLASSE<TAB>NR<TAB>DATEI<TAB>ZIEL`:
#   B = nackt (bare)   W = gewacht, gleiche Anweisung   S = getrennte Form
# Die getrennte Form (`#guard_msgs` allein auf einer Zeile) kommt im Bestand nicht
# vor — geprueft, null Treffer. Sie gilt als gewacht und wird eigens ausgewiesen,
# damit ein kuenftiger Fall nicht stillschweigend unter W verschwindet.
bare_scan_file() {
  awk -v FN="$1" '
    function blank(s) { return s ~ /^[[:space:]]*$/ }
    BEGIN { depth = 0; prev = "" }
    {
      line = $0; out = ""; i = 1; n = length(line)
      while (i <= n) {
        c = substr(line, i, 1); two = substr(line, i, 2)
        if (depth == 0 && c == "\"") {                    # String ueberspringen
          j = i + 1
          while (j <= n) {
            cc = substr(line, j, 1)
            if (cc == "\\") { j += 2; continue }
            if (cc == "\"") break
            j++
          }
          out = out substr(line, i, j - i + 1); i = j + 1; continue
        }
        if (two == "/-") { depth++; i += 2; continue }     # fasst /-- und /-! mit
        if (two == "-/" && depth > 0) { depth--; i += 2; continue }
        if (depth == 0 && two == "--") break               # Rest der Zeile ist Kommentar
        if (depth == 0) out = out c
        i++
      }
      if (index(out, "#print axioms") > 0) {
        if (index(out, "#guard_msgs") > 0) cls = "W"
        else if (prev ~ /#guard_msgs[[:space:]]*(in)?[[:space:]]*$/) cls = "S"
        else cls = "B"
        t = out
        sub(/^.*#print axioms[[:space:]]*/, "", t)
        sub(/[[:space:]].*$/, "", t)
        printf "%s\t%d\t%s\t%s\n", cls, NR, FN, t
      }
      if (!blank(out)) prev = out
    }
  ' "$1"
}

# Alle Fundstellen des Bereichs, mit Spalte 5 = "AUSNAHME" oder "GEPRUEFT".
bare_collect() {
  local f base
  while IFS= read -r -d '' f; do
    case "$f" in (*/.lake/*) continue;; esac
    if grep -qE "${AUSNAHME_RE}" "$f" 2>/dev/null; then base="AUSNAHME"; else base="GEPRUEFT"; fi
    bare_scan_file "$f" | awk -v M="$base" -F'\t' '{ printf "%s\t%s\n", $0, M }'
  done < <(
    find "${ROOT}" \
      \( -name '.lake' -o -name '.git' -o -name '.claude' -o -name 'node_modules' \) -prune -o \
      -name '*.lean' -type f -print0 | sort -z
  )
}

# ANKER, im Skript und nicht im Befund — sonst gelten sie einmal und nie wieder.
# Sie sind INHALTLICH und nicht ueber Zeilennummern verankert: der Zug, der diese
# Pruefung anlegte, hat den beiden Werkzeugdateien die Ausnahme-Marke vorangestellt
# und damit ihre Zeilennummern verschoben. Ein Zeilenanker haette das nicht
# ueberlebt (CLAUDE.md §12 Regel 8).
#   MUSS       — zwei nackte Aufrufe im Ausschlussbereich. Ohne Ausschluss zu
#                finden, mit Ausschluss nicht: prueft Route und Ausschluss in einem.
#   DARF NICHT — eine Prosastelle (Kommentar mit dem Suchbegriff), eine in Zug B
#                geheilte Datei, eine durchweg gewachte Datei. Keine der drei darf
#                als nackt erscheinen. Alle drei liegen in Dateien, die der
#                anlegende Zug nicht angefasst hat.
# Form `Datei::Ziel`, damit die Anwesenheit der Ankerdatei getrennt von der des
# Ziels geprueft werden kann: bei einem Lauf ueber einen FREMDEN Pfad
# (`doc_lint.sh <pfad>`) liegt keine Ankerdatei im Bereich, und ein Selbsttest,
# der dann zwangslaeufig failt, waere ein Konstruktionsfehler und kein Befund.
BARE_MUSS='Diagnostics/AxiomProbe.lean::Reformulation.Kenogram.soundness Diagnostics/SwapSatzProbe.lean::Reformulation.PathC.elementaryTopos_of_components'
BARE_DARFNICHT='Kenogram/Operational.lean Proemial/K4DiscontexturalityProbe.lean Proemial/AlphaGamma.lean'

bare_report() {
  local all rc=0 n_alle n_geprueft n_ausnahme n_getrennt hit
  all="$(bare_collect)"
  if [ -z "${all}" ]; then
    echo "  (keine \`#print axioms\`-Anweisung im Bereich — Gruppe (D) nicht anwendbar)"
    echo "  ── (D) 0 Verstöße"
    return 0
  fi
  n_alle="$(printf '%s\n' "${all}" | awk -F'\t' '$1=="B"' | wc -l | tr -d ' ')"
  n_ausnahme="$(printf '%s\n' "${all}" | awk -F'\t' '$1=="B" && $5=="AUSNAHME"' | wc -l | tr -d ' ')"
  n_geprueft="$(printf '%s\n' "${all}" | awk -F'\t' '$1=="B" && $5=="GEPRUEFT"' | wc -l | tr -d ' ')"
  n_getrennt="$(printf '%s\n' "${all}" | awk -F'\t' '$1=="S"' | wc -l | tr -d ' ')"

  # --- Anker zuerst: eine gebrochene Probe ist ein Routenfehler, kein Bestandsfund.
  local ankerdatei ankerziel
  for hit in ${BARE_MUSS}; do
    ankerdatei="${hit%%::*}"; ankerziel="${hit##*::}"
    if ! printf '%s\n' "${all}" | awk -F'\t' -v d="${ankerdatei}" 'index($3,d)>0' | grep -q .; then
      echo "  [ANKER] ${ankerdatei} liegt nicht im Bereich — Selbsttest für diesen Anker übersprungen."
      continue
    fi
    if ! printf '%s\n' "${all}" | awk -F'\t' -v h="${ankerziel}" '$1=="B" && $4==h' | grep -q .; then
      echo "  [ANKER] MUSS-Fall NICHT getroffen: ${ankerziel} in ${ankerdatei}"
      echo "          Die Route ist zuerst zu verdaechtigen, nicht der Bestand."
      rc=1
    fi
    # Zweite Haelfte desselben Ankers: die Route findet ihn, der Ausschluss haelt
    # ihn aus der Wertung. Faellt eine der beiden Haelften, ist entweder die Route
    # blind oder der Ausschluss unwirksam — beides waere still.
    if printf '%s\n' "${all}" | awk -F'\t' -v h="${ankerziel}" '$1=="B" && $4==h && $5=="GEPRUEFT"' | grep -q .; then
      echo "  [ANKER] Ausschluss unwirksam: ${ankerziel} steht trotz Marke in der Wertung."
      rc=1
    fi
  done
  for hit in ${BARE_DARFNICHT}; do
    if printf '%s\n' "${all}" | awk -F'\t' -v h="${hit}" '$1=="B" && index($3,h)>0' | grep -q .; then
      echo "  [ANKER] DARF-NICHT-Fall getroffen: ${hit}"
      rc=1
    fi
  done

  if [ "${n_getrennt}" -gt 0 ]; then
    echo "  Hinweis: ${n_getrennt} Aufruf(e) in getrennter Form (\`#guard_msgs\` auf eigener Zeile)."
    echo "           Gilt als gewacht; der Fall kam im Bestand bisher nicht vor und gehört in den Befund."
  fi

  if [ "${n_geprueft}" -gt 0 ]; then
    printf '%s\n' "${all}" | awk -F'\t' '$1=="B" && $5=="GEPRUEFT" { printf "  %s:%s  nackt: %s\n", $3, $2, $4 }'
    echo "  Heilung: \`#guard_msgs in #print axioms …\` mit dem GEMESSENEN Profil davor —"
    echo "           oder, wenn die Datei ein Messwerkzeug ist, die Marke \`-- LINT-AUSNAHME (D):\`"
    echo "           im Dateikopf, mit Begründung."
    rc=1
  else
    echo "  (keine nackten \`#print axioms\` im geprüften Bereich)"
  fi
  printf "  ── (D) %d Verstöße; %d nackte Aufrufe insgesamt, davon %d in Dateien mit Ausnahme-Marke\n" \
         "${n_geprueft}" "${n_alle}" "${n_ausnahme}"
  return "${rc}"
}

# --- (F) Sprungziele: jeder Verweis loest auf --------------------------------
# Eine Ausgabe verweist ueber `href="#x"` auf ihre eigene Traegertafel und ihre
# Kapitel. Loest ein Verweis nicht auf, fuehrt ein Klick ins Leere — und zwar
# still: der Browser meldet nichts, und keine der uebrigen Proben sieht es.
#
# ANLASS (Sondierung zur Erzeugungsstrecke, 6. August 2026): unter den
# eingesetzten Treffern war ein zerstoertes Sprungziel `#t7` -> `#t77`. Weder
# `ausgabe_probe.sh` noch `figures.sh` haben es gesehen — beide blind. Es ist
# einer von drei gemessenen blinden Flecken und der einzige, der sich OHNE
# Vergleichsstueck pruefen laesst: die Ausgabe traegt Frage und Antwort selbst.
#
# GRUNDLINIE NULL, gemessen ueber ALLE elf Fassungen unter docs/ — die laufenden
# und die vier archivierten, deutsch und englisch: null unaufgeloeste Verweise
# und null doppelt vergebene Anker. Kein Archivschnitt noetig; die eingefrorenen
# Fassungen sind selbst sauber. Kein Ermessen im Befund: ein Verweis loest auf
# oder nicht.
#
# ZWEI VERSTOSSARTEN, beide brechend:
#   F1  ein `href="#x"` ohne `id="x"` in derselben Datei;
#   F2  ein `id` zweimal vergeben — dann ist unbestimmt, wohin der Verweis geht.
anker_report() {
  local rc=0 n_dateien=0 n_refs=0 n_ids=0 v1=0 v2=0 ausgabe=""
  local datei
  while IFS= read -r datei; do
    [ -f "$datei" ] || continue
    n_dateien=$((n_dateien + 1))
    local bericht
    bericht="$(python3 - "$datei" <<'PY_ANKER'
import re, sys
p = sys.argv[1]
s = open(p, encoding='utf-8', errors='replace').read()
ids = re.findall(r'\bid="([^"]+)"', s)
refs = re.findall(r'\bhref="#([^"]+)"', s)
gesetzt = set(ids)
offen = sorted({r for r in refs if r not in gesetzt})
doppelt = sorted({i for i in gesetzt if ids.count(i) > 1})
print(f"ZAHL\t{len(set(refs))}\t{len(gesetzt)}\t{len(offen)}\t{len(doppelt)}")
for x in offen:
    print(f"F1\t{x}")
for x in doppelt:
    print(f"F2\t{x}")
PY_ANKER
)"
    local zahl
    zahl="$(printf '%s\n' "$bericht" | awk -F'\t' '$1=="ZAHL"{print $2" "$3}')"
    n_refs=$((n_refs + $(echo "$zahl" | cut -d' ' -f1)))
    n_ids=$((n_ids + $(echo "$zahl" | cut -d' ' -f2)))
    local zeile
    while IFS= read -r zeile; do
      case "$zeile" in
        F1*) v1=$((v1 + 1)); rc=1
             ausgabe="${ausgabe}  ${datei}: Verweis auf #$(printf '%s' "$zeile" | cut -f2) ohne Anker"$'\n' ;;
        F2*) v2=$((v2 + 1)); rc=1
             ausgabe="${ausgabe}  ${datei}: Anker $(printf '%s' "$zeile" | cut -f2) zweimal vergeben"$'\n' ;;
      esac
    done <<< "$bericht"
  done <<< "$(find -L "${ROOT}/docs" -name '*.html' -type f 2>/dev/null | sort)"

  if [ -n "$ausgabe" ]; then
    printf '%s' "$ausgabe"
    echo "  Heilung: den Anker setzen oder den Verweis entfernen — ein Verweis ins Leere"
    echo "           meldet sich nie von selbst."
  else
    echo "  (jeder Verweis loest auf, kein Anker doppelt)"
  fi
  printf "  ── (F) %d Verstöße (F1 %d, F2 %d); %d Dateien, %d Verweise, %d Anker\n" \
         "$((v1 + v2))" "${v1}" "${v2}" "${n_dateien}" "${n_refs}" "${n_ids}"
  return "${rc}"
}

# --- (E) Ausgabeinterne Ziffern ---------------------------------------------
# Teil A der Papierfassung verweist ueber Ziffern in eckigen Klammern auf die
# Traegertafel in Teil B. FESTLEGUNG: diese Ziffern sind AUSGABEINTERN — sie
# werden je Ausgabe neu vergeben und nirgends ausserhalb von Ausgabe und Entwurf
# zitiert, wie Fussnotennummern.
#
# WARUM DIE FESTLEGUNG: neue Saetze in den vorderen Kapiteln muessen in der
# Lesereihenfolge eingefuegt werden; dann verschiebt sich alles Folgende. Die
# Alternative — fortlaufend anhaengen — liesse die Zifferfolge im Text
# unmonoton. Neu vergeben ist billiger, ABER nur solange niemand von aussen
# zitiert; sonst zeigt jede Ziffer nach der naechsten Ausgabe falsch.
#
# WARUM DIE WACHE: die Festlegung ist ohne Route eine Absicht. Die erste
# Zitierung von aussen faellt niemandem auf — kein Bau bricht, kein Lint schlaegt
# an —, und dann altert die Festlegung wie die Liste, die sie ersetzt.
# Gemessen bei der Anlage: NULL Zitierungen von aussen. Die Wache haelt die
# Grundlinie, sie heilt keinen Bestand.
#
# BRECHEND wie (C) und (D), und aus demselben Grund: der Befund ist nicht
# auslegungsbeduerftig, und die Grundlinie ist null.
#
# ROUTE — VERENGUNG STATT BEREICHSSCHNITT. Ein Muster, das jedes `[n]` faengt,
# meldet im Bestand 34 Fundstellen, von denen KEINE eine Verweisung ist:
# Listenliterale (`[0]`, `[0,1]`), Iterationsnotation (`f^[2]`), Feldindizes der
# Shell (`BASH_SOURCE[0]`, `sys.argv[1]`). Eine Meldung, die man
# gewohnheitsmaessig wegdrueckt, ist schlechter als keine — dasselbe Argument,
# mit dem die Nackt-Pruefung ihren Pfadausschluss bekam. Die Lean- und
# Shell-Quellen GANZ auszunehmen waere der falsche Ausweg: dort koennte eine
# spaetere Zitierung stehen. Verengt wird darum das Muster, in zwei Schritten:
#   1. Nur PROSA wird gelesen. `.md` ohne Zaunbloecke; `.lean` nur die
#      Kommentarregionen (`--` bis Zeilenende, `/- … -/` verschachtelt, fasst
#      `/--` und `/-!` mit); `.sh` nur ab `#`; `.html` markup-entfernt. In allen
#      vier Faellen werden danach die Backtick-Spannen getilgt — dort steht Code,
#      auch wenn er in einem Kommentar zitiert wird.
#   2. Ein `[n]` unmittelbar nach `^` ist Lean-Iterationsnotation und nie eine
#      Verweisung. Gemessen: genau EIN Rest ueberlebte Schritt 1 —
#      `(reflect f)^[1]` in einem `--`-Kommentar von `MediationProcess.lean`.
#      Ohne diesen zweiten Schritt waere die Grundlinie eins statt null.
#   3. Ein `[n]` unmittelbar VOR einer tiefgestellten Ziffer ist die
#      Morphogramm-Notation `[15]₄` — Morphogramm Nr. 15 der Stelligkeit 4 — und
#      nie eine Verweisung. Gemessen: sechs Reste ueberlebten die Schritte 1 und 2,
#      alle sechs von dieser Gestalt, in `Definitionen.md` (Guenther-Zitat) und in
#      den beiden Morphogramm-Dokumenten. Erst mit diesem Schritt ist die
#      Grundlinie null.
# Alle drei Schritte sind Verengungen des Musters und keine Ausschluesse von Orten.
# Die dritte war erst sichtbar, nachdem der Korpus wirklich gelesen wurde — vorher
# stieg `find` nicht in den Symlink hinab, und der Bereich war leer.
#
# BEREICHSSCHNITT, dreiteilig: Ausgabe (`docs/*.html`, `docs/rev<n>/*.html`),
# Entwuerfe (`Entwurf_*.md`) und ERGEBNISDOKUMENTE EINER AUSGABE
# (`Papierausgabe_*.md`). Fuer die ersten beiden ist der Grund offensichtlich:
# dort IST die Tafel, und dort sind die Ziffern genau das Verweisungsmittel, fuer
# das sie gebaut sind.
#
# DER DRITTE TEIL BRAUCHT SEINEN SATZ, sonst waere er eine stille Ausnahme:
#
#   Ein Ergebnisdokument haelt einen Stand SEINES DATUMS fest (§11: Fund ja,
#   Stand nein). Seine Kennzahlen werden nicht nachgefuehrt, wenn sich der
#   Bestand bewegt — sie sind an ihren Commit gebunden und dort richtig. Seine
#   Ziffern sind derselbe Fall: sie meinen die Traegertafel seines Datums.
#
# Der Schnitt ist damit keine Ausnahme von der Festlegung, sondern die Anwendung
# einer Regel, die der Korpus schon fuehrt. Gemessen bei der Anlage: 25 echte
# Verweisungen im Korpus, saemtlich in `Papierausgabe_Rev4_Befund/_Vorgabe/
# _Abnahme.md` — den Arbeitsdokumenten des Zuges, der die Tafel angelegt hat.
# Sie sind mit dem Gesuchten GESTALTGLEICH; keine Verengung trennt sie, und wer
# es doch versuchte, schloesse denselben Zug auch fuer die Zukunft aus.
#
# WAS DER SCHNITT KOSTET, und es ist nicht nichts: die Wache sieht gerade die
# Dokumente nicht, in denen die Ziffern am dichtesten stehen. Sie bewacht den
# LAUFENDEN Bestand — Lean-Quellen, Repo-Doku, Sonden, Befunde ausserhalb der
# Ausgabenreihe —, und dort ist die Grundlinie null.
#
# `docs/index.html` faellt unter das erste Glob und traegt null Ziffern — der
# Schnitt kostet dort nichts, gemessen und nicht angenommen.
#
# BEREICH: der Lauf-ROOT und, wenn ROOT das Repo ist, zusaetzlich ein
# geschwisterliches `KorpusRev2/`. Der Korpus ist kein Teil des Repos; ohne ihn
# bewachte die Gruppe gerade den Ort NICHT, an dem eine Zitierung am ehesten
# stuende — einen Befund. Seine Erreichbarkeit wird BERICHTET und nicht
# vorausgesetzt: fehlt er, laeuft die Gruppe ueber das Repo allein und sagt es.
ZIFFER_ROOTS=()
ziffer_roots_bestimmen() {
  ZIFFER_ROOTS=("${ROOT}")
  ZIFFER_KORPUS_LAGE="nicht gesucht (Lauf ueber Argument-Pfad)"
  local self korpus
  self="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
  [ "${ROOT}" = "${self}" ] || return 0
  korpus="$(dirname "${ROOT}")/KorpusRev2"
  if [ -d "${korpus}" ] && ls -A "${korpus}" >/dev/null 2>&1; then
    ZIFFER_ROOTS+=("${korpus}")
    ZIFFER_KORPUS_LAGE="erreichbar: ${korpus}"
  else
    ZIFFER_KORPUS_LAGE="NICHT erreichbar — Bereich ist das Repo allein"
  fi
}

# Die Dateizahl je Wurzel wird BERICHTET, und der Grund ist gemessen: der Korpus
# haengt als Symlink im Baum (hier nach iCloud), und `find` ohne `-L` steigt in
# einen Symlink NICHT hinab. Der erste Lauf dieser Gruppe meldete darum
# „Korpus: erreichbar" ueber einem Bereich von NULL Dateien — eine beruhigende
# Zeile ueber einer leeren Menge, die schlimmste Form. Gefunden hat es nicht die
# Grundlinie (die war so oder so null), sondern eine eingesetzte Zitierung.
# Seither `find -L`, und die Zahl steht im Report: eine Null ist sichtbar.
ziffer_bereich_zeile() {
  local r n out=""
  for r in "${ZIFFER_ROOTS[@]}"; do
    n="$(find -L "$r" \
          \( -name '.lake' -o -name '.git' -o -name '.claude' -o -name 'node_modules' \) -prune -o \
          \( -name '*.md' -o -name '*.lean' -o -name '*.html' -o -name '*.sh' \) -type f -print \
          2>/dev/null | wc -l | tr -d ' ')"
    out="${out}${out:+ · }$(basename -- "$r"): ${n}"
  done
  printf '%s' "${out}"
}

# Der Kern-Scanner. Gibt je Fundstelle `DATEI<TAB>ZEILE<TAB>ZIFFER<TAB>KONTEXT`.
# Die Prosa-Gewinnung laeuft zeilenweise mit mitgefuehrter Kommentartiefe, wie
# bei (D); `--` innerhalb eines `/- … -/` ist dort kein Zeilenkommentar.
ziffer_scan_file() {
  awk -v FN="$1" -v EXT="$2" '
    function entbacktick(s,   r, p, q) {
      r = ""
      while ((p = index(s, "`")) > 0) {
        r = r substr(s, 1, p - 1); s = substr(s, p + 1)
        q = index(s, "`"); if (q == 0) { s = ""; break }
        s = substr(s, q + 1)
      }
      return r s
    }
    # Die zehn tiefgestellten Ziffern als DREI-BYTE-Literale. Der naheliegende
    # Weg — eine Zeichenklasse `/^[₀…₉]/` — funktioniert, wirft aber bei jeder
    # Zeile mit einem Mehrbyte-Zeichen `awk: towc: multibyte conversion failure`
    # auf stderr; gemessen an `Definitionen.md:281`. Eine Pruefung, die Muell
    # ausgibt, wird nicht gelesen. `substr` arbeitet hier BYTEWEISE (gemessen:
    # `substr(s,i,3)` liefert genau die drei Bytes eines Subskripts), darum ist
    # der Nachschlag in einer Tabelle exakt und ohne Regex-Maschine.
    BEGIN {
      depth = 0; zaun = 0
      split("₀ ₁ ₂ ₃ ₄ ₅ ₆ ₇ ₈ ₉", t9, " ")
      for (q = 1; q <= 10; q++) TIEF[t9[q]] = 1
    }
    {
      line = $0; prosa = ""
      if (EXT == "md") {
        if (line ~ /^[[:space:]]*```/) { zaun = 1 - zaun; next }
        if (zaun) next
        prosa = line
      } else if (EXT == "sh") {
        p = index(line, "#"); if (p == 0) next
        prosa = substr(line, p)
      } else if (EXT == "html") {
        prosa = line; gsub(/<[^>]*>/, " ", prosa)
      } else {                                        # lean
        i = 1; n = length(line)
        while (i <= n) {
          two = substr(line, i, 2)
          if (two == "/-") { depth++; i += 2; continue }
          if (two == "-/" && depth > 0) { depth--; i += 2; continue }
          if (depth == 0 && two == "--") { prosa = prosa substr(line, i); break }
          if (depth > 0) prosa = prosa substr(line, i, 1)
          i++
        }
      }
      prosa = entbacktick(prosa)
      rest = prosa; vorher = ""
      while (match(rest, /\[[0-9][0-9]?\]/)) {
        vor = (RSTART > 1) ? substr(rest, RSTART - 1, 1) : substr(vorher, length(vorher), 1)
        nach = substr(rest, RSTART + RLENGTH, 3)
        z = substr(rest, RSTART, RLENGTH)
        if (vor != "^" && !(nach in TIEF)) {
          k = prosa; gsub(/\t/, " ", k); sub(/^[[:space:]]+/, "", k)
          printf "%s\t%d\t%s\t%s\n", FN, NR, z, substr(k, 1, 90)
        }
        vorher = vorher substr(rest, 1, RSTART + RLENGTH - 1)
        rest = substr(rest, RSTART + RLENGTH)
      }
    }
  ' "$1"
}

# $1 = "mit" (Bereichsschnitt aktiv) oder "ohne" (Vergleichslauf)
ziffer_collect() {
  local modus="$1" f base ext
  local r
  for r in "${ZIFFER_ROOTS[@]}"; do
    while IFS= read -r -d '' f; do
      base="$(basename -- "$f")"
      if [ "${modus}" = "mit" ]; then
        case "$f" in (*/docs/*.html) continue;; esac
        case "${base}" in (Entwurf_*.md|Papierausgabe_*.md) continue;; esac
      fi
      case "${base}" in
        (*.md)   ext="md";;
        (*.lean) ext="lean";;
        (*.sh)   ext="sh";;
        (*.html) ext="html";;
        (*)      continue;;
      esac
      ziffer_scan_file "$f" "$ext"
    done < <(
      find -L "$r" \
        \( -name '.lake' -o -name '.git' -o -name '.claude' -o -name 'node_modules' \) -prune -o \
        \( -name '*.md' -o -name '*.lean' -o -name '*.html' -o -name '*.sh' \) -type f -print0 \
        2>/dev/null | sort -z
    )
  done
}

# ANKER, im Skript und nicht im Befund. INHALTLICH verankert, nicht ueber
# Zeilennummern (§12 Regel 8) — und samtlich in Dateien, die der anlegende Zug
# NICHT angefasst hat: er fasst `doc_lint.sh` und `CLAUDE.md` an, sonst nichts.
# Aus demselben Grund ist `doc_lint.sh` KEIN Darf-nicht-Anker, obwohl es mit
# `k[2]` und `k[3]` zwei Feldindizes traegt.
#   MUSS       — die Traegertafel selbst. Ohne Schnitt zu finden, mit Schnitt
#                nicht: prueft Route und Schnitt in einem Zug.
#   DARF NICHT — je eine der drei Fremdgestalten. Die zweite ist die schaerfste:
#                sie steht in einem `--`-Kommentar und ueberlebt die
#                Prosa-Verengung; nur die `^`-Regel haelt sie heraus.
#
# BEIDE HAELFTEN DES SCHNITTS SIND JETZT VERANKERT. Bis zur fuenften Ausgabe war
# die Archiv-Haelfte leer: die Traegertafel ist eine Erfindung der VIERTEN
# Ausgabe, und `docs/rev1|rev2|rev3` tragen je NULL Ziffern — gemessen, nachdem
# ein geratener Anker dort fehlgeschlagen war. Der damals vermerkte AUSLOESER hat
# mit der Archivierung von Rev4 gefeuert: `docs/rev4/de.html` traegt 106 Ziffern
# und steht seither in der MUSS-Liste. Der Glob `docs/rev<n>/*.html` schneidet
# damit nachweislich etwas, was die Route sonst faende.
ZIFFER_MUSS='docs/de.html docs/en.html docs/rev4/de.html'
ZIFFER_DARFNICHT='Reformulation/Kenogram/Basic.lean Reformulation/Proemial/MediationProcess.lean docs/parity.sh'

ziffer_report() {
  local mit ohne rc=0 n_mit n_ohne hit
  ziffer_roots_bestimmen
  mit="$(ziffer_collect mit)"
  ohne="$(ziffer_collect ohne)"
  n_mit="$(printf '%s' "${mit}" | grep -c . || true)"
  n_ohne="$(printf '%s' "${ohne}" | grep -c . || true)"

  echo "  Korpus: ${ZIFFER_KORPUS_LAGE}"
  echo "  Dateien je Wurzel: $(ziffer_bereich_zeile)"

  # --- Anker zuerst: eine gebrochene Probe ist ein Routenfehler, kein Bestandsfund.
  for hit in ${ZIFFER_MUSS}; do
    if ! printf '%s\n' "${ohne}" | awk -F'\t' -v d="${hit}" 'index($1,d)>0' | grep -q .; then
      echo "  [ANKER] MUSS-Fall NICHT getroffen: ${hit}"
      echo "          Die Route ist zuerst zu verdaechtigen, nicht der Bestand."
      rc=1
    fi
    if printf '%s\n' "${mit}" | awk -F'\t' -v d="${hit}" 'index($1,d)>0' | grep -q .; then
      echo "  [ANKER] Bereichsschnitt unwirksam: ${hit} steht trotz Schnitt in der Wertung."
      rc=1
    fi
  done
  for hit in ${ZIFFER_DARFNICHT}; do
    if printf '%s\n' "${ohne}" | awk -F'\t' -v d="${hit}" 'index($1,d)>0' | grep -q .; then
      echo "  [ANKER] DARF-NICHT-Fall getroffen: ${hit}"
      echo "          Die Verengung greift nicht mehr — Muster pruefen, nicht Bestand heilen."
      rc=1
    fi
  done

  if [ "${n_mit}" -gt 0 ]; then
    printf '%s\n' "${mit}" | awk -F'\t' '{ printf "  %s:%s  Ziffer %s — %s\n", $1, $2, $3, $4 }'
    echo "  Heilung: die Ziffer NICHT zitieren, sondern den Traeger beim Namen nennen."
    echo "           Die Ziffern sind ausgabeintern und zeigen nach der naechsten Ausgabe falsch."
    rc=1
  else
    echo "  (keine ausgabeinternen Ziffern ausserhalb von Ausgabe und Entwurf)"
  fi
  printf "  ── (E) %d Verstöße; Vergleichslauf ohne Bereichsschnitt: %d Fundstellen\n" \
         "${n_mit}" "${n_ohne}"
  return "${rc}"
}

# Gruppe (C) vorab fahren: ihre Rückgabecodes bestimmen den Exit-Code des Laufs.
C_RC=0
BLOCK_C1="$(ledger_report)"  || C_RC=1
BLOCK_C2="$(ledger7_report)" || C_RC=1
BLOCK_C3="$(ledger8_report)" || C_RC=1

# Gruppe (D) ebenso vorab: sie bricht wie (C).
D_RC=0
BLOCK_D="$(bare_report)" || D_RC=1

# Gruppe (E) ebenso: sie bricht wie (C) und (D).
E_RC=0
BLOCK_E="$(ziffer_report)" || E_RC=1

# Gruppe (F) ebenso: Grundlinie null ueber alle elf Fassungen unter docs/.
F_RC=0
BLOCK_F="$(anker_report)" || F_RC=1

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
echo "── Gruppe (D) GEDRUCKT GEGEN GEWACHT — \`#print axioms\` ohne \`#guard_msgs\` ─────"
echo "     Ein gedrucktes Profil sichert nichts: aendert der Satz sein Profil, druckt es"
echo "     das neue und der Bau bleibt gruen. Grundlinie null (CLAUDE.md §8 Fallstrick 16)."
echo "     Bereich: *.lean; Kommentare werden zuerst entfernt, dann wird gesucht."
echo "     Ausnahme: Dateien mit der Marke \`-- LINT-AUSNAHME (D):\` im Kopf — Messwerkzeuge,"
echo "     die Profile anzeigen und darum nicht einfrieren duerfen. Pfadschnitt, keine"
echo "     Zahlentoleranz: ein Lint mit geduldeten Treffern wird ueberlesen."
printf '%s\n' "$BLOCK_D"
echo

echo "── Gruppe (E) AUSGABEINTERNE ZIFFERN — Traegertafel-Verweisungen von aussen ───"
echo "     Die Ziffern in eckigen Klammern verweisen auf die Traegertafel und werden je"
echo "     Ausgabe NEU vergeben. Wer sie ausserhalb von Ausgabe und Entwurf zitiert, zeigt"
echo "     nach der naechsten Ausgabe falsch — und niemand merkt es. Grundlinie null."
echo "     Bereich: *.md, *.lean, *.sh, *.html; nur Prosa (Zaunbloecke, Code-Regionen und"
echo '     Backtick-Spannen entfallen); `^[n]` ist Iterationsnotation und `[n]₄` ist die'
echo "     Morphogramm-Notation — beides keine Verweisung."
echo "     Schnitt: docs/*.html, docs/rev<n>/*.html, Entwurf_*.md — dort IST die Tafel;"
echo "     dazu Papierausgabe_*.md: ein Ergebnisdokument haelt einen Stand seines Datums"
echo "     fest, und seine Ziffern meinen die Tafel dieses Datums — wie seine Kennzahlen."
printf '%s\n' "$BLOCK_E"
echo

echo "── Gruppe (F) SPRUNGZIELE — jeder Verweis loest auf ──────────────────────────"
echo "     Ein href=\"#x\" ohne id=\"x\" fuehrt ins Leere, und zwar still: der Browser"
echo "     meldet nichts, und keine andere Probe sieht es. Grundlinie null, gemessen"
echo "     ueber ALLE Fassungen unter docs/ — die laufenden und die archivierten."
echo "     F1: Verweis ohne Anker.  F2: Anker zweimal vergeben (Ziel unbestimmt)."
echo "     Kein Archivschnitt: die eingefrorenen Fassungen sind selbst sauber."
printf '%s\n' "$BLOCK_F"
echo

if [ "${C_RC}" -ne 0 ] || [ "${D_RC}" -ne 0 ] || [ "${E_RC}" -ne 0 ] || [ "${F_RC}" -ne 0 ]; then
  betroffen=""
  [ "${C_RC}" -ne 0 ] && betroffen="${betroffen}(C) "
  [ "${D_RC}" -ne 0 ] && betroffen="${betroffen}(D) "
  [ "${E_RC}" -ne 0 ] && betroffen="${betroffen}(E) "
  [ "${F_RC}" -ne 0 ] && betroffen="${betroffen}(F) "
  echo "── Ende Report.  Exit 1: ${betroffen}melden Verstöße. ────────────────"
  echo "   (A) und (B) beeinflussen den Exit-Code nicht — sie melden."
  exit 1
fi
echo "── Ende Report.  Exit 0: Gruppen (C), (D), (E) und (F) ohne Verstoß. ────────"
echo "   (A) und (B) melden nur; ihre Treffer setzen keinen Exit-Code."

exit 0
