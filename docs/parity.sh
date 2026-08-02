#!/usr/bin/env bash
# =============================================================================
# parity.sh — Paritaetsprobe de gegen en  (Vorgang 12, Ausweg C, Posten B)
# -----------------------------------------------------------------------------
#   ./docs/parity.sh                  vergleicht docs/de.html und docs/en.html
#   ./docs/parity.sh <de> <en>        vergleicht zwei genannte Fassungen
#
# DIESE PROBE MELDET UND BRICHT NICHT — wie Gruppe (A) des Doc-Lints. Eine
# Abweichung kann eine begruendete Uebersetzungsentscheidung sein; der Befund
# fuehrt jede einzeln. (`figures.sh` daneben bricht: dort ist nichts zu ermessen.)
#
# WOZU: unter Ausweg C ist HTML der Bestand und Markdown Entwurfsmedium. Damit
# entfaellt die Divergenz Markdown/HTML konstruktiv — aber NICHT die zwischen
# den beiden Sprachfassungen. Ein Wandler haette sie ohnehin nie geprueft: er
# prueft nicht, ob zwei Quellen dasselbe sagen. Genau darauf zielt diese Probe.
#
# WAS SIE AUSDRUECKLICH NICHT VERGLEICHT: den Fliesstext. Er ist uebersetzt;
# jede Wortzaehlung meldete Rauschen. Eine Probe, die Fehlalarme erzeugt, wird
# nach kurzer Zeit nicht mehr gelesen. Sie prueft nur, was in beiden Fassungen
# gleich sein MUSS.
#
# In Vorgang 11 ist eine solche Probe eigens gebaut und danach weggeworfen
# worden. Das war der wirkliche Aufwand jeder Nachfuehrung, nicht der Text.
# =============================================================================

set -uo pipefail

DOCS="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
DE="${1:-${DOCS}/de.html}"
EN="${2:-${DOCS}/en.html}"

for f in "$DE" "$EN"; do
  [ -f "$f" ] || { echo "parity: Datei nicht gefunden: $f" >&2; exit 2; }
done

python3 - "$DE" "$EN" <<'PY'
import re, sys, html, collections

de_p, en_p = sys.argv[1], sys.argv[2]

def lade(p):
    t = open(p, encoding='utf-8', errors='replace').read()
    t = re.sub(r'<!--.*?-->', ' ', t, flags=re.S)
    return t

DE, EN = lade(de_p), lade(en_p)

def rumpf(t):
    """ohne <head>, Kopfleiste, Inhaltsverzeichnis und Fusszeile — das ist
       Geruest und in beiden Fassungen absichtlich verschieden."""
    t = re.sub(r'<head>.*?</head>', ' ', t, flags=re.S)
    t = re.sub(r'<div class="topbar">.*?</div>\s*</div>', ' ', t, flags=re.S)
    t = re.sub(r'<nav class="toc".*?</nav>', ' ', t, flags=re.S)
    t = re.sub(r'<footer.*?</footer>', ' ', t, flags=re.S)
    return t

RDE, REN = rumpf(DE), rumpf(EN)
befunde = []
def melde(nr, text): befunde.append(f"{nr}  {text}")

# --- B1  Folge der Ueberschriften, nach Nummer -------------------------------
# Der Wortlaut ist uebersetzt; vergleichbar sind die Ebenenfolge und die
# Abschnittsnummern (I · II · … bzw. der Anhang).
def kopfe(t):
    ebenen, nummern = [], []
    for m in re.finditer(r'<h([1-6])\b[^>]*>(.*?)</h\1>', t, re.S):
        ebenen.append(m.group(1))
        txt = ' '.join(html.unescape(re.sub(r'<[^>]+>', '', m.group(2))).split())
        n = re.match(r'^((?:I|V|X)+)\s*·', txt)
        if n: nummern.append(n.group(1))
        elif re.match(r'^(Anhang|Appendix)\b', txt): nummern.append('ANHANG')
    return ebenen, nummern

e_de, n_de = kopfe(RDE); e_en, n_en = kopfe(REN)
if e_de != e_en:
    melde("B1", f"Ebenenfolge verschieden: de {len(e_de)} Ueberschriften, en {len(e_en)}")
    if len(e_de) == len(e_en):
        melde("B1", f"   erste Abweichung an Position {next(i for i,(a,b) in enumerate(zip(e_de,e_en),1) if a!=b)}")
if n_de != n_en:
    melde("B1", f"Abschnittsnummern verschieden: de {n_de} · en {n_en}")

# --- B2  Tabellen, Zeilen und Spalten je Tabelle -----------------------------
def tabellen(t):
    out = []
    for tb in re.findall(r'<table\b.*?</table>', t, re.S):
        zeilen = re.findall(r'<tr\b.*?</tr>', tb, re.S)
        out.append([len(re.findall(r'<t[hd]\b', z)) for z in zeilen])
    return out

t_de, t_en = tabellen(RDE), tabellen(REN)
if len(t_de) != len(t_en):
    melde("B2", f"Tabellenzahl verschieden: de {len(t_de)} · en {len(t_en)}")
else:
    for i, (a, b) in enumerate(zip(t_de, t_en), 1):
        if len(a) != len(b):
            melde("B2", f"Tabelle {i}: Zeilenzahl de {len(a)} · en {len(b)}")
        elif a != b:
            melde("B2", f"Tabelle {i}: Spaltenzahl je Zeile verschieden: de {a} · en {b}")

# --- B3  Figuren ---------------------------------------------------------------
for name, pat in [('<figure>', r'<figure\b'), ('<svg>', r'<svg\b'), ('<figcaption>', r'<figcaption\b')]:
    a, b = len(re.findall(pat, RDE)), len(re.findall(pat, REN))
    if a != b: melde("B3", f"{name}: de {a} · en {b}")

# --- B4  Kaesten, Blockzitate, Codebloecke, Listen ---------------------------
for name, pat in [('callout', r'class="callout"'), ('theorem', r'class="theorem"'),
                  ('formula', r'class="formula"'), ('blockquote', r'<blockquote\b'),
                  ('<pre>', r'<pre\b'), ('<ul>', r'<ul\b'), ('<ol>', r'<ol\b'),
                  ('<li>', r'<li\b')]:
    a, b = len(re.findall(pat, RDE)), len(re.findall(pat, REN))
    if a != b: melde("B4", f"{name}: de {a} · en {b}")

# --- B5  <code>-Inhalte, in Reihenfolge  [die tragende Probe] ----------------
# Lean-Namen, Kommandos und Axiomprofile werden nicht uebersetzt; eine
# Abweichung ist immer ein Fehler und nie eine Uebersetzungsentscheidung.
def codes(t):
    return [' '.join(html.unescape(re.sub(r'<[^>]+>', '', c)).split())
            for c in re.findall(r'<code\b[^>]*>(.*?)</code>', t, re.S)]
c_de, c_en = codes(RDE), codes(REN)
if len(c_de) != len(c_en):
    melde("B5", f"Zahl der <code>-Spannen: de {len(c_de)} · en {len(c_en)}")
md, me = collections.Counter(c_de), collections.Counter(c_en)
for k in sorted((md - me) | (me - md)):
    melde("B5", f"<code>-Inhalt ungleich haeufig: {k!r}  de {md[k]} · en {me[k]}")
if len(c_de) == len(c_en):
    stellen = [i for i, (a, b) in enumerate(zip(c_de, c_en), 1) if a != b]
    if stellen:
        melde("B5", f"Reihenfolge weicht an {len(stellen)} Stelle(n) ab, zuerst Nr. {stellen[0]}: "
                    f"de {c_de[stellen[0]-1]!r} · en {c_en[stellen[0]-1]!r}")

# --- B6  Zellen mit class="num", tablewrap -----------------------------------
for name, pat in [('class="num"', r'class="num"'), ('tablewrap', r'class="tablewrap')]:
    a, b = len(re.findall(pat, RDE)), len(re.findall(pat, REN))
    if a != b: melde("B6", f"{name}: de {a} · en {b}")

# --- B7  Ziffernfolgen ab drei Stellen  [die zweittragende Probe] ------------
# Kennzahlen werden nicht uebersetzt. 3018 gegen 3017 ist ein Fund, keine Nuance.
def zahlen(t):
    nur_text = html.unescape(re.sub(r'<[^>]+>', ' ', re.sub(r'<svg\b.*?</svg>', ' ', t, flags=re.S)))
    # Tausendertrennung ZUERST aufloesen, sonst meldet die Probe die Schreib-
    # konvention statt der Zahl: `de` trennt mit einfachem Leerzeichen (19 683),
    # `en` mit Komma (19,683). Gemessen, nicht vermutet — die erste Fassung
    # dieser Probe fuehrte U+202F und U+00A0 in der Klasse, aber nicht U+0020,
    # und meldete darum vier Fehlalarme. Nur zwischen einer Ziffer und genau
    # drei folgenden Ziffern, damit `1. August` und `R3 bis R8` unberuehrt bleiben.
    nur_text = re.sub(r'(?<=\d)[\s\u202f\u00a0,.](?=\d{3}(?!\d))', '', nur_text)
    return collections.Counter(re.findall(r'\d{3,}', nur_text))
z_de, z_en = zahlen(RDE), zahlen(REN)
for k in sorted(set(z_de) | set(z_en)):
    if z_de[k] != z_en[k]:
        melde("B7", f"Ziffernfolge {k}: de {z_de[k]}x · en {z_en[k]}x")

# --- B8  Typografische Anfuehrungszeichen je Sprache -------------------------
# de: deutsche Form „…"   ·   en: englische Form "…" oder gerade
def zit(t):
    nur = html.unescape(re.sub(r'<[^>]+>', ' ', re.sub(r'<svg\b.*?</svg>', ' ', t, flags=re.S)))
    return {z: nur.count(z) for z in ['„', '“', '”', '‘', '’']}
q_de, q_en = zit(RDE), zit(REN)
if q_de['„'] == 0 and any(q_de.values()):
    melde("B8", f"de traegt keine deutsche Anfuehrung, aber andere: {q_de}")
if q_en['„'] > 0:
    melde("B8", f"en traegt {q_en['„']} deutsche Anfuehrung(en) „ — englische Fassung, "
                f"deutsche Form")

# --- Ausgabe ------------------------------------------------------------------
print("=" * 78)
print("  parity — Paritaetsprobe de gegen en")
print(f"  de: {de_p}")
print(f"  en: {en_p}")
print("=" * 78)
print("  B1 Ueberschriftenfolge · B2 Tabellen · B3 Figuren · B4 Kaesten und Listen")
print("  B5 <code>-Inhalte · B6 num/tablewrap · B7 Ziffernfolgen · B8 Anfuehrungen")
print()
if befunde:
    for b in befunde: print("  " + b)
    print(f"\n  ── {len(befunde)} Meldung(en). parity meldet und bricht nicht;")
    print("     jede Abweichung gehoert einzeln beurteilt in den Befund.")
else:
    print("  (keine Abweichung)")
    print("\n  ── 0 Meldungen.")
PY
exit 0
