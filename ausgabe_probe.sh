#!/usr/bin/env bash
# =============================================================================
# ausgabe_probe.sh — die veroeffentlichte Fassung gegen den abgenommenen Entwurf
# -----------------------------------------------------------------------------
# Zwischen Entwurf und Ausgabe gab es bis hierher KEINE Probe. Eine ausgelassene
# Tafelzeile, ein nicht uebernommener Absatz, eine falsch gesetzte Ziffer fielen
# niemandem auf, und zwar dauerhaft. Ausweg C bleibt — die HTML-Fassung ist
# Bestand und wird von Hand gefuehrt; diese Probe ersetzt sie nicht, sie macht
# sie pruefbar.
#
#   ./ausgabe_probe.sh <entwurf> <ausgabe> [<entwurf2> <ausgabe2> …]
#
# Beide Seiten duerfen .md oder .html sein; die Auszuege sind formatbewusst.
# Ein Entwurf darf aus mehreren Dateien bestehen (Teil A und Teil B), dann
# werden sie in der genannten Reihenfolge aneinandergehaengt:
#   ./ausgabe_probe.sh "teilA.md teilB.md" docs/de.html
#
# FUENF BRECHENDE GROESSEN, je Sprachpaar:
#   1. Ueberschriften — Folge und Wortlaut, in Dokumentreihenfolge
#   2. Traegertafel   — Zahl der Zeilen und Menge der Ziffern
#   3. Ziffern        — die MENGE der Ziffern des Dokuments, nicht die Zahl der
#                       Vorkommen: eine Ziffer darf in Teil A mehrfach stehen
#                       (Querverweise sind ein Bogen des Papiers, kein Fehler)
#   4. Figuren        — Zahl und Reihenfolge der Bildunterschriften
#   5. Absatz-Anfaenge — die ersten sechs Woerter jedes Textabsatzes, in Folge
#
# Die fuenfte steht NICHT in der Vorgabe. Sie ist hinzugekommen, weil die vier
# einen gestrichenen Absatz NICHT fangen — gemessen an der Saat: nur der
# berichtende Volltext sah ihn, und der bricht nicht. Ein nicht uebernommener
# Absatz ist aber genau einer der drei Faelle, gegen die die Probe gebaut ist.
# Sie ist exakt und traegt keine Zahlentoleranz: Markup faellt vor dem Vergleich
# weg, verglichen werden Woerter.
#
# EIN BERICHTENDES MASS: der volle Textvergleich. Er traegt Rauschen, solange die
# Normalisierung zwischen Markdown und HTML nicht gemessen ist. Er wird
# ausgewiesen und setzt KEINEN Exit-Code. Ob er brechend wird, entscheidet eine
# spaetere Messung und nicht dieses Skript.
#
# WERKZEUG, NOCH KEINE WACHE. Eine Wache braucht eine Grundlinie null; die kann
# es erst geben, wenn eine Ausgabe zum aktuellen Entwurf existiert. Bis dahin
# laeuft die Probe auf Aufruf und nicht im Lint.
#
# Sie KORRIGIERT NICHT. Ob Entwurf oder Ausgabe recht hat, ist eine Entscheidung
# — in der Regel die Ausgabe, weil sie spaeter ist, und genau darum eine.
# =============================================================================
set -u
cd "$(dirname "$0")" || exit 2

if [ "$#" -lt 2 ] || [ $(( $# % 2 )) -ne 0 ]; then
  sed -n '2,38p' "$0"
  exit 2
fi

# Die Argumente zeilenweise weitergeben — "$*" wuerde die Gruppierung verlieren,
# und ein Entwurf DARF aus mehreren Dateien bestehen.
AP_ARGS=$(printf '%s\n' "$@")
export AP_ARGS

python3 - <<'PY'
import os, re, sys, html as htmlmod, difflib

# Ein Argument je Zeile; ein Argument darf eine leerzeichengetrennte Dateiliste
# sein (Teil A und Teil B einer Sprache).
roh = [z for z in os.environ['AP_ARGS'].split('\n') if z != '']
paare = []
i = 0
while i + 1 < len(roh):
    paare.append((roh[i], roh[i + 1])); i += 2

def lies(spez):
    """Eine Seite: eine oder mehrere Dateien, in genannter Reihenfolge."""
    teile, art = [], None
    for p in spez.split():
        if not os.path.exists(p):
            print(f"  FEHLT: {p}"); sys.exit(2)
        s = open(p, encoding='utf-8', errors='replace').read()
        a = 'html' if p.endswith('.html') else 'md'
        art = a if art is None else ('gemischt' if art != a else art)
        teile.append((a, s))
    return teile, art

# ---------------------------------------------------------------- Auszuege ---
def entferne_html(s):
    s = re.sub(r'(?is)<(script|style)\b.*?</\1>', ' ', s)
    s = re.sub(r'<[^>]+>', ' ', s)
    return htmlmod.unescape(s)

def ueberschriften(art, s):
    if art == 'html':
        roh = re.findall(r'(?is)<h[1-6][^>]*>(.*?)</h[1-6]>', s)
        return [norm_text(entferne_html(x)) for x in roh]
    aus, zaun = [], False
    for z in s.split('\n'):
        if z.startswith('```'):
            zaun = not zaun; continue
        if zaun:
            continue
        m = re.match(r'^#{1,6}\s+(.*)$', z)
        if m:
            aus.append(norm_text(m.group(1)))
    return aus

def norm_text(t):
    t = t.replace(' ', ' ')
    t = re.sub(r'[*_`]', '', t)
    t = re.sub(r'[«»„“”"‚‘’\']', '', t)
    t = re.sub(r'[–—−]', '-', t)
    t = re.sub(r'\s+', ' ', t).strip()
    return t

def tafelzeilen(art, s):
    """Zeilen der Traegertafel: eine Ziffer, ein Traeger. Formatunabhaengig
    ueber die Ziffer am Zeilen- bzw. Zellenanfang."""
    if art == 'html':
        zeilen = re.findall(r'(?is)<tr[^>]*>(.*?)</tr>', s)
        aus = []
        for z in zeilen:
            zellen = [norm_text(entferne_html(c)) for c in
                      re.findall(r'(?is)<t[dh][^>]*>(.*?)</t[dh]>', z)]
            if zellen and re.match(r'^\[\d+\]$|^—$|^-$', zellen[0]):
                aus.append(zellen[0])
        return aus
    aus = []
    for z in s.split('\n'):
        m = re.match(r'^\|\s*(\[\d+\]|—)\s*\|', z)
        if m:
            aus.append(m.group(1))
    return aus

def ziffern(art, s):
    text = entferne_html(s) if art == 'html' else s
    # Iterationsnotation ^[n] und Morphogramm-Notation [n]₄ sind keine Ziffern.
    treffer = set()
    for m in re.finditer(r'\[(\d+)\]', text):
        vor = text[m.start() - 1] if m.start() else ''
        nach = text[m.end():m.end() + 1]
        if vor == '^' or nach in '₀₁₂₃₄₅₆₇₈₉':
            continue
        treffer.add(int(m.group(1)))
    return treffer

def figuren(art, s):
    text = entferne_html(s) if art == 'html' else s
    text = norm_text(text)
    return [norm_text(m.group(0)) for m in
            re.finditer(r'(?:Figur|Figure|Abbildung)\s+\d+', text)]

def absatz_anfaenge(art, s, woerter=6):
    """Der Anfang jedes Textabsatzes, normalisiert. Faengt einen gestrichenen,
    eingefuegten oder verschobenen Absatz — und zwar EXAKT, ohne Zahlentoleranz.
    Markup faellt vorher weg, darum traegt die Groesse ueber beide Formate."""
    aus = []
    if art == 'html':
        for roh in re.findall(r'(?is)<p[^>]*>(.*?)</p>', s):
            if '<path' in roh or '<line' in roh or '<text' in roh:
                continue
            t = norm_text(entferne_html(roh))
            if len(t.split(' ')) >= woerter:
                aus.append(' '.join(t.split(' ')[:woerter]))
        return aus
    zaun, block = False, []
    def schliesse():
        t = norm_text(' '.join(block))
        if t and len(t.split(' ')) >= woerter and not t.startswith('|'):
            aus.append(' '.join(t.split(' ')[:woerter]))
        block.clear()
    for z in s.split('\n'):
        if z.startswith('```'):
            zaun = not zaun; schliesse(); continue
        if zaun:
            continue
        if not z.strip():
            schliesse(); continue
        if re.match(r'^#{1,6}\s|^\||^---\s*$|^>', z):
            schliesse(); continue
        block.append(z)
    schliesse()
    return aus

def volltext(art, s):
    t = entferne_html(s) if art == 'html' else s
    t = re.sub(r'```.*?```', ' ', t, flags=re.S)
    t = re.sub(r'⟦[^⟧]*⟧', ' ', t)
    return [w for w in norm_text(t).split(' ') if w]

# ------------------------------------------------------------- Vergleichen ---
def mengen_bericht(name, a, b, zeigen=8):
    nur_a, nur_b = sorted(set(a) - set(b)), sorted(set(b) - set(a))
    if not nur_a and not nur_b:
        print(f"  {name:22s} ✓  {len(set(a))} gleich")
        return True
    print(f"  {name:22s} ✗  nur im Entwurf: {nur_a[:zeigen]}  nur in der Ausgabe: {nur_b[:zeigen]}")
    return False

def folgen_bericht(name, a, b, zeigen=6):
    if a == b:
        print(f"  {name:22s} ✓  {len(a)} gleich, in gleicher Folge")
        return True
    if len(a) != len(b):
        print(f"  {name:22s} ✗  Zahl {len(a)} gegen {len(b)}")
    else:
        print(f"  {name:22s} ✗  gleiche Zahl ({len(a)}), andere Folge oder Wortlaut")
    gezeigt = 0
    for zeile in difflib.unified_diff(a, b, 'Entwurf', 'Ausgabe', lineterm='', n=0):
        if zeile.startswith(('---', '+++', '@@')):
            continue
        print(f"      {zeile[:110]}")
        gezeigt += 1
        if gezeigt >= zeigen:
            print("      …"); break
    return False

rc = 0
for entwurf_spez, ausgabe_spez in paare:
    print()
    print(f"── {entwurf_spez}")
    print(f"   gegen {ausgabe_spez}")
    print("   " + "─" * 74)
    e_teile, e_art = lies(entwurf_spez)
    a_teile, a_art = lies(ausgabe_spez)
    if 'gemischt' in (e_art, a_art):
        print("  FEHLER: eine Seite mischt .md und .html"); sys.exit(2)

    def sammle(teile, f):
        aus = []
        for art, s in teile:
            r = f(art, s)
            aus = (aus | r) if isinstance(r, set) else aus + r
        return aus

    def sammle_menge(teile, f):
        aus = set()
        for art, s in teile:
            aus |= f(art, s)
        return aus

    ok = True
    ok &= folgen_bericht("Ueberschriften", sammle(e_teile, ueberschriften), sammle(a_teile, ueberschriften))
    ok &= folgen_bericht("Traegertafel", sammle(e_teile, tafelzeilen), sammle(a_teile, tafelzeilen))
    ok &= mengen_bericht("Ziffern (Menge)", sammle_menge(e_teile, ziffern), sammle_menge(a_teile, ziffern))
    ok &= folgen_bericht("Figuren", sammle(e_teile, figuren), sammle(a_teile, figuren))
    ok &= folgen_bericht("Absatz-Anfaenge", sammle(e_teile, absatz_anfaenge), sammle(a_teile, absatz_anfaenge))

    we, wa = sammle(e_teile, volltext), sammle(a_teile, volltext)
    sm = difflib.SequenceMatcher(None, we, wa, autojunk=False)
    gleich = sum(b.size for b in sm.get_matching_blocks())
    quote = 100.0 * gleich / max(len(we), len(wa), 1)
    print(f"  {'Volltext (berichtend)':22s} ·  {len(we)} gegen {len(wa)} Woerter, "
          f"{quote:.1f}% gemeinsam — setzt KEINEN Exit-Code")
    if not ok:
        rc = 1

print()
print("── " + ("alle fuenf brechenden Groessen gleich." if rc == 0 else
               "MINDESTENS EINE brechende Groesse weicht ab."))
sys.exit(rc)
PY
