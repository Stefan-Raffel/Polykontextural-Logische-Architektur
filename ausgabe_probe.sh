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
# NEUN BRECHENDE GROESSEN, je Sprachpaar:
#   1. Ueberschriften — Folge und Wortlaut, in Dokumentreihenfolge
#   2. Traegertafel   — Zahl der Zeilen und Menge der Ziffern
#   3. Ziffern        — die MENGE der Ziffern des Dokuments, nicht die Zahl der
#                       Vorkommen: eine Ziffer darf in Teil A mehrfach stehen
#                       (Querverweise sind ein Bogen des Papiers, kein Fehler)
#   4. Figuren        — Nummer UND WORTLAUT der Bildunterschriften; im Entwurf
#                       steht er in der Marke hinter "Bildunterschrift:"/"Caption:"
#   5. Absatz-Anfaenge — die ersten sechs Woerter jedes Textabsatzes, in Folge
#   6. Zitatbloecke   — dort stehen die Setzungen; im Entwurf ohne den Vorspann
#                       vor der ersten Trennlinie
#   7. Code           — Code-Spannen und Code-Bloecke, in Folge, exakt
#   8. Formeln        — Anzeigeformeln; verglichen wird die LaTeX-QUELLE
#                       ($$…$$ gegen data-tex), nicht die Darstellung
#   9. Ueberschriftenraenge — die Gliederungstiefe nach festgelegter Abbildung
#                       (siehe `raenge`), exakt und ohne Toleranz
#
# DIE AUSNAHMEN, GEPRUEFT (Auflage aus der Sondierung: jede begruendete Ausnahme
# einer Probe ist ein blinder Fleck mit Begruendung). Je Klasse: was sie traegt,
# und welche Groesse sie deckt.
#
#   Inhaltsverzeichnis  eine Kopie der Ueberschriften und Navigationsziele
#                       -> Ziele: Lint-Gruppe (F); Wortlaut: abgeleitet, behauptet
#                          nichts. MOEBEL-GRUND.
#   Zitatblock          die SETZUNGEN des Papiers            -> Groesse 6
#   Code                Musterbeispiele und Lean-Namen        -> Groesse 7
#   Bildunterschrift    die Deutung jeder Figur               -> Groesse 4
#   Titelblock          Ausgabebezeichnung, Datum, Zeiger auf den Stand-Anker
#                       -> keine Behauptung, nur eine Ortsangabe; dass der Zeiger
#                          aufloest, prueft die Erzeugungs-Vorgabe. MOEBEL-GRUND.
#   Fusszeile           Ausgabe, Datum, Verweise auf die Archive
#                       -> die Quellenangaben stehen im FLIESSTEXT am Ende von
#                          Teil A und gehoeren NICHT zusaetzlich in die Fusszeile:
#                          zweimal dieselbe Auskunft, und die zweite saehe keine
#                          Probe. MOEBEL-GRUND, sobald die Doppelung entfaellt.
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
def ohne_moebel(s, auch_kopf=True):
    """Die Moebel einer Ausgabe sind kein Text des Papiers: Titelblock,
    Inhaltsverzeichnis, Fusszeile und Bildunterschriften. Das
    Inhaltsverzeichnis faellt IMMER weg — es ist eine Kopie der Ueberschriften
    und wuerde jede von ihnen doppelt zaehlen."""
    s = re.sub(r'(?is)<nav\b.*?</nav>', ' ', s)
    if auch_kopf:
        # Ein Zitatblock ist kein Absatz: im Entwurf steht er als >-Zeile und
        # wird dort uebersprungen.
        s = re.sub(r'(?is)<blockquote\b.*?</blockquote>', ' ', s)
        s = re.sub(r'(?is)<header\b.*?</header>', ' ', s)
        s = re.sub(r'(?is)<footer\b.*?</footer>', ' ', s)
        s = re.sub(r'(?is)<figure\b.*?</figure>', ' ', s)
    return s

def entferne_html(s):
    s = re.sub(r'(?is)<(script|style)\b.*?</\1>', ' ', s)
    s = re.sub(r'<[^>]+>', ' ', s)
    return htmlmod.unescape(s)

def ueberschriften(art, s):
    if art == 'html':
        roh = re.findall(r'(?is)<h[1-6][^>]*>(.*?)</h[1-6]>', ohne_moebel(s, auch_kopf=False))
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
    t = re.sub(r'\s+', ' ', t)
    # Inline-Auszeichnung wird beim Entfernen zu einem Leerzeichen; ohne diese
    # Zeile stuende "evolutiv ," gegen "evolutiv,".
    t = re.sub(r'\s+([,.;:!?])', r'\1', t)
    # Dasselbe an Klammern: `(\`2^1 = 2\`)` wird im Entwurf zu "(2^1 = 2)" und in
    # der Ausgabe ueber <code> zu "( 2^1 = 2 )".
    t = re.sub(r'\(\s+', '(', t)
    t = re.sub(r'\s+\)', ')', t)
    return t.strip()

def tafelzeilen(art, s):
    """Zeilen der Traegertafel: Ziffer UND Traeger, nicht nur die Ziffer.

    Bis zur Sondierung verglich diese Groesse allein die Ziffernspalte. Gemessen
    an einem eingesetzten Treffer war das der teuerste der drei blinden Flecken:
    eine geaenderte Tabellenzelle bei gleicher Zeilenzahl blieb unsichtbar — und
    der Traegername ist der tragende Inhalt von Teil B. Verglichen wird jetzt die
    Zeile als Ganzes, exakt und ohne Toleranz."""
    if art == 'html':
        aus = []
        for z in re.findall(r'(?is)<tr[^>]*>(.*?)</tr>', s):
            zellen = [norm_text(entferne_html(c)) for c in
                      re.findall(r'(?is)<t[dh][^>]*>(.*?)</t[dh]>', z)]
            if zellen and re.match(r'^\[\d+\]$|^—$|^-$', zellen[0]):
                aus.append(' | '.join(zellen[:2]))
        return aus
    aus = []
    for z in s.split('\n'):
        m = re.match(r'^\|\s*(\[\d+\]|—)\s*\|([^|]*)\|', z)
        if m:
            aus.append(norm_text(m.group(1)) + ' | ' + norm_text(m.group(2)))
    return aus

def ziffern(art, s):
    # Code ist keine Prosa: `[0,1]` ist eine Liste und keine Verweisung. Erst
    # die Code-Spannen entfernen, dann suchen — dieselbe Reihenfolge wie in der
    # Ziffern-Wache des Lints.
    if art == 'html':
        text = entferne_html(re.sub(r'(?is)<(code|pre)\b.*?</\1>', ' ', ohne_moebel(s, auch_kopf=False)))
    else:
        text = re.sub(r'```.*?```', ' ', s, flags=re.S)
        text = re.sub(r'`[^`\n]*`', ' ', text)
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
    """Im Entwurf steht eine Figur als Marke ⟦Figur n …⟧, in der Ausgabe als
    <figcaption>. Der blosse Wortlaut "Figur n" taugt nicht: der Entwurf nennt
    fruehere Nummern im Fliesstext ("dort Figur 1")."""
    if art == 'html':
        return [norm_text(entferne_html(q))
                for q in re.findall(r'(?is)<figcaption[^>]*>(.*?)</figcaption>', s)]
    aus = []
    for q in re.findall(r'⟦(.*?)⟧', s, flags=re.S):
        t = norm_text(q)
        m = re.match(r'\s*(Figur|Figure|Abbildung)\s+(\d+)', t)
        if not m:
            continue
        # Der Wortlaut steht in der Marke hinter "Bildunterschrift:" bzw.
        # "Caption:". Bis zur Entscheidung zu Schritt 4 verglich diese Groesse
        # nur die NUMMER — die Deutung jeder Figur war damit ungeprueft.
        u = re.search(r'(?:Bildunterschrift|Caption):\s*(.*)$', t)
        aus.append(f'{m.group(1)} {m.group(2)} - {u.group(1).strip()}' if u
                   else f'{m.group(1)} {m.group(2)}')
    return aus

def absatz_anfaenge(art, s, woerter=6):
    """Der Anfang jedes Textabsatzes, normalisiert. Faengt einen gestrichenen,
    eingefuegten oder verschobenen Absatz — und zwar EXAKT, ohne Zahlentoleranz.
    Markup faellt vorher weg, darum traegt die Groesse ueber beide Formate."""
    aus = []
    if art == 'html':
        # <p…> und NICHT <pre>: `<p[^>]*>` faengt beides, und dann wandert
        # ein Codeblock in den Absatz davor.
        rumpf = re.sub(r'(?is)<p class="formel".*?</p>', ' ', ohne_moebel(s))
        for roh in re.findall(r'(?is)<p(?:\s[^>]*)?>(.*?)</p>', rumpf):
            if '<path' in roh or '<line' in roh or '<text' in roh:
                continue
            t = norm_text(entferne_html(roh))
            if len(t.split(' ')) >= woerter:
                aus.append(' '.join(t.split(' ')[:woerter]))
        return aus
    # Marken ⟦…⟧ sind Anweisungen an die Erzeugung und kein Text der Ausgabe;
    # sie fallen vor der Absatzbildung weg. Anzeigeformeln ebenso: sie sind kein
    # Absatz, und die Formel-Groesse vergleicht sie an ihrer Quelle.
    s = re.sub(r'⟦.*?⟧', '', s, flags=re.S)
    s = re.sub(r'\$\$.+?\$\$', '', s, flags=re.S)
    zaun, block, liste = False, [], False
    def schliesse():
        t = norm_text(' '.join(block))
        if t and len(t.split(' ')) >= woerter:
            aus.append(' '.join(t.split(' ')[:woerter]))
        block.clear()
    for z in s.split('\n'):
        if z.startswith('```'):
            zaun = not zaun; schliesse(); liste = False; continue
        if zaun:
            continue
        if not z.strip():
            schliesse(); liste = False; continue
        # Ein Listenpunkt laeuft bis zur naechsten Leerzeile. Ohne diesen Zustand
        # wird jede Fortsetzungszeile eines umbrochenen Punktes zu einem
        # Phantom-Absatz — an Teil B waren es fuenfzehn.
        if liste:
            continue
        # Ueberschrift, Tafelzeile, Trennlinie, Zitatblock und Listenpunkt sind
        # keine Absaetze: im HTML stehen sie als h/tr/hr/blockquote/li und nicht
        # als p. Verglichen wird Prosa gegen Prosa.
        if re.match(r'^#{1,6}\s|^\||^---\s*$|^>', z):
            schliesse(); continue
        if re.match(r'^\s*[-*+]\s|^\s*\d+\.\s', z):
            schliesse(); liste = True; continue
        # Ein eingerueckter Block ist Code (Markdown-Konvention: vier Leerzeichen)
        # und steht in der Ausgabe als pre/code, nicht als p.
        if re.match(r'^(    |\t)', z):
            schliesse(); continue
        if z.startswith(' '):
            block.append(z.strip()); continue
        block.append(z)
    schliesse()
    return aus

def zitatbloecke(art, s, woerter=8):
    """Zitatbloecke — dort stehen die Setzungen.

    Gebaut nach einem Fund der Streckenprobe: ein Wandler liess die Setzung aus
    Kapitel 2 fallen ("Eine zweielementige Menge benachbarter Werte ist eine
    Elementarkontextur"), und ALLE Groessen schwiegen — Zitatbloecke waren aus
    dem Absatzvergleich beidseits ausgenommen. Der tragendste Satz eines
    Kapitels fiel unbemerkt aus der Ausgabe.

    Im Entwurf faellt der Vorspann vor der ersten Trennlinie weg: dort steht,
    was den Entwurf betrifft und nicht die Ausgabe. Das ist eine Ortsangabe und
    kein Ermessen."""
    aus = []
    if art == 'html':
        for roh in re.findall(r'(?is)<blockquote\b[^>]*>(.*?)</blockquote>', s):
            t = norm_text(entferne_html(roh))
            if len(t.split(' ')) >= woerter:
                aus.append(' '.join(t.split(' ')[:woerter]))
        return aus
    if re.search(r'(?m)^---\s*$', s):
        s = s[re.search(r'(?m)^---\s*$', s).end():]
    block = []
    def schliesse():
        t = norm_text(' '.join(x.lstrip('> ').rstrip() for x in block))
        if len(t.split(' ')) >= woerter:
            aus.append(' '.join(t.split(' ')[:woerter]))
        block.clear()
    for z in s.split('\n'):
        if z.startswith('>'):
            block.append(z)
        elif block:
            schliesse()
    schliesse()
    return aus

# ABBILDUNG DER RAENGE, festgelegt (Vorgabe zur Streckenprobe an Teil B, §2):
#     erstes `#` einer Entwurfsdatei  -> h1   (der Titel des Teils)
#     jedes weitere `#`              -> h2   (Kapitel)
#     `##`                           -> h3   (Abschnitt)
#     `###`                          -> h4   (Unterabschnitt)
# Sie ist eine ENTSCHEIDUNG und keine Duldung: weicht eine Strecke ab, wird die
# Strecke berichtigt und nicht die Groesse. Vier <h1> in einem Dokument sind
# gueltig und nicht die Gliederung, die dieses Papier fuehrt.
#
# ABWEICHUNG VON DER VORGABE, gemeldet: die Tafel dort fuehrt h1 als
# "Dokumenttitel, einmal je Datei" ohne Gegenstueck im Entwurf. Das traegt nicht,
# wenn ZWEI Teile in EINER Datei stehen — und die Entwuerfe fuehren ihre
# Teiltitel als `#`. Die Regel oben ist positionsgenau und ohne Ermessen; sie
# liefert je Teil genau ein h1 statt je Datei.
def raenge(art, s):
    if art == 'html':
        return [int(m.group(1)) for m in
                re.finditer(r'(?is)<h([1-6])[^>]*>', ohne_moebel(s, auch_kopf=False))]
    aus, zaun, erstes = [], False, True
    for z in s.split('\n'):
        if z.startswith('```'):
            zaun = not zaun; continue
        if zaun:
            continue
        m = re.match(r'^(#{1,6})\s+\S', z)
        if not m:
            continue
        tiefe = len(m.group(1))
        if tiefe == 1 and erstes:
            aus.append(1); erstes = False
        else:
            aus.append(tiefe + 1)
    return aus

def code(art, s):
    """Code-Spannen und Code-Bloecke, in Folge.

    Kapitel 1 argumentiert an Musterbeispielen, Teil B traegt die Lean-Namen in
    Code-Spannen: der tragende Inhalt beider Teile — und bis zur Entscheidung zu
    Schritt 4 gegenueber dem Entwurf ungeprueft. `parity.sh` deckt ihn nur
    zwischen den Sprachen und nur meldend."""
    aus = []
    if art == 'html':
        # Bildunterschriften tragen Code ("Marke `k`, `k+2` Fortsetzungen") und
        # werden von der Figuren-Groesse verglichen; im Entwurf stehen sie in der
        # Marke und fallen dort weg. Ohne diesen Schnitt zaehlte die Ausgabe sie
        # ein zweites Mal — gemessen: 20 gegen 18.
        rest = re.sub(r'(?is)<(nav|header|footer|figure)\b.*?</\1>', ' ', s)
        for m in re.finditer(r'(?is)<pre\b[^>]*>(.*?)</pre>|<code\b[^>]*>(.*?)</code>', rest):
            aus.append(norm_text(entferne_html(m.group(1) if m.group(1) is not None else m.group(2))))
        return aus
    # Dieselben zwei Ausnahmen wie bei den uebrigen Groessen, und aus demselben
    # Grund: der Vorspann vor der ersten Trennlinie betrifft den Entwurf, und
    # die ⟦Marken⟧ sind Anweisungen an die Erzeugung. Beides ist kein Text der
    # Ausgabe. Gemessen ohne sie: `docs/` aus dem Vorspann und `2^C(m,2)` aus
    # der Marke zu Figur 1 waren die einzigen zwei Ueberzaehligen.
    if re.search(r'(?m)^---\s*$', s):
        s = s[re.search(r'(?m)^---\s*$', s).end():]
    s = re.sub(r'⟦.*?⟧', ' ', s, flags=re.S)
    zaun, block = False, []
    for z in s.split('\n'):
        if z.startswith('```'):
            if zaun:
                aus.append(norm_text(' '.join(block))); block = []
            zaun = not zaun
            continue
        if zaun:
            block.append(z); continue
        if re.match(r'^(    |\t)\S', z):
            block.append(z); continue
        if block:
            aus.append(norm_text(' '.join(block))); block = []
        for m in re.finditer(r'`([^`\n]+)`', z):
            aus.append(norm_text(m.group(1)))
    if block:
        aus.append(norm_text(' '.join(block)))
    return aus

def formeln(art, s):
    """Anzeigeformeln: im Entwurf $$…$$, in der Ausgabe das Attribut data-tex.

    Verglichen wird die QUELLE und nicht die Darstellung. Der Bestand hat keinen
    Formelsetzer; die Ausgabe uebersetzt die Formel in den Zeichenvorrat des
    Papiers (∧ ∨ ¬) und behaelt die LaTeX-Quelle im Artefakt. Ohne diese Groesse
    stand die rohe Quelle sichtbar auf der Seite, und keine andere sah es:
    `$$…$$` ist weder Code noch Absatzanfang noch Ueberschrift."""
    if art == 'html':
        roh = re.findall(r'(?is)data-tex="([^"]*)"', s)
    else:
        roh = re.findall(r'\$\$(.+?)\$\$', s, flags=re.S)
    return [re.sub(r'\s+', ' ', x).strip() for x in roh]

def volltext(art, s):
    t = entferne_html(ohne_moebel(s)) if art == 'html' else s
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
    ok &= folgen_bericht("Zitatbloecke", sammle(e_teile, zitatbloecke), sammle(a_teile, zitatbloecke))
    ok &= folgen_bericht("Code", sammle(e_teile, code), sammle(a_teile, code))
    ok &= folgen_bericht("Formeln", sammle(e_teile, formeln), sammle(a_teile, formeln))
    ok &= folgen_bericht("Ueberschriftenraenge",
                         [str(x) for x in sammle(e_teile, raenge)],
                         [str(x) for x in sammle(a_teile, raenge)])

    we, wa = sammle(e_teile, volltext), sammle(a_teile, volltext)
    sm = difflib.SequenceMatcher(None, we, wa, autojunk=False)
    gleich = sum(b.size for b in sm.get_matching_blocks())
    quote = 100.0 * gleich / max(len(we), len(wa), 1)
    print(f"  {'Volltext (berichtend)':22s} ·  {len(we)} gegen {len(wa)} Woerter, "
          f"{quote:.1f}% gemeinsam — setzt KEINEN Exit-Code")
    if not ok:
        rc = 1

print()
print("── " + ("alle neun brechenden Groessen gleich." if rc == 0 else
               "MINDESTENS EINE brechende Groesse weicht ab."))
sys.exit(rc)
PY
