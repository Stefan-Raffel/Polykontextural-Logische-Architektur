#!/usr/bin/env python3
"""erzeuge_pdf.py — die Papierausgabe als PDF, aus derselben Quelle wie die Seite.

    ./erzeuge_pdf.py de ../KorpusRev2/PKL-Rev6-de.pdf
    ./erzeuge_pdf.py en ../KorpusRev2/PKL-Rev6-en.pdf
    ./erzeuge_pdf.py de ../KorpusRev2/PKL-Rev6-de-TeilA.pdf --nur-teil-a

DAS ERZEUGNIS LIEGT IM KORPUS UND NICHT IM REPOSITORIUM. Zwei Fassungen sind
zusammen rund 2,4 MB Binaerdaten; `CLAUDE.md` §7 haelt den Quellbestand bei
wenigen hundert Dateien unter 1 MB, und zwei Ausgaben waeren ein
Vielfaches des Bestandes, den sie beschreiben. Verfolgt wird darum die ROUTE und
nicht ihr Ergebnis: wer das PDF braucht, erzeugt es aus `docs/<sprache>.html`,
und das Ergebnis haengt am selben Stand wie die Seite.

DIE QUELLE IST `docs/<sprache>.html` UND NICHT DER ENTWURF. Der Grund ist die
Hausform: die HTML-Fassung IST der Bestand (`erzeuge_ausgabe.py` stellt sie her,
`ausgabe_probe.sh` haelt sie gegen den Entwurf). Ein PDF, das noch einmal aus dem
Entwurf gesetzt wuerde, waere eine ZWEITE Darstellung ohne Route dazwischen —
genau das, was Ausweg C beseitigt hat. So ist das PDF ein Abzug des Bestandes,
und jede Probe, die fuer die Seite gilt, gilt fuer den Abzug mit.

Renderer: Chromium ueber Playwright (`python3 -m playwright install chromium`).
Auf dieser Maschine war beim Bau KEIN Renderer vorhanden — kein wkhtmltopdf, kein
weasyprint, kein pandoc, kein Browser, kein brew; `cupsfilter` hat keinen Filter
text/html -> application/pdf. Chromium ist gewaehlt, weil es dieselbe Engine-Art
ist, fuer die das Stylesheet geschrieben wurde: der `@media print`-Block in
`docs/assets/style.css` greift, ohne dass eine zweite Formatvorlage entsteht.

WAS DIESES SKRIPT AM DOKUMENT AENDERT, tut es im Browser und nicht an der Datei:
  1. die Kopfleiste und das Inhaltsverzeichnis der Seite entfallen (Bildschirm-
     moebel; das PDF bekommt sein eigenes, siehe 3);
  2. die Fusszeile mit den Archivverweisen entfaellt — ein Papierabzug kann
     nirgendwohin klicken, und die Quellenangaben stehen im Fliesstext;
  3. ein Deckblatt und ein gedrucktes Inhaltsverzeichnis mit SEITENZAHLEN
     kommen hinzu, beides aus den Ueberschriften des Dokuments erzeugt;
  4. `--nur-teil-a` schneidet Teil B heraus und setzt an seine Stelle einen
     Verweis auf die Netzfassung.

Die Seitenzahlen des Inhaltsverzeichnisses sind GEMESSEN und nicht geschaetzt:
das Dokument wird zweimal gesetzt. Der erste Lauf legt zu jeder Ueberschrift eine
Marke, aus deren Lage im ersten PDF die Seite folgt; der zweite Lauf setzt die
Zahlen ein. Ein Inhaltsverzeichnis mit geratenen Zahlen waere schlimmer als
keines.
"""
import asyncio
import os
import re
import sys

REPO = os.path.dirname(os.path.abspath(__file__))

SPRACHEN = {
    'de': dict(
        quelle='docs/de.html',
        titel='Die mathematische Gestalt der Architektur',
        untertitel='Polykontexturale Logik in Lean 4 und Mathlib',
        fassung='Fassung PKL Rev6, in zwei Teilen',
        datum='8. August 2026',
        inhalt='Inhalt',
        seite='Seite',
        teilb_titel='Teil B · Der Apparat',
        teilb_hinweis=(
            'Teil B — der Apparat: Trägertafel, Beweisform, Register, Sicherungen, '
            'Werkzeuge, Fehlerliste und Zählrouten — steht in der Netzfassung. '
            'Er ist zum Nachschlagen gebaut und nicht zum Lesen am Stück; die '
            'Ziffern dieses Teils verweisen dorthin.'),
        anker='Netzfassung: ',
    ),
    'en': dict(
        quelle='docs/en.html',
        titel='The Mathematical Shape of the Architecture',
        untertitel='Polycontextural logic in Lean 4 and Mathlib',
        fassung='Edition PKL Rev6, in two parts',
        datum='8 August 2026',
        inhalt='Contents',
        seite='Page',
        teilb_titel='Part B · The Apparatus',
        teilb_hinweis=(
            'Part B — the apparatus: carrier table, mode of proof, register, '
            'safeguards, instruments, list of errors and counting routes — is in '
            'the web edition. It is built for looking things up, not for reading '
            'through; the numerals of this part point there.'),
        anker='Web edition: ',
    ),
}

NETZ = 'https://stefan-raffel.github.io/Polykontextural-Logische-Architektur/'

# --- Druckformat -------------------------------------------------------------
# Der Kopf bleibt leer, die Fusszeile traegt allein die Seitenzahl: eine
# Kopfzeile mit Dateinamen und Datum ist Browser-Moebel und keine Auskunft des
# Papiers.
KOPF = '<div></div>'
FUSS = ('<div style="width:100%;font:9pt Georgia,serif;color:#555;'
        'text-align:center;padding-top:6mm;">'
        '<span class="pageNumber"></span></div>')

DRUCK_CSS = """
/* --- Bildschirmmoebel entfaellt ---------------------------------------- */
.topbar, nav.toc, footer.pagefoot { display: none !important; }

/* --- Satzspiegel -------------------------------------------------------- */
html, body { background: #fff !important; color: #111 !important; }
main { max-width: none !important; margin: 0 !important; padding: 0 !important; }
body { font-size: 10.5pt; line-height: 1.55; }

/* --- Umbruchdisziplin ---------------------------------------------------
   Eine Ueberschrift am Seitenfuss ist ein Fehler, keine Geschmacksfrage;
   dasselbe gilt fuer eine zerrissene Figur, eine zerrissene Tafelzeile und
   fuer Schusterjungen. */
h1 { break-before: page; page-break-before: always; }
h1:first-of-type { break-before: auto; page-break-before: avoid; }
h1, h2, h3, h4 { break-after: avoid; page-break-after: avoid; }
figure, table, pre, blockquote, p.formel { break-inside: avoid; page-break-inside: avoid; }
tr, li { break-inside: avoid; }
p { orphans: 3; widows: 3; }

/* --- Figuren: das SVG muss in den Satzspiegel ---------------------------- */
figure svg { max-width: 100% !important; height: auto !important; }

/* --- Tafeln ------------------------------------------------------------- */
table { font-size: 8.6pt; width: 100%; }
td, th { padding: 2.5pt 4pt; }
.tablewrap { overflow: visible !important; }

/* --- Verweise: im Abzug ist eine Farbe ohne Ziel eine Behauptung --------- */
a { color: #111 !important; text-decoration: none !important; }

/* --- Deckblatt und gedrucktes Inhaltsverzeichnis ------------------------ */
#pdf-deckblatt {
  break-after: page; page-break-after: always;
  display: flex; flex-direction: column; justify-content: center;
  min-height: 210mm; text-align: left;
}
#pdf-deckblatt .t  { font-size: 22pt; line-height: 1.25; margin: 0 0 1.2rem 0; font-weight: 600; }
#pdf-deckblatt .u  { font-size: 12pt; color: #333; margin: 0 0 2.6rem 0; }
#pdf-deckblatt .f  { font-size: 11pt; color: #333; margin: 0 0 .3rem 0; }
#pdf-deckblatt .d  { font-size: 11pt; color: #333; margin: 0 0 2.2rem 0; }
/* Die Adresse ohne Ligaturen: Georgia setzt `ff` als ein Zeichen, und eine
   Adresse, die man nicht sauber herauskopieren kann, ist keine Adresse. */
#pdf-deckblatt .n  { font-size: 9.5pt; color: #555; font-variant-ligatures: none; }
#pdf-teilb-ersatz strong { font-variant-ligatures: none; }
#pdf-inhalt { break-after: page; page-break-after: always; }
#pdf-inhalt h2 { font-size: 13pt; margin: 0 0 1.2rem 0; }
#pdf-inhalt ol { list-style: none; margin: 0; padding: 0; }
#pdf-inhalt li { display: flex; align-items: baseline; gap: .4rem; font-size: 10pt; margin: .28rem 0; }
#pdf-inhalt li.e2 { padding-left: 1.4rem; font-size: 9.2pt; color: #333; }
#pdf-inhalt .punkte { flex: 1; border-bottom: 1px dotted #aaa; transform: translateY(-.22em); }
#pdf-inhalt .nr { font-variant-numeric: tabular-nums; color: #333; }
#pdf-teilb-ersatz { break-before: page; page-break-before: always; }
#pdf-teilb-ersatz p { font-size: 10.5pt; }
"""


def js_umbau(c, nur_teil_a, mit_marken):
    """Was im Browser am DOM geschieht — als eine Funktion, damit beide Laeufe
    dasselbe Dokument sehen und die gemessenen Seitenzahlen gelten."""
    return f"""
(() => {{
  const c = {{
    titel: {c['titel']!r}, untertitel: {c['untertitel']!r},
    fassung: {c['fassung']!r}, datum: {c['datum']!r},
    inhalt: {c['inhalt']!r}, seite: {c['seite']!r},
    teilbTitel: {c['teilb_titel']!r}, teilbHinweis: {c['teilb_hinweis']!r},
    anker: {c['anker']!r}, netz: {NETZ!r},
  }};
  const nurTeilA = {str(bool(nur_teil_a)).lower()};
  const mitMarken = {str(bool(mit_marken)).lower()};
  const main = document.querySelector('main') || document.body;

  // --- Teil B herausnehmen -------------------------------------------------
  // Geschnitten wird an der Ueberschrift, die Teil B eroeffnet, und zwar bis
  // zum Ende des Dokuments — nicht ueber eine Zaehlung von Elementen.
  if (nurTeilA) {{
    const hs = [...main.querySelectorAll('h1')];
    const b = hs.find(h => h.textContent.trim().startsWith(c.teilbTitel.split('·')[0].trim())
                        || h.id === 'b0' || /(^|\\s)Teil B|Part B/.test(h.textContent));
    if (b) {{
      let n = b;
      while (n) {{ const w = n.nextSibling; n.remove(); n = w; }}
      const ers = document.createElement('section');
      ers.id = 'pdf-teilb-ersatz';
      ers.innerHTML = '<h1>' + c.teilbTitel + '</h1><p>' + c.teilbHinweis
                    + '</p><p>' + c.anker + '<strong>' + c.netz + '</strong></p>';
      main.appendChild(ers);
    }}
  }}

  // --- Ueberschriften einsammeln, BEVOR Deckblatt und Inhalt entstehen -----
  const eintraege = [...main.querySelectorAll('h1, h2')]
    .filter(h => !h.closest('#pdf-inhalt') && !h.closest('#pdf-deckblatt'))
    .map((h, i) => {{
      if (!h.id) h.id = 'pdfh' + i;
      return {{ id: h.id, rang: h.tagName === 'H1' ? 1 : 2, text: h.textContent.trim() }};
    }});

  // --- Marken fuer die Seitenmessung --------------------------------------
  // Eine Marke ist ein leeres Element mit bekanntem Text; im ersten PDF wird
  // ihre Seite ueber die Textlage bestimmt. Im zweiten Lauf entfaellt sie.
  if (mitMarken) {{
    eintraege.forEach((e, i) => {{
      const m = document.createElement('span');
      m.textContent = '\\u2063PDFMARKE' + i + '\\u2063';
      m.style.cssText = 'font-size:6pt;color:#fff;';
      document.getElementById(e.id).prepend(m);
    }});
  }}

  // --- Deckblatt -----------------------------------------------------------
  const deck = document.createElement('section');
  deck.id = 'pdf-deckblatt';
  deck.innerHTML =
      '<p class="t">' + c.titel + '</p>'
    + '<p class="u">' + c.untertitel + '</p>'
    + '<p class="f">' + c.fassung + '</p>'
    + '<p class="d">' + c.datum + '</p>'
    + '<p class="n">' + c.anker + c.netz + '</p>';
  main.prepend(deck);

  // --- Inhaltsverzeichnis --------------------------------------------------
  const inh = document.createElement('section');
  inh.id = 'pdf-inhalt';
  inh.innerHTML = '<h2>' + c.inhalt + '</h2><ol>' + eintraege.map((e, i) =>
      '<li class="e' + e.rang + '"><span class="tx">' + e.text + '</span>'
    + '<span class="punkte"></span><span class="nr" data-nr="' + i + '">·</span></li>'
  ).join('') + '</ol>';
  deck.after(inh);

  return eintraege.map(e => e.text);
}})();
"""


async def setze(sprache, ziel, nur_teil_a):
    from playwright.async_api import async_playwright

    c = SPRACHEN[sprache]
    quelle = 'file://' + os.path.join(REPO, c['quelle'])
    os.makedirs(os.path.dirname(os.path.abspath(ziel)) or '.', exist_ok=True)

    pdf_args = dict(format='A4', print_background=True,
                    margin=dict(top='18mm', bottom='18mm', left='20mm', right='20mm'),
                    display_header_footer=True,
                    header_template=KOPF, footer_template=FUSS)

    async with async_playwright() as p:
        browser = await p.chromium.launch()
        seite = await browser.new_page()

        # --- Lauf 1: mit Marken, nur um die Seitenzahlen zu messen ----------
        await seite.goto(quelle, wait_until='networkidle')
        await seite.add_style_tag(content=DRUCK_CSS)
        ueberschriften = await seite.evaluate(js_umbau(c, nur_teil_a, mit_marken=True))
        roh = await seite.pdf(**pdf_args)

        seiten = seiten_der_marken(roh, len(ueberschriften))

        # --- Lauf 2: ohne Marken, mit den gemessenen Zahlen -----------------
        await seite.goto(quelle, wait_until='networkidle')
        await seite.add_style_tag(content=DRUCK_CSS)
        await seite.evaluate(js_umbau(c, nur_teil_a, mit_marken=False))
        await seite.evaluate("""(s) => {
          document.querySelectorAll('#pdf-inhalt .nr').forEach(n => {
            const v = s[+n.dataset.nr];
            n.textContent = (v === undefined || v === null) ? '·' : String(v);
          });
        }""", seiten)

        # Deckblatt und Inhalt tragen KEINE Seitenzahl: eine Ziffer auf dem
        # Deckblatt sieht nach unfertigem Auszug aus. Chromium kann die
        # Fusszeile nicht seitenweise abschalten — also zwei Auszuege mit
        # `page_ranges` und ein Zusammenfuegen. Die Zaehlung bleibt dieselbe:
        # das Inhaltsverzeichnis nennt die PHYSISCHE Seite, und die ist in
        # beiden Auszuegen dieselbe.
        vorspann = await seite.pdf(**{**pdf_args,
                                      'display_header_footer': False,
                                      'page_ranges': '1-2'})
        rumpf = await seite.pdf(**{**pdf_args, 'page_ranges': '3-'})
        await browser.close()

    fertig = _fuege(vorspann, rumpf)
    open(ziel, 'wb').write(fertig)
    return sum(1 for s in seiten if s), len(seiten), zaehle_seiten(fertig)


def _leser(roh):
    import io
    import pypdf
    return pypdf.PdfReader(io.BytesIO(roh))


def _fuege(*teile):
    import io
    import pypdf
    schreiber = pypdf.PdfWriter()
    for t in teile:
        for s in _leser(t).pages:
            schreiber.add_page(s)
    puffer = io.BytesIO()
    schreiber.write(puffer)
    return puffer.getvalue()


def zaehle_seiten(roh):
    return len(_leser(roh).pages)


def seiten_der_marken(roh, anzahl):
    """Zu jeder Marke die Seite, auf der sie steht — am gesetzten PDF gelesen.

    Ein erster Anlauf las die Inhaltsstroeme selbst und fand NICHTS: Chromium
    bettet Schriften als Teilmenge ein, und der Text steht als Glyphenkette und
    nicht als ASCII im Strom. Die Route lieferte kein falsches Ergebnis, sondern
    ein leeres — der Fallstrick, der wie eine gute Nachricht aussieht. Die
    tragende Route ist die Textentnahme mit der ToUnicode-Tafel, also `pypdf`.

    Findet sich eine Marke nicht, traegt ihr Eintrag `None` und das
    Inhaltsverzeichnis an dieser Stelle einen Punkt — keine geratene Zahl.
    """
    leser = _leser(roh)
    lage = {}
    for nr, seite in enumerate(leser.pages, start=1):
        try:
            text = seite.extract_text() or ''
        except Exception:
            continue
        for treffer in re.finditer(r'PDFMARKE(\d+)', text):
            k = int(treffer.group(1))
            lage.setdefault(k, nr)
    return [lage.get(k) for k in range(anzahl)]


def main():
    if len(sys.argv) < 3 or sys.argv[1] not in SPRACHEN:
        print(__doc__)
        sys.exit(2)
    sprache, ziel = sys.argv[1], sys.argv[2]
    nur_teil_a = '--nur-teil-a' in sys.argv[3:]
    gemessen, gesamt, seiten = asyncio.run(setze(sprache, ziel, nur_teil_a))
    art = 'Teil A allein' if nur_teil_a else 'beide Teile'
    fehlt = gesamt - gemessen
    warnung = '' if not fehlt else f'  ACHTUNG: {fehlt} ohne gemessene Seite (tragen einen Punkt)'
    print(f'  {ziel}: {seiten} Seiten, {gemessen}/{gesamt} Inhaltseintraege '
          f'mit gemessener Seitenzahl ({art}){warnung}')


if __name__ == '__main__':
    main()
