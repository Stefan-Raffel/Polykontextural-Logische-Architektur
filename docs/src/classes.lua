-- classes.lua — pandoc-Filter fuer die Papierstrecke (Vorgang 8, V8.2)
--
-- Zwei Aufgaben, beide aus dem Stylesheet begruendet und nicht aus Geschmack:
--
--   1. class="num" statt style="text-align: right"
--      `docs/assets/style.css` traegt `td.num, th.num { text-align: right;
--      font-variant-numeric: tabular-nums; }`. pandoc schreibt fuer eine
--      rechtsbuendige Spalte ein Inline-`style` und keine Klasse; damit ginge
--      `tabular-nums` verloren — die Ziffern stuenden nicht mehr in Spalten.
--      Der Filter setzt die Klasse und nimmt die Ausrichtung aus der
--      Spaltenangabe, damit pandoc das `style` nicht zusaetzlich schreibt.
--
--   2. <div class="tablewrap"> um jede Tabelle
--      `.tablewrap { overflow-x: auto; }` faengt den waagerechten Ueberlauf;
--      die Tabellen tragen `min-width: 30rem`. Ohne den Umschlag laeuft die
--      Seite auf schmalen Geraeten waagerecht ueber.
--
-- Beide Klassen stehen in der Handfassung an denselben Stellen. Der Filter
-- stellt sie her, er erfindet sie nicht.
--
--   3. Abschnittstrenner bleiben unsichtbar
--      Die Quelle trennt ihre Abschnitte mit `---`. Die Handfassung setzt an
--      diesen vierzehn Stellen einen Kommentar und keine Linie; `hr` ist im
--      Stylesheet ueberhaupt nicht gefuehrt. Ohne diese Regel erschienen
--      vierzehn waagerechte Linien, die die Seite nie hatte. Der Trenner ist
--      eine Lesehilfe der Quelle und keine Aussage der Seite.

local RULE = "<!-- ===================================================================== -->"

function HorizontalRule()
  return pandoc.RawBlock("html", RULE)
end

local function mark_right(rows, aligns)
  for _, row in ipairs(rows) do
    for i, cell in ipairs(row.cells) do
      if aligns[i] == "AlignRight" then
        cell.attr.classes:insert("num")
      end
    end
  end
end

function Table(tbl)
  local aligns = {}
  for i, spec in ipairs(tbl.colspecs) do
    aligns[i] = spec[1]
  end

  mark_right(tbl.head.rows, aligns)
  for _, body in ipairs(tbl.bodies) do
    mark_right(body.head, aligns)
    mark_right(body.body, aligns)
  end
  mark_right(tbl.foot.rows, aligns)

  -- Ausrichtung aus der Spaltenangabe nehmen: die Klasse traegt sie jetzt.
  for i, spec in ipairs(tbl.colspecs) do
    tbl.colspecs[i] = { "AlignDefault", spec[2] }
  end

  return pandoc.Div(tbl, pandoc.Attr("", { "tablewrap" }))
end

-- Eine Tafel traegt in der Handfassung zusaetzlich `stand` (nur Aussenabstand,
-- `.stand { margin: 2.4rem 0; }`). Eine Pipe-Tabelle kann kein Attribut tragen;
-- die Quelle umschliesst sie darum mit `::: stand`. Der Table-Filter ist zu
-- diesem Zeitpunkt schon gelaufen, die Tabelle also bereits ein tablewrap-Div —
-- die beiden Klassen werden hier zu einem Umschlag zusammengezogen statt
-- ineinandergeschachtelt.
function Div(div)
  if div.classes:includes("stand") and #div.content == 1
     and div.content[1].t == "Div" and div.content[1].classes:includes("tablewrap") then
    local inner = div.content[1]
    inner.classes = pandoc.List({ "tablewrap", "stand" })
    return inner
  end
end
