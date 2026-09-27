# -*- coding: utf-8 -*-
"""Rev9 figures, English variant.

Reads the German figure scripts, replaces every label by its English
counterpart (literal source fragments, checked: each must be found), and
runs them with REV9_FIG_SUFFIX=_EN.  The German scripts stay canonical;
this file holds nothing but the translations.

    REV9_FIG_OUT=<dir> python3 rev9_fig_en.py
"""
import os, sys

HERE = os.path.dirname(os.path.abspath(__file__))

EN = {
"fig_oktaeder.py": [
 (r'"Das Negationssystem f\u00fcr vier Werte"', r'"The negation system for four values"'),
 (r'"24 Anordnungen, 36 Negatorkanten \u2014 das abgestumpfte Oktaeder"',
  r'"24 arrangements, 36 negator edges \u2014 the truncated octahedron"'),
 (r'"G\u00fcnthers Kreis 2 als Weg \u00fcber die Kanten"', r'"G\u00fcnther\u2019s circle 2 as a path along the edges"'),
 (r'"24 Negationen, jede Anordnung genau einmal, zur\u00fcck zu p"',
  r'"24 negations, every arrangement exactly once, back to p"'),
 (r'vertauscht 1 \u2194 2', r'exchanges 1 \u2194 2'),
 (r'vertauscht 2 \u2194 3', r'exchanges 2 \u2194 3'),
 (r'vertauscht 3 \u2194 4', r'exchanges 3 \u2194 4'),
 (r'"Fl\u00e4chen, in beiden H\u00e4lften:"', r'"faces, in both halves:"'),
 (r'"Quadrat: N\u2081 und N\u2083 im Wechsel"', r'"square: N\u2081 and N\u2083 alternating"'),
 (r'"Sechseck: N\u2081, N\u2082 oder N\u2082, N\u2083 im Wechsel"', r'"hexagon: N\u2081, N\u2082 or N\u2082, N\u2083 alternating"'),
 (r'"gestrichelt: die zwei emendierten Schritte (N\u2081, N\u2083)"', r'"dashed: the two emended steps (N\u2081, N\u2083)"'),
],
"fig_achse_sechseck.py": [
 (r'"Lille: eine ansteigende Skala, addiert"', r'"Lille: an ascending scale, summed"'),
 (r'"Designation durch einen Wert, durch zwei, durch drei \u2026 \u2014 addiert"',
  r'"designation by one value, by two, by three \u2026 \u2014 added up"'),
 (r'f"durch {k} Wert" + ("" if k == 1 else "e")', r'f"by {k} value" + ("" if k == 1 else "s")'),
 (r'"Die historische Kategorie des Neuen: Paare, gez\u00e4hlt"', r'"Die historische Kategorie des Neuen: pairs, counted"'),
 (r'"m(m\u22121)/2 \u2014 die Paare aus m"', r'"m(m\u22121)/2 \u2014 the pairs from m"'),
 (r'f"{m*(m-1)//2} Paare"', r'f"{m*(m-1)//2} pairs"'),
 (r'"Intervall-Anf\u00e4nge der Thematik"', r'"interval starts of the thematic"'),
 (r'"Wertzahlen der Verbundkontexturen"', r'"value numbers of the compound contextures"'),
 (r'"Drei Werte: das Sechseck und die zwei Genesen"', r'"Three values: the hexagon and the two geneses"'),
 (r'"Ecken: die sechs Anordnungen dreier Werte \u00b7 Kanten: N\u2081 und N\u2082"',
  r'"vertices: the six arrangements of three values \u00b7 edges: N\u2081 and N\u2082"'),
 (r'"der R\u00fccklauf"', r'"the reversal"'),
 (r'"G\u00fcnthers Schreibweise, Tafel II"', r'"G\u00fcnther\u2019s notation, Table II"'),
 (r'vertauscht 1 \u2194 2', r'exchanges 1 \u2194 2'),
 (r'vertauscht 2 \u2194 3', r'exchanges 2 \u2194 3'),
],
}

def run(name):
    src = open(os.path.join(HERE, name), encoding="utf-8").read()
    for de, en in EN[name]:
        if de not in src:
            sys.exit(f"{name}: label not found — {de[:60]}")
        src = src.replace(de, en)
    os.environ["REV9_FIG_SUFFIX"] = "_EN"
    exec(compile(src, name + " [EN]", "exec"), {"__name__": "__main__"})

if __name__ == "__main__":
    for n in EN:
        run(n)
