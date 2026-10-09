# -*- coding: utf-8 -*-
"""Rev10, Abschnitt O7 — Abb. Sechseck, halbe Drehung.

Zeigt nur, was am Anker steht (tafelVI_tausch_halbe_drehung, cc0110b):
die sechs Stationen dreier Werte in der Reihenfolge des Kreises, die
Kanten N1/N2, und drei gestrichelte Durchmesser zwischen jeder Station
und ihrem Bild unter dem Tausch der Werte 1 und 3.  Keine Aussage im
Bild;  Herkunft und Status stehen allein in der Unterschrift.

    REV9_FIG_OUT=<dir> python3 fig_sechseck_halbe_drehung.py
erzeugt Abb_Sechseck_Halbe_Drehung(.svg/.png) und _EN.
"""
import os, math
import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.patches import Polygon
from matplotlib import font_manager as fm

OUT = os.environ.get("REV9_FIG_OUT", ".")
D = os.path.join(os.path.dirname(matplotlib.__file__), "mpl-data", "fonts", "ttf") + "/"  # Rev10-Roll-out: DejaVu aus matplotlib selbst, wie die Rev9-Skripte
for f in ["DejaVuSerif.ttf", "DejaVuSerif-Bold.ttf", "DejaVuSans.ttf"]:
    if os.path.exists(D + f):
        fm.fontManager.addfont(D + f)
plt.rcParams["font.family"] = "DejaVu Sans"
plt.rcParams["svg.hashsalt"] = "pkl-rev9"  # Rev10-Roll-out: feste SVG-IDs (byte-reproduzierbar), wie die Rev9-Skripte

INK = "#141414"; GREY = "#8a8a8a"; FILL = "#f4f1ea"
NEG = ["#b0763a", "#3f6f8f"]                      # N1, N2 — wie in den Rev9-Figuren

TXT = {
 "de": {"title": "Drei Werte: die sechs Stationen",
        "sub":   "Kanten: N\u2081 und N\u2082 \u00b7 gestrichelt: Tausch der Werte 1 und 3",
        "n1":    "N\u2081  vertauscht 1 \u2194 2", "n2": "N\u2082  vertauscht 2 \u2194 3",
        "dash":  "Tausch der Werte 1 und 3", "suf": ""},
 "en": {"title": "Three values: the six stations",
        "sub":   "edges: N\u2081 and N\u2082 \u00b7 dashed: exchange of the values 1 and 3",
        "n1":    "N\u2081  exchanges 1 \u2194 2", "n2": "N\u2082  exchanges 2 \u2194 3",
        "dash":  "exchange of the values 1 and 3", "suf": "_EN"},
}

def sw(p, i):                 # N_{i+1}: Werte i+1 und i+2 vertauschen
    a, b = i + 1, i + 2
    return tuple(b if v == a else a if v == b else v for v in p)

def tau(p):                   # Tausch der Werte 1 und 3
    return tuple(3 if v == 1 else 1 if v == 3 else v for v in p)

# die Stationen in der Reihenfolge des Kreises (Guenthers Folge mit N1 beginnend)
p0 = (1, 2, 3); seq = [0, 1, 0, 1, 0, 1]
ring = [p0]
for i in seq:
    ring.append(sw(ring[-1], i))
assert ring[-1] == p0 and len(set(ring[:-1])) == 6
st = ring[:-1]

# gerechnet, wie der Satz es sagt:  tau(Station k) = Station k+3, fuer beide Richtungen
for k, s in enumerate(st):
    assert tau(s) == st[(k + 3) % 6], (s, tau(s))
rev = list(reversed(st))
for k, s in enumerate(rev):
    assert tau(s) == rev[(k + 3) % 6]

def draw(lang):
    T = TXT[lang]
    fig = plt.figure(figsize=(8.6, 7.6), dpi=200)
    ax = fig.add_axes([0.04, 0.12, 0.92, 0.74]); ax.set_aspect("equal"); ax.axis("off")
    fig.text(0.5, 0.94, T["title"], ha="center", fontsize=13, color=INK, family="DejaVu Serif", weight="bold")
    fig.text(0.5, 0.905, T["sub"], ha="center", fontsize=9, color=GREY, family="DejaVu Serif")
    R = 2.2
    pos = {s: np.array([R * math.cos(math.pi / 2 - k * math.pi / 3),
                        R * math.sin(math.pi / 2 - k * math.pi / 3)]) for k, s in enumerate(st)}
    ax.add_patch(Polygon([pos[s] for s in st], closed=True, facecolor=FILL, edgecolor="none"))
    for k in range(3):                                   # die drei Durchmesser
        a, b = st[k], st[k + 3]
        ax.plot(*zip(pos[a], pos[b]), color=INK, lw=1.3, ls=(0, (4, 3)), alpha=0.75, zorder=2)
    for k in range(6):                                   # die Kanten
        a, b = st[k], st[(k + 1) % 6]
        ax.plot(*zip(pos[a], pos[b]), color=NEG[seq[k]], lw=4.2, solid_capstyle="round", zorder=3)
    for s, xy in pos.items():
        ax.plot(*xy, "o", ms=8, color=INK, zorder=5)
        off = xy / np.linalg.norm(xy) * 0.55
        ax.text(*(xy + off), "\u202f".join(map(str, s)), ha="center", va="center",
                fontsize=12, color=INK, family="DejaVu Serif")
    ax.set_xlim(-3.4, 3.4); ax.set_ylim(-3.2, 3.2)
    axG = fig.add_axes([0.06, 0.02, 0.88, 0.07]); axG.axis("off"); axG.set_xlim(0, 1); axG.set_ylim(0, 1)
    axG.plot([0.0, 0.05], [0.5, 0.5], color=NEG[0], lw=3.4, solid_capstyle="round")
    axG.text(0.06, 0.5, T["n1"], va="center", fontsize=9, color=INK)
    axG.plot([0.33, 0.38], [0.5, 0.5], color=NEG[1], lw=3.4, solid_capstyle="round")
    axG.text(0.39, 0.5, T["n2"], va="center", fontsize=9, color=INK)
    axG.plot([0.66, 0.71], [0.5, 0.5], color=INK, lw=1.3, ls=(0, (4, 3)), alpha=0.75)
    axG.text(0.72, 0.5, T["dash"], va="center", fontsize=9, color=INK)
    for ext in ["svg", "png"]:
        fig.savefig(os.path.join(OUT, f"Abb_Sechseck_Halbe_Drehung{T['suf']}.{ext}"),
                    facecolor="white", bbox_inches="tight", pad_inches=0.18)
    plt.close(fig)

for lang in ("de", "en"):
    draw(lang)
print("ok:", " ".join("".join(map(str, s)) for s in st))
