
# -*- coding: utf-8 -*-
import math, itertools
import os
OUT = os.environ.get("REV9_FIG_OUT", ".")
SUF = os.environ.get("REV9_FIG_SUFFIX", "")
import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.patches import Polygon, Rectangle, FancyArrowPatch
from matplotlib import font_manager as fm

D = os.path.join(os.path.dirname(matplotlib.__file__), "mpl-data", "fonts", "ttf") + "/"  # Rev9-Roll-out: DejaVu aus matplotlib selbst, statt /usr/share/fonts/truetype/dejavu/
plt.rcParams["svg.hashsalt"] = "pkl-rev9"  # Rev9-Roll-out: feste SVG-IDs (byte-reproduzierbar)
for f in ["DejaVuSerif.ttf", "DejaVuSerif-Italic.ttf", "DejaVuSerif-Bold.ttf", "DejaVuSans.ttf", "DejaVuSans-Bold.ttf"]:
    fm.fontManager.addfont(D + f)
plt.rcParams["font.family"] = "DejaVu Sans"

INK = "#141414"; GREY = "#8a8a8a"; LGREY = "#c8c2b6"; ACC = "#7a6a52"
NEG = ["#b0763a", "#3f6f8f", "#8f3f4f"]           # N1, N2, N3 (as in the octahedron figure)
BLOCK = "#e3d8c3"; BLOCK2 = "#efe8da"; FILL = "#f4f1ea"

def title(ax, t, sub):
    ax.text(0.5, 1.06, t, transform=ax.transAxes, ha="center", fontsize=12.5, color=INK,
            family="DejaVu Serif", weight="bold")
    ax.text(0.5, 1.005, sub, transform=ax.transAxes, ha="center", fontsize=9, color=GREY,
            family="DejaVu Serif")

# =====================================================================
# FIGURE 1 — the axis: two constructions, one identity
# =====================================================================
fig = plt.figure(figsize=(12.4, 7.4), dpi=200)

# ---- left: Lille, the ascending scale, summed
axL = fig.add_axes([0.03, 0.40, 0.44, 0.44]); axL.set_aspect("equal"); axL.axis("off")
fig.text(0.25, 0.925, "Lille: eine ansteigende Skala, addiert", ha="center", fontsize=12.5, color=INK,
         family="DejaVu Serif", weight="bold")
fig.text(0.25, 0.895, "Designation durch einen Wert, durch zwei, durch drei \u2026 \u2014 addiert",
         ha="center", fontsize=9, color=GREY, family="DejaVu Serif")
sums = [1, 3, 6, 10]
s = 0.78
for k in range(1, 5):
    y = (4 - k) * 1.05
    for j in range(k):
        axL.add_patch(Rectangle((0.6 + j * 0.95, y), s, s, facecolor=BLOCK,
                                edgecolor=ACC, lw=0.8))
    axL.text(0.35, y + s / 2, f"durch {k} Wert" + ("" if k == 1 else "e"), ha="right", va="center",
             fontsize=8.6, color=GREY, family="DejaVu Serif")
    axL.text(5.05, y + s / 2, f"\u03a3 = {sums[k-1]}", ha="left", va="center", fontsize=11.5,
             color=INK, family="DejaVu Serif", weight="bold")
axL.text(2.6, -0.55, "\u22ee", ha="center", fontsize=14, color=GREY)
axL.text(5.05, -0.55, "\u2026", ha="left", fontsize=12, color=GREY)
axL.set_xlim(-2.4, 6.8); axL.set_ylim(-1.1, 4.3)

# ---- right: HKN, the pairs
axR = fig.add_axes([0.52, 0.40, 0.45, 0.44]); axR.set_aspect("equal"); axR.axis("off")
fig.text(0.745, 0.925, "Die historische Kategorie des Neuen: Paare, gez\u00e4hlt", ha="center", fontsize=12.5, color=INK,
         family="DejaVu Serif", weight="bold")
fig.text(0.745, 0.895, "m(m\u22121)/2 \u2014 die Paare aus m",
         ha="center", fontsize=9, color=GREY, family="DejaVu Serif")
for idx, m in enumerate([3, 4, 5]):
    cx = 1.2 + idx * 2.75; cy = 2.1; r = 0.95
    pts = [(cx + r * math.sin(2 * math.pi * i / m), cy + r * math.cos(2 * math.pi * i / m)) for i in range(m)]
    for a, b in itertools.combinations(range(m), 2):
        axR.plot([pts[a][0], pts[b][0]], [pts[a][1], pts[b][1]], color=ACC, lw=1.4, alpha=0.85)
    for p in pts:
        axR.plot(*p, "o", ms=6.5, color=INK)
    axR.text(cx, cy - 1.55, f"m = {m}", ha="center", fontsize=9, color=GREY, family="DejaVu Serif")
    axR.text(cx, cy - 2.05, f"{m*(m-1)//2} Paare", ha="center", fontsize=11.5, color=INK,
             family="DejaVu Serif", weight="bold")
axR.text(8.9, 2.1, "\u2026", ha="center", va="center", fontsize=14, color=GREY)
axR.set_xlim(-0.3, 9.4); axR.set_ylim(-0.4, 3.4)

# ---- the identity
axI = fig.add_axes([0.03, 0.29, 0.94, 0.07]); axI.axis("off"); axI.set_xlim(0, 1); axI.set_ylim(0, 1)
axI.text(0.5, 0.5, "1 + 2 + \u2026 + k   =   k(k+1)/2   =   C(k+1, 2)", ha="center", va="center",
         fontsize=15, color=INK, family="DejaVu Serif")

# ---- the two sequences, aligned
axS = fig.add_axes([0.06, 0.10, 0.88, 0.13]); axS.axis("off")
axS.set_xlim(-2.3, 9.2); axS.set_ylim(-0.1, 2.3)
top = [1, 3, 6, 10, 15, 21, 28, 36]
bot = [None, 3, 6, 10, 15, 21, 28, "\u2026"]
for i, (a, b) in enumerate(zip(top, bot)):
    axS.add_patch(Rectangle((i, 1.2), 0.86, 0.82, facecolor=BLOCK2, edgecolor=LGREY, lw=0.6))
    axS.text(i + 0.43, 1.61, str(a), ha="center", va="center", fontsize=11, color=INK, family="DejaVu Serif")
    if b is None:
        axS.text(i + 0.43, 0.61, "\u2014", ha="center", va="center", fontsize=11, color=GREY)
    else:
        axS.add_patch(Rectangle((i, 0.2), 0.86, 0.82, facecolor=FILL, edgecolor=LGREY, lw=0.6))
        axS.text(i + 0.43, 0.61, str(b), ha="center", va="center", fontsize=11, color=INK, family="DejaVu Serif")
axS.text(-0.2, 1.61, "Intervall-Anf\u00e4nge der Thematik", ha="right", va="center", fontsize=8.8, color=INK)
axS.text(-0.2, 0.61, "Wertzahlen der Verbundkontexturen", ha="right", va="center", fontsize=8.8, color=INK)


for ext in ["svg", "png"]:
    fig.savefig(os.path.join(OUT, f"Abb_Achse_Zwei_Konstruktionen{SUF}.{ext}"),
                facecolor="white", bbox_inches="tight", pad_inches=0.18)
plt.close(fig)

# =====================================================================
# FIGURE 2 — the hexagon of three values, and the two geneses
# =====================================================================
def sw(p, i):   # N_{i+1}: swap VALUES i+1 and i+2 everywhere (values 1..3)
    a, b = i + 1, i + 2
    return tuple(b if v == a else a if v == b else v for v in p)

p0 = (1, 2, 3)
ring = [p0]
seq = [0, 1, 0, 1, 0, 1]                       # the boundary, starting with N1
for i in seq:
    ring.append(sw(ring[-1], i))
assert ring[-1] == p0 and len(set(ring[:-1])) == 6
A = [p0]; [A.append(sw(A[-1], i)) for i in (0, 1, 0)]     # N1 N2 N1
B = [p0]; [B.append(sw(B[-1], i)) for i in (1, 0, 1)]     # N2 N1 N2
assert A[-1] == B[-1] == (3, 2, 1)

fig = plt.figure(figsize=(12.4, 6.6), dpi=200)
ax = fig.add_axes([0.03, 0.12, 0.56, 0.76]); ax.set_aspect("equal"); ax.axis("off")
title(ax, "Drei Werte: das Sechseck und die zwei Genesen",
      "Ecken: die sechs Anordnungen dreier Werte \u00b7 Kanten: N\u2081 und N\u2082")

# place ring: p at top, 321 at bottom; ring order goes clockwise down the right side
R = 2.2
pos = {}
for k, v in enumerate(ring[:-1]):
    ang = math.pi / 2 - k * math.pi / 3
    pos[v] = np.array([R * math.cos(ang), R * math.sin(ang)])

ax.add_patch(Polygon([pos[v] for v in ring[:-1]], closed=True, facecolor=FILL, edgecolor="none"))
for k in range(6):
    a, b = ring[k], ring[k + 1]
    ax.plot(*zip(pos[a], pos[b]), color=NEG[seq[k]], lw=2.2, alpha=0.35, solid_capstyle="round")

def draw_path(P, word, side):
    for k in range(3):
        a, b = pos[P[k]], pos[P[k + 1]]
        ax.plot(*zip(a, b), color=NEG[word[k]], lw=5.2, solid_capstyle="round", zorder=3)
        mid = (a + b) / 2; d = (b - a) / np.linalg.norm(b - a)
        ax.add_patch(FancyArrowPatch(mid - 0.14 * d, mid + 0.14 * d, arrowstyle="-|>",
                                     mutation_scale=14, color=INK, lw=1.2, zorder=5))
draw_path(A, (0, 1, 0), "right")
draw_path(B, (1, 0, 1), "left")

for v, xy in pos.items():
    special = v in (p0, (3, 2, 1))
    ax.plot(*xy, "o", ms=11 if special else 7, mfc="white" if special else INK, mec=INK,
            mew=1.8 if special else 0, zorder=6)
    lab = "\u202f".join(str(x) for x in v)
    off = xy / np.linalg.norm(xy) * 0.52
    ax.text(*(xy + off), lab, ha="center", va="center", fontsize=11, color=INK, family="DejaVu Serif",
            weight="bold" if special else "normal")
ax.text(*(pos[p0] + np.array([0, 0.95])), "p", ha="center", fontsize=12, color=INK,
        family="DejaVu Serif", style="italic")
ax.text(*(pos[(3, 2, 1)] + np.array([0, -1.0])), "der R\u00fccklauf", ha="center", fontsize=9.5,
        color=INK, family="DejaVu Serif", style="italic")
ax.text(2.35, 0.0, "N\u2081\u00b7N\u2082\u00b7N\u2081", ha="left", va="center", fontsize=12, color=INK,
        family="DejaVu Serif", bbox=dict(boxstyle="round,pad=0.25", fc="white", ec="none", alpha=0.9))
ax.text(-2.35, 0.0, "N\u2082\u00b7N\u2081\u00b7N\u2082", ha="right", va="center", fontsize=12, color=INK,
        family="DejaVu Serif", bbox=dict(boxstyle="round,pad=0.25", fc="white", ec="none", alpha=0.9))
ax.set_xlim(-4.6, 4.6); ax.set_ylim(-3.6, 3.6)

# ---- right: Guenther's notation in Tafel II
axT = fig.add_axes([0.62, 0.28, 0.34, 0.52]); axT.axis("off"); axT.set_xlim(0, 1); axT.set_ylim(0, 1)
axT.add_patch(Rectangle((0.22, 0.06), 0.56, 0.86, facecolor="white", edgecolor=LGREY, lw=0.8))
axT.text(0.36, 0.73, "N", ha="center", va="center", fontsize=30, color=INK, family="DejaVu Serif")
axT.text(0.44, 0.815, "2.1.2", ha="left", va="center", fontsize=11, color=INK, family="DejaVu Serif")
axT.text(0.44, 0.65, "1.2.1", ha="left", va="center", fontsize=11, color=INK, family="DejaVu Serif")
axT.text(0.59, 0.735, "p", ha="left", va="center", fontsize=15, color=INK, family="DejaVu Serif",
         style="italic")
axT.plot([0.27, 0.73], [0.56, 0.56], color=LGREY, lw=0.8)
for j, v in enumerate([3, 2, 1]):
    axT.text(0.5, 0.44 - j * 0.12, str(v), ha="center", va="center", fontsize=15, color=INK,
             family="DejaVu Serif")
axT.text(0.5, 1.0, "G\u00fcnthers Schreibweise, Tafel II", ha="center", fontsize=10.5, color=INK,
         family="DejaVu Serif", weight="bold")

# ---- legend / caption
axG = fig.add_axes([0.04, 0.0, 0.92, 0.10]); axG.axis("off"); axG.set_xlim(0, 1); axG.set_ylim(0, 1)
axG.plot([0.0, 0.035], [0.5, 0.5], color=NEG[0], lw=3.4, solid_capstyle="round")
axG.text(0.045, 0.5, "N\u2081  vertauscht 1 \u2194 2", va="center", fontsize=9, color=INK)
axG.plot([0.20, 0.235], [0.5, 0.5], color=NEG[1], lw=3.4, solid_capstyle="round")
axG.text(0.245, 0.5, "N\u2082  vertauscht 2 \u2194 3", va="center", fontsize=9, color=INK)

for ext in ["svg", "png"]:
    fig.savefig(os.path.join(OUT, f"Abb_Sechseck_Drei_Werte{SUF}.{ext}"),
                facecolor="white", bbox_inches="tight", pad_inches=0.18)
plt.close(fig)
print("ok")
