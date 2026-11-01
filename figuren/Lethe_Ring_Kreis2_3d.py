# -*- coding: utf-8 -*-
"""Günthers zweiter Kreis als Ring — der Körper, von der Seite, leicht von oben.  Bild der Hinführung Philosophie, Blatt 1.

Geometrie:  ein flacher Ring (Innenradius RI, Außenradius RO, Höhe H), 24 Segmente in der Folge von Kreis 2, p = 1234 vorn.  Orthografische
Projektion mit Erhebung ELEV;  Flächen nach Tiefe sortiert (Maler-Verfahren);  sichtbar sind die Deckfläche, die vordere Außenwand und die
hintere Innenwand.  Schattierung nach einer Lichtrichtung, wie in der Portalgrafik.  Richtungszeichen auf der Deckfläche.
Definitionen wörtlich nach dem Bestand;  Eichungen als assert.
    REV9_FIG_OUT=<dir> python3 Lethe_Ring_Kreis2_3d.py

UNTERSCHRIFT:  die Zeile unter dem Bild steht im Text der Seite (Hinführung Philosophie, Blatt 1), nicht hier.
"""
import math, os
import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.patches import Polygon

OUT = os.environ.get("REV9_FIG_OUT", ".")
plt.rcParams["svg.hashsalt"] = "pkl-rev9"
INK = "#141414"
NEG = ["#b0763a", "#3f6f8f", "#8f3f4f"]
HEX_FILL = "#f4f1ea"

def sw(i, v): return i + 1 if v == i else i if v == i + 1 else v
def negate(i, l): return tuple(sw(i, v) for v in l)
def stations(w, l):
    out = []
    for i in w: out.append(l); l = negate(i, l)
    return out
def endpoint(w, l):
    for i in w: l = negate(i, l)
    return l
umkehr = lambda w: [2 - i for i in w]
dreh = lambda w: list(reversed(w))
rotate = lambda w, n: w[n:] + w[:n]
kreis2 = [0,1,2,0,2,1,0,2,0,1,2,0,2,1,0,2,0,1,2,0,2,1,0,2]
p = (0, 1, 2, 3); S = stations(kreis2, p)
assert endpoint(kreis2, p) == p and len(set(S)) == 24
assert umkehr(kreis2) == rotate(kreis2, 4) and dreh(kreis2) == rotate(kreis2, 7)
assert [kreis2.count(i) for i in range(3)] == [9, 6, 9]

RI, RO, H = 2.55, 3.0, 0.34
ELEV = math.radians(30)
d = np.array([0.0, -math.cos(ELEV), math.sin(ELEV)])          # Richtung zum Betrachter:  von vorn (−y), von oben
LIGHT = np.array([-0.5, -0.55, 0.75]); LIGHT /= np.linalg.norm(LIGHT)
def proj(P):  # 3D → Bild
    x, y, z = P
    return np.array([x, y * math.sin(ELEV) + z * math.cos(ELEV)])
def depth(P): return float(np.dot(P, d))                         # größer = näher am Betrachter
def shade(hexcol, f):
    h = hexcol.lstrip("#"); r, g, b = (int(h[i:i+2], 16) / 255 for i in (0, 2, 4))
    return (min(1, r * f), min(1, g * f), min(1, b * f))
ang = lambda k: -math.pi / 2 - 2 * math.pi * k / 24              # p vorn (−y), dann im Uhrzeigersinn von oben gesehen
def arcpts(a0, a1, r, z, n=14):
    return [np.array([r * math.cos(t), r * math.sin(t), z]) for t in np.linspace(a0, a1, n)]

faces = []   # (depth, polygon2d, facecolor, zorder-hint)
for k, i in enumerate(kreis2):
    a1, a0 = ang(k), ang(k + 1)                                   # a0 < a1
    am = (a0 + a1) / 2
    n_out = np.array([math.cos(am), math.sin(am), 0.0])
    # Deckfläche
    top = arcpts(a0, a1, RO, H) + arcpts(a1, a0, RI, H)
    lam = 0.86 + 0.24 * max(0.0, float(np.dot([0, 0, 1], LIGHT)))
    faces.append((np.mean([depth(q) for q in top]) + 0.0, [proj(q) for q in top], shade(NEG[i], lam), top))
    # Außenwand (sichtbar, wenn sie dem Betrachter zugewandt ist)
    if np.dot(n_out, d) > 0:
        wall = arcpts(a0, a1, RO, 0) + arcpts(a1, a0, RO, H)
        lam = 0.62 + 0.38 * max(0.0, float(np.dot(n_out, LIGHT)))
        faces.append((np.mean([depth(q) for q in wall]), [proj(q) for q in wall], shade(NEG[i], lam), None))
    # Innenwand (sichtbar, wenn ihre Normale −n_out dem Betrachter zugewandt ist)
    if np.dot(-n_out, d) > 0:
        wall = arcpts(a0, a1, RI, 0) + arcpts(a1, a0, RI, H)
        lam = 0.55 + 0.30 * max(0.0, float(np.dot(-n_out, LIGHT)))
        faces.append((np.mean([depth(q) for q in wall]) - 10, [proj(q) for q in wall], shade(NEG[i], lam), None))

fig = plt.figure(figsize=(8.4, 5.2), dpi=200)
ax = fig.add_axes([0, 0, 1, 1]); ax.set_aspect("equal"); ax.axis("off")
# Bodenfläche im Ring (die Mitte), ganz hinten
hole = [proj(q) for q in arcpts(0, 2 * math.pi, RI, 0, 120)]
ax.add_patch(Polygon(hole, closed=True, facecolor=HEX_FILL, edgecolor="none", zorder=1))
faces.sort(key=lambda f: f[0])
for z, (dep, poly, col, top) in enumerate(faces):
    ax.add_patch(Polygon(poly, closed=True, facecolor=col, edgecolor=INK, lw=0.55, zorder=2 + z * 0.001))
# Richtungszeichen auf der Deckfläche, nach den Deckflächen gezeichnet
for k in range(24):
    am = (ang(k) + ang(k + 1)) / 2; r = (RI + RO) / 2
    c = np.array([r * math.cos(am), r * math.sin(am), H])
    tng = np.array([math.sin(am), -math.cos(am), 0.0])          # Uhrzeigersinn von oben
    nrm = np.array([math.cos(am), math.sin(am), 0.0])
    L, hw = 0.17, 0.05
    tri = [proj(c + 0.5 * L * tng), proj(c - 0.5 * L * tng + hw * nrm), proj(c - 0.5 * L * tng - hw * nrm)]
    zo = 2 + 0.001 * len(faces) + 0.0005 * depth(c)
    ax.add_patch(Polygon(tri, closed=True, facecolor="white", edgecolor=INK, lw=0.6, zorder=zo))
P0 = proj(np.array([(RI + RO) / 2 * math.cos(ang(0)), (RI + RO) / 2 * math.sin(ang(0)), H]))
ax.plot(*P0, "o", ms=12, mfc="white", mec=INK, mew=1.9, zorder=50)
ax.set_xlim(-RO * 1.08, RO * 1.08); ax.set_ylim(-RO * math.sin(ELEV) * 1.25 - 0.1, RO * math.sin(ELEV) * 1.15 + H)
for ext in ["svg", "png"]:
    fig.savefig(os.path.join(OUT, f"Lethe_Ring_Kreis2_3d.{ext}"), transparent=True, bbox_inches="tight", pad_inches=0.05,
                metadata=({"Date": None} if ext == "svg" else {}))
print("Flächen gezeichnet:", len(faces), " ok")
