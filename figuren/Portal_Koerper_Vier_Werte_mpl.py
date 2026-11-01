# -*- coding: utf-8 -*-
"""Portalgrafik der Startseite:  Günthers zweiter Kreis auf dem Körper der vier Werte (abgestumpftes Oktaeder).

Technisch wie die Figuren des Papiers (fig_oktaeder.py, linkes Feld von Figur 4):  matplotlib, undurchsichtige, schattierte Flächen
(Quadrate und Sechsecke in den Flächenfarben von Figur 4), nur die sichtbaren Kanten in den Negatorfarben, darüber Günthers Kreis 2
dick mit Richtungszeichen, der Ausgang p als weißer Kreis.  Keine Wörter im Bild.
Definitionen wörtlich nach dem Bestand am Tag rev11 (NegationCycle.lean:  sw, negate, kreis2);  umkehr = i ↦ 2 − i, dreh = reverse.
Blick fast entlang der dreizähligen Achse (Sechseck „Wert 4 an letzter Stelle"), gekippt 0.42 / 0.24.  Eichungen als assert.
    REV9_FIG_OUT=<dir> python3 Portal_Koerper_Vier_Werte_mpl.py

Keine Unterschrift:  die Startseite setzt nur einen Alt-Text;  er steht im Text der Seite, nicht hier.
"""
import itertools, math, os
import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.patches import Polygon

OUT = os.environ.get("REV9_FIG_OUT", ".")
plt.rcParams["svg.hashsalt"] = "pkl-rev9"
INK = "#141414"
NEG = ["#b0763a", "#3f6f8f", "#8f3f4f"]                 # N1, N2, N3 — wie Figur 4
SQ_FACE, HEX_FACE = "#d8ccb6", "#efe8da"                # Flächen wie Figur 4, linkes Feld

def sw(i, v): return i + 1 if v == i else i if v == i + 1 else v
def negate(i, l): return tuple(sw(i, v) for v in l)
def stations(w, l):
    out = []
    for i in w: out.append(l); l = negate(i, l)
    return out
def endpoint(w, l):
    for i in w: l = negate(i, l)
    return l
def kanten(w, x):
    S = stations(w, x) + [endpoint(w, x)]
    return list(zip(S[:-1], S[1:]))
umkehr = lambda w: [2 - i for i in w]
dreh = lambda w: list(reversed(w))
rotate = lambda w, n: w[n:] + w[:n]

kreis2 = [0,1,2,0,2,1,0,2,0,1,2,0,2,1,0,2,0,1,2,0,2,1,0,2]
p = (0, 1, 2, 3)

# ---------- Eichungen ----------
EICH = []
def eich(name, ok):
    EICH.append((name, bool(ok))); assert ok, name
verts = list(itertools.permutations(range(4))); idx = {v: k for k, v in enumerate(verts)}
edges = {}
for v in verts:
    for i in range(3): edges[frozenset((idx[v], idx[negate(i, v)]))] = i
def face_cycle(start, a, b, L):
    cyc, v = [start], start
    for t in range(L - 1):
        v = negate(a if t % 2 == 0 else b, v); cyc.append(v)
    return cyc
faces = {}
for v in verts:
    for (a, b, L, kind) in [(0, 2, 4, "sq"), (0, 1, 6, "hex"), (1, 2, 6, "hex")]:
        c = face_cycle(v, a, b, L); key = frozenset(idx[u] for u in c)
        if key not in faces: faces[key] = ([idx[u] for u in c], kind)
eich("Ecken = 24", len(verts) == 24)
eich("Kanten = 36, je Negator 12", len(edges) == 36 and sorted(list(edges.values()).count(i) for i in range(3)) == [12, 12, 12])
eich("Flächen = 14:  8 Sechsecke, 6 Quadrate", len(faces) == 14 and sum(k == "hex" for _, k in faces.values()) == 8)
S = stations(kreis2, p)
eich("kreis2 Vollkreis (zurück zu p, 24 verschiedene Stationen)", endpoint(kreis2, p) == p and len(set(S)) == 24)
eich("umkehr kreis2 = kreis2.rotate 4", umkehr(kreis2) == rotate(kreis2, 4))
eich("dreh kreis2 = kreis2.rotate 7", dreh(kreis2) == rotate(kreis2, 7))

# ---------- Geometrie:  die Anordnung als Punkt in R^4, in die Hyperebene projiziert ----------
B = np.array([[1,-1,0,0],[1,1,-2,0],[1,1,1,-3]], float); B = (B.T / np.linalg.norm(B, axis=1)).T
to3 = lambda l: B @ (np.array(l, float) - 1.5)
X = np.array([to3(v) for v in verts])
eich("jede Negatorkante hat die Länge √2", all(abs(np.linalg.norm(X[a]-X[b]) - math.sqrt(2)) < 1e-12 for a, b in (tuple(e) for e in edges)))
nrm = lambda v: v / np.linalg.norm(v)
axis3 = nrm(B @ (np.array([0,0,0,1.]) - 0.25))
t0 = B @ (np.array([1,0,0,0.]) - 0.25)
ta = nrm(t0 - (t0 @ axis3) * axis3); tb = np.cross(axis3, ta)
view = nrm(axis3 + 0.42 * ta + 0.24 * tb)
up = nrm(ta - (ta @ view) * view); right = np.cross(up, view)
P2 = np.array([[x @ right, x @ up] for x in X])

LIGHT = nrm(0.5 * up - 0.35 * right + 0.8 * view)
def shade(hexcol, f):
    h = hexcol.lstrip("#"); r, g, b = (int(h[i:i+2], 16) / 255 for i in (0, 2, 4))
    return (min(1, r * f), min(1, g * f), min(1, b * f))

vis = []
for cyc, kind in faces.values():
    c = X[cyc].mean(axis=0); n = nrm(c)
    if n @ view > 1e-9: vis.append((c @ view, cyc, kind, n))
vis.sort(key=lambda t: t[0])
front_edges = set(); front_v = set()
for _, cyc, _, _ in vis:
    front_v.update(cyc)
    for k in range(len(cyc)): front_edges.add(frozenset((cyc[k], cyc[(k + 1) % len(cyc)])))
eich("ein Quadrat ist vorn sichtbar", any(k == "sq" for _, _, k, _ in vis))

def richtung(ax, A, Bp, l=0.11, hw=0.033):
    L = np.linalg.norm(Bp - A); d = (Bp - A) / L; n = np.array([-d[1], d[0]])
    if l > 0.4 * L: hw *= 0.4 * L / l; l = 0.4 * L
    mid = A + 0.5 * (Bp - A); tip = mid + 0.5 * l * d; base = mid - 0.5 * l * d
    ax.add_patch(Polygon([tip, base + hw * n, base - hw * n], closed=True, facecolor="white", edgecolor=INK, lw=0.7, zorder=8))

fig = plt.figure(figsize=(7.2, 6.6), dpi=200)
ax = fig.add_axes([0, 0, 1, 1]); ax.set_aspect("equal"); ax.axis("off")
for _, cyc, kind, n in vis:
    lam = 0.86 + 0.22 * max(0.0, n @ LIGHT)
    ax.add_patch(Polygon(P2[cyc], closed=True, facecolor=shade(SQ_FACE if kind == "sq" else HEX_FACE, lam),
                         edgecolor="none", zorder=2))
kreis_e = {frozenset((idx[a], idx[b])) for a, b in kanten(kreis2, p)}
for e, i in edges.items():
    if e in front_edges and e not in kreis_e:
        a, b = tuple(e); ax.plot(*zip(P2[a], P2[b]), color=NEG[i], lw=2.0, solid_capstyle="round", zorder=3)
for k, (a, b) in enumerate(kanten(kreis2, p)):
    e = frozenset((idx[a], idx[b]))
    if e in front_edges:
        A, Bp = P2[idx[a]], P2[idx[b]]
        ax.plot([A[0], Bp[0]], [A[1], Bp[1]], color=NEG[kreis2[k]], lw=6.0, solid_capstyle="round", zorder=4)
        richtung(ax, A, Bp)
for k in front_v:
    ax.plot(*P2[k], "o", ms=4.2, color=INK, zorder=6)
if idx[p] in front_v:
    ax.plot(*P2[idx[p]], "o", ms=12, mfc="white", mec=INK, mew=2.0, zorder=7)
m = 0.25
ax.set_xlim(P2[:, 0].min() - m, P2[:, 0].max() + m); ax.set_ylim(P2[:, 1].min() - m, P2[:, 1].max() + m)
eich("der Ausgang p ist vorn sichtbar", idx[p] in front_v)
for ext in ["svg", "png"]:
    fig.savefig(os.path.join(OUT, f"Portal_Koerper_Vier_Werte_mpl.{ext}"), transparent=True, bbox_inches="tight", pad_inches=0.05,
                metadata=({"Date": None} if ext == "svg" else {}))
print("Eichungen:")
for name, ok in EICH: print(f"  {'WAHR ' if ok else 'FALSCH'}  {name}")
print("sichtbar:", len(vis), "Flächen,", len(front_edges), "Kanten,", len(front_v), "Ecken;  Kreis-2-Kanten sichtbar:", len(kreis_e & front_edges), "von 24")
print("ok")
