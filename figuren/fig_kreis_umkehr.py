# -*- coding: utf-8 -*-
"""Rev11, Kapitel 8 — Bild 1:  Günthers Kreis 2 und seine Umkehr, beide ab dem Ausgang p.

Vorgabe:  KorpusRev2/Vorgabe_Figuren_Kapitel8_Rev11_Signum.md §2 (31.10.).  Stil:  figuren/fig_oktaeder.py (Rev10, Figur 4);
die Schlegel-Projektion ist von dort übernommen (äußere Fläche:  das N₁/N₂-Sechseck durch p, eps 0.40).

Definitionen WÖRTLICH nach Lean (main 55c6cf5):
  sw, negate, stations, endpoint, origin      NegationCycle.lean Z. 588–605
  kreis2                                      NegationCycle.lean Z. 1098
  umkehr w = w.map Fin.rev,  dreh w = w.reverse   GegenidentitaetProbe.lean Z. 203, 206
  kanten w x = S.zip S.tail, S = stations ++ [endpoint];  gemeinsam   DrehsinnUmkehrProbe.lean Z. 88, 93
Eichungen als assert (Lean-Namen daneben);  am Ende die Liste und die Stationentafel.

    REV9_FIG_OUT=<dir> python3 fig_kreis_umkehr.py
erzeugt Abb_Kreis_und_Umkehr(.svg/.png) und _EN.
"""
import itertools, math, os
import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.patches import Polygon
from matplotlib.path import Path as MPath
from matplotlib import font_manager as fm

OUT = os.environ.get("REV9_FIG_OUT", ".")
D = os.path.join(os.path.dirname(matplotlib.__file__), "mpl-data", "fonts", "ttf") + "/"
plt.rcParams["svg.hashsalt"] = "pkl-rev9"
for f in ["DejaVuSerif.ttf", "DejaVuSerif-Italic.ttf", "DejaVuSerif-Bold.ttf", "DejaVuSans.ttf", "DejaVuSans-Bold.ttf"]:
    if os.path.exists(D + f):
        fm.fontManager.addfont(D + f)
plt.rcParams["font.family"] = "DejaVu Sans"

INK = "#141414"; GREY = "#8a8a8a"
NEG = ["#b0763a", "#3f6f8f", "#8f3f4f"]              # N1, N2, N3 — wie Figur 4
SQ_FILL, HEX_FILL = "#e9e3d6", "#f4f1ea"
# Richtungszeichen (Auflage A1, Signum 31.10. 07:06):  statt Pfeil mit Schaft ein gefülltes Dreieck (weiß, Rand INK), mittig auf der Kante,
# Spitze in Laufrichtung.  Länge TRI_L, halbe Breite TRI_W (Dateneinheiten;  1 Einheit ≈ 119 pt);  auf kurzen Kanten höchstens 0.4 der Länge.
TRI_L, TRI_W, TRI_FRAC, VERT_R = 0.11, 0.033, 0.4, 0.02   # A1 zweiter Stand (Signum 07:10):  schlank, halbe Breite = 0.3 × Länge
def richtung(ax, A, Bp, l, hw):
    Lk = np.linalg.norm(Bp - A); d = (Bp - A) / Lk; nrm = np.array([-d[1], d[0]])
    l = min(l, TRI_FRAC * Lk); hw = hw * l / TRI_L if l < TRI_L else hw
    mid = A + 0.5 * (Bp - A); tip = mid + 0.5 * l * d; base = mid - 0.5 * l * d
    assert np.linalg.norm(tip - A) < Lk - VERT_R and np.linalg.norm(base - A) > VERT_R, "Richtungszeichen ragt über die Ecke"
    ax.add_patch(Polygon([tip, base + hw * nrm, base - hw * nrm], closed=True, facecolor="white", edgecolor=INK, lw=0.7, zorder=8))

# ---------- Bestand, wörtlich ----------
def sw(i, v):                                   # sw i v
    return i + 1 if v == i else i if v == i + 1 else v
def negate(i, l):                               # negate i l = l.map (sw i)
    return tuple(sw(i, v) for v in l)
def stations(w, l):                             # ohne die zuletzt erreichte
    out = []
    for i in w:
        out.append(l); l = negate(i, l)
    return out
def endpoint(w, l):
    for i in w:
        l = negate(i, l)
    return l
def origin(m):                                  # List.finRange (m+1)
    return tuple(range(m + 1))
def umkehr(w, m=3):                             # w.map Fin.rev,  Fin.rev i = m-1-i  (m = Zahl der Negatoren)
    return [m - 1 - i for i in w]
def dreh(w):                                    # w.reverse
    return list(reversed(w))
def kanten(w, x):
    S = stations(w, x) + [endpoint(w, x)]
    return list(zip(S[:-1], S[1:]))
def gemeinsam(E1, E2):
    return sum(1 for e in E1 if e in E2 or (e[1], e[0]) in E2)
def rotate(w, n):                               # List.rotate
    return w[n:] + w[:n]
def is_full_cycle(w, l):                        # schließt, jede Anordnung genau einmal
    S = stations(w, l)
    return endpoint(w, l) == l and len(set(S)) == len(S) == math.factorial(len(l))

kreis2 = [0,1,2,0,2,1,0,2,0,1,2,0,2,1,0,2,0,1,2,0,2,1,0,2]
p = origin(3)                                   # (0,1,2,3) = 1234
q = (1, 2, 3, 0)                                # Günthers 2341

# ---------- Eichungen ----------
EICH = []
def eich(name, lean, ok):
    EICH.append((name, lean, bool(ok)))
    assert ok, f"Eichung gefallen: {name} ({lean})"
eich("kreis2 schließt und trifft 24 verschiedene Stationen", "kreis2_emendation, kreis2_eq", is_full_cycle(kreis2, p))
eich("umkehr kreis2 = kreis2.rotate 4", "kreis2_drehungen", umkehr(kreis2) == rotate(kreis2, 4))
eich("dreh kreis2 = kreis2.rotate 7", "kreis2_drehungen", dreh(kreis2) == rotate(kreis2, 7))
eich("umkehr kreis2 ≠ kreis2", "umkehr_ne_self_all", umkehr(kreis2) != kreis2)
K_p, U_p, K_q = kanten(kreis2, p), kanten(umkehr(kreis2), p), kanten(kreis2, q)
eich("gemeinsame Kanten (kreis2 ab p, umkehr ab p) = 14", "kanten_kreis2 (1)", gemeinsam(K_p, U_p) == 14)
eich("Kanten der Umkehr ab p ⊆ Kanten von kreis2 ab q (ohne Richtung)", "kanten_kreis2 (2)",
     all(e in K_q or (e[1], e[0]) in K_q for e in U_p))
eich("Kanten von kreis2 ab q ⊆ Kanten der Umkehr ab p (ohne Richtung)", "kanten_kreis2 (3)",
     all(e in U_p or (e[1], e[0]) in U_p for e in K_q))
S_k = stations(kreis2, p)
eich("stations (dreh kreis2) p = p :: (stations kreis2 p).drop 1 .reverse", "stations_reverse",
     stations(dreh(kreis2), p) == [p] + list(reversed(S_k[1:])))
eich("umkehr kreis2 schließt und trifft 24 Stationen", "umkehr_full", is_full_cycle(umkehr(kreis2), p))

# ---------- Geometrie (wie Figur 4):  Permutoeder, Schlegel durch das N1/N2-Sechseck an p ----------
verts = list(itertools.permutations(range(4)))
idx = {v: k for k, v in enumerate(verts)}
edges = {}
for v in verts:
    for i in range(3):
        edges[frozenset((idx[v], idx[negate(i, v)]))] = i
assert len(edges) == 36
X4 = np.array(verts, float) + 1.0; X4 -= X4.mean(axis=0)
B = np.array([[1,-1,0,0],[1,1,-2,0],[1,1,1,-3]], float); B = (B.T / np.linalg.norm(B, axis=1)).T
X = X4 @ B.T
def face_cycle(start, a, b, length):
    cyc, v, t = [start], start, 0
    for _ in range(length - 1):
        v = negate(a if t % 2 == 0 else b, v); cyc.append(v); t += 1
    return cyc
faces = {}
for v in verts:
    for (a, b, L, kind) in [(0, 2, 4, "sq"), (0, 1, 6, "hex"), (1, 2, 6, "hex")]:
        c = face_cycle(v, a, b, L); key = frozenset(idx[u] for u in c)
        if key not in faces:
            faces[key] = ([idx[u] for u in c], kind, (a, b))
assert len(faces) == 14
s0 = idx[p]
outer = next(cyc for cyc, kind, g in faces.values() if kind == "hex" and g == (0, 1) and s0 in cyc)
cF = X[outer].mean(axis=0); n = cF / np.linalg.norm(cF)
EPS = 0.40
E = cF + EPS * np.linalg.norm(cF) * n
u = X[outer[0]] - cF; u -= (u @ n) * n; u /= np.linalg.norm(u); w_ = np.cross(n, u)
def schlegel(v):
    s = ((cF - E) @ n) / ((v - E) @ n); r = E + s * (v - E) - cF
    return np.array([r @ u, r @ w_])
S = np.array([schlegel(v) for v in X])
th = math.radians(90 - math.degrees(math.atan2(S[s0][1], S[s0][0])))
S = S @ np.array([[math.cos(th), -math.sin(th)], [math.sin(th), math.cos(th)]]).T
poly = MPath(S[outer])
assert all(poly.contains_point(S[k], radius=-1e-6) for k in range(24) if k not in outer)

TXT = {
 "de": {"suf": "", "tl": "Kreis 2 ab p", "tr": "Die Umkehr von Kreis 2 ab p",
        "sl": "24 Negationen, zurück zu p", "sr": "dieselbe Folge, vier Wechsel sp\u00e4ter begonnen \u00b7 ab q: die Kanten von Kreis 2",
        "n": ["N₁  vertauscht 1 ↔ 2", "N₂  vertauscht 2 ↔ 3", "N₃  vertauscht 3 ↔ 4"],
        "shared": "ohne Saum: Kante beider Wege (14)", "own": "mit Saum: Kante nur dieses Weges (10 je Weg)",
        "dreh": "Die Pfeile zeigen die Laufrichtung; der Drehsinn l\u00e4uft dieselben Kanten gegen die Pfeile.",
        "pq": "p = 1234 (Ausgang) · q = 2341"},
 "en": {"suf": "_EN", "tl": "Circle 2 from p", "tr": "The reversal of circle 2 from p",
        "sl": "24 negations, back to p", "sr": "the same sequence, begun four exchanges later \u00b7 from q: the edges of circle 2",
        "n": ["N₁  exchanges 1 ↔ 2", "N₂  exchanges 2 ↔ 3", "N₃  exchanges 3 ↔ 4"],
        "shared": "no rim: edge of both paths (14)", "own": "with rim: edge of this path only (10 per path)",
        "dreh": "The arrows show the direction of travel; the sense of rotation runs the same edges against the arrows.",
        "pq": "p = 1234 (origin) · q = 2341"},
}

def draw_body(ax):
    for cyc, kind, g in faces.values():
        if cyc is outer: continue
        ax.add_patch(Polygon(S[cyc], closed=True, facecolor=SQ_FILL if kind == "sq" else HEX_FILL,
                             edgecolor="none", alpha=0.75, zorder=1))
    for e, i in edges.items():
        a, b = tuple(e)
        ax.plot(*zip(S[a], S[b]), color=NEG[i], lw=1.1, alpha=0.45, zorder=2)

def undirected(E):
    return {frozenset(e) for e in E}

def draw_path(ax, word, start, other_edges):
    E = kanten(word, start); shared = undirected(other_edges)
    for k, (a, b) in enumerate(E):
        A, Bp = S[idx[a]], S[idx[b]]
        own = frozenset((a, b)) not in shared
        if own:
            ax.plot([A[0], Bp[0]], [A[1], Bp[1]], color=INK, lw=7.0, solid_capstyle="round", zorder=3)
        ax.plot([A[0], Bp[0]], [A[1], Bp[1]], color=NEG[word[k]], lw=4.2, solid_capstyle="round", zorder=4)
        richtung(ax, A, Bp, TRI_L, TRI_W)
    return E

def mark(ax, v, label, dy=11):
    ax.plot(*S[idx[v]], "o", ms=10, mfc="white", mec=INK, mew=1.8, zorder=7)
    ax.annotate(label, S[idx[v]], xytext=(0, dy), textcoords="offset points", ha="center",
                fontsize=11, color=INK, family="DejaVu Serif", style="italic", zorder=9)

def draw(lang):
    T = TXT[lang]
    fig = plt.figure(figsize=(12.4, 6.9), dpi=200)
    axes = []
    for k, (word, title, sub) in enumerate([(kreis2, T["tl"], T["sl"]), (umkehr(kreis2), T["tr"], T["sr"])]):
        ax = fig.add_axes([0.02 + 0.50 * k, 0.17, 0.46, 0.72]); ax.set_aspect("equal"); ax.axis("off")
        draw_body(ax)
        other = U_p if k == 0 else K_p
        draw_path(ax, word, p, other)
        for j in range(24):
            ax.plot(*S[j], "o", ms=3.8, color=INK, zorder=6)
        mark(ax, p, "p")
        if k == 1:
            mark(ax, q, "q", dy=-17)
        pad = 0.5
        ax.set_xlim(S[:, 0].min() - pad, S[:, 0].max() + pad); ax.set_ylim(S[:, 1].min() - pad, S[:, 1].max() + pad)
        ax.text(0.5, 1.06, title, transform=ax.transAxes, ha="center", fontsize=12.5, color=INK, family="DejaVu Serif", weight="bold")
        ax.text(0.5, 1.005, sub, transform=ax.transAxes, ha="center", fontsize=9, color=GREY, family="DejaVu Serif")
        axes.append(ax)
    axG = fig.add_axes([0.04, 0.0, 0.92, 0.13]); axG.axis("off"); axG.set_xlim(0, 1); axG.set_ylim(0, 1)
    x = 0.0
    for i, lab in enumerate(T["n"]):
        axG.plot([x, x + 0.035], [0.86, 0.86], color=NEG[i], lw=3.4, solid_capstyle="round")
        axG.text(x + 0.045, 0.86, lab, va="center", fontsize=9, color=INK); x += 0.2
    axG.text(0.61, 0.86, T["pq"], va="center", fontsize=9, color=INK)
    axG.plot([0.0, 0.035], [0.58, 0.58], color=NEG[1], lw=3.4, solid_capstyle="round")
    axG.text(0.045, 0.58, T["shared"], va="center", fontsize=8.8, color=INK)
    axG.plot([0.36, 0.395], [0.58, 0.58], color=INK, lw=6.0, solid_capstyle="round")
    axG.plot([0.36, 0.395], [0.58, 0.58], color=NEG[1], lw=3.4, solid_capstyle="round")
    axG.text(0.405, 0.58, T["own"], va="center", fontsize=8.8, color=INK)
    axG.text(0.0, 0.28, T["dreh"], va="center", fontsize=8.8, color=INK)
    for ext in ["svg", "png"]:
        fig.savefig(os.path.join(OUT, f"Abb_Kreis_und_Umkehr{T['suf']}.{ext}"), facecolor="white", bbox_inches="tight", pad_inches=0.18,
                    metadata=({"Date": None} if ext == "svg" else {}))  # SVG ohne Zeitstempel:  byte-reproduzierbar
    plt.close(fig)

for lang in ("de", "en"):
    draw(lang)

fmt = lambda v: "".join(str(x + 1) for x in v)
print("Eichungen:")
for name, lean, ok in EICH:
    print(f"  {'WAHR ' if ok else 'FALSCH'}  {name}   [{lean}]")
print("Stationen kreis2 ab p:        ", " ".join(fmt(v) for v in stations(kreis2, p)))
print("Stationen umkehr kreis2 ab p: ", " ".join(fmt(v) for v in stations(umkehr(kreis2), p)))
print("Stationen kreis2 ab q:        ", " ".join(fmt(v) for v in stations(kreis2, q)))
print("eigene Kanten je Weg:", 24 - gemeinsam(K_p, U_p))
print("ok")
