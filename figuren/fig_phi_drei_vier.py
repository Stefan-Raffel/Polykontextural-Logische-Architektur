# -*- coding: utf-8 -*-
"""Rev11, Kapitel 8 — Bild 3:  der Schritt Φ von drei auf vier Werten, an EINEM Fall (w = sjt 2).

Vorgabe:  KorpusRev2/Vorgabe_Figuren_Kapitel8_Rev11_Signum.md §3 (31.10.).  Stil:  figuren/fig_oktaeder.py (Figur 4) und
figuren/fig_sechseck_halbe_drehung.py (Rev10, O7);  die Schlegel-Projektion wie in Figur 4.

Definitionen WÖRTLICH nach Lean (main 55c6cf5):
  sw, negate, stations, endpoint, origin      NegationCycle.lean Z. 588–605
  kreis2                                      NegationCycle.lean Z. 1098
  umkehr w = w.map Fin.rev,  dreh w = w.reverse   GegenidentitaetProbe.lean Z. 203, 206
  blocks, sjtNat, toFin, sjt                  NegationCycleSJT.lean Z. 105–122
  phi b w = toFin (m+2) (blocks (m+2+1) b (w.map val))   AkkretivitaetsBruecke.lean Z. 295
Eichungen als assert (Lean-Namen daneben);  am Ende die Liste und die Stationentafeln.

Stand in docs/abb, gemessen 31.10. (Python 3.13, Pillow 13.0.0):  unter matplotlib 3.10.9 SVG byte-gleich, PNG pixelgleich (die PNG-Bytes
haengen an der Kompression);  unter 3.9.4 stimmen Eichungen und Stationen, nicht die Bytes.  Darum liegen die abgenommenen Dateien im Repo.

    REV9_FIG_OUT=<dir> python3 fig_phi_drei_vier.py
erzeugt Abb_Phi_Drei_Vier(.svg/.png) und _EN.
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
# Richtungszeichen (Auflage A1, Signum 31.10. 07:06):  gefülltes Dreieck statt Pfeil mit Schaft;  Sechseck l 0.30 / hw 0.14
# (1 Einheit ≈ 38 pt), Körper l 0.11 / hw 0.052 (1 Einheit ≈ 91 pt);  auf kurzen Kanten höchstens 0.4 der Länge.
TRI_FRAC, VERT_R = 0.4, 0.02

# ---------- Bestand, wörtlich ----------
def sw(i, v):
    return i + 1 if v == i else i if v == i + 1 else v
def negate(i, l):
    return tuple(sw(i, v) for v in l)
def stations(w, l):
    out = []
    for i in w:
        out.append(l); l = negate(i, l)
    return out
def endpoint(w, l):
    for i in w:
        l = negate(i, l)
    return l
def origin(m):
    return tuple(range(m + 1))
def umkehr(w, m):                               # w.map Fin.rev über Fin m
    return [m - 1 - i for i in w]
def dreh(w):
    return list(reversed(w))
def kanten(w, x):
    S = stations(w, x) + [endpoint(w, x)]
    return list(zip(S[:-1], S[1:]))
def is_full_cycle(w, l):
    S = stations(w, l)
    return endpoint(w, l) == l and len(set(S)) == len(S) == math.factorial(len(l))

def blocks(k, b, l):                            # NegationCycleSJT.lean Z. 105
    if not l: return []
    s, ss = l[0], l[1:]
    if b:  return list(reversed(range(k - 1))) + [s + 1] + blocks(k, False, ss)
    else:  return list(range(k - 1)) + [s] + blocks(k, True, ss)
def sjtNat(n):                                  # Z. 112
    if n <= 1: return []
    if n == 2: return [0, 0]
    return blocks(n, True, sjtNat(n - 1))
def toFin(m, l):                                # Z. 119:  filterMap, k < m
    return [k for k in l if k < m]
def sjt(m):                                     # Z. 122
    return toFin(m, sjtNat(m + 1))
def phi(b, w, m):                               # AkkretivitaetsBruecke.lean Z. 295;  w : List (Fin (m+1))
    return toFin(m + 2, blocks(m + 2 + 1, b, list(w)))

kreis2 = [0,1,2,0,2,1,0,2,0,1,2,0,2,1,0,2,0,1,2,0,2,1,0,2]
w3 = sjt(2)                                     # über Fin 2:  drei Werte
o3, p = origin(2), origin(3)                    # 123, 1234
W4 = phi(True, w3, 1)                           # Φ_true w  (m = 1:  Fin 2 → Fin 3)
U4 = phi(False, umkehr(w3, 2), 1)               # Φ_false (umkehr w)

EICH = []
def eich(name, lean, ok):
    EICH.append((name, lean, bool(ok)))
    assert ok, f"Eichung gefallen: {name} ({lean})"
eich("w = sjt 2 ist ein Vollkreis auf drei Werten", "sjt_full", is_full_cycle(w3, o3))
eich("umkehr w = dreh w (drei Werte)", "umkehr_eq_dreh_three", umkehr(w3, 2) == dreh(w3))
eich("phi true w = sjt 3", "phi_sjt", W4 == sjt(3))
eich("phi true w ist ein Vollkreis auf vier Werten", "phi_full", is_full_cycle(W4, p))
eich("phi false (umkehr w) ist ein Vollkreis auf vier Werten", "phi_false_full", is_full_cycle(U4, p))
eich("umkehr (phi true w) = phi false (umkehr w)", "phi_umkehr", umkehr(W4, 3) == U4)
eich("umkehr (sjt 3) = kreis2", "sjt3_mirror_kreis2", umkehr(sjt(3), 3) == kreis2)
eich("Länge:  6 Schritte links, 24 rechts", "length_blocks", len(w3) == 6 and len(W4) == 24 and len(U4) == 24)

# ---------- Geometrie:  Sechseck (drei Werte) und Schlegel (vier Werte, wie Figur 4) ----------
st3 = stations(w3, o3)                          # die sechs Stationen in der Folge von w
R = 2.2
pos3 = {s: np.array([R * math.cos(math.pi / 2 - k * math.pi / 3), R * math.sin(math.pi / 2 - k * math.pi / 3)])
        for k, s in enumerate(st3)}

verts = list(itertools.permutations(range(4))); idx = {v: k for k, v in enumerate(verts)}
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
E = cF + 0.40 * np.linalg.norm(cF) * n
u = X[outer[0]] - cF; u -= (u @ n) * n; u /= np.linalg.norm(u); w_ = np.cross(n, u)
def schlegel(v):
    s = ((cF - E) @ n) / ((v - E) @ n); r = E + s * (v - E) - cF
    return np.array([r @ u, r @ w_])
S = np.array([schlegel(v) for v in X])
th = math.radians(90 - math.degrees(math.atan2(S[s0][1], S[s0][0])))
S = S @ np.array([[math.cos(th), -math.sin(th)], [math.sin(th), math.cos(th)]]).T
assert all(MPath(S[outer]).contains_point(S[k], radius=-1e-6) for k in range(24) if k not in outer)

TXT = {
 "de": {"suf": "",
        "t1": "w auf drei Werten", "s1": "sechs Schritte, zur\u00fcck zum Ausgang",
        "t2": "Φ w auf vier Werten", "s2": "die Schubrichtung zuerst links: Bl\u00f6cke N\u2083N\u2082N\u2081, N\u2081N\u2082N\u2083, \u2026",
        "t3": "\u03a6 auf die Umkehr von w", "s3": "zuerst rechts: N\u2081N\u2082N\u2083, \u2026 \u00b7 gleich der Umkehr von \u03a6 w",
        "n": ["N₁  vertauscht 1 ↔ 2", "N₂  vertauscht 2 ↔ 3", "N₃  vertauscht 3 ↔ 4"],
        "phi": "\u03a6 setzt vor jeden Schritt von w einen Block N\u2083N\u2082N\u2081 oder N\u2081N\u2082N\u2083, im Wechsel; nach N\u2083N\u2082N\u2081 r\u00fcckt der Schritt von w um eins (N\u2081 wird N\u2082, N\u2082 wird N\u2083).",
        "drei": "Bei drei Werten ist die Umkehr von w dasselbe Wort rückwärts; darum links nur ein Weg.",
        "pp": "Ausgang: 123 links, p = 1234 rechts · die Pfeile zeigen die Laufrichtung"},
 "en": {"suf": "_EN",
        "t1": "w on three values", "s1": "six steps, back to the start",
        "t2": "Φ w on four values", "s2": "shift left first: blocks N\u2083N\u2082N\u2081, N\u2081N\u2082N\u2083, \u2026",
        "t3": "\u03a6 applied to the reversal of w", "s3": "right first: N\u2081N\u2082N\u2083, \u2026 \u00b7 equal to the reversal of \u03a6 w",
        "n": ["N₁  exchanges 1 ↔ 2", "N₂  exchanges 2 ↔ 3", "N₃  exchanges 3 ↔ 4"],
        "phi": "\u03a6 puts a block N\u2083N\u2082N\u2081 or N\u2081N\u2082N\u2083, alternately, before each step of w; after N\u2083N\u2082N\u2081 the step of w moves up by one (N\u2081 becomes N\u2082, N\u2082 becomes N\u2083).",
        "drei": "On three values the reversal of w is the same word read backwards; hence only one path on the left.",
        "pp": "start: 123 on the left, p = 1234 on the right · the arrows show the direction of travel"},
}

def arrow(ax, A, Bp, l=0.13, hw=0.039):     # A1 zweiter Stand:  halbe Breite = 0.3 × Länge                 # Richtungszeichen (A1):  gefülltes Dreieck, mittig, Spitze in Laufrichtung
    Lk = np.linalg.norm(Bp - A); d = (Bp - A) / Lk; nrm = np.array([-d[1], d[0]])
    if l > TRI_FRAC * Lk:
        hw = hw * TRI_FRAC * Lk / l; l = TRI_FRAC * Lk
    mid = A + 0.5 * (Bp - A); tip = mid + 0.5 * l * d; base = mid - 0.5 * l * d
    assert np.linalg.norm(tip - A) < Lk - VERT_R and np.linalg.norm(base - A) > VERT_R, "Richtungszeichen ragt über die Ecke"
    ax.add_patch(Polygon([tip, base + hw * nrm, base - hw * nrm], closed=True, facecolor="white", edgecolor=INK, lw=0.7, zorder=8))

def draw_hex(ax, T):
    ax.add_patch(Polygon([pos3[s] for s in st3], closed=True, facecolor=HEX_FILL, edgecolor="none"))
    for k in range(6):
        a, b = st3[k], st3[(k + 1) % 6]
        ax.plot(*zip(pos3[a], pos3[b]), color=NEG[w3[k]], lw=4.2, solid_capstyle="round", zorder=3)
        arrow(ax, pos3[a], pos3[b], l=0.36, hw=0.108)
    for s, xy in pos3.items():
        ax.plot(*xy, "o", ms=6, color=INK, zorder=5)
        off = xy / np.linalg.norm(xy) * 0.5
        ax.text(*(xy + off), " ".join(str(v + 1) for v in s), ha="center", va="center", fontsize=10.5, color=INK, family="DejaVu Serif")
    ax.plot(*pos3[o3], "o", ms=10, mfc="white", mec=INK, mew=1.8, zorder=7)
    ax.set_xlim(-3.3, 3.3); ax.set_ylim(-3.3, 3.3)

def draw_body(ax):
    for cyc, kind, g in faces.values():
        if cyc is outer: continue
        ax.add_patch(Polygon(S[cyc], closed=True, facecolor=SQ_FILL if kind == "sq" else HEX_FILL, edgecolor="none", alpha=0.75, zorder=1))
    for e, i in edges.items():
        a, b = tuple(e)
        ax.plot(*zip(S[a], S[b]), color=NEG[i], lw=1.1, alpha=0.45, zorder=2)

def draw_path(ax, word):
    for k, (a, b) in enumerate(kanten(word, p)):
        A, Bp = S[idx[a]], S[idx[b]]
        ax.plot([A[0], Bp[0]], [A[1], Bp[1]], color=NEG[word[k]], lw=4.2, solid_capstyle="round", zorder=4)
        arrow(ax, A, Bp)
    for j in range(24):
        ax.plot(*S[j], "o", ms=3.8, color=INK, zorder=6)
    ax.plot(*S[s0], "o", ms=10, mfc="white", mec=INK, mew=1.8, zorder=7)
    ax.annotate("p", S[s0], xytext=(0, 11), textcoords="offset points", ha="center", fontsize=11, color=INK, family="DejaVu Serif", style="italic", zorder=9)
    pad = 0.5
    ax.set_xlim(S[:, 0].min() - pad, S[:, 0].max() + pad); ax.set_ylim(S[:, 1].min() - pad, S[:, 1].max() + pad)

def head(ax, t, s):
    ax.text(0.5, 1.06, t, transform=ax.transAxes, ha="center", fontsize=12.5, color=INK, family="DejaVu Serif", weight="bold")
    ax.text(0.5, 1.005, s, transform=ax.transAxes, ha="center", fontsize=9, color=GREY, family="DejaVu Serif")

def draw(lang):
    T = TXT[lang]
    fig = plt.figure(figsize=(13.6, 6.6), dpi=200)
    ax1 = fig.add_axes([0.01, 0.20, 0.26, 0.66]); ax1.set_aspect("equal"); ax1.axis("off")
    draw_hex(ax1, T); head(ax1, T["t1"], T["s1"])
    ax2 = fig.add_axes([0.32, 0.17, 0.32, 0.72]); ax2.set_aspect("equal"); ax2.axis("off")
    draw_body(ax2); draw_path(ax2, W4); head(ax2, T["t2"], T["s2"])
    ax3 = fig.add_axes([0.67, 0.17, 0.32, 0.72]); ax3.set_aspect("equal"); ax3.axis("off")
    draw_body(ax3); draw_path(ax3, U4); head(ax3, T["t3"], T["s3"])
    # der Schritt Φ zwischen den Feldern
    axA = fig.add_axes([0.0, 0.0, 1.0, 1.0]); axA.axis("off"); axA.set_xlim(0, 1); axA.set_ylim(0, 1)
    axA.annotate("", xy=(0.315, 0.53), xytext=(0.265, 0.53), arrowprops=dict(arrowstyle="-|>", color=INK, lw=1.6, mutation_scale=16))
    axA.text(0.29, 0.565, "Φ", ha="center", fontsize=15, color=INK, family="DejaVu Serif", style="italic")
    axG = fig.add_axes([0.04, 0.0, 0.92, 0.13]); axG.axis("off"); axG.set_xlim(0, 1); axG.set_ylim(0, 1)
    x = 0.0
    for i, lab in enumerate(T["n"]):
        axG.plot([x, x + 0.035], [0.88, 0.88], color=NEG[i], lw=3.4, solid_capstyle="round")
        axG.text(x + 0.045, 0.88, lab, va="center", fontsize=9, color=INK); x += 0.2
    axG.text(0.61, 0.88, T["pp"], va="center", fontsize=8.8, color=INK)
    axG.text(0.0, 0.58, T["phi"], va="center", fontsize=8.8, color=INK)
    axG.text(0.0, 0.28, T["drei"], va="center", fontsize=8.8, color=INK)
    for ext in ["svg", "png"]:
        fig.savefig(os.path.join(OUT, f"Abb_Phi_Drei_Vier{T['suf']}.{ext}"), facecolor="white", bbox_inches="tight", pad_inches=0.18,
                    metadata=({"Date": None} if ext == "svg" else {}))  # SVG ohne Zeitstempel:  byte-reproduzierbar
    plt.close(fig)

for lang in ("de", "en"):
    draw(lang)

fmt = lambda v: "".join(str(x + 1) for x in v)
print("Eichungen:")
for name, lean, ok in EICH:
    print(f"  {'WAHR ' if ok else 'FALSCH'}  {name}   [{lean}]")
print("w = sjt 2 (Negatoren 1-basiert):   ", " ".join(str(i + 1) for i in w3))
print("phi true w = sjt 3:                ", " ".join(str(i + 1) for i in W4))
print("phi false (umkehr w) = kreis2:     ", " ".join(str(i + 1) for i in U4))
print("Stationen w ab 123:                ", " ".join(fmt(v) for v in st3))
print("Stationen phi true w ab p:         ", " ".join(fmt(v) for v in stations(W4, p)))
print("Stationen phi false (umkehr w) ab p:", " ".join(fmt(v) for v in stations(U4, p)))
print("ok")
