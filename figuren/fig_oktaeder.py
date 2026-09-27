
# -*- coding: utf-8 -*-
import itertools, math
import os
OUT = os.environ.get("REV9_FIG_OUT", ".")
SUF = os.environ.get("REV9_FIG_SUFFIX", "")
import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.patches import Polygon
from matplotlib import font_manager as fm

D = os.path.join(os.path.dirname(matplotlib.__file__), "mpl-data", "fonts", "ttf") + "/"  # Rev9-Roll-out: DejaVu aus matplotlib selbst, statt /usr/share/fonts/truetype/dejavu/
plt.rcParams["svg.hashsalt"] = "pkl-rev9"  # Rev9-Roll-out: feste SVG-IDs (byte-reproduzierbar)
for f in ["DejaVuSerif.ttf", "DejaVuSerif-Italic.ttf", "DejaVuSans.ttf", "DejaVuSans-Bold.ttf"]:
    fm.fontManager.addfont(D + f)
plt.rcParams["font.family"] = "DejaVu Sans"

# ---------- the negation system for four values ----------
verts = list(itertools.permutations(range(4)))       # value at positions 1..4
idx = {p: k for k, p in enumerate(verts)}

def sw(p, i):                        # negator N_{i+1}: swap VALUES i and i+1 everywhere
    return tuple(i + 1 if v == i else i if v == i + 1 else v for v in p)

edges = {}
for p in verts:
    for i in range(3):
        q = sw(p, i)
        edges[frozenset((idx[p], idx[q]))] = i
assert len(edges) == 36

# Guenther's Kreis 2 (IGN S. 44), as in the corpus: kreis2 (emended by the last two steps)
kreis2 = [0,1,2,0,2,1,0,2,0,1,2,0,2,1,0,2,0,1,2,0,2,1,0,2]
path = [(0, 1, 2, 3)]
for i in kreis2:
    path.append(sw(path[-1], i))
assert path[-1] == path[0], "kreis2 does not close"
assert len(set(path[:-1])) == 24, "kreis2 is not Hamiltonian"

# ---------- geometry: permutohedron in R^4 -> R^3 ----------
X4 = np.array(verts, float) + 1.0                      # values 1..4
X4 -= X4.mean(axis=0)
B = np.array([[1,-1,0,0],[1,1,-2,0],[1,1,1,-3]], float)
B = (B.T / np.linalg.norm(B, axis=1)).T
X = X4 @ B.T                                          # 24 x 3

# faces: squares (N1,N3 alternate) and hexagons (N1,N2 / N2,N3 alternate)
def face_cycle(start, a, b, length):
    cyc, p, t = [start], start, 0
    for _ in range(length - 1):
        p = sw(p, a if t % 2 == 0 else b); cyc.append(p); t += 1
    return cyc

faces = {}
for p in verts:
    for (a, b, L, kind) in [(0, 2, 4, "sq"), (0, 1, 6, "hex"), (1, 2, 6, "hex")]:
        c = face_cycle(p, a, b, L)
        key = frozenset(idx[v] for v in c)
        if key not in faces:
            faces[key] = ([idx[v] for v in c], kind, (a, b))
assert len(faces) == 14

# ---------- palette ----------
INK = "#141414"; GREY = "#8a8a8a"; ACC = "#7a6a52"
NEG = ["#b0763a", "#3f6f8f", "#8f3f4f"]              # N1, N2, N3
SQ_FILL, HEX_FILL = "#e9e3d6", "#f4f1ea"

def rot(ax_deg, ay_deg):
    ax, ay = math.radians(ax_deg), math.radians(ay_deg)
    Rx = np.array([[1,0,0],[0,math.cos(ax),-math.sin(ax)],[0,math.sin(ax),math.cos(ax)]])
    Ry = np.array([[math.cos(ay),0,math.sin(ay)],[0,1,0],[-math.sin(ay),0,math.cos(ay)]])
    return Ry @ Rx

s0 = idx[(0, 1, 2, 3)]
fig = plt.figure(figsize=(12.4, 6.3), dpi=200)

# =============== left panel: the solid ===============
axL = fig.add_axes([0.02, 0.10, 0.46, 0.78]); axL.set_aspect("equal"); axL.axis("off")
# view: between a square face and a neighbouring hexagon
sq = [c for c,(cyc,kind,g) in ((k,v) for k,v in faces.items()) if False]
sq_c = [X[cyc].mean(axis=0) for key,(cyc,kind,g) in faces.items() if kind=="sq"]
hx_c = [X[cyc].mean(axis=0) for key,(cyc,kind,g) in faces.items() if kind=="hex"]
ns = sq_c[0]/np.linalg.norm(sq_c[0])
nh = max(hx_c, key=lambda c: (c/np.linalg.norm(c))@ns); nh = nh/np.linalg.norm(nh)
view = 0.62*ns + 0.38*nh; view /= np.linalg.norm(view)
up0 = np.cross(ns, nh); up0 /= np.linalg.norm(up0)
upv = up0 - (up0@view)*view; upv /= np.linalg.norm(upv)
right = np.cross(upv, view)
Rm = np.vstack([right, upv, view])
Rm = rot(0, 0) @ Rm
tilt = rot(-20, 13)
Y = (X @ Rm.T) @ tilt.T
P2 = Y[:, :2]
L = np.array([-0.45, 0.55, 0.70]); L /= np.linalg.norm(L)
def shade(hexcol, f):
    h = hexcol.lstrip("#"); r,g,b = (int(h[i:i+2],16)/255 for i in (0,2,4))
    return (min(1,r*f), min(1,g*f), min(1,b*f))
vis_faces = []
for key,(cyc,kind,gens) in faces.items():
    c3 = Y[cyc].mean(axis=0); nrm = c3/np.linalg.norm(c3)
    if nrm[2] > 0.0:
        vis_faces.append((c3[2], cyc, kind, nrm))
vis_faces.sort(key=lambda t:t[0])
front_edges=set()
for _,cyc,kind,nrm in vis_faces:
    lam = 0.90 + 0.18*max(0.0, nrm@L)
    axL.add_patch(Polygon(P2[cyc], closed=True,
        facecolor=shade("#d8ccb6" if kind=="sq" else "#efe8da", lam),
        edgecolor="none", zorder=2))
    for k in range(len(cyc)):
        front_edges.add(frozenset((cyc[k], cyc[(k+1)%len(cyc)])))
for e,i in edges.items():
    if e in front_edges:
        a,b = tuple(e)
        axL.plot(*zip(P2[a],P2[b]), color=NEG[i], lw=2.6, solid_capstyle="round", zorder=3)
front_v = set(v for _,cyc,_,_ in vis_faces for v in cyc)
for k in front_v:
    axL.plot(*P2[k], "o", ms=3.8, color=INK, zorder=4)
if s0 in front_v:
    axL.plot(*P2[s0], "o", ms=9, mfc="white", mec=INK, mew=1.7, zorder=5)
    axL.annotate("p", P2[s0], xytext=(-12, 6), textcoords="offset points",
                 fontsize=11, color=INK, family="DejaVu Serif", style="italic")
m = 0.45
axL.set_xlim(P2[:,0].min()-m, P2[:,0].max()+m); axL.set_ylim(P2[:,1].min()-m, P2[:,1].max()+m)
axL.text(0.5, 1.06, "Das Negationssystem f\u00fcr vier Werte", transform=axL.transAxes,
         ha="center", fontsize=12.5, color=INK, family="DejaVu Serif", weight="bold")
axL.text(0.5, 1.005, "24 Anordnungen, 36 Negatorkanten \u2014 das abgestumpfte Oktaeder",
         transform=axL.transAxes, ha="center", fontsize=9, color=GREY, family="DejaVu Serif")

# =============== right panel: Schlegel diagram with Kreis 2 ===============
axR = fig.add_axes([0.52, 0.10, 0.46, 0.78]); axR.set_aspect("equal"); axR.axis("off")
# outer face: the N1/N2 hexagon through p
outer = None
for key, (cyc, kind, gens) in faces.items():
    if kind == "hex" and gens == (0, 1) and s0 in cyc:
        outer = cyc
cF = X[outer].mean(axis=0); n = cF / np.linalg.norm(cF)
def _proj(eps):
    E_ = cF + eps*np.linalg.norm(cF)*n
    uu = X[outer[0]] - cF; uu -= (uu@n)*n; uu /= np.linalg.norm(uu); ww = np.cross(n, uu)
    out=[]
    for v in X:
        s = ((cF-E_)@n)/((v-E_)@n); q = E_ + s*(v-E_) - cF
        out.append([q@uu, q@ww])
    return np.array(out)
def _cross(P):
    def ccw(A,B,C): return (C[1]-A[1])*(B[0]-A[0]) - (B[1]-A[1])*(C[0]-A[0])
    E_=[tuple(e) for e in edges]
    for x in range(len(E_)):
        for y in range(x+1,len(E_)):
            a,b=E_[x]; c,d=E_[y]
            if len({a,b,c,d})<4: continue
            A,B,C,D=P[a],P[b],P[c],P[d]
            if (ccw(A,C,D)*ccw(B,C,D)<0) and (ccw(A,B,C)*ccw(A,B,D)<0): return True
    return False
EPS = None
for eps in [0.40]:
    Pq = _proj(eps)
    from matplotlib.path import Path as _P
    poly = _P(Pq[outer])
    inside = all(poly.contains_point(Pq[k], radius=-1e-6) for k in range(24) if k not in outer)
    if inside and not _cross(Pq):
        EPS = eps; break
print("Schlegel eps:", EPS)
E = cF + EPS * np.linalg.norm(cF) * n
u = X[outer[0]] - cF; u -= (u @ n) * n; u /= np.linalg.norm(u); w = np.cross(n, u)
def schlegel(v):
    s = ((cF - E) @ n) / ((v - E) @ n)
    q = E + s * (v - E) - cF
    return np.array([q @ u, q @ w])
S = np.array([schlegel(v) for v in X])
th = math.radians(90 - math.degrees(math.atan2(S[s0][1], S[s0][0])))
Rot = np.array([[math.cos(th), -math.sin(th)], [math.sin(th), math.cos(th)]])
S = S @ Rot.T

for key, (cyc, kind, gens) in faces.items():
    if cyc is outer:
        continue
    axR.add_patch(Polygon(S[cyc], closed=True, facecolor=SQ_FILL if kind == "sq" else HEX_FILL,
                          edgecolor="none", alpha=0.75, zorder=1))
for e, i in edges.items():
    a, b = tuple(e)
    axR.plot(*zip(S[a], S[b]), color=NEG[i], lw=1.1, alpha=0.45, zorder=2)

pts = [S[idx[v]] for v in path]
for k in range(24):
    a, b = pts[k], pts[k + 1]
    emended = k >= 22
    axR.plot([a[0], b[0]], [a[1], b[1]], color=NEG[kreis2[k]], lw=4.2,
             solid_capstyle="round", zorder=4 if not emended else 5,
             ls=(0, (1.2, 1.6)) if emended else "-")
for k in range(24):
    axR.plot(*S[k], "o", ms=3.8, color=INK, zorder=6)
axR.plot(*S[s0], "o", ms=10, mfc="white", mec=INK, mew=1.8, zorder=7)
axR.annotate("p", S[s0], xytext=(0, 11), textcoords="offset points", ha="center",
             fontsize=11, color=INK, family="DejaVu Serif", style="italic")
# direction arrow on the first step
a, b = pts[0], pts[1]; mid = (a + b) / 2; d = (b - a) / np.linalg.norm(b - a)
axR.annotate("", xy=mid + 0.18 * d, xytext=mid - 0.18 * d,
             arrowprops=dict(arrowstyle="-|>", color=INK, lw=1.3, mutation_scale=13), zorder=8)
pad = 0.5
axR.set_xlim(S[:, 0].min() - pad, S[:, 0].max() + pad)
axR.set_ylim(S[:, 1].min() - pad, S[:, 1].max() + pad)
axR.text(0.5, 1.06, "G\u00fcnthers Kreis 2 als Weg \u00fcber die Kanten", transform=axR.transAxes,
         ha="center", fontsize=12.5, color=INK, family="DejaVu Serif", weight="bold")
axR.text(0.5, 1.005, "24 Negationen, jede Anordnung genau einmal, zur\u00fcck zu p",
         transform=axR.transAxes, ha="center", fontsize=9, color=GREY, family="DejaVu Serif")

# =============== legend ===============
axG = fig.add_axes([0.04, -0.02, 0.92, 0.11]); axG.axis("off")
axG.set_xlim(0, 1); axG.set_ylim(0, 1)
x = 0.0
for i, lab in enumerate(["N\u2081  vertauscht 1 \u2194 2", "N\u2082  vertauscht 2 \u2194 3", "N\u2083  vertauscht 3 \u2194 4"]):
    axG.plot([x, x + 0.035], [0.83, 0.83], color=NEG[i], lw=3.4, solid_capstyle="round")
    axG.text(x + 0.045, 0.83, lab, va="center", fontsize=9, color=INK)
    x += 0.2
axG.text(0.0, 0.5, "Fl\u00e4chen, in beiden H\u00e4lften:", va="center", fontsize=8.8, color=INK)
axG.add_patch(Polygon([[0.2, 0.36], [0.225, 0.36], [0.225, 0.64], [0.2, 0.64]], facecolor=SQ_FILL, edgecolor=GREY, lw=0.5))
axG.text(0.232, 0.5, "Quadrat: N\u2081 und N\u2083 im Wechsel", va="center", fontsize=8.8, color=INK)
axG.add_patch(Polygon([[0.5, 0.36], [0.525, 0.36], [0.525, 0.64], [0.5, 0.64]], facecolor=HEX_FILL, edgecolor=GREY, lw=0.5))
axG.text(0.532, 0.5, "Sechseck: N\u2081, N\u2082 oder N\u2082, N\u2083 im Wechsel", va="center", fontsize=8.8, color=INK)
axG.plot([0.0, 0.035], [0.17, 0.17], color=INK, lw=2.6, ls=(0, (1.2, 1.6)))
axG.text(0.045, 0.17, "gestrichelt: die zwei emendierten Schritte (N\u2081, N\u2083)", va="center", fontsize=8.8, color=INK)

for out in [os.path.join(OUT, "Abb_Negationssystem_Oktaeder" + SUF + ".svg"),
            os.path.join(OUT, "Abb_Negationssystem_Oktaeder" + SUF + ".png")]:
    fig.savefig(out, facecolor="white", bbox_inches="tight", pad_inches=0.18)
print("ok")
