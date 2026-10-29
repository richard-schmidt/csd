"""Figures of DDD/docs/approach.md.

Run `python3 DDD/docs/figures.py` from the repository root to write the SVG files
to DDD/docs/figures/. Each figure is drawn once; `standalone` adds the styles for
light and dark themes, so the files render on their own.
"""

import html
import math
import os

SANS = "'IBM Plex Sans', 'Segoe UI', system-ui, sans-serif"
MONO = "'IBM Plex Mono', ui-monospace, Menlo, monospace"

# Colour tokens: light, dark.
TOKENS = {
    "surface": ("#ffffff", "#19212a"),
    "region": ("#f3f5f8", "#202a35"),
    "fg": ("#1b232c", "#e3e9ef"),
    "muted": ("#5a6675", "#9aa7b5"),
    "line": ("#c9d1da", "#34414f"),
    "accent": ("#17708f", "#5db4d3"),
    "accentfill": ("rgba(23,112,143,0.10)", "rgba(93,180,211,0.14)"),
    "kern": ("#2f7a4b", "#6cc28d"),
    "kernfill": ("rgba(47,122,75,0.10)", "rgba(108,194,141,0.13)"),
    "warn": ("#b4421b", "#f08c5e"),
    "warnfill": ("rgba(180,66,27,0.08)", "rgba(240,140,94,0.11)"),
}

# Rules shared by the standalone files and the page; colours as var(--x).
RULES = """
.bgr { fill: var(--surface); }
.n rect { fill: var(--surface); stroke: var(--fg); stroke-width: 1.2; }
.n.pl rect { fill: var(--accentfill); stroke: var(--accent); stroke-width: 1.5; }
.n.kern rect { fill: var(--kernfill); stroke: var(--kern); stroke-width: 1.5; }
.n.glued rect { fill: var(--kernfill); stroke: var(--kern); stroke-width: 1.5; }
.n.muted rect { fill: var(--surface); stroke: var(--muted); stroke-dasharray: 4 3; }
.n.warn rect { fill: var(--warnfill); stroke: var(--warn); stroke-width: 1.5; stroke-dasharray: 4 3; }
.n.val rect { fill: var(--region); stroke: var(--muted); }
.n.chip rect { fill: var(--surface); stroke: var(--muted); }
.n.chip.s rect { fill: var(--accentfill); stroke: var(--accent); }
.n.dot rect { fill: var(--region); stroke: var(--muted); }
.n .t { fill: var(--fg); font: 500 12.5px SANS; }
.n .s { fill: var(--muted); font: 400 10.5px MONO; }
.n .a { fill: var(--fg); font: 400 10.5px MONO; }
.n.chip .t, .n.val .t, .n.dot .t { font: 400 11.5px MONO; }
.n .hr { stroke: var(--line); stroke-width: 1; }
.badge { font: 500 10px MONO; }
.b-pl { fill: var(--accent); } .b-kern { fill: var(--kern); } .b-warn { fill: var(--warn); }
.b-muted { fill: var(--muted); }
.e { fill: none; stroke-width: 1.4; }
.e.acl { stroke: var(--fg); }
.e.muted { stroke: var(--muted); }
.e.incl { stroke: var(--accent); stroke-dasharray: 6 4; }
.e.kern { stroke: var(--kern); stroke-dasharray: 6 4; stroke-width: 1.6; }
.e.eq { stroke: var(--accent); stroke-width: 2.2; }
.e.warn { stroke: var(--warn); stroke-width: 1.8; }
.e.ghost { stroke: var(--warn); stroke-dasharray: 3 3; }
.e.uniq { stroke: var(--fg); stroke-dasharray: 3 3; }
.e.map { stroke: var(--accent); stroke-dasharray: 2 3; stroke-width: 1.3; }
.e.glued { stroke: var(--kern); stroke-width: 1.6; }
.mk-acl, .mk-uniq { fill: var(--fg); } .mk-muted { fill: var(--muted); }
.mk-incl, .mk-eq, .mk-map { fill: var(--accent); } .mk-kern, .mk-glued { fill: var(--kern); }
.mk-warn, .mk-ghost { fill: var(--warn); }
.lbg { fill: var(--surface); }
.lb { font: 400 10.5px MONO; }
.c-acl, .c-muted, .c-uniq { fill: var(--muted); } .c-fg { fill: var(--fg); }
.c-incl, .c-eq, .c-map, .c-pl { fill: var(--accent); }
.c-kern, .c-glued { fill: var(--kern); } .c-warn, .c-ghost { fill: var(--warn); }
.rg { fill: var(--region); stroke: var(--line); }
.rg.pl { fill: var(--accentfill); stroke: var(--accent); stroke-dasharray: 3 3; }
.rg.kern { fill: var(--kernfill); stroke: var(--kern); stroke-dasharray: 3 3; }
.rg.warn { fill: var(--warnfill); stroke: var(--warn); stroke-dasharray: 3 3; }
.rg.plain { fill: none; stroke: var(--line); }
.rgl { font: 500 10.5px MONO; fill: var(--muted); letter-spacing: 0.04em; }
.rgl.pl { fill: var(--accent); } .rgl.kern { fill: var(--kern); } .rgl.warn { fill: var(--warn); }
.hull { fill: none; stroke: var(--fg); stroke-dasharray: 2 3; stroke-width: 1; }
.hl { font: 500 10.5px MONO; fill: var(--fg); }
.note { font: 400 11px SANS; fill: var(--muted); }
.note.fg { fill: var(--fg); }
.mono { font: 400 11px MONO; fill: var(--fg); }
.mono.m { fill: var(--muted); } .mono.acc { fill: var(--accent); } .mono.warn { fill: var(--warn); }
.mono.kern { fill: var(--kern); }
.br { fill: none; stroke: var(--muted); stroke-width: 1; }
.br.acc { stroke: var(--accent); }
""".replace("SANS", SANS).replace("MONO", MONO)

MARKERS = ["acl", "muted", "incl", "kern", "eq", "warn", "ghost", "uniq", "map", "glued"]


def esc(s):
    return html.escape(s, quote=True)


def text_width(s, mono=True, size=10.5):
    return len(s) * size * (0.6 if mono else 0.56)


class Fig:
    def __init__(self, name, w, h, label):
        self.name, self.w, self.h, self.label = name, w, h, label
        self.back, self.parts, self.front = [], [], []
        self.nodes = {}

    # Nodes

    def node(self, key, cx, cy, title, kind="", w=120, h=None, sub=None, lines=None,
             badge=None, badge_kind="muted", badge_below=False):
        lines = lines or []
        if h is None:
            h = 34 if not lines else 26 + 14 * len(lines) + 4
            if sub and not lines:
                h = 40
        self.nodes[key] = (cx, cy, w, h)
        x, y = cx - w / 2, cy - h / 2
        rx = 11 if kind == "val" else 5
        s = [f'<g class="n {kind}"><rect x="{x:.1f}" y="{y:.1f}" width="{w}" height="{h}" rx="{rx}"/>']
        if lines:
            s.append(f'<text class="t" x="{cx:.1f}" y="{y + 17:.1f}" text-anchor="middle">{esc(title)}</text>')
            s.append(f'<line class="hr" x1="{x:.1f}" y1="{y + 24:.1f}" x2="{x + w:.1f}" y2="{y + 24:.1f}"/>')
            for i, ln in enumerate(lines):
                s.append(f'<text class="a" x="{x + 8:.1f}" y="{y + 38 + 14 * i:.1f}">{esc(ln)}</text>')
        elif sub:
            s.append(f'<text class="t" x="{cx:.1f}" y="{cy - 3:.1f}" text-anchor="middle">{esc(title)}</text>')
            s.append(f'<text class="s" x="{cx:.1f}" y="{cy + 12:.1f}" text-anchor="middle">{esc(sub)}</text>')
        else:
            s.append(f'<text class="t" x="{cx:.1f}" y="{cy + 4.5:.1f}" text-anchor="middle">{esc(title)}</text>')
        if badge:
            by = y + h + 13 if badge_below else y - 5
            s.append(f'<text class="badge b-{badge_kind}" x="{x + 2:.1f}" y="{by:.1f}">{esc(badge)}</text>')
        s.append("</g>")
        self.parts.append("".join(s))

    def chip(self, key, x, cy, title, kind="chip"):
        w = text_width(title, size=11.5) + 16
        self.node(key, x + w / 2, cy, title, kind=kind, w=round(w, 1), h=24)
        return x + w

    # Geometry

    def _boundary(self, key, tx, ty, pad=2.5):
        cx, cy, w, h = self.nodes[key]
        dx, dy = tx - cx, ty - cy
        if dx == 0 and dy == 0:
            return cx, cy
        sx = (w / 2 + pad) / abs(dx) if dx else math.inf
        sy = (h / 2 + pad) / abs(dy) if dy else math.inf
        s = min(sx, sy)
        return cx + dx * s, cy + dy * s

    def _pt(self, p):
        if isinstance(p, str):
            return self.nodes[p][:2]
        return p

    # Edges

    def arrow(self, a, b, label="", kind="acl", bend=0.0, lpos=0.5, loff=10, lside=1,
              head=True, lkind=None, lanchor="auto"):
        ax, ay = self._pt(a)
        bx, by = self._pt(b)
        mx, my = (ax + bx) / 2, (ay + by) / 2
        d = math.hypot(bx - ax, by - ay)
        ux, uy = (bx - ax) / d, (by - ay) / d
        px, py = -uy, ux
        cx, cy = mx + px * bend * 2, my + py * bend * 2
        if isinstance(a, str):
            x1, y1 = self._boundary(a, cx, cy) if bend else self._boundary(a, bx, by)
        else:
            x1, y1 = ax, ay
        if isinstance(b, str):
            x2, y2 = self._boundary(b, cx, cy, pad=4) if bend else self._boundary(b, ax, ay, pad=4)
        else:
            x2, y2 = bx, by
        mk = f' marker-end="url(#{self.name}-{kind})"' if head else ""
        if bend:
            self.parts.append(f'<path class="e {kind}" d="M{x1:.1f},{y1:.1f} Q{cx:.1f},{cy:.1f} '
                              f'{x2:.1f},{y2:.1f}"{mk}/>')
            t = lpos
            lx = (1 - t) ** 2 * x1 + 2 * (1 - t) * t * cx + t ** 2 * x2
            ly = (1 - t) ** 2 * y1 + 2 * (1 - t) * t * cy + t ** 2 * y2
        else:
            self.parts.append(f'<line class="e {kind}" x1="{x1:.1f}" y1="{y1:.1f}" x2="{x2:.1f}" '
                              f'y2="{y2:.1f}"{mk}/>')
            lx, ly = x1 + (x2 - x1) * lpos, y1 + (y2 - y1) * lpos
        if label:
            sgn = lside
            anchor = lanchor
            if anchor == "auto":
                ox = px * sgn
                anchor = "middle" if abs(ox) < 0.7 else ("start" if ox > 0 else "end")
            self.label_at(lx + px * loff * sgn, ly + py * loff * sgn, label, lkind or kind, anchor)

    def poly(self, pts, kind="acl", label="", lat=None, head=True, lkind=None, lanchor="middle"):
        d = "M" + " L".join(f"{x:.1f},{y:.1f}" for x, y in pts)
        mk = f' marker-end="url(#{self.name}-{kind})"' if head else ""
        self.parts.append(f'<path class="e {kind}" d="{d}"{mk}/>')
        if label and lat:
            self.label_at(lat[0], lat[1], label, lkind or kind, lanchor)

    def label_at(self, x, y, s, kind="acl", anchor="middle", bg=True):
        tw = text_width(s) + 8
        rx = {"middle": x - tw / 2, "start": x - 4, "end": x - tw + 4}[anchor]
        if bg:
            self.front.append(f'<rect class="lbg" x="{rx:.1f}" y="{y - 9:.1f}" width="{tw:.1f}" '
                              f'height="13" rx="2"/>')
        self.front.append(f'<text class="lb c-{kind}" x="{x:.1f}" y="{y + 1.5:.1f}" '
                          f'text-anchor="{anchor}">{esc(s)}</text>')

    # Backgrounds and text

    def region(self, x, y, w, h, label="", kind="", lx=None, ly=None):
        self.back.append(f'<rect class="rg {kind}" x="{x}" y="{y}" width="{w}" height="{h}" rx="8"/>')
        if label:
            self.back.append(f'<text class="rgl {kind}" x="{lx if lx is not None else x + 10}" '
                             f'y="{ly if ly is not None else y + 17}">{esc(label)}</text>')

    def hull(self, x, y, w, h, label="", lx=None, ly=None):
        self.back.append(f'<rect class="hull" x="{x}" y="{y}" width="{w}" height="{h}" rx="10"/>')
        if label:
            self.back.append(f'<text class="hl" x="{lx if lx is not None else x + 10}" '
                             f'y="{ly if ly is not None else y - 6}">{esc(label)}</text>')

    def text(self, x, y, s, cls="note", anchor="start"):
        self.front.append(f'<text class="{cls}" x="{x:.1f}" y="{y:.1f}" '
                          f'text-anchor="{anchor}">{esc(s)}</text>')

    def raw(self, s, layer="parts"):
        getattr(self, layer).append(s)

    def bracket(self, x1, x2, y, label, kind="", down=True):
        t = 6 if down else -6
        self.parts.append(f'<path class="br {kind}" d="M{x1:.1f},{y - t:.1f} L{x1:.1f},{y:.1f} '
                          f'L{x2:.1f},{y:.1f} L{x2:.1f},{y - t:.1f}"/>')
        cls = "mono acc" if kind == "acc" else "mono m"
        self.text((x1 + x2) / 2, y + (14 if down else -6), label, cls, "middle")

    # Output

    def body(self):
        defs = "".join(
            f'<marker id="{self.name}-{m}" viewBox="0 0 10 10" refX="8.5" refY="5" '
            f'markerWidth="7" markerHeight="7" orient="auto-start-reverse">'
            f'<path class="mk-{m}" d="M0,0 L10,5 L0,10 z"/></marker>' for m in MARKERS)
        return (f'<defs>{defs}</defs><rect class="bgr" width="{self.w}" height="{self.h}"/>'
                + "".join(self.back) + "".join(self.parts) + "".join(self.front))

    def inline(self):
        return (f'<svg viewBox="0 0 {self.w} {self.h}" role="img" aria-label="{esc(self.label)}">'
                + self.body() + "</svg>")

    def standalone(self):
        light = "".join(f"--{k}: {v[0]}; " for k, v in TOKENS.items())
        dark = "".join(f"--{k}: {v[1]}; " for k, v in TOKENS.items())
        style = (f"svg {{ {light}}} @media (prefers-color-scheme: dark) {{ svg {{ {dark}}} }}"
                 + RULES)
        return (f'<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 {self.w} {self.h}" '
                f'width="{self.w}" height="{self.h}" role="img" aria-label="{esc(self.label)}">'
                f"<style>{style}</style>" + self.body() + "</svg>\n")


FIGS = []


def fig(f):
    FIGS.append(f)
    return f


# 1. Checked data and its meaning ------------------------------------------------

def embeddings():
    f = Fig("embeddings", 900, 300,
            "Deep data is checked by Bool functions; soundness lemmas turn a true check into "
            "a proposition, which the shallow constructions consume.")
    f.region(150, 28, 380, 150, "DEEP EMBEDDING: FINITE DATA")
    f.region(600, 28, 290, 150, "SHALLOW EMBEDDING: MATHLIB")
    f.node("julia", 70, 100, "Julia, Catlab", "muted", w=112, sub="phase 4")
    f.node("data", 245, 100, "deep data", w=140, sub="Schema, Translation")
    f.node("check", 435, 100, "Bool checker", w=150, sub="checkValid S S' peq")
    f.node("prop", 680, 100, "proposition", w=120, sub="T.Valid S S'")
    f.node("sem", 832, 100, "construction", w=100, sub="T.functor")
    f.arrow("julia", "data", "JSON", "muted", lside=-1)
    f.arrow("data", "check", "input", "acl", lside=-1)
    f.arrow("check", "prop", "soundness lemma", "eq", lside=-1, loff=11)
    f.arrow("prop", "sem", "uses", "acl", lside=-1)
    f.text(832, 140, "S.cat ⥤ S'.cat", "mono m", "middle")
    f.node("kernel", 330, 245, "decide, decide +kernel", w=190, sub="the kernel evaluates")
    f.node("native", 590, 245, "native_decide, csd-check", "muted", w=200,
           sub="trusts the compiler; marked")
    f.arrow("kernel", "check", "evaluates to true", "acl", lside=-1, loff=8, lpos=0.5)
    f.arrow("native", "check", "evaluates to true", "muted", lside=1, loff=8, lpos=0.5)
    return f


# 2. A schema --------------------------------------------------------------------

def schema_orders():
    f = Fig("schema-orders", 800, 420,
            "The Orders schema: five entity types, six references, attributes into value types, "
            "two equations and one aggregate with a member.")
    f.hull(292, 120, 476, 150, "aggregate: root Order, member OrderLine", ly=113)
    f.node("cust", 130, 80, "Customer", lines=["name : string"], w=150)
    f.node("addr", 130, 300, "Address", lines=["street : string", "city : string"], w=150,
           badge="value object", badge_kind="muted", badge_below=True)
    f.node("order", 395, 195, "Order", lines=["id : uuid", "placedOn : date",
                                              "status : OrderStatus"], w=170)
    f.node("line", 660, 195, "OrderLine", lines=["quantity : int", "unitPrice : decimal",
                                                 "sku : string"], w=170)
    f.node("prod", 660, 345, "Product", lines=["sku : string", "name : string",
                                               "listPrice : decimal"], w=170)
    f.arrow("order", "cust", "customer", "eq", lside=-1, lpos=0.45, loff=14)
    f.arrow("cust", "addr", "address", "eq", lside=1, lpos=0.5, loff=8)
    f.arrow("order", "addr", "billTo", "eq", lside=1, lpos=0.55, loff=12)
    f.arrow("order", "addr", "shipTo", "acl", bend=34, lpos=0.55, lside=1, loff=10)
    f.arrow("line", "order", "order (owner)", "acl", lside=-1, loff=12)
    f.arrow("line", "prod", "product", "acl", lside=1, lpos=0.62, loff=8)
    f.text(24, 404, "equations:", "mono m")
    f.text(100, 404, "billTo = customer.address", "mono acc")
    f.text(300, 404, "sku = product.sku  (out of OrderLine, ends in string)", "mono")
    return f


# 3. Path equality by rewriting --------------------------------------------------

def rewriting():
    f = Fig("rewriting", 820, 280,
            "A rewrite replaces one side of an equation inside a path; the class of a path is "
            "computed in rounds of rewrites until a round adds nothing.")
    f.text(24, 30, "paths out of OrderLine, in Orders", "rgl")
    x = 40
    x = f.chip("a0", x, 70, "order")
    xs1 = x + 6
    x = f.chip("a1", x + 6, 70, "billTo", "chip s")
    xe1 = x
    x = f.chip("a2", x + 6, 70, "city")
    f.bracket(40, xs1 - 6, 92, "u")
    f.bracket(xs1, xe1, 92, "s.1 = [billTo]", "acc")
    f.bracket(xe1 + 6, x, 92, "v")
    x = 40
    x = f.chip("b0", x, 190, "order")
    xs2 = x + 6
    x = f.chip("b1", x + 6, 190, "customer", "chip s")
    x = f.chip("b2", x + 6, 190, "address", "chip s")
    xe2 = x
    x = f.chip("b3", x + 6, 190, "city")
    f.bracket(40, xs2 - 6, 212, "u")
    f.bracket(xs2, xe2, 212, "s.2 = [customer, address]", "acc")
    f.bracket(xe2 + 6, x, 212, "v")
    f.arrow((150, 118), (150, 172), "", "eq", head=True)
    f.arrow((170, 172), (170, 118), "", "eq", head=True)
    f.text(186, 140, "Rewrite: tgt? OrderLine u = Order, the source of", "note fg")
    f.text(186, 155, "the equation billTo = customer.address", "note fg")
    f.region(470, 24, 330, 226, "classOf OrderLine [order, billTo, city]")
    rows = [("round 0", "order.billTo.city"),
            ("round 1", "+ order.customer.address.city"),
            ("round 2", "no new path: the class is closed")]
    for i, (r, s) in enumerate(rows):
        y = 64 + 30 * i
        f.text(486, y, r, "mono m")
        f.text(546, y, s, "mono acc" if i == 1 else "mono")
    f.text(486, 172, "candidates: paths of at most n generators,", "note")
    f.text(486, 187, "n = number of entity types (Acyclic)", "note")
    f.text(486, 222, "pathEqAcyclic o l l' := l' ∈ classOf o l", "mono")
    return f


# 4. A translation ---------------------------------------------------------------

def translation():
    f = Fig("translation", 820, 500,
            "The translation CatalogPL to Orders sends both entity types to Product and each "
            "generator to a path; a translation that breaks an equation fails the check.")
    f.region(20, 24, 230, 270, "CATALOGPL", "pl")
    f.region(570, 24, 230, 270, "ORDERS (PART)")
    f.node("v", 135, 88, "Variant", "pl", lines=["sku : string", "price : decimal"], w=160)
    f.node("p", 135, 215, "Product", "pl", lines=["name : string"], w=160)
    f.arrow("v", "p", "product", "acl", lside=1, loff=8)
    f.node("op", 685, 150, "Product", lines=["sku : string", "name : string",
                                             "listPrice : decimal"], w=170)
    f.node("ol", 685, 248, "OrderLine", "muted", w=120, h=26)
    f.arrow("ol", "op", "", "muted")
    f.arrow("v", "op", "Variant ↦ Product", "map", bend=-12, lpos=0.42, loff=14, lside=-1)
    f.arrow("p", "op", "Product ↦ Product", "map", bend=8, lpos=0.4, loff=13, lside=-1)
    f.text(410, 222, "generator images", "rgl", "middle")
    imgs = ["product ↦ [ ]  (identity)", "price ↦ [listPrice]", "sku ↦ [sku]  (unlisted)",
            "name ↦ [name]  (unlisted)"]
    for i, s in enumerate(imgs):
        f.text(410, 241 + 15 * i, s, "mono", "middle")
    f.region(20, 314, 780, 170, "ORDERSPL → PAYMENTS WITH billTo ↦ [shipTo]: NOT VALID", "warn")
    f.text(40, 352, "equation of OrdersPL, out of Order", "note")
    f.text(40, 376, "billTo", "mono acc")
    f.text(100, 376, "=", "mono")
    f.text(118, 376, "customer.address", "mono acc")
    f.arrow((250, 372), (420, 372), "mapPath", "acl", lside=-1, loff=10)
    f.text(440, 352, "image out of Invoice, in Payments", "note")
    f.text(440, 376, "shipTo", "mono warn")
    f.text(500, 376, "≠", "mono warn")
    f.text(518, 376, "payer.address", "mono")
    f.text(440, 406, "pathEq Invoice [shipTo] [payer, address] = false", "mono warn")
    f.text(440, 426, "Payments is acyclic, so false refutes PathEq", "note")
    f.text(440, 441, "(pathEq_iff_of_acyclic): the eqn clause fails.", "note")
    f.text(40, 406, "with billTo ↦ [payer, address] (ordersPayments)", "note")
    f.text(40, 421, "both sides go to payer.address: the clause holds.", "note")
    return f


# 5. The example context map -----------------------------------------------------

def context_map():
    f = Fig("context-map", 860, 420,
            "The example context map: seven contexts in the four Showcase domains, with "
            "inclusions out of published languages and the kernel, and two anti-corruption "
            "translations.")
    f.region(20, 20, 210, 260, "DOMAIN CATALOG")
    f.region(262, 20, 316, 384, "DOMAIN ORDERS")
    f.region(610, 20, 230, 260, "DOMAIN PAYMENTS")
    f.region(610, 296, 230, 108, "DOMAIN SHIPPING")
    f.node("cpl", 125, 92, "CatalogPL", "pl", w=170, sub="Product, Variant")
    f.node("cat", 125, 220, "Catalog", w=170, sub="4 entity types")
    f.node("opl", 420, 92, "OrdersPL", "pl", w=200, sub="Customer, Address, Order")
    f.node("ord", 420, 220, "Orders", w=200, sub="5 entity types")
    f.node("ker", 420, 350, "Customers", "kern", w=200, sub="Customer, Address",
           badge="kernel", badge_kind="kern")
    f.node("pay", 725, 220, "Payments", w=170, sub="6 entity types")
    f.node("shp", 725, 350, "Shipping", w=170, sub="5 entity types")
    f.arrow("cpl", "cat", "inclusion", "incl", lside=-1, loff=8, lanchor="start")
    f.arrow("cpl", "ord", "catalogOrders", "acl", lside=1, lpos=0.42, loff=12)
    f.arrow("opl", "ord", "inclusion", "incl", lside=-1, loff=8, lanchor="start")
    f.arrow("opl", "pay", "ordersPayments", "acl", lside=-1, lpos=0.5, loff=12)
    f.arrow("ker", "ord", "inclusion", "kern", lside=1, loff=8, lanchor="start")
    f.arrow("ker", "shp", "inclusion", "kern", lside=-1, loff=10)
    return f


# 6. Declared and free diamonds --------------------------------------------------

def routes():
    f = Fig("routes", 820, 260,
            "A declared route equation identifies two routes in J, and D must send them to the "
            "same functor; an undeclared diamond keeps two morphisms and one reference per route.")
    for i, (title, kind) in enumerate([("DECLARED: routeEqns p q", "pl"),
                                       ("FREE: no declaration", "")]):
        x0 = 20 + i * 410
        f.region(x0, 20, 390, 220, title, kind)
        u, a, b, d = f"u{i}", f"a{i}", f"b{i}", f"d{i}"
        f.node(u, x0 + 60, 130, "U", w=44)
        f.node(a, x0 + 195, 70, "A", w=44)
        f.node(b, x0 + 195, 190, "B", w=44)
        f.node(d, x0 + 330, 130, "D", w=44)
        f.arrow(u, a, "f", "acl", lside=-1, loff=9)
        f.arrow(a, d, "g", "acl", lside=-1, loff=9)
        f.arrow(u, b, "f'", "acl", lside=1, loff=9)
        f.arrow(b, d, "g'", "acl", lside=1, loff=9)
    f.text(215, 126, "p = f ≫ g", "mono acc", "middle")
    f.text(215, 141, "q = f' ≫ g'", "mono acc", "middle")
    f.text(215, 228, "coherent: D.map p = D.map q", "mono acc", "middle")
    f.text(625, 126, "p ≠ q in J", "mono", "middle")
    f.text(625, 228, "y ↦ D p y and D q y: two references", "mono m", "middle")
    return f


# 7. Lax integration -------------------------------------------------------------

def lax():
    f = Fig("lax", 860, 410,
            "Three fibers of the lax integration; references across contexts end at objects of "
            "the published language, and the projection sends them to arrows of the opposite of J.")
    f.region(20, 20, 250, 250, "FIBER ORDERS")
    f.region(305, 20, 250, 250, "FIBER ORDERSPL", "pl")
    f.region(590, 20, 250, 250, "FIBER PAYMENTS")
    f.node("oO", 145, 100, "Order", w=110)
    f.node("oC", 145, 210, "Customer", w=110)
    f.arrow("oO", "oC", "customer", "acl", lside=-1, loff=8)
    f.node("pO", 430, 100, "Order", "pl", w=110)
    f.node("pC", 430, 210, "Customer", "pl", w=110)
    f.arrow("pO", "pC", "customer", "acl", lside=-1, loff=8)
    f.node("yR", 715, 60, "Refund", w=110)
    f.node("yI", 715, 140, "Invoice", w=110, sub="= T Order")
    f.node("yP", 715, 225, "Payer", w=110, sub="= T Customer")
    f.arrow("yR", "yI", "invoice", "acl", lside=-1, loff=8)
    f.arrow("yI", "yP", "payer", "acl", lside=-1, loff=8)
    f.arrow("oO", "pO", "publishedOrder", "incl", lside=-1, loff=10)
    f.arrow("yI", "pO", "transport", "muted", lside=-1, loff=11, lpos=0.3)
    f.arrow("yP", "pC", "transport", "muted", lside=-1, loff=11, lpos=0.3)
    f.arrow("yR", "pO", "refundOfOrder", "eq", bend=22, lpos=0.7, lside=1, loff=11)
    f.text(20, 402, "projection onto J^op", "rgl")
    f.node("jO", 145, 360, "Orders", "dot", w=90, h=26)
    f.node("jP", 430, 360, "OrdersPL", "dot", w=90, h=26)
    f.node("jY", 715, 360, "Payments", "dot", w=90, h=26)
    f.arrow("jO", "jP", "(ordersPL_orders).op", "muted", lside=-1, loff=10)
    f.arrow("jY", "jP", "ordersToPayments.op", "eq", lside=1, loff=10)
    for x in (145, 430, 715):
        f.poly([(x, 274), (x, 342)], "muted", head=False)
    return f


# 8. Published languages ---------------------------------------------------------

def published():
    f = Fig("published-language", 820, 360,
            "OrdersPL contains roots of Orders only; adding OrderLine, a member of the Order "
            "aggregate, fails RootsOnly.")
    f.region(20, 20, 220, 320, "ORDERSPL", "pl")
    f.region(330, 20, 470, 320, "ORDERS (OWNER)")
    f.node("pc", 130, 70, "Customer", "pl", w=130)
    f.node("pa", 130, 135, "Address", "pl", w=130)
    f.node("po", 130, 200, "Order", "pl", w=130)
    f.node("pl", 130, 290, "OrderLine", "warn", w=130, badge="withLines", badge_kind="warn")
    f.node("oc", 440, 70, "Customer", w=130, badge="root", badge_kind="muted")
    f.node("oa", 440, 135, "Address", w=130, badge="root", badge_kind="muted")
    f.node("oo", 440, 200, "Order", w=130, badge="root", badge_kind="muted")
    f.node("ol", 440, 290, "OrderLine", w=130, badge="member", badge_kind="muted")
    f.node("op", 680, 290, "Product", w=130, badge="root", badge_kind="muted")
    f.hull(362, 168, 156, 152, "")
    f.text(526, 196, "aggregate Order", "hl")
    f.arrow("ol", "oo", "order (owner)", "acl", lside=-1, loff=8, lanchor="start")
    f.arrow("ol", "op", "product", "acl", lside=-1, loff=10)
    for a, b in [("pc", "oc"), ("pa", "oa"), ("po", "oo")]:
        f.arrow(a, b, "", "incl")
    f.arrow("pl", "ol", "member: RootsOnly fails", "warn", lside=-1, loff=10)
    f.text(556, 70, "RootsOnly P S:", "mono")
    f.text(556, 86, "∀ e ∈ P.entities,", "mono")
    f.text(556, 102, "∀ A ∈ S.aggregates,", "mono")
    f.text(556, 118, "e ∉ members of A", "mono")
    return f


# 9. The pushout of a kernel span ------------------------------------------------

def pushout():
    f = Fig("pushout", 820, 430,
            "The two arrows out of the Customers kernel and the legs into the glued schema form "
            "a pushout square in Cat; functors that agree on the kernel factor uniquely through it.")
    f.node("k", 120, 70, "Customers", "kern", w=150, sub="kernel")
    f.node("o", 470, 70, "Orders", w=150, sub="5 entity types")
    f.node("s", 120, 250, "Shipping", w=150, sub="5 entity types")
    f.node("g", 470, 250, "Orders ⊔ Shipping", "glued", w=170, sub="8 entity types")
    f.node("x", 720, 335, "X", w=60, h=30)
    f.arrow("k", "o", "ι₁ = D.map f₁", "kern", lside=-1, loff=10)
    f.arrow("k", "s", "ι₂ = D.map f₂", "kern", lside=1, loff=8)
    f.arrow("o", "g", "inl", "glued", lside=-1, loff=8)
    f.arrow("s", "g", "inr", "glued", lside=1, loff=11)
    f.arrow("o", "x", "F₁", "acl", bend=-30, lpos=0.5, lside=-1, loff=10)
    f.arrow("s", "x", "F₂", "acl", bend=26, lpos=0.5, lside=1, loff=10)
    f.arrow("g", "x", "desc (unique)", "uniq", lside=-1, loff=10, lpos=0.45)
    f.raw('<path class="br" d="M436,212 L436,198 L450,198"/>')
    f.text(24, 380, "f₁ = customers_orders, f₂ = customers_shipping; condition: ι₁ ⋙ F₁ = ι₂ ⋙ F₂",
           "mono")
    f.text(24, 398, "isPushout_kernel, from Gluing.isPushout", "mono m")
    f.text(24, 416, "glued: entities of both, Customer and Address once; equations of both",
           "note")
    return f


# 10. A failing kernel -----------------------------------------------------------

def failing():
    f = Fig("failing-kernel", 820, 360,
            "Shipping's equation deliveryAddress = address holds in the glued schema, so the leg "
            "from Orders identifies two distinct morphisms and is not faithful.")
    f.region(20, 20, 300, 150, "ORDERS₂")
    f.region(20, 190, 300, 150, "SHIPPING₂")
    f.region(470, 100, 330, 160, "GLUED", "kern")
    for i, y in enumerate((95, 265)):
        c, a = f"c{i}", f"a{i}"
        f.node(c, 80, y, "Customer", w=90)
        f.node(a, 260, y, "Address", w=90)
        f.arrow(c, a, "address", "acl", bend=-18, lside=-1, loff=8)
        f.arrow(c, a, "deliveryAddress", "acl", bend=18, lside=1, loff=8)
    f.text(170, 162, "distinct paths: address ≠ deliveryAddress", "mono m", "middle")
    f.text(170, 332, "equation: deliveryAddress = address", "mono acc", "middle")
    f.node("gc", 540, 180, "Customer", "glued", w=90)
    f.node("ga", 720, 180, "Address", "glued", w=90)
    f.arrow("gc", "ga", "address", "glued", bend=-18, lside=-1, loff=8)
    f.arrow("gc", "ga", "deliveryAddress", "glued", bend=18, lside=1, loff=8)
    f.text(635, 248, "equal morphisms of the glued schema", "mono warn", "middle")
    f.poly([(322, 95), (468, 150)], "warn", "inl: not faithful", lat=(395, 108),
           lkind="warn")
    f.poly([(322, 265), (468, 210)], "glued", "inr", lat=(395, 252))
    return f


# 12. Data gluing ----------------------------------------------------------------

def data_gluing():
    f = Fig("data-gluing", 860, 300,
            "Restriction is contravariant: the pushout of schema categories becomes a "
            "correspondence between states of the glued schema and pairs of states that agree "
            "on the kernel.")
    f.text(20, 26, "schema categories: pushout in Cat", "rgl")
    f.node("k", 80, 80, "Customers", "kern", w=110)
    f.node("o", 290, 80, "Orders", w=110)
    f.node("s", 80, 230, "Shipping", w=110)
    f.node("g", 290, 230, "glued", "glued", w=110)
    f.arrow("k", "o", "ι₁", "kern", lside=-1, loff=9)
    f.arrow("k", "s", "ι₂", "kern", lside=1, loff=8)
    f.arrow("o", "g", "inl", "glued", lside=-1, loff=8)
    f.arrow("s", "g", "inr", "glued", lside=1, loff=9)
    f.raw('<path class="br" d="M250,204 L250,190 L264,190"/>')
    f.text(470, 26, "states, Δ = precomposition: pullback of sets", "rgl")
    f.node("Sg", 520, 80, "State glued", "glued", w=130)
    f.node("So", 760, 80, "State Orders", w=130)
    f.node("Ss", 520, 230, "State Shipping", w=130)
    f.node("Sk", 760, 230, "State Customers", "kern", w=130)
    f.arrow("Sg", "So", "Δ inl", "glued", lside=-1, loff=9)
    f.arrow("Sg", "Ss", "Δ inr", "glued", lside=1, loff=8)
    f.arrow("So", "Sk", "Δ ι₁", "kern", lside=-1, loff=8)
    f.arrow("Ss", "Sk", "Δ ι₂", "kern", lside=1, loff=9)
    f.raw('<path class="br" d="M598,120 L612,120 L612,106"/>')
    f.text(640, 155, "stateEquiv", "mono acc", "middle")
    f.text(640, 170, "X ↦ (Δ inl X, Δ inr X)", "mono", "middle")
    f.text(20, 290, "values: each state carries values v : X(v) ≃ K v; restriction keeps them, "
           "since translations fix value types", "note")
    return f


# 11. Merging a component ---------------------------------------------------------

def merge():
    f = Fig("merge", 940, 430,
            "Two kernels shared by Orders, Shipping and Payments form a component; merging it "
            "gives one glued context, and the arrows into its members become arrows into the "
            "glued context.")
    f.region(20, 24, 450, 300, "COMPONENT")
    f.region(500, 24, 420, 300, "MERGED MAP")
    f.node("kc", 135, 80, "Customers", "kern", w=150, sub="Customer, Address",
           badge="kernel", badge_kind="kern")
    f.node("ka", 355, 80, "Addresses", "kern", w=150, sub="Address",
           badge="kernel", badge_kind="kern")
    f.node("o", 85, 230, "Orders", w=120, sub="5 entity types")
    f.node("s", 245, 230, "Shipping", w=120, sub="5 entity types")
    f.node("p", 405, 230, "Payments", w=120, sub="6 entity types")
    f.arrow("kc", "o", "", "kern")
    f.arrow("kc", "s", "", "kern")
    f.arrow("ka", "o", "", "kern")
    f.arrow("ka", "s", "", "kern")
    f.arrow("ka", "p", "", "kern")
    f.text(36, 300, "Shipping shares Customer, Address with Orders through Customers", "mono")
    f.text(36, 314, "Payments shares Address with Orders through Addresses", "mono")
    f.node("cpl", 580, 80, "CatalogPL", "pl", w=120)
    f.node("opl", 840, 80, "OrdersPL", "pl", w=120)
    f.node("cat", 580, 250, "Catalog", w=120)
    f.node("g", 765, 250, "glued", "glued", w=150, sub="13 entity types")
    f.arrow("cpl", "cat", "inclusion", "incl", lside=-1, loff=8, lanchor="end", lpos=0.45)
    f.arrow("cpl", "g", "catalogOrders", "acl", lside=1, lpos=0.62, loff=10)
    f.arrow("opl", "g", "via Orders", "incl", bend=22, lpos=0.45, lside=1, loff=8,
            lanchor="end")
    f.arrow("opl", "g", "via Payments", "acl", bend=-22, lpos=0.45, lside=-1, loff=8,
            lanchor="start")
    f.text(24, 350, "glued = glueAll [Orders, Shipping, Payments, Customers, Addresses]", "mono")
    f.text(24, 368, "isColimit: the glued schema category is the colimit of D restricted to "
           "the component", "mono m")
    f.text(24, 386, "an arrow into a member goes to glued, its translation composed with the "
           "leg of the member (diagram_into)", "note")
    f.text(24, 404, "every leg fully faithful; the merged map has no cycle, so lax "
           "non-interference holds for its four contexts", "note")
    return f


# 14. Modules --------------------------------------------------------------------

def modules():
    f = Fig("modules", 1060, 400,
            "Imports between the modules of the DDD library: a chain from value types to "
            "certificates, context maps beside it, and the examples on top.")
    f.text(20, 18, "on Mathlib: Paths, Quotient, Grothendieck, IsPushout, Kan extensions", "note")
    core = [("Values", 55), ("Schema", 158), ("Semantics", 263), ("PathEq", 368),
            ("Translation", 475), ("Glue", 582), ("States", 685), ("Data", 785),
            ("Json", 885), ("Certificate", 995)]
    for name, x in core:
        f.node(name, x, 55, name, w=92 if name != "Certificate" else 100, h=30)
    for (a, _), (b, _) in zip(core, core[1:]):
        f.arrow(a, b, "", "acl")
    f.node("Compose", 420, 125, "Compose", w=92, h=30)
    f.node("ContextMap", 530, 125, "ContextMap", w=100, h=30)
    f.node("Union", 640, 125, "Union", w=80, h=30)
    f.node("Merge", 750, 125, "Merge", w=80, h=30)
    f.arrow("Translation", "Compose", "", "acl")
    f.arrow("Compose", "ContextMap", "", "acl")
    f.arrow("Glue", "ContextMap", "", "acl")
    f.arrow("Glue", "Union", "", "acl")
    f.arrow("Union", "Merge", "", "acl")
    f.poly([(530, 141), (530, 158), (750, 158), (750, 145)], "acl")
    f.region(20, 175, 1020, 205, "EXAMPLES")
    f.raw('<rect class="rg plain" x="38" y="206" width="358" height="44" rx="6"/>', "back")
    for name, x in [("Catalog", 82), ("Orders", 172), ("Payments", 262), ("Shipping", 352)]:
        f.node("x" + name, x, 228, name, w=82, h=30)
    f.poly([(368, 72), (368, 204)], "muted")
    f.node("xIntegration", 470, 228, "Integration", "pl", w=110, h=30)
    f.node("xRoutes", 600, 228, "Routes", w=90, h=30)
    f.node("xGluing", 470, 305, "Gluing", "kern", w=100, h=30)
    f.node("xExchange", 885, 305, "Exchange", w=100, h=30)
    f.node("xMerge", 600, 355, "Merge", "kern", w=100, h=30)
    f.node("xShowcase", 270, 305, "Showcase.ContextMapNotifications", "muted", w=240, h=26)
    f.node("xValues", 82, 305, "Values", w=82, h=30)
    f.poly([(397, 228), (413, 228)], "muted")
    f.arrow("ContextMap", "xIntegration", "", "muted")
    f.arrow("ContextMap", "xRoutes", "", "muted")
    f.arrow("xIntegration", "xGluing", "", "muted")
    f.arrow("xShowcase", "xIntegration", "", "muted")
    f.poly([(685, 72), (685, 297), (523, 297)], "muted")
    f.poly([(82, 321), (82, 338), (470, 338), (470, 322)], "muted")
    f.poly([(521, 313), (833, 313)], "muted")
    f.poly([(885, 72), (885, 288)], "muted")
    f.poly([(470, 244), (470, 260), (600, 260), (600, 336)], "muted")
    f.poly([(790, 125), (810, 125), (810, 355), (654, 355)], "muted")
    f.text(1040, 396, "arrows point from a module to the modules that import it; "
           "Certificate and Union also import Compose", "note", "end")
    return f


# 13. Next steps ------------------------------------------------------------------

def next_steps():
    f = Fig("next-steps", 940, 300,
            "The next steps in order, left to right, with the dependencies between them.")
    f.text(24, 28, "order of work", "rgl")
    f.poly([(120, 23), (910, 23)], "muted")
    f.node("s1", 85, 120, "1. Coherence by check", w=152, sub="Translation.comp", h=44)
    f.node("s2", 275, 120, "2. Phase 4", "pl", w=150, sub="JSON, certificates", h=44)
    f.node("s3", 465, 120, "3. Several inclusions", w=150, sub="n-ary gluing", h=44)
    f.node("s4", 655, 120, "4. Attributed states", w=150, sub="limits, colimits, Σ", h=44)
    f.node("s5", 845, 120, "5. Phase 5", "kern", w=150, sub="open systems", h=44)
    f.arrow("s1", "s3", "composite translations", "acl", bend=-26, lpos=0.5, lside=-1,
            loff=10)
    f.arrow("s3", "s5", "gluing along interfaces", "acl", bend=26, lpos=0.5, lside=1, loff=10)
    f.arrow("s4", "s5", "states", "acl", lside=-1, loff=12)
    f.node("c1", 300, 250, "names as indices", "muted", w=190,
           sub="if checks exceed CI time", h=40)
    f.node("c2", 580, 250, "rewriting certificates", "muted", w=260,
           sub="if a model has cycles and equations", h=40)
    f.text(24, 254, "conditional", "rgl")
    return f


# 13. The phase 4 pipeline -------------------------------------------------------

def pipeline():
    f = Fig("pipeline", 920, 260,
            "Lean exports the example map, Julia computes with Catlab and writes a "
            "certificate, and Lean checks each claim of the certificate.")
    f.region(20, 24, 200, 210, "LEAN")
    f.region(330, 24, 250, 210, "JULIA, CATLAB")
    f.region(690, 24, 210, 210, "LEAN")
    f.node("ex", 120, 80, "Examples/Exchange", "pl", w=150)
    f.node("ws", 275, 80, "workspace.json", "muted", w=104, h=30)
    f.node("run", 455, 80, "julia/run.jl", w=150)
    f.node("cert", 635, 80, "certificate.json", "muted", w=104, h=30)
    f.node("chk", 795, 80, "csd-check", "pl", w=150)
    f.arrow("ex", "ws", "", "acl")
    f.arrow("ws", "run", "", "acl")
    f.arrow("run", "cert", "", "acl")
    f.arrow("cert", "chk", "", "acl")
    for i, line in enumerate(["gluing: acset pushout", "sample states",
                              "restriction along images", "homomorphism search"]):
        f.text(345, 140 + 20 * i, line, "mono")
    for i, line in enumerate(["checkClaim per claim", "checkClaim_sound:",
                              "a passing claim holds", "32 claims, all hold"]):
        f.text(705, 140 + 20 * i, line, "mono acc" if i == 3 else "mono")
    for i, line in enumerate(["csd-export writes", "the map, the kernel", "expectations, the",
                              "failing scenario"]):
        f.text(35, 140 + 20 * i, line, "mono")
    return f


ALL = [embeddings, schema_orders, rewriting, translation, context_map, routes, lax,
       published, pushout, failing, merge, data_gluing, modules, next_steps, pipeline]


def build():
    return [g() for g in ALL]


if __name__ == "__main__":
    out = os.path.join(os.path.dirname(os.path.abspath(__file__)), "figures")
    os.makedirs(out, exist_ok=True)
    for g in build():
        with open(os.path.join(out, g.name + ".svg"), "w", encoding="utf-8") as fh:
            fh.write(g.standalone())
        print(g.name)
