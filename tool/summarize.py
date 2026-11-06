"""Reduce a set of proved properties to a core: hide those that follow from others
by chaining implications (a presentation step only; Lean proved all of them)."""
from __future__ import annotations
import itertools
from cands import Cand


def comp_src(s2, m1):
    """Source s2 (over e3's positions) composed with m1 (e3's args from e1's)."""
    if isinstance(s2, int):
        return m1[s2]
    if s2[0] in ("fst", "snd"):
        x = m1[s2[1]]
        if isinstance(x, int):
            return (s2[0], x)
        if x[0] == "pair":
            return x[1] if s2[0] == "fst" else x[2]
        return None
    a, b = m1[s2[1]], m1[s2[2]]
    if isinstance(a, tuple) and isinstance(b, tuple) and a[0] == "fst" and b[0] == "snd" and a[1] == b[1]:
        return a[1]
    if isinstance(a, int) and isinstance(b, int):
        return ("pair", a, b)
    return None


def compose(m2, m1):
    out = tuple(comp_src(s, m1) for s in m2)
    return None if any(x is None for x in out) else out


def consequences(props):
    """One round of derivations from a set of properties."""
    out = set()
    impl = [p for p in props if p.kind == "impl" and not p.ne]
    for p in impl:
        for q in props:
            if q.e1 != p.e2:
                continue
            if q.kind in ("impl", "excl") and not q.ne:
                m = compose(q.m, p.m)
                if m is not None:
                    out.add(Cand(q.kind, p.e1, q.e2, m))
            if q.kind in ("neq", "eq"):
                m = compose(q.m, p.m)
                if m is not None:
                    out.add(Cand(q.kind, p.e1, "", m))
            if q.kind == "empty":
                out.add(Cand("empty", p.e1))
    neqs = [p for p in props if p.kind == "neq"]
    for q in props:
        if q.kind == "excl" and not q.ne:
            for p in neqs:
                if p.e1 == q.e2 and comp_src(p.m[0], q.m) == comp_src(p.m[1], q.m):
                    out.add(q)
            if Cand("empty", q.e2) in props:
                out.add(q)
        if q.kind == "impl" and q.ne and Cand("impl", q.e1, q.e2, q.m) in props:
            out.add(q)
    return out


def derivable(p, others, depth=3):
    known = set(others)
    for _ in range(depth):
        new = consequences(known) - known
        if not new:
            break
        known |= new
    if p in known:
        return True
    if p.kind == "excl" and not p.ne:
        if Cand("empty", p.e2) in known:
            return True
        for q in known:
            if q.kind == "neq" and q.e1 == p.e2 and comp_src(q.m[0], p.m) == comp_src(q.m[1], p.m):
                return True
    if p.kind == "impl" and p.ne and Cand("impl", p.e1, p.e2, p.m) in known:
        return True
    return False


def core(props):
    order = {"bound": 0, "neq": 1, "eq": 1, "impl": 2, "empty": 3, "excl": 4}
    ps = sorted(props, key=lambda p: (order[p.kind], len(p.m), str(p)))
    keep = list(ps)
    for p in reversed(ps):
        others = [q for q in keep if q != p]
        if derivable(p, others):
            keep = others
    return keep


if __name__ == "__main__":
    import sys
    from parse import parse_contract
    import cands as C
    c = parse_contract(open(sys.argv[1]).read(), sys.argv[2])
    allc = C.gen(c)
    allc += C.gen_ne(c, [x for x in allc if x.kind == "impl"])
    by_text = {C.text(x, c): x for x in allc}
    props = [by_text[l.strip()] for l in open(sys.argv[3]) if l.strip()]
    k = core(props)
    print(f"{len(props)} proved; core of {len(k)}:")
    for x in k:
        print("  " + C.text(x, c))
