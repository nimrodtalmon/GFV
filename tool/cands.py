"""Candidate properties: generic templates over a contract's predicates.

Templates (all universally quantified over the atom's arguments):
  empty(e)               e never holds
  bound(e)               e is held at most once (no duplicate atoms)
  eq / neq(e, s, t)      in every e-atom, two agent terms are equal / distinct
  impl(e1, e2, map)      e1(..) held  =>  e2(..) held     (map: e2's args from e1's)
  excl(e1, e2, map)      e1(..) held  =>  e2(..) not held
Agent terms of an atom: its agent positions and the base (first component) of a
community name.  Every candidate is checked on simulated runs first; survivors go
to Lean.
"""
from __future__ import annotations
import itertools
from dataclasses import dataclass
from parse import A, D, N, NAT, Contract
from leangen import LEAN_T

MAX_PER_PAIR = 400


@dataclass(frozen=True)
class Cand:
    kind: str
    e1: str
    e2: str = ""
    m: tuple = ()          # for impl/excl: source of each e2 position; for eq/neq: (s, t)
    ne: tuple = ()         # impl_ne: (s, t) agent terms of e1 that must differ

    def preds(self):
        return {self.e1, self.e2} - {""}

    def ident(self):
        return f"{self.kind}_{self.e1}_{self.e2}_{'_'.join(map(fmt_src, self.m))}"


def fmt_src(s):
    if isinstance(s, int):
        return str(s)
    return "".join(map(str, s))


def terms_of(sorts, want):
    """Sources in an atom with sorts `sorts` producing a value of sort `want`."""
    out = []
    for i, t in enumerate(sorts):
        if t == want:
            out.append(i)
    if want == A:
        out += [("fst", i) for i, t in enumerate(sorts) if t == N]
    if want == D:
        out += [("snd", i) for i, t in enumerate(sorts) if t == N]
    if want == N:
        out += [("pair", i, k) for i, t in enumerate(sorts) if t == A
                for k, u in enumerate(sorts) if u == D]
    return out


def gen(c: Contract):
    preds = list(c.sorts)
    out = []
    for e in preds:
        out.append(Cand("empty", e))
        out.append(Cand("bound", e))
        at = terms_of(c.sorts[e], A)
        for s_, t_ in itertools.combinations(at, 2):
            out.append(Cand("eq", e, "", (s_, t_)))
            out.append(Cand("neq", e, "", (s_, t_)))
    for e1 in preds:
        for e2 in preds:
            choices = [terms_of(c.sorts[e1], t) for t in c.sorts[e2]]
            if any(not ch for ch in choices):
                continue
            n = 0
            for m in itertools.product(*choices):
                if e1 == e2 and m == tuple(range(len(c.sorts[e1]))):
                    continue
                out.append(Cand("impl", e1, e2, m))
                out.append(Cand("excl", e1, e2, m))
                n += 1
                if n >= MAX_PER_PAIR:
                    break
    return out


def src_val(t, s):
    if isinstance(s, int):
        return t[s]
    if s[0] == "fst":
        return t[s[1]][0]
    if s[0] == "snd":
        return t[s[1]][1]
    return (t[s[1]], t[s[2]])


def holds(cd: Cand, st) -> bool:
    c1 = st.m.get(cd.e1, {})
    if cd.kind == "empty":
        return all(n == 0 for n in c1.values())
    if cd.kind == "bound":
        return all(n <= 1 for n in c1.values())
    for t, n in c1.items():
        if n <= 0:
            continue
        if cd.kind in ("eq", "neq"):
            a, b = src_val(t, cd.m[0]), src_val(t, cd.m[1])
            if (a == b) != (cd.kind == "eq"):
                return False
            continue
        if cd.ne and src_val(t, cd.ne[0]) == src_val(t, cd.ne[1]):
            continue
        tgt = tuple(src_val(t, s) for s in cd.m)
        has = st.m.get(cd.e2, {}).get(tgt, 0) > 0
        if has != (cd.kind == "impl"):
            return False
    return True


def filter_sim(cands, states):
    alive = list(cands)
    for st in states:
        alive = [cd for cd in alive if holds(cd, st)]
    return alive


# ---------------------------------------------------------------- rendering

VARN = {A: ["X", "Y", "Z", "W", "V", "U"], D: ["d", "d'", "d''", "d3"],
        N: ["n", "n'", "n''"], NAT: ["t", "t'", "t''"]}


def names_for(sorts):
    cnt = {k: 0 for k in VARN}
    out = []
    for t in sorts:
        out.append(VARN[t][cnt[t]])
        cnt[t] += 1
    return out


def src_text(s, nm):
    if isinstance(s, int):
        return nm[s]
    if s[0] == "fst":
        return f"base({nm[s[1]]})"
    if s[0] == "snd":
        return f"act({nm[s[1]]})"
    return f"<{nm[s[1]]}>.{nm[s[2]]}"


def text(cd: Cand, c: Contract) -> str:
    nm = names_for(c.sorts[cd.e1])
    a1 = f"{cd.e1}({', '.join(nm)})"
    if cd.kind == "empty":
        return f"no agent ever holds {cd.e1}"
    if cd.kind == "bound":
        return f"{a1} is never held twice"
    if cd.kind in ("eq", "neq"):
        op = "=" if cd.kind == "eq" else "≠"
        return f"{a1}  ⇒  {src_text(cd.m[0], nm)} {op} {src_text(cd.m[1], nm)}"
    a2 = f"{cd.e2}({', '.join(src_text(s, nm) for s in cd.m)})"
    if cd.ne:
        a1 += f" and {src_text(cd.ne[0], nm)} ≠ {src_text(cd.ne[1], nm)}"
    return f"{a1}  ⇒  {'' if cd.kind == 'impl' else 'not '}{a2}"


def lean_src(s, xs):
    if isinstance(s, int):
        return xs[s]
    if s[0] == "fst":
        return f"{xs[s[1]]}.1"
    if s[0] == "snd":
        return f"{xs[s[1]]}.2"
    return f"({xs[s[1]]}, {xs[s[2]]})"


def lean(cd: Cand, c: Contract, st="s") -> str:
    srt = c.sorts[cd.e1]
    xs = [f"x{i}" for i in range(len(srt))]
    binders = " ".join(f"({x} : {LEAN_T[t]})" for x, t in zip(xs, srt))
    a1 = f"{st}.{cd.e1} {' '.join(xs)}"
    if cd.kind == "empty":
        return f"∀ {binders}, {a1} = 0"
    if cd.kind == "bound":
        return f"∀ {binders}, {a1} ≤ 1"
    if cd.kind in ("eq", "neq"):
        op = "=" if cd.kind == "eq" else "≠"
        return f"∀ {binders}, {a1} > 0 → {lean_src(cd.m[0], xs)} {op} {lean_src(cd.m[1], xs)}"
    a2 = f"{st}.{cd.e2} {' '.join(lean_src(s, xs) for s in cd.m)}"
    rel = "> 0" if cd.kind == "impl" else "= 0"
    ne = f"{lean_src(cd.ne[0], xs)} ≠ {lean_src(cd.ne[1], xs)} → " if cd.ne else ""
    return f"∀ {binders}, {a1} > 0 → {ne}{a2} {rel}"


def gen_ne(c: Contract, refuted):
    """impl candidates refuted on runs, retried with 'unless two agent terms coincide'."""
    out = []
    for cd in refuted:
        if cd.kind != "impl":
            continue
        at = terms_of(c.sorts[cd.e1], A)
        for s_, t_ in itertools.combinations(at, 2):
            out.append(Cand("impl", cd.e1, cd.e2, cd.m, (s_, t_)))
    return out
