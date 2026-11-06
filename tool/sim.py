"""Explicit-state simulator of the same semantics, over a tiny universe.

Used only to discard candidate properties quickly; it decides nothing.  Lean is
the judge of what holds.
"""
from __future__ import annotations
import itertools
import random
from collections import Counter
from parse import A, D, N, NAT, Contract, Schema, Role, Atom, Arg

AGENTS = [0, 1, 2]
SACTS = ["d0", "d1"]
NATS = [0, 1, 2, 3]
MULTS = [1, 2]


def domain(srt):
    if srt == A:
        return AGENTS
    if srt == D:
        return SACTS
    if srt == N:
        return [(a, d) for a in AGENTS for d in SACTS]
    return NATS


class State:
    __slots__ = ("m",)

    def __init__(self, m=None):
        self.m = m or {}   # pred -> Counter of tuples (holder first)

    def get(self, pred, tup):
        return self.m.get(pred, Counter())[tup]

    def key(self):
        return tuple(sorted((p, tuple(sorted((t, n) for t, n in c.items() if n > 0)))
                            for p, c in self.m.items() if any(n > 0 for n in c.values())))

    def copy(self):
        return State({p: Counter(c) for p, c in self.m.items()})


def ev(x: Arg, b: dict):
    if x.kind == "name":
        return b[x.name]
    if x.kind == "nterm":
        return (b[x.name], b[x.y])
    if x.kind == "num":
        return x.val
    raise ValueError(x)


def matches(tup, a: Atom, b):
    for t, x in zip(tup[1:], a.args[1:]):
        if x.kind == "wild":
            continue
        if x.kind == "nterm" and x.y == "_":
            if t[0] != b[x.name]:
                return False
            continue
        if t != ev(x, b):
            return False
    return True


def mult(a: Atom, b):
    return a.mult if isinstance(a.mult, int) else b[a.mult]


def extent(st: State, r: Role, b):
    if not r.listed:
        return [b[r.name]]
    cond = r.cond
    lv = r.name[:-2]
    out = []
    for q in AGENTS:
        bb = dict(b)
        bb[lv] = q
        if st.get(cond.pred, tuple(ev(x, bb) for x in cond.args)) > 0:
            out.append(q)
    return out


def eval_constraint(k, b):
    def val(ts):
        expr = " ".join(str(b[t]) if t in b else t for t in ts)
        return eval(expr)
    l, r = val(k.lhs), val(k.rhs)
    return {"=": l == r, "<=": l <= r, ">=": l >= r, "<": l < r, ">": l > r}[k.op]


def bindings(c: Contract, s: Schema):
    roles = [r.name for r in s.roles if not r.listed]
    for ra in itertools.permutations(AGENTS, len(roles)):
        for av in itertools.product(AGENTS, repeat=len(s.avars)):
            for sv in itertools.product(SACTS, repeat=len(s.svars)):
                nv_dom = [MULTS if v in s.mvars else NATS for v in s.nvars]
                for nv in itertools.product(*nv_dom):
                    b = dict(zip(roles, ra))
                    b.update(zip(s.avars, av))
                    b.update(zip(s.svars, sv))
                    b.update(zip(s.nvars, nv))
                    if all(eval_constraint(k, b) for k in s.constraints):
                        yield b


def fire(c: Contract, s: Schema, st: State, b) -> State | None:
    ext = {}
    for r in s.roles:
        ext[r.name] = extent(st, r, b)
    # preconditions
    for r in s.roles:
        for q in ext[r.name]:
            bb = dict(b)
            if r.listed:
                bb[r.name[:-2]] = q
            need = Counter()
            for a in r.req:
                need[(a.pred, tuple(ev(x, bb) for x in a.args))] += mult(a, bb)
            for (p, t), m in need.items():
                if st.get(p, t) < m:
                    return None
            for a in r.forb:
                if st.get(a.pred, tuple(ev(x, bb) for x in a.args)) > 0:
                    return None
    # freshness of name terms in no required atom
    req_nt = set()
    for r in s.roles:
        for a in r.req + ([r.cond] if r.cond else []):
            for x in a.args:
                if x.kind == "nterm":
                    req_nt.add((x.name, x.y))
    for r in s.roles:
        for a in r.add + r.dele + r.forb:
            for x in a.args:
                if x.kind == "nterm" and x.y != "_" and (x.name, x.y) not in req_nt:
                    nt = (b[x.name], b[x.y])
                    for p, cnt in st.m.items():
                        for t, n in cnt.items():
                            if n > 0 and nt in t[1:]:
                                return None
    # per agent: joins of add / del, cleared, disjointness
    agents = sorted({q for r in s.roles for q in ext[r.name]})
    new = st.copy()
    for p in agents:
        adds, dels = Counter(), Counter()
        clears = []
        for r in s.roles:
            if p not in ext[r.name]:
                continue
            bb = dict(b)
            if r.listed:
                bb[r.name[:-2]] = p
            ra, rd = Counter(), Counter()
            for a in r.add:
                ra[(a.pred, (p,) + tuple(ev(x, bb) for x in a.args[1:]))] += mult(a, bb)
            for a in r.dele:
                rd[(a.pred, (p,) + tuple(ev(x, bb) for x in a.args[1:]))] += mult(a, bb)
            for a in r.clear:
                clears.append((a, bb))
            adds |= ra       # join = max
            dels |= rd
        K = Counter()
        for pred, cnt in st.m.items():
            for t, n in cnt.items():
                if n > 0 and t[0] == p:
                    for a, bb in clears:
                        if a.pred == pred and matches(t, a, bb):
                            K[(pred, t)] = n
        for key in adds:
            if dels[key] > 0 or K[key] > 0:
                return None
        for (pred, t), m in dels.items():
            cnt = new.m.setdefault(pred, Counter())
            cnt[t] = max(0, cnt[t] - m)
        for (pred, t), m in K.items():
            cnt = new.m.setdefault(pred, Counter())
            cnt[t] = max(0, cnt[t] - m)
        for (pred, t), m in adds.items():
            new.m.setdefault(pred, Counter())[t] += m
    return new


def successors(c: Contract, st: State, rng=None):
    for s in c.schemas:
        for b in bindings(c, s):
            n = fire(c, s, st, b)
            if n is not None:
                yield (s.name, n)
    for e in c.env_preds:
        for p in AGENTS:
            for d in NATS:
                n = st.copy()
                cnt = n.m.setdefault(e, Counter())
                for t in list(cnt):
                    if t[0] == p:
                        cnt[t] = 0
                cnt[(p, d)] = 1
                yield (f"env_{e}", n)


def explore(c: Contract, max_states=4000, walks=200, walk_len=40, seed=0):
    """BFS up to max_states, plus random walks; returns the list of visited states."""
    rng = random.Random(seed)
    init = State()
    seen = {init.key(): init}
    frontier = [init]
    while frontier and len(seen) < max_states:
        nxt = []
        for st in frontier:
            for _, n in successors(c, st):
                k = n.key()
                if k not in seen:
                    seen[k] = n
                    nxt.append(n)
                    if len(seen) >= max_states:
                        break
            if len(seen) >= max_states:
                break
        frontier = nxt
    states = list(seen.values())
    for _ in range(walks):
        st = init
        for _ in range(walk_len):
            succ = list(successors(c, st))
            if not succ:
                break
            st = rng.choice(succ)[1]
            k = st.key()
            if k not in seen:
                seen[k] = st
                states.append(st)
    return states
