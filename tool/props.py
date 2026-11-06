"""Properties as people write them, and as people read them.

Formal lines (what a user types or the builder produces):
    friend(Alice, Bob) => friend(Bob, Alice)
    friend(Alice, Bob) => not knows(Bob, Alice)
    friend(Alice, Bob) => Alice != Bob
    coin(Alice, Bob) and Alice != Bob => knows(Alice, Bob)
    member(Alice, g) => listed(base(g), Alice, act(g))
    never twice friend(Alice, Bob)
    never friend(Alice, Bob)
The premise is one fact with distinct variables; the conclusion's arguments are
those variables, base(g) / act(g) of a community name g, or <Alice>.x.
"""
from __future__ import annotations
import re
from cands import Cand
from parse import A, D, N, NAT

NAMES = {A: ["Alice", "Bob", "Carol", "Dave", "Eve", "Frank"], D: ["x", "y", "z", "w"],
         N: ["g", "h", "k"], NAT: ["t", "u", "v"]}


class PropError(Exception):
    pass


def var_names(sorts):
    cnt = {k: 0 for k in NAMES}
    out = []
    for s in sorts:
        out.append(NAMES[s][cnt[s]])
        cnt[s] += 1
    return out


def src_formal(s, nm):
    if isinstance(s, int):
        return nm[s]
    if s[0] == "fst":
        return f"base({nm[s[1]]})"
    if s[0] == "snd":
        return f"act({nm[s[1]]})"
    return f"<{nm[s[1]]}>.{nm[s[2]]}"


def formal(cd: Cand, c) -> str:
    nm = var_names(c.sorts[cd.e1])
    a1 = f"{cd.e1}({', '.join(nm)})"
    if cd.kind == "empty":
        return f"never {a1}"
    if cd.kind == "bound":
        return f"never twice {a1}"
    prem = a1
    if cd.ne:
        prem += f" and {src_formal(cd.ne[0], nm)} != {src_formal(cd.ne[1], nm)}"
    if cd.kind in ("eq", "neq"):
        op = "=" if cd.kind == "eq" else "!="
        return f"{prem} => {src_formal(cd.m[0], nm)} {op} {src_formal(cd.m[1], nm)}"
    a2 = f"{cd.e2}({', '.join(src_formal(s, nm) for s in cd.m)})"
    return f"{prem} => {'not ' if cd.kind == 'excl' else ''}{a2}"


# ------------------------------------------------------------------ parsing

ATOM = re.compile(r"^\s*([a-z_]\w*)\s*\((.*)\)\s*$")


def split_args(s):
    out, depth, cur = [], 0, ""
    for ch in s:
        if ch in "(<":
            depth += 1
        elif ch in ")>":
            depth -= 1
        if ch == "," and depth == 0:
            out.append(cur.strip())
            cur = ""
        else:
            cur += ch
    if cur.strip():
        out.append(cur.strip())
    return out


def parse_atom(s):
    m = ATOM.match(s)
    if not m:
        raise PropError(f"not a fact: {s.strip()}")
    return m.group(1), split_args(m.group(2))


def parse_term(t, env, sorts):
    """env: variable -> premise position.  Returns (source, sort)."""
    t = t.strip()
    m = re.fullmatch(r"(base|act)\((\w+)\)", t)
    if m:
        v = m.group(2)
        if v not in env or sorts[env[v]] != N:
            raise PropError(f"{m.group(1)}(..) needs a community name from the premise: {t}")
        return (("fst" if m.group(1) == "base" else "snd"), env[v]), (A if m.group(1) == "base" else D)
    m = re.fullmatch(r"<(\w+)>\.(\w+)", t)
    if m:
        a, d = m.group(1), m.group(2)
        if a not in env or d not in env or sorts[env[a]] != A or sorts[env[d]] != D:
            raise PropError(f"<person>.act needs a person and an act from the premise: {t}")
        return ("pair", env[a], env[d]), N
    if t in env:
        return env[t], sorts[env[t]]
    raise PropError(f"unknown variable {t} (use variables of the premise)")


def parse_prop(line: str, c) -> Cand:
    s = " ".join(line.strip().split())
    if not s:
        raise PropError("empty property")
    if s.startswith("never twice "):
        kind, rest = "bound", s[len("never twice "):]
    elif s.startswith("never "):
        kind, rest = "empty", s[len("never "):]
    else:
        kind, rest = None, s
    if kind:
        pred, args = parse_atom(rest)
        check_premise(pred, args, c)
        return Cand(kind, pred)
    if "=>" not in s:
        raise PropError("expected 'premise => conclusion', 'never twice fact' or 'never fact'")
    lhs, rhs = s.split("=>", 1)
    ne = ()
    parts = re.split(r"\s+and\s+", lhs.strip())
    pred, args = parse_atom(parts[0])
    check_premise(pred, args, c)
    sorts = c.sorts[pred]
    env = {a: i for i, a in enumerate(args)}
    if len(parts) > 2:
        raise PropError("at most one extra condition (a != b) in the premise")
    if len(parts) == 2:
        m = re.fullmatch(r"(.+?)\s*!=\s*(.+)", parts[1])
        if not m:
            raise PropError(f"the extra condition must read 'a != b': {parts[1]}")
        s1, t1 = parse_term(m.group(1), env, sorts)
        s2, t2 = parse_term(m.group(2), env, sorts)
        if t1 != A or t2 != A:
            raise PropError("the extra condition compares two persons")
        ne = (s1, s2)
    rhs = rhs.strip()
    m = re.fullmatch(r"(.+?)\s*(!=|=)\s*(.+)", rhs)
    if m and not ATOM.match(rhs):
        s1, t1 = parse_term(m.group(1), env, sorts)
        s2, t2 = parse_term(m.group(3), env, sorts)
        if t1 != A or t2 != A:
            raise PropError("(in)equalities compare two persons")
        if ne:
            raise PropError("an extra condition goes with a fact in the conclusion")
        return Cand("neq" if m.group(2) == "!=" else "eq", pred, "", (s1, s2))
    neg = False
    if rhs.startswith("not "):
        neg, rhs = True, rhs[4:]
    p2, args2 = parse_atom(rhs)
    if p2 not in c.sorts:
        raise PropError(f"unknown fact {p2}; this contract has: {', '.join(c.sorts)}")
    if len(args2) != len(c.sorts[p2]):
        raise PropError(f"{p2} takes {len(c.sorts[p2])} arguments")
    m2 = []
    for i, t in enumerate(args2):
        src, srt = parse_term(t, env, sorts)
        if srt != c.sorts[p2][i]:
            raise PropError(f"argument {i + 1} of {p2} must be a {sort_word(c.sorts[p2][i])}: {t}")
        m2.append(src)
    return Cand("excl" if neg else "impl", pred, p2, tuple(m2), ne)


def sort_word(s):
    return {A: "person", D: "act", N: "community name", NAT: "number"}[s]


def check_premise(pred, args, c):
    if pred not in c.sorts:
        raise PropError(f"unknown fact {pred}; this contract has: {', '.join(c.sorts)}")
    if len(args) != len(c.sorts[pred]):
        raise PropError(f"{pred} takes {len(c.sorts[pred])} arguments")
    if len(set(args)) != len(args) or not all(re.fullmatch(r"\w+", a) for a in args):
        raise PropError("the premise names each argument by its own variable")


# ------------------------------------------------------------------ English

def english(cd: Cand, c, gloss: dict) -> str:
    nm = var_names(c.sorts[cd.e1])
    g = gloss.get("facts", {})

    def term(s):
        if isinstance(s, int):
            return nm[s]
        if s[0] == "fst":
            return gloss.get("base", "the owner of {0}").format(nm[s[1]])
        if s[0] == "snd":
            return gloss.get("act", "{0}").format(nm[s[1]])
        return gloss.get("nterm", "{0}'s {1}").format(nm[s[1]], nm[s[2]])

    def fact(pred, args, neg=False):
        e = g.get(pred)
        if not e:
            return f"{'not ' if neg else ''}{pred}({', '.join(args)})"
        return (e["neg"] if neg else e["pos"]).format(*args)

    p = fact(cd.e1, nm)
    if cd.kind == "empty":
        return f"It never happens that {p}."
    if cd.kind == "bound":
        return cap(gloss.get("twice", "{0} is never recorded twice").format(p) + ".")
    prem = p
    if cd.ne:
        prem += f", and {term(cd.ne[0])} is not {term(cd.ne[1])}"
    if cd.kind == "neq":
        return f"If {prem}, then {term(cd.m[0])} and {term(cd.m[1])} are different people."
    if cd.kind == "eq":
        return f"If {prem}, then {term(cd.m[0])} is {term(cd.m[1])}."
    q = fact(cd.e2, [term(s) for s in cd.m], cd.kind == "excl")
    return f"If {prem}, then {q}."


def cap(s):
    return s[0].upper() + s[1:]
