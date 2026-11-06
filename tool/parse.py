"""Parser for speech-act schemas in GSC's clause notation (the cascade's schemas.txt).

Produces an IR: Contract(schemas, preds, env_preds) with sorts inferred.
Supported fragment: agent roles, agent variables, speech-act variables, one-level
name terms <X>.y and <X>._, wildcards in cleared atoms, multiplicities k.atom,
value variables with simple linear constraints, environment predicates, and
quantified conjuncts (listed roles).  Unsupported (refused): one(..), sgn(..).
"""
from __future__ import annotations
import re
from dataclasses import dataclass, field

A, D, N, NAT = "A", "D", "N", "Nat"


class Unsupported(Exception):
    pass


@dataclass(frozen=True)
class Arg:
    kind: str            # 'name' (identifier), 'nterm' (<base>.y), 'wild', 'num'
    name: str = ""       # identifier, or base for nterm
    y: str = ""          # speech-act variable of nterm, '_' for wildcard
    val: int = 0

    def __str__(self):
        if self.kind == "name":
            return self.name
        if self.kind == "nterm":
            return f"<{self.name}>.{self.y}"
        if self.kind == "wild":
            return "_"
        return str(self.val)


@dataclass
class Atom:
    pred: str
    args: list            # list[Arg]; args[0] is the holder
    mult: object = 1      # int or variable name

    def __str__(self):
        m = "" if self.mult == 1 else f"{self.mult}."
        return f"{m}{self.pred}({', '.join(map(str, self.args))})"


@dataclass
class Lit:
    neg: bool
    atom: Atom


@dataclass
class Forall:
    var: str
    cond: Atom
    lits: list            # list[Lit]


@dataclass
class Constraint:
    lhs: list             # tokens of a linear expression
    op: str
    rhs: list


@dataclass
class Role:
    name: str
    listed: bool = False
    base: str = ""                 # for a listed role, its base agent role
    cond: Atom | None = None       # rho(base, X, u2, ...)
    req: list = field(default_factory=list)    # =(i)  atoms, holder dropped later
    forb: list = field(default_factory=list)   # not(i)
    add: list = field(default_factory=list)    # +(i)
    dele: list = field(default_factory=list)   # -(i)
    clear: list = field(default_factory=list)  # _(i)


@dataclass
class Schema:
    name: str
    roles: list                    # list[Role]
    guards: list                   # role names
    avars: list = field(default_factory=list)   # agent variables (not roles)
    svars: list = field(default_factory=list)   # speech-act variables
    nvars: list = field(default_factory=list)   # value variables (incl. multiplicities)
    mvars: list = field(default_factory=list)   # multiplicity variables (subset of nvars)
    constraints: list = field(default_factory=list)
    text: str = ""

    def role(self, name):
        for r in self.roles:
            if r.name == name:
                return r
        return None


@dataclass
class Contract:
    name: str
    schemas: list
    sorts: dict          # pred -> list of sorts (position 0 = holder, sort A)
    env_preds: list
    reflexive: list


# ---------------------------------------------------------------- lexing helpers

def split_top(s: str, sep=","):
    out, depth, cur = [], 0, []
    i = 0
    while i < len(s):
        ch = s[i]
        if ch in "([":
            depth += 1
        elif ch in ")]":
            depth -= 1
        if ch == sep and depth == 0:
            out.append("".join(cur).strip())
            cur = []
        else:
            cur.append(ch)
        i += 1
    if "".join(cur).strip():
        out.append("".join(cur).strip())
    return out


ATOM_RE = re.compile(r"^(?:(\w+)\.)?([a-z_][\w]*)\((.*)\)$", re.S)
NT_RE = re.compile(r"^<(\w+)>\.(\w+|_)$")
CMP_RE = re.compile(r"(<=|>=|=|<|>)")


def parse_arg(t: str) -> Arg:
    t = t.strip()
    if t == "_":
        return Arg("wild")
    m = NT_RE.match(t)
    if m:
        return Arg("nterm", m.group(1), m.group(2))
    if t.startswith("one(") or t.startswith("sgn("):
        raise Unsupported(f"argument {t}")
    if re.fullmatch(r"\d+", t):
        return Arg("num", val=int(t))
    if re.fullmatch(r"\w+", t):
        return Arg("name", t)
    raise Unsupported(f"argument {t}")


def parse_atom(t: str) -> Atom:
    t = t.strip()
    m = ATOM_RE.match(t)
    if not m:
        raise Unsupported(f"atom {t}")
    mult, pred, inner = m.group(1), m.group(2), m.group(3)
    args = [parse_arg(a) for a in split_top(inner)] if inner.strip() else []
    if mult is None:
        mv = 1
    elif re.fullmatch(r"\d+", mult):
        mv = int(mult)
    else:
        mv = mult
    return Atom(pred, args, mv)


def parse_lit(t: str):
    t = t.strip()
    if t.startswith("forall "):
        m = re.match(r"^forall\s+(\w+)\s*\((.*)\)$", t, re.S)
        if not m:
            raise Unsupported(f"forall {t}")
        var, inner = m.group(1), m.group(2)
        cond_s, lits_s = inner.split("->", 1)
        cond = parse_atom(cond_s)
        lits = [parse_lit(x) for x in split_top(lits_s)]
        return Forall(var, cond, lits)
    if t.startswith("not "):
        return Lit(True, parse_atom(t[4:]))
    if ATOM_RE.match(t):
        return Lit(False, parse_atom(t))
    m = CMP_RE.search(t)
    if m:
        lhs, op, rhs = t[:m.start()], m.group(1), t[m.end():]
        return Constraint(lhs.split(), op, rhs.split())
    raise Unsupported(f"literal {t}")


# ---------------------------------------------------------------- schema parsing

def parse_schema(name: str, head_s: str, body_s: str) -> Schema:
    guards = []
    m = re.search(r"\bguarded by\b(.*)$", body_s, re.S)
    if m:
        guards = [g.strip() for g in m.group(1).split(",") if g.strip()]
        body_s = body_s[:m.start()]
    head = [parse_lit(x) for x in split_top(head_s)] if head_s.strip() else []
    body = [parse_lit(x) for x in split_top(body_s)] if body_s.strip() else []

    roles: dict[str, Role] = {}
    order = []

    def agent_role(n):
        if n not in roles:
            roles[n] = Role(n)
            order.append(n)
        return roles[n]

    # agent roles: holders of literals outside quantified conjuncts (def:role)
    for lit in body + head:
        if isinstance(lit, Lit):
            h = lit.atom.args[0]
            if h.kind != "name":
                raise Unsupported(f"holder {h}")
            agent_role(h.name)
    listed: dict[str, Role] = {}
    for lit in body + head:
        if isinstance(lit, Forall):
            base = lit.cond.args[0].name
            agent_role(base)
            if lit.var not in listed:
                listed[lit.var + "#L"] = None
    constraints = []

    def strip(a: Atom) -> Atom:
        return a

    for lit in body:
        if isinstance(lit, Constraint):
            constraints.append(lit)
        elif isinstance(lit, Forall):
            key = lit.var + "#L"
            if listed.get(key) is None:
                listed[key] = Role(key, True, lit.cond.args[0].name, lit.cond)
            r = listed[key]
            for l in lit.lits:
                (r.forb if l.neg else r.req).append(l.atom)
        else:
            r = roles[lit.atom.args[0].name]
            (r.forb if lit.neg else r.req).append(lit.atom)
    for lit in head:
        if isinstance(lit, Constraint):
            raise Unsupported("constraint in head")
        if isinstance(lit, Forall):
            key = lit.var + "#L"
            if listed.get(key) is None:
                listed[key] = Role(key, True, lit.cond.args[0].name, lit.cond)
            r = listed[key]
            for l in lit.lits:
                if l.neg:
                    (r.clear if any_wild(l.atom) else r.dele).append(l.atom)
                else:
                    r.add.append(l.atom)
        else:
            r = roles[lit.atom.args[0].name]
            if lit.neg:
                (r.clear if any_wild(lit.atom) else r.dele).append(lit.atom)
            else:
                r.add.append(lit.atom)
    all_roles = [roles[n] for n in order] + [r for r in listed.values() if r is not None]
    return Schema(name, all_roles, guards, constraints=constraints)


def any_wild(a: Atom):
    return any(x.kind == "wild" or (x.kind == "nterm" and x.y == "_") for x in a.args)


def parse_contract(text: str, name: str) -> Contract:
    env, refl = [], []
    lines = text.splitlines()
    chunks, cur = [], []
    for ln in lines:
        if ln.startswith("Environment predicates:"):
            env = [x.strip() for x in ln.split(":", 1)[1].split(",")]
            continue
        if ln.startswith("Reflexive predicates:"):
            refl = [x.strip() for x in ln.split(":", 1)[1].split(",")]
            continue
        if re.match(r"^\w+(\(.*\))?\s*:", ln) and not ln.startswith(" "):
            if cur:
                chunks.append("\n".join(cur))
            cur = [ln]
        elif ln.strip():
            cur.append(ln)
    if cur:
        chunks.append("\n".join(cur))
    schemas = []
    for ch in chunks:
        m = re.match(r"^(\w+):\s*(.*)$", ch, re.S)
        if not m or "<-" not in ch:
            raise Unsupported(f"schema form: {ch.splitlines()[0]}")
        sname, rest = m.group(1), m.group(2)
        head_s, body_s = rest.split("<-", 1)
        s = parse_schema(sname, head_s, body_s)
        s.text = ch.strip()
        schemas.append(s)
    c = Contract(name, schemas, {}, env, refl)
    infer_sorts(c)
    return c


# ---------------------------------------------------------------- sort inference

class UF:
    def __init__(self):
        self.p = {}
        self.sort = {}

    def find(self, x):
        self.p.setdefault(x, x)
        while self.p[x] != x:
            self.p[x] = self.p[self.p[x]]
            x = self.p[x]
        return x

    def union(self, a, b):
        ra, rb = self.find(a), self.find(b)
        if ra == rb:
            return
        sa, sb = self.sort.get(ra), self.sort.get(rb)
        if sa and sb and sa != sb:
            raise Unsupported(f"sort clash {a}:{sa} vs {b}:{sb}")
        self.p[ra] = rb
        if sa and not sb:
            self.sort[rb] = sa

    def set(self, x, s):
        r = self.find(x)
        if self.sort.get(r) and self.sort[r] != s:
            raise Unsupported(f"sort clash {x}: {self.sort[r]} vs {s}")
        self.sort[r] = s

    def get(self, x):
        return self.sort.get(self.find(x))


def schema_atoms(s: Schema):
    for r in s.roles:
        for a in r.req + r.forb + r.add + r.dele + r.clear:
            yield a
        if r.cond is not None:
            yield r.cond


def infer_sorts(c: Contract):
    uf = UF()
    arity = {}
    for s in c.schemas:
        role_names = {r.name for r in s.roles if not r.listed}
        listed_vars = {r.name[:-2] for r in s.roles if r.listed}
        for a in schema_atoms(s):
            if a.pred in arity and arity[a.pred] != len(a.args):
                raise Unsupported(f"arity of {a.pred}")
            arity[a.pred] = len(a.args)
            for i, x in enumerate(a.args):
                pos = ("pos", a.pred, i)
                if i == 0:
                    uf.set(pos, A)
                if x.kind == "name":
                    v = ("var", s.name, x.name)
                    uf.union(v, pos)
                    if x.name in role_names or x.name in listed_vars:
                        uf.set(v, A)
                elif x.kind == "nterm":
                    uf.set(pos, N)
                    uf.set(("var", s.name, x.name), A)
                    if x.y != "_":
                        uf.set(("var", s.name, x.y), D)
                elif x.kind == "num":
                    uf.set(pos, NAT)
            if isinstance(a.mult, str):
                uf.set(("var", s.name, a.mult), NAT)
        for k in s.constraints:
            for tok in k.lhs + k.rhs:
                if re.fullmatch(r"[A-Za-z_]\w*", tok):
                    uf.set(("var", s.name, tok), NAT)
    # environment predicates: non-holder positions default Nat
    for e in c.env_preds:
        for i in range(1, arity.get(e, 1)):
            if uf.get(("pos", e, i)) is None:
                uf.set(("pos", e, i), NAT)
    sorts = {}
    for p, n in arity.items():
        sorts[p] = [uf.get(("pos", p, i)) or D for i in range(n)]
    c.sorts = sorts
    for s in c.schemas:
        role_names = {r.name for r in s.roles if not r.listed}
        listed_vars = {r.name[:-2] for r in s.roles if r.listed}
        seen = []
        for a in schema_atoms(s):
            for x in a.args:
                for nm in ([x.name] if x.kind == "name" else
                           [x.name] + ([x.y] if x.y != "_" else []) if x.kind == "nterm" else []):
                    if nm not in seen:
                        seen.append(nm)
            if isinstance(a.mult, str) and a.mult not in seen:
                seen.append(a.mult)
        for k in s.constraints:
            for tok in k.lhs + k.rhs:
                if re.fullmatch(r"[A-Za-z_]\w*", tok) and tok not in seen:
                    seen.append(tok)
        for nm in seen:
            if nm in role_names or nm in listed_vars:
                continue
            srt = uf.get(("var", s.name, nm)) or D
            if srt == A:
                s.avars.append(nm)
            elif srt == NAT:
                s.nvars.append(nm)
            elif srt == D:
                s.svars.append(nm)
            else:
                raise Unsupported(f"variable {nm} of sort {srt}")
        for a in schema_atoms(s):
            if isinstance(a.mult, str) and a.mult not in s.mvars:
                s.mvars.append(a.mult)
    return c


if __name__ == "__main__":
    import sys
    c = parse_contract(open(sys.argv[1]).read(), sys.argv[2] if len(sys.argv) > 2 else "C")
    print("sorts:", c.sorts, "env:", c.env_preds)
    for s in c.schemas:
        print(s.name, "guards", s.guards, "avars", s.avars, "svars", s.svars, "nvars", s.nvars)
        for r in s.roles:
            print("   ", r.name, "listed" if r.listed else "", "req", [str(a) for a in r.req],
                  "forb", [str(a) for a in r.forb], "add", [str(a) for a in r.add],
                  "del", [str(a) for a in r.dele], "clear", [str(a) for a in r.clear])
