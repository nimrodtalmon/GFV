"""Compile a parsed contract (parse.py IR) to a Lean 4 transition system.

State: one function per predicate, holder first, returning a multiplicity (Nat).
Step: one constructor per schema, quantified over its binding, carrying the
schema's provisos (def:compile), and an environment step per environment predicate.

Faithfulness notes.  Provisos encoded: distinct agent roles, required/forbidden
atoms per role (listed roles over their extent), the disjointness of what is added
and what is deleted or cleared at an agent, freshness of name terms in no required
atom, value constraints, multiplicities >= 1.  Not encoded (each omission only
adds transitions, so every invariant proved remains a theorem of the real
protocol): admissibility of bindings (signers of speech acts), possibly-one roles,
the people's will (guards are recorded in the constructor's docstring only).
"""
from __future__ import annotations
from collections import Counter, OrderedDict
import re
from parse import A, D, N, NAT, Contract, Schema, Role, Atom, Arg

LEAN_T = {A: "A", D: "D", N: "(A × D)", NAT: "Nat"}
HYPCOUNT = {}


def lid(name: str, role_names) -> str:
    return ("r_" if name in role_names else "v_") + name


class Ctx:
    """Translation of schema arguments to Lean terms."""

    def __init__(self, s: Schema, listed_map=None):
        self.s = s
        self.agent_roles = [r.name for r in s.roles if not r.listed]
        self.listed_map = listed_map or {}   # listed variable -> Lean term

    def term(self, x: Arg) -> str:
        if x.kind == "name":
            if x.name in self.listed_map:
                return self.listed_map[x.name]
            return lid(x.name, self.agent_roles)
        if x.kind == "nterm":
            b = self.listed_map.get(x.name, lid(x.name, self.agent_roles))
            return f"({b}, {lid(x.y, self.agent_roles)})"
        if x.kind == "num":
            return str(x.val)
        raise ValueError(x)

    def mult(self, a: Atom) -> str:
        return str(a.mult) if isinstance(a.mult, int) else lid(a.mult, self.agent_roles)


def listed_var(r: Role) -> str:
    return r.name[:-2]


def role_ctx(s: Schema, r: Role, who: str) -> Ctx:
    """Context for atoms held at role r, with the listed variable mapped to `who`."""
    return Ctx(s, {listed_var(r): who} if r.listed else {})


def membership(s: Schema, r: Role, p: str) -> str:
    """Lean proposition: agent p is in the extent of role r."""
    c0 = Ctx(s)
    if not r.listed:
        return f"{p} = {c0.term(Arg('name', r.name))}"
    cond = r.cond
    cx = Ctx(s, {listed_var(r): p})
    args = " ".join(cx.term(x) for x in cond.args)
    return f"s.{cond.pred} {args} > 0"


def match_cond(params, a: Atom, cx: Ctx) -> list[str]:
    """Conditions equating the state function's argument params with a's non-holder args."""
    out = []
    for prm, x in zip(params, a.args[1:]):
        if x.kind == "wild":
            continue
        if x.kind == "nterm" and x.y == "_":
            b = cx.listed_map.get(x.name, lid(x.name, cx.agent_roles))
            out.append(f"{prm}.1 = {b}")
            continue
        out.append(f"{prm} = {cx.term(x)}")
    return out


def conj(xs):
    xs = [x for x in xs if x]
    return " ∧ ".join(f"({x})" if " " in x else x for x in xs) if xs else "True"


def gen_contract(c: Contract, ns: str) -> str:
    L = []
    preds = list(c.sorts.keys())
    L.append(f"namespace {ns}")
    L.append("")
    L.append("structure St (A D : Type) where")
    for e in preds:
        ty = " → ".join(LEAN_T[t] for t in c.sorts[e]) + " → Nat"
        L.append(f"  {e} : {ty}")
    L.append("")
    L.append("variable {A D : Type} [DecidableEq A] [DecidableEq D]")
    L.append("")
    zeros = ", ".join("fun " + " ".join("_" for _ in c.sorts[e]) + " => 0" for e in preds)
    L.append(f"def init : St A D := ⟨{zeros}⟩")
    L.append("")
    L.append("inductive Step : St A D → St A D → Prop")
    for s in c.schemas:
        L.extend(gen_schema(c, s))
    for e in c.env_preds:
        ty = " → ".join(LEAN_T[t] for t in c.sorts[e]) + " → Nat"
        L.append(f"  /-- environment: the platform keeps `{e}` current (any update) -/")
        L.append(f"  | env_{e} (s : St A D) (f : {ty}) : Step s {{ s with {e} := f }}")
    L.append("")
    L.append("inductive Reach : St A D → Prop")
    L.append("  | init : Reach init")
    L.append("  | step {s s' : St A D} : Reach s → Step s s' → Reach s'")
    L.append("")
    return "\n".join(L)


def gen_schema(c: Contract, s: Schema) -> list[str]:
    agent_roles = [r for r in s.roles if not r.listed]
    listed_roles = [r for r in s.roles if r.listed]
    c0 = Ctx(s)
    binders = []
    for r in agent_roles:
        binders.append(f"({lid(r.name, c0.agent_roles)} : A)")
    for v in s.avars:
        binders.append(f"({lid(v, c0.agent_roles)} : A)")
    for v in s.svars:
        binders.append(f"({lid(v, c0.agent_roles)} : D)")
    for v in s.nvars:
        binders.append(f"({lid(v, c0.agent_roles)} : Nat)")
    hyps = []
    # distinct agent roles (def:binding)
    for i in range(len(agent_roles)):
        for j in range(i + 1, len(agent_roles)):
            hyps.append(f"{lid(agent_roles[i].name, c0.agent_roles)} ≠ {lid(agent_roles[j].name, c0.agent_roles)}")
    for v in s.mvars:
        hyps.append(f"{lid(v, c0.agent_roles)} ≥ 1")
    for k in s.constraints:
        hyps.append(constraint_lean(k, c0))
    # required / forbidden at each role
    for r in s.roles:
        who = "q" if r.listed else lid(r.name, c0.agent_roles)
        cx = role_ctx(s, r, who)
        req = OrderedDict()
        for a in r.req:
            key = (a.pred, tuple(cx.term(x) for x in a.args[1:]))
            req.setdefault(key, []).append(cx.mult(a))
        conds = []
        for (pred, args), ms in req.items():
            m = " + ".join(ms) if len(ms) > 1 else ms[0]
            conds.append(f"s.{pred} {who} {' '.join(args)} ≥ {m}".replace("  ", " "))
        for a in r.forb:
            args = " ".join(cx.term(x) for x in a.args[1:])
            conds.append(f"s.{a.pred} {who} {args} = 0".replace("  ", " "))
        if r.listed:
            for cnd in conds:
                hyps.append(f"∀ q : A, {membership(s, r, 'q')} → {cnd}")
        else:
            hyps.extend(conds)
    # disjointness of added and deleted/cleared at an agent (def:compile)
    for ri in s.roles:
        for a in ri.add:
            for rj in s.roles:
                if ri is not rj and not ri.listed and not rj.listed:
                    continue
                for b in rj.dele + rj.clear:
                    if b.pred != a.pred:
                        continue
                    p = "p"
                    cxi, cxj = role_ctx(s, ri, p), role_ctx(s, rj, p)
                    eqs = []
                    for xa, xb in zip(a.args[1:], b.args[1:]):
                        if xb.kind == "wild":
                            continue
                        if xb.kind == "nterm" and xb.y == "_":
                            ta = cxi.term(xa)
                            bb = cxj.listed_map.get(xb.name, lid(xb.name, cxj.agent_roles))
                            eqs.append(f"({ta}).1 = {bb}")
                            continue
                        eqs.append(f"{cxi.term(xa)} = {cxj.term(xb)}")
                    body = f"¬ ({conj(eqs)})"
                    mi, mj = membership(s, ri, p), membership(s, rj, p)
                    hyps.append(f"∀ p : A, {mi} → {mj} → {body}")
    # freshness of name terms in no required atom
    req_nterms = set()
    for r in s.roles:
        for a in r.req + ([r.cond] if r.cond else []):
            for x in a.args:
                if x.kind == "nterm":
                    req_nterms.add((x.name, x.y))
    all_nterms = set()
    for r in s.roles:
        for a in r.add + r.dele + r.forb:
            for x in a.args:
                if x.kind == "nterm" and x.y != "_":
                    all_nterms.add((x.name, x.y))
    for (b, y) in sorted(all_nterms - req_nterms):
        nt = f"({c0.term(Arg('name', b))}, {lid(y, c0.agent_roles)})"
        for e, srt in c.sorts.items():
            for j, t in enumerate(srt):
                if t == N and j > 0:
                    vs = [f"z{i}" for i in range(len(srt))]
                    vs[j] = nt
                    qs = " ".join(f"(z{i} : {LEAN_T[srt[i]]})" for i in range(len(srt)) if i != j)
                    hyps.append(f"∀ {qs}, s.{e} {' '.join(vs)} = 0")
    # post-state
    changed = OrderedDict()
    for r in s.roles:
        for kind, lst in (("add", r.add), ("del", r.dele), ("clr", r.clear)):
            for a in lst:
                changed.setdefault(a.pred, []).append((kind, r, a))
    any_listed = bool(listed_roles)
    fields = []
    for e, items in changed.items():
        srt = c.sorts[e]
        params = [f"x{i}" for i in range(1, len(srt))]
        p = "p"

        def part(kind):
            per_role = []
            for r in s.roles:
                terms = []
                for k, rr, a in items:
                    if k != kind or rr is not r:
                        continue
                    cx = role_ctx(s, r, p)
                    cond = [membership(s, r, p)] + match_cond(params, a, cx)
                    if kind == "clr":
                        terms.append(conj(cond))
                    else:
                        terms.append(f"(if {conj(cond)} then {cx.mult(a)} else 0)")
                if terms:
                    per_role.append(terms)
            return per_role

        adds, dels, clrs = part("add"), part("del"), part("clr")

        def combine(per_role):
            if not per_role:
                return None
            sums = [" + ".join(t) if len(t) == 1 else "(" + " + ".join(t) + ")" for t in per_role]
            if len(sums) == 1 or not any_listed:
                return " + ".join(sums)
            acc = sums[0]
            for x in sums[1:]:
                acc = f"(max {acc} {x})"
            return acc

        old = f"s.{e} {p} {' '.join(params)}".rstrip()
        cur = old
        dl = combine(dels)
        if dl:
            cur = f"({cur} - ({dl}))"
        if clrs:
            cc = " ∨ ".join(f"({t})" for pr in clrs for t in pr)
            cur = f"(if {cc} then 0 else {cur})"
        ad = combine(adds)
        if ad:
            cur = f"{cur} + ({ad})"
        fields.append(f"{e} := fun {p} {' '.join(params)} => {cur}".replace("  ", " "))
    guards = ", ".join(s.guards) if s.guards else "none (unguarded: taken by liveness)"
    out = [f"  /-- {s.name}; guarded by {guards} -/"]
    hyp_binders = [f"(h{i} : {h})" for i, h in enumerate(hyps)]
    HYPCOUNT[s.name] = len(hyps)
    post = "{ s with " + ", ".join(fields) + " }" if fields else "s"
    out.append(f"  | {s.name} (s : St A D) " + " ".join(binders + hyp_binders) + f" :\n      Step s {post}")
    return out


def constraint_lean(k, c0: Ctx) -> str:
    def toks(ts):
        out = []
        for t in ts:
            if re.fullmatch(r"[A-Za-z_]\w*", t):
                out.append(lid(t, c0.agent_roles))
            else:
                out.append(t)
        return " ".join(out)
    op = {"=": "=", "<=": "≤", ">=": "≥", "<": "<", ">": ">"}[k.op]
    return f"{toks(k.lhs)} {op} {toks(k.rhs)}"


if __name__ == "__main__":
    import sys
    from parse import parse_contract
    c = parse_contract(open(sys.argv[1]).read(), sys.argv[2])
    print(gen_contract(c, sys.argv[2]))
    print(f"end {sys.argv[2]}")
