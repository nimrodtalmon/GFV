"""Ask for a property of a contract; get a Lean-checked answer.

  proved   - Lean proves it holds in every reachable state (assuming the stamps,
             which Lean already proved);
  refuted  - a concrete run (three persons) ends in a state where it fails, and
             Lean checks both the run and the failure;
  unknown  - no counterexample among the simulated runs, and no proof found.
"""
from __future__ import annotations
import json
import os
import pickle
import random
import subprocess
import time
from collections import Counter

from parse import parse_contract, A, D, N, NAT
from leangen import gen_contract, HYPCOUNT, LEAN_T
import sim
import cands as C
from props import parse_prop, formal, english, PropError, var_names
from prove import contexts, relevant


# ------------------------------------------------------------ explored runs, with parents

def explore_traced(c, max_states=4000, walks=150, walk_len=30, seed=0):
    """Like sim.explore, but remembers how each state was reached."""
    rng = random.Random(seed)
    init = sim.State()
    states, parent, step = [init], [-1], [None]
    index = {init.key(): 0}

    def add(st, par, lab):
        k = st.key()
        if k in index:
            return index[k], False
        index[k] = len(states)
        states.append(st)
        parent.append(par)
        step.append(lab)
        return index[k], True

    frontier = [0]
    while frontier and len(states) < max_states:
        nxt = []
        for i in frontier:
            for lab, n in successors_labeled(c, states[i]):
                j, new = add(n, i, lab)
                if new:
                    nxt.append(j)
                if len(states) >= max_states:
                    break
            if len(states) >= max_states:
                break
        frontier = nxt
    for _ in range(walks):
        i = 0
        for _ in range(walk_len):
            succ = list(successors_labeled(c, states[i]))
            if not succ:
                break
            lab, n = rng.choice(succ)
            i, _ = add(n, i, lab)
    return {"states": [s.m for s in states], "parent": parent, "step": step}


def successors_labeled(c, st):
    for s in c.schemas:
        for b in sim.bindings(c, s):
            n = sim.fire(c, s, st, b)
            if n is not None:
                yield (s.name, dict(b)), n
    for e in c.env_preds:
        for p in sim.AGENTS:
            for d in sim.NATS:
                n = st.copy()
                cnt = n.m.setdefault(e, Counter())
                for t in list(cnt):
                    if t[0] == p:
                        cnt[t] = 0
                cnt[(p, d)] = 1
                yield (f"env_{e}", {"p": p, "d": d}), n


def path_to(cache, i):
    out = []
    while cache["parent"][i] != -1:
        out.append((i, cache["step"][i]))
        i = cache["parent"][i]
    return list(reversed(out))


def violation(cd, m):
    """A tuple of argument values at which property cd fails in state m, or None."""
    c1 = m.get(cd.e1, {})
    for t, n in c1.items():
        if n <= 0:
            continue
        if cd.kind == "empty":
            return t
        if cd.kind == "bound":
            if n > 1:
                return t
            continue
        if cd.kind in ("eq", "neq"):
            a, b = C.src_val(t, cd.m[0]), C.src_val(t, cd.m[1])
            if (a == b) != (cd.kind == "eq"):
                return t
            continue
        if cd.ne and C.src_val(t, cd.ne[0]) == C.src_val(t, cd.ne[1]):
            continue
        tgt = tuple(C.src_val(t, s) for s in cd.m)
        has = m.get(cd.e2, {}).get(tgt, 0) > 0
        if has != (cd.kind == "impl"):
            return t
    return None


# ------------------------------------------------------------ Lean terms

def lean_val(v, srt):
    if srt == A:
        return f"({v} : Fin 3)"
    if srt == D:
        return f"({int(str(v)[1:])} : Fin 2)"
    if srt == N:
        return f"(({v[0]} : Fin 3), ({int(str(v[1])[1:])} : Fin 2))"
    return str(v)


def env_fun(c, e, m):
    srt = c.sorts[e]
    xs = [f"z{i}" for i in range(len(srt))]
    body = "0"
    for t, n in sorted(m.get(e, {}).items(), key=str):
        if n > 0:
            cond = " ∧ ".join(f"{x} = {lean_val(v, s)}" for x, v, s in zip(xs, t, srt))
            body = f"(if {cond} then {n} else {body})"
    return f"(fun {' '.join(xs)} => {body})"


def run_term(c, cache, path):
    term = "Reach.init"
    for i, (name, b) in path:
        if name.startswith("env_"):
            e = name[4:]
            term = f"(Reach.step {term} (Step.{name} _ {env_fun(c, e, cache['states'][i])}))"
            continue
        s = next(x for x in c.schemas if x.name == name)
        args = [b[r.name] for r in s.roles if not r.listed] + [b[v] for v in s.avars] + \
               [int(str(b[v])[1:]) for v in s.svars] + [b[v] for v in s.nvars]
        hyps = " ".join(["(by decide)"] * HYPCOUNT[name])
        term = f"(Reach.step {term} (Step.{name} _ {' '.join(map(str, args))} {hyps}))"
    return term


# ------------------------------------------------------------ the engine

class Engine:
    def __init__(self, cdir, name, lake="lake", lean_env=None):
        self.dir, self.name, self.lake = cdir, name, lake
        self.c = parse_contract(open(os.path.join(cdir, "schemas.txt"), encoding="utf-8").read(), name)
        self.model = gen_contract(self.c, name)          # fills HYPCOUNT
        self.gloss = json.load(open(os.path.join(cdir, "glossary.json"), encoding="utf-8"))
        self.stamps = json.load(open(os.path.join(cdir, "stamps.json"), encoding="utf-8"))
        self.props = [parse_prop(s["formal"], self.c) for s in self.stamps]
        self.proj = os.path.join(cdir, "proj")
        self.cache = None
        self.lean_env = lean_env

    def load_cache(self):
        if self.cache is None:
            self.cache = pickle.load(open(os.path.join(self.dir, "runs.pkl"), "rb"))
        return self.cache

    def render(self, line):
        cd = parse_prop(line, self.c)
        return cd, formal(cd, self.c), english(cd, self.c, self.gloss)

    def lean_run(self, fname, text, timeout=1800):
        path = os.path.join(self.proj, fname)
        open(path, "w", encoding="utf-8").write(text)
        t = time.time()
        try:
            p = subprocess.run([self.lake, "env", "lean", fname], cwd=self.proj, capture_output=True,
                               text=True, encoding="utf-8", errors="replace", timeout=timeout, env=self.lean_env)
            out, ok = p.stdout + p.stderr, p.returncode == 0 and "error" not in (p.stdout + p.stderr)
        except subprocess.TimeoutExpired:
            out, ok = "timeout", False
        return ok, out, time.time() - t

    def ask(self, line, jid="q"):
        try:
            cd, fl, en = self.render(line)
        except PropError as e:
            return {"verdict": "invalid", "message": str(e)}
        res = {"formal": fl, "english": en, "lean_statement": C.lean(cd, self.c, "s")}
        if cd in self.props:
            k = self.props.index(cd)
            return {**res, "verdict": "proved", "message": "Already a stamp of this contract.",
                    "stamp": k}
        cache = self.load_cache()
        for i, m in enumerate(cache["states"]):
            t = violation(cd, m)
            if t is not None:
                return {**res, **self.refute(cd, cache, i, t, jid)}
        return {**res, **self.prove(cd, jid)}

    def refute(self, cd, cache, i, t, jid):
        path = path_to(cache, i)
        srt = self.c.sorts[cd.e1]
        q = C.lean(cd, self.c, "s")
        insts = " ".join(lean_val(v, s) for v, s in zip(t, srt))
        ns = self.name
        text = (f"import {ns}.Model\nnamespace {ns}\n\n"
                f"def Q {{A D : Type}} [DecidableEq A] [DecidableEq D] (s : St A D) : Prop :=\n  {q}\n\n"
                f"/-- A run of the contract, three persons, ending where the property fails. -/\n"
                f"theorem refuted : ¬ (∀ s : St (Fin 3) (Fin 2), Reach s → Q s) := by\n"
                f"  intro h\n  have hq := h _ {run_term(self.c, cache, path)}\n"
                f"  unfold Q at hq\n  exact absurd (hq {insts}) (by decide)\n\nend {ns}\n")
        ok, out, dt = self.lean_run(f"Refute_{jid}.lean", text)
        run = [self.step_text(name, b) for _, (name, b) in path]
        names = ["Ann", "Ben", "Cat"]
        at = ", ".join(self.val_text(v, s) for v, s in zip(t, srt))
        if ok:
            return {"verdict": "refuted", "run": run, "at": f"{cd.e1}({at})",
                    "lean": text, "seconds": round(dt, 1),
                    "message": "A run where it fails; Lean checked the run and the failure."}
        return {"verdict": "unknown", "message": "A simulated run seemed to refute it, but Lean did "
                "not confirm the run; no claim is made.", "lean": text, "log": out[-2000:]}

    def prove(self, cd, jid):
        ns = self.name
        ctx = contexts(self.c)
        rel = relevant(cd, ctx)
        q = lambda st: C.lean(cd, self.c, st)
        uses = [j for j, h in enumerate(self.props) if h.preds() <= rel]
        hs = " ".join(f"(H{j} : {C.lean(self.props[j], self.c, 's')})" for j in uses)
        n = len(self.props)
        pat = "⟨" + ", ".join(f"h{j}" for j in range(n)) + "⟩"
        text = (f"import {ns}.Final\nnamespace {ns}\nvariable {{A D : Type}} [DecidableEq A] [DecidableEq D]\n\n"
                f"theorem q_init : {q('(init : St A D)')} := by\n  simp [init]\n\n"
                f"theorem q_step (s s' : St A D) {hs} (HQ : {q('s')}) (h : Step s s') :\n    {q(chr(115) + chr(39))} := by\n"
                f"  cases h <;> grind\n\n"
                f"/-- Every reachable state satisfies the property. -/\n"
                f"theorem q_reach {{s : St A D}} (h : Reach s) : {q('s')} := by\n"
                f"  induction h with\n  | init => exact q_init\n  | step hr hs ih =>\n"
                f"    obtain {pat} := reach_props hr\n"
                f"    exact q_step _ _ {' '.join(f'h{j}' for j in uses)} ih hs\n\nend {ns}\n")
        if n == 1:
            text = text.replace(f"obtain {pat} := reach_props hr", "have h0 := reach_props hr")
        ok, out, dt = self.lean_run(f"Query_{jid}.lean", text)
        if ok:
            return {"verdict": "proved", "lean": text, "seconds": round(dt, 1),
                    "message": "Lean proved it holds in every reachable state."}
        return {"verdict": "unknown", "lean": text, "seconds": round(dt, 1), "log": out[-2000:],
                "message": "No counterexample in the simulated runs, and Lean found no proof "
                           "from the stamps. It may hold or not; no claim is made."}

    def val_text(self, v, s):
        names = ["Ann", "Ben", "Cat"]
        if s == A:
            return names[v]
        if s == D:
            return str(v)
        if s == N:
            return f"{names[v[0]]}'s {v[1]}"
        return str(v)

    def step_text(self, name, b):
        names = ["Ann", "Ben", "Cat"]
        if name.startswith("env_"):
            return f"{names[b['p']]}'s calendar moves to {b['d']}"
        s = next(x for x in self.c.schemas if x.name == name)
        parts = []
        for r in s.roles:
            if not r.listed:
                parts.append(f"{r.name}={names[b[r.name]]}")
        for v in s.avars:
            parts.append(f"{v}={names[b[v]]}")
        for v in s.svars + s.nvars:
            parts.append(f"{v}={b[v]}")
        return f"{name}({', '.join(parts)})"
