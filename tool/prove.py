"""Discover and prove invariants of a contract, automatically.

  python3 prove.py <schemas.txt> <Name> [outdir]

1. parse the contract and compile it to Lean (leangen) -> <Name>/Model.lean;
2. explore its runs on a tiny universe (sim) and keep the template candidates
   that no run refutes;
3. Houdini loop in Lean: every candidate gets an init theorem and a step theorem
   (Step preserves it, assuming the relevant other candidates); theorems live in
   small modules of a Lake project, built in parallel and cached between rounds;
   failures are dropped and the loop repeats until nothing fails;
4. <Name>/Final.lean imports every module and proves, by induction on runs,
   that every reachable state satisfies every surviving property.

Lean's kernel checks every proof; nothing else is trusted.
"""
from __future__ import annotations
import os
import re
import shutil
import subprocess
import sys
import time

from parse import parse_contract
from leangen import gen_contract
import sim
import cands as C

LAKE = os.path.expanduser("~/.elan/bin/lake")
CHUNK = 3


def contexts(c):
    """pred -> predicates read or changed by the schemas that change it."""
    ctx = {}
    for s in c.schemas:
        changed, read = set(), set()
        for r in s.roles:
            for a in r.add + r.dele + r.clear:
                changed.add(a.pred)
            for a in r.req + r.forb + ([r.cond] if r.cond else []):
                read.add(a.pred)
        for e in changed:
            ctx.setdefault(e, set()).update(read | changed)
    return ctx


def relevant(cd, ctx):
    r = set(cd.preds())
    for e in cd.preds():
        r |= ctx.get(e, set())
    return r


def thm_name(k):
    return f"p{k}"


def init_thm(k, cd, c):
    return f"theorem {thm_name(k)}_init : {C.lean(cd, c, '(init : St A D)')} := by\n  simp [init]\n"


def step_thm(k, cd, hyps, c):
    hs = " ".join(f"(H{j} : {C.lean(h, c, 's')})" for j, h in hyps)
    goal = C.lean(cd, c, "s'")
    return (f"theorem {thm_name(k)}_step (s s' : St A D) {hs} (h : Step s s') :\n    {goal} := by\n"
            f"  cases h <;> grind\n")


class Project:
    def __init__(self, root, ns, c, code):
        self.root, self.ns, self.c = root, ns, c
        os.makedirs(os.path.join(root, ns), exist_ok=True)
        open(os.path.join(root, "lakefile.toml"), "w").write(
            f'name = "{ns}"\ndefaultTargets = ["{ns}"]\n\n[[lean_lib]]\nname = "{ns}"\nglobs = ["{ns}.+"]\n')
        open(os.path.join(root, "lean-toolchain"), "w").write("leanprover/lean4:v4.32.0\n")
        self.write("Model", code + f"end {ns}\n")

    def path(self, mod):
        return os.path.join(self.root, self.ns, mod + ".lean")

    def write(self, mod, text):
        p = self.path(mod)
        if os.path.exists(p) and open(p).read() == text:
            return
        open(p, "w").write(text)

    def build(self):
        t = time.time()
        p = subprocess.run([LAKE, "build"], cwd=self.root, capture_output=True, text=True)
        return p.stdout + p.stderr, time.time() - t


def chunk_text(ns, items, c, alive_idx, ctx):
    """items: list of (k, cand). alive_idx: dict k -> cand of the current round."""
    t = f"import {ns}.Model\nnamespace {ns}\nvariable {{A D : Type}} [DecidableEq A] [DecidableEq D]\n\n"
    spans = []
    for k, cd in items:
        rel = relevant(cd, ctx)
        hyps = [(j, h) for j, h in sorted(alive_idx.items()) if h.preds() <= rel]
        start = t.count("\n") + 1
        t += f"/-- {C.text(cd, c)} -/\n" + init_thm(k, cd, c) + "\n" + step_thm(k, cd, hyps, c) + "\n"
        spans.append((start, t.count("\n") + 1, k, [j for j, _ in hyps]))
    t += f"end {ns}\n"
    return t, spans


def houdini(prj: Project, c, cand_list, log):
    ns = prj.ns
    ctx = contexts(c)
    alive = dict(enumerate(cand_list))          # stable index -> candidate
    nchunks = (len(cand_list) + CHUNK - 1) // CHUNK
    rnd = 0
    while True:
        rnd += 1
        spans_of = {}
        for ch in range(nchunks):
            items = [(k, alive[k]) for k in range(ch * CHUNK, (ch + 1) * CHUNK) if k in alive]
            text, spans = chunk_text(ns, items, c, alive, ctx)
            prj.write(f"C{ch}", text)
            spans_of[f"C{ch}"] = spans
        out, dt = prj.build()
        failed = set()
        for m in re.finditer(rf"error: (?:\./)?{ns}/(C\d+)\.lean:(\d+):\d+", out):
            mod, ln = m.group(1), int(m.group(2))
            for a, b, k, _ in spans_of.get(mod, []):
                if a <= ln < b:
                    failed.add(k)
        log(f"  round {rnd}: {len(alive)} candidates, {len(failed)} not proved ({dt:.1f}s)")
        if not failed:
            if "error" in out:
                raise RuntimeError(out[-3000:])
            return alive, spans_of
        for k in failed:
            log(f"    dropped: {C.text(alive[k], c)}")
            del alive[k]


def final(prj: Project, c, alive, spans_of):
    ns = prj.ns
    mods = sorted(spans_of, key=lambda m: int(m[1:]))
    uses = {k: hs for spans in spans_of.values() for (_, _, k, hs) in spans}
    ks = sorted(alive)
    t = "".join(f"import {ns}.{m}\n" for m in mods)
    t += f"namespace {ns}\nvariable {{A D : Type}} [DecidableEq A] [DecidableEq D]\n\n"
    t += "/-- The properties proved, conjoined. -/\ndef Props (s : St A D) : Prop :=\n  " + \
         " ∧\n  ".join(f"({C.lean(alive[k], c, 's')})" for k in ks) + "\n\n"
    hs = ", ".join(f"h{k}" for k in ks)
    inits = ", ".join(f"{thm_name(k)}_init" for k in ks)
    steps = ", ".join(f"{thm_name(k)}_step _ _ {' '.join(f'h{j}' for j in uses[k])} hs" for k in ks)
    t += ("/-- Every reachable state satisfies every property. -/\n"
          "theorem reach_props {s : St A D} (h : Reach s) : Props s := by\n"
          "  induction h with\n"
          f"  | init => exact ⟨{inits}⟩\n"
          f"  | step _ hs ih =>\n    obtain ⟨{hs}⟩ := ih\n    exact ⟨{steps}⟩\n\n"
          f"end {ns}\n")
    prj.write("Final", t)
    out, dt = prj.build()
    return ("error" not in out), out, dt


def main(path, ns, outdir):
    outdir = os.path.abspath(outdir)
    os.makedirs(outdir, exist_ok=True)
    logf = open(os.path.join(outdir, f"{ns}.log"), "w")

    def log(m):
        print(m, flush=True)
        logf.write(m + "\n")
        logf.flush()

    c = parse_contract(open(path).read(), ns)
    code = gen_contract(c, ns)
    prj = Project(os.path.join(outdir, "proj"), ns, c, code)
    log(f"{ns}: {len(c.schemas)} schemas, {len(c.sorts)} predicates")
    t0 = time.time()
    states = sim.explore(c)
    log(f"  explored {len(states)} states ({time.time() - t0:.1f}s)")
    allc = C.gen(c)
    alive = C.filter_sim(allc, states)
    refuted = [cd for cd in allc if cd not in set(alive)]
    extra = C.filter_sim(C.gen_ne(c, refuted), states)
    alive += extra
    log(f"  {len(allc) + len(extra)} template candidates, {len(alive)} survive simulation")
    props, spans_of = houdini(prj, c, alive, log)
    log(f"  {len(props)} properties proved inductive")
    ok, out, dt = final(prj, c, props, spans_of)
    log(f"  final theorem reach_props: {'OK' if ok else 'FAILED'} ({dt:.1f}s)")
    if not ok:
        log(out[-3000:])
    with open(os.path.join(outdir, f"{ns}_properties.txt"), "w") as f:
        for k in sorted(props):
            f.write(C.text(props[k], c) + "\n")
    return props, ok


if __name__ == "__main__":
    main(sys.argv[1], sys.argv[2], sys.argv[3] if len(sys.argv) > 3 else f"out/{sys.argv[2]}")
