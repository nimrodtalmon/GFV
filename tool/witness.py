"""Non-vacuity: a concrete run (3 agents, 2 speech acts) in which every schema fires,
emitted as a Lean term whose provisos are discharged by `decide`."""
import sys
from parse import parse_contract
from leangen import gen_contract, HYPCOUNT
import sim


def find_run(c):
    used, path, st = set(), [], sim.State()
    names = [s.name for s in c.schemas]
    while len(used) < len(names):
        par = {st.key(): None}
        q, found = [st], None
        while q and found is None:
            cur = q.pop(0)
            for s in c.schemas:
                for b in sim.bindings(c, s):
                    n = sim.fire(c, s, cur, b)
                    if n is None:
                        continue
                    if s.name not in used:
                        found = (cur, s, b, n)
                        break
                    if n.key() not in par:
                        par[n.key()] = (cur, s, b)
                        q.append(n)
                if found:
                    break
        if found is None:
            return path, sorted(set(names) - used)
        cur, s, b, n = found
        seg, k = [], cur
        while par[k.key()] is not None:
            pc, ps, pb = par[k.key()]
            seg.append((ps, pb)); k = pc
        path += list(reversed(seg)) + [(s, b)]
        used |= {x[0].name for x in seg} | {s.name}
        st = n
    return path, []


def val(v):
    if isinstance(v, str):
        return v[1:]          # d0 -> 0
    return str(v)


def emit(c, ns, path):
    term = "Reach.init"
    for s, b in path:
        args = [val(b[r.name]) for r in s.roles if not r.listed] + [val(b[v]) for v in s.avars] + \
               [val(b[v]) for v in s.svars] + [val(b[v]) for v in s.nvars]
        hyps = " ".join(["(by decide)"] * HYPCOUNT[s.name])
        term = f"(Reach.step {term} (Step.{s.name} _ {' '.join(args)} {hyps}))"
    return (f"/-- A run in which every schema fires: the Step relation is not vacuous. -/\n"
            f"theorem nonvacuous : ∃ s : St (Fin 3) (Fin 2), Reach s :=\n  ⟨_, {term}⟩\n")


if __name__ == "__main__":
    c = parse_contract(open(sys.argv[1]).read(), sys.argv[2])
    code = gen_contract(c, sys.argv[2])
    path, missing = find_run(c)
    print(code + emit(c, sys.argv[2], path) + f"end {sys.argv[2]}\n")
    print(f"-- schemas fired: {len({s.name for s, _ in path})}/{len(c.schemas)}; never enabled: {missing}; steps: {len(path)}", file=sys.stderr)
