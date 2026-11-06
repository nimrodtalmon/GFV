"""Non-vacuity: a concrete run (3 persons, 2 speech acts) in which every schema fires,
emitted as a Lean term whose provisos are discharged by `decide`."""
import sys
from parse import parse_contract
from leangen import gen_contract
import sim
from ask import successors_labeled, run_term


def find_run(c):
    names = {s.name for s in c.schemas}
    used, st, path, cache = set(), sim.State(), [], {"states": []}
    while not names <= used:
        par = {st.key(): None}
        q, found = [st], None
        while q and found is None:
            cur = q.pop(0)
            for lab, n in successors_labeled(c, cur):
                if lab[0] in names and lab[0] not in used:
                    found = (cur, lab, n)
                    break
                if n.key() not in par:
                    par[n.key()] = (cur, lab, n)
                    q.append(n)
        if found is None:
            return path, cache, sorted(names - used)
        cur, lab, n = found
        seg, k = [], cur
        while par[k.key()] is not None:
            pc, pl, pn = par[k.key()]
            seg.append((pl, pn)); k = pc
        for pl, pn in list(reversed(seg)) + [(lab, n)]:
            cache["states"].append(pn.m)
            path.append((len(cache["states"]) - 1, pl))
            used.add(pl[0])
        st = n
    return path, cache, []


if __name__ == "__main__":
    c = parse_contract(open(sys.argv[1]).read(), sys.argv[2])
    code = gen_contract(c, sys.argv[2])
    path, cache, missing = find_run(c)
    term = run_term(c, cache, path)
    print(code + "/-- A run in which every schema fires: the Step relation is not vacuous. -/\n"
          f"theorem nonvacuous : ∃ s : St (Fin 3) (Fin 2), Reach s :=\n  ⟨_, {term}⟩\n" + f"end {sys.argv[2]}\n")
    print(f"-- {sys.argv[2]}: schemas fired {len({l[0] for _, l in path} & {s.name for s in c.schemas})}/{len(c.schemas)}; "
          f"never: {missing}; steps: {len(path)}", file=sys.stderr)
