"""Emit a contract (agent-role fragment) as GSCA.Contract data for route A."""
from parse import parse_contract, Unsupported


def term(x, s, roles):
    if x.kind != "name":
        raise Unsupported(f"route A fragment: argument {x}")
    if x.name in roles:
        return f".role {roles.index(x.name)}"
    if x.name in s.avars:
        return f".avar {s.avars.index(x.name)}"
    if x.name in s.svars:
        return f".svar {s.svars.index(x.name)}"
    raise Unsupported(f"route A fragment: variable {x.name}")


def atoms(lst, s, roles):
    out = []
    for a in lst:
        args = ", ".join(term(x, s, roles) for x in a.args[1:])
        out.append(f'⟨"{a.pred}", [{args}]⟩')
    return "[" + ", ".join(out) + "]"


def emit(c, name):
    L = []
    for s in c.schemas:
        if any(r.listed for r in s.roles):  # multiplicities name no agent: dropped
            raise Unsupported(f"route A fragment: schema {s.name}")
        roles = [r.name for r in s.roles]
        rs = []
        for r in s.roles:
            rs.append(f"{{ req := {atoms(r.req + r.dele, s, roles)}, forb := {atoms(r.forb, s, roles)}, "
                      f"add := {atoms(r.add, s, roles)}, del := {atoms(r.dele, s, roles)} }}")
        guards = [roles.index(g) for g in s.guards]
        L.append(f'  {{ name := "{s.name}", guards := {guards},\n    roles := [{", ".join(rs)}] }}')
    return f"def {name} : Contract := [\n" + ",\n".join(L) + "]\n"


if __name__ == "__main__":
    import sys
    c = parse_contract(open(sys.argv[1]).read(), sys.argv[2])
    print(emit(c, sys.argv[2].lower()))


def role_graph(s):
    roles = [r.name for r in s.roles]
    n = len(roles)
    adj = {i: set() for i in range(n)}
    for i, r in enumerate(s.roles):
        for a in r.req + r.dele:
            for x in a.args[1:]:
                if x.kind == "name" and x.name in roles:
                    j = roles.index(x.name)
                    adj[i].add(j); adj[j].add(i)
    return adj


def bfs_path(adj, i, j):
    prev, seen, q = {i: None}, {i}, [i]
    while q:
        u = q.pop(0)
        if u == j:
            path = []
            while u != i:
                path.append(u); u = prev[u]
            return list(reversed(path))
        for v in sorted(adj[u]):
            if v not in seen:
                seen.add(v); prev[v] = u; q.append(v)
    return None


def cert(s):
    roles = [r.name for r in s.roles]
    adj = role_graph(s)
    n = len(roles)
    ps = [bfs_path(adj, 0, i) for i in range(n)]
    if all(p is not None for p in ps):
        return ".connected [" + ", ".join("[" + ", ".join(map(str, p)) + "]" for p in ps) + "]"
    guards = [roles.index(g) for g in s.guards]
    out = []
    for i in range(n):
        best = None
        for g in guards:
            p = bfs_path(adj, i, g)
            if p is not None and (best is None or len(p) < len(best[1])):
                best = (g, p)
        if best is None:
            return None
        out.append(f"({best[0]}, [{', '.join(map(str, best[1]))}])")
    return ".guarded [" + ", ".join(out) + "]"


def emit_certified(c, name):
    full = emit(c, name + "_schemas")
    body = full.split(":= [\n",1)[1].rsplit("]",1)[0]
    items = [x.strip().rstrip(",") for x in body.split("\n  { name")]
    items = [("{ name" + x if not x.startswith("{") else x) for x in items]
    base = "".join(f"def {name}_s{i} : Schema :=\n  {it}\n" for i, it in enumerate(items))
    certs = []
    for s in c.schemas:
        k = cert(s)
        if k is None:
            return base + f"-- {name}: schema {s.name} has no volition certificate\n", False
        certs.append(k)
    n = len(c.schemas)
    pairs = ", ".join(f"({name}_s{i}, {k})" for i, k in enumerate(certs))
    return base + f"def {name}_certified : List (Schema × VolCert) := [{pairs}]\n", True
