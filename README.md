# GFV: Grassroots Formal Verification

Verified properties for grassroots apps: speech-act schemas of a grassroots contract
(the `schemas.txt` of the GLP cascade, github.com/EShapiro2/GLP) are compiled to Lean 4,
and properties of the contract are discovered and proved automatically. Only Lean's
kernel is trusted; no external solvers (Lean's built-in `grind`).

- `tool/` — Python: `parse.py` (schemas), `leangen.py` (schemas → Lean transition system),
  `sim.py` + `cands.py` (candidate properties, filtered on simulated runs),
  `prove.py` (Houdini loop in Lean, final theorem `reach_props`),
  `summarize.py` (core of the proved set), `witness.py` (non-vacuity run),
  `emitA.py` (contracts as Lean data for `generic/`).
- `generic/` — Lean: schemas as data; theorems proved once for all contracts
  (traceable provenance ⇒ records within instances; + volition ⇒ closure) and stamps by `decide`.
- `results/` — generated Lean projects and property lists for GSG, GSN, GB, GC, GDO.

Usage (Lean 4.32 via elan):

    cd tool && python3 prove.py <GLP>/cascade/GSG/schemas.txt GSG ../out/GSG
    python3 summarize.py <GLP>/cascade/GSG/schemas.txt GSG ../out/GSG/GSG_properties.txt
