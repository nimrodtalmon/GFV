# GCV: Grassroots Contracts Verifier

GCV attaches to each grassroots app (a contract of the GLP cascade, github.com/EShapiro2/GLP)
a list of properties that hold in every reachable state, each proved by Lean 4, and answers
questions about further properties: proved, false (with a concrete run that Lean checks),
or not decided. Only Lean is trusted for the proofs; no external solvers (Lean's `grind`).

Live: https://talmonlab.bgu.ac.il/gcv/

## Layout

- `tool/` (Python, standard library):
  - `parse.py`: the speech-act schemas (`schemas.txt` of the cascade)
  - `leangen.py`: schemas to a Lean transition system (`St`, `Step`, `Reach`)
  - `sim.py`, `cands.py`: candidate properties, filtered on simulated runs
  - `prove.py`: Houdini loop in Lean (Lake project, parallel and cached), final theorem `reach_props`
  - `summarize.py`: the core of the proved set
  - `props.py`: the property language (one line) and its English rendering via a glossary
  - `ask.py`: answering a question (Lean proof, or Lean-checked counterexample run)
  - `export.py`: package a contract for the app; `witness.py`: non-vacuity run
- `glossary/`: per-contract phrases for the facts
- `app/`: the web app (`server.py`, `index.html`, `contracts/<C>/`), Python standard library only;
  on first start it downloads Lean 4.32 (Windows) into `DATA` and checks every contract's Lean project
- `results/`: Lean projects and property lists; `results/nonvacuity/`: runs in which every schema fires
- `generic/`: an earlier experiment, theorems proved once for all contracts (agent-role fragment)

## Usage (Lean 4.32 via elan)

    cd tool
    python3 prove.py <GLP>/cascade/GSG/schemas.txt GSG ../out/GSG
    python3 export.py <GLP>/cascade GSG ../out/GSG ../glossary/GSG.json ../app/contracts
    cd ../app && python3 server.py 4901
