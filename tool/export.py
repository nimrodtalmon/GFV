"""Package a contract's results for the app.

  python3 export.py <GLP cascade dir> <Name> <outdir of prove.py> <glossary.json> <dest dir>

Writes <dest>/<Name>/: schemas.txt, contract.txt, glossary.json, stamps.json,
runs.pkl (simulated runs with parents, for counterexamples), proj/ (the Lean project).
"""
import json
import os
import pickle
import shutil
import sys

from parse import parse_contract
import cands as C
from props import formal, english
from summarize import core
from ask import explore_traced


def main(cascade, name, outdir, gloss_path, dest):
    d = os.path.join(dest, name)
    os.makedirs(d, exist_ok=True)
    src = os.path.join(cascade, name)
    shutil.copy(os.path.join(src, "schemas.txt"), os.path.join(d, "schemas.txt"))
    text = [l for l in open(os.path.join(src, f"{name}.txt")) if not l.startswith("%")]
    open(os.path.join(d, "contract.txt"), "w").write("".join(text))
    shutil.copy(gloss_path, os.path.join(d, "glossary.json"))
    gloss = json.load(open(gloss_path))
    c = parse_contract(open(os.path.join(src, "schemas.txt")).read(), name)
    allc = C.gen(c)
    allc += C.gen_ne(c, [x for x in allc if x.kind == "impl"])
    by_text = {C.text(x, c): x for x in allc}
    props = [by_text[l.strip()] for l in open(os.path.join(outdir, f"{name}_properties.txt")) if l.strip()]
    k = set(core(props))
    stamps = [{"formal": formal(p, c), "english": english(p, c, gloss), "lean": C.lean(p, c, "s"),
               "core": p in k} for p in props]
    json.dump(stamps, open(os.path.join(d, "stamps.json"), "w"), indent=1, ensure_ascii=False)
    proj = os.path.join(d, "proj")
    if os.path.exists(proj):
        shutil.rmtree(proj)
    shutil.copytree(os.path.join(outdir, "proj"), proj,
                    ignore=shutil.ignore_patterns(".lake", "Query_*", "Refute_*"))
    if not os.path.exists(os.path.join(d, "runs.pkl")):
        cache = explore_traced(c)
        pickle.dump(cache, open(os.path.join(d, "runs.pkl"), "wb"))
    print(name, len(props), "stamps,", len(k), "core")


if __name__ == "__main__":
    main(*sys.argv[1:6])
