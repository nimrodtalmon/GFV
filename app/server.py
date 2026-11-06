"""GCV (Grassroots Contracts Verifier) web app: grassroots contracts with their Lean-verified properties, and a box to ask for more.

Python standard library only.  Usage:  python server.py [port]
Env: DATA (writable folder; default ./data), LEAN_HOME (a Lean 4.32 toolchain; if absent,
the app downloads the official release into DATA), BASE (unused: links are relative).
"""
from __future__ import annotations
import json
import os
import queue
import shutil
import subprocess
import sys
import threading
import time
import traceback
import urllib.request
import zipfile
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "tool"))
from ask import Engine  # noqa: E402
from props import PropError  # noqa: E402

ORDER = [n for n in ["GKK", "GSG", "GDO", "GSN", "GC", "GB"]
         if os.path.exists(os.path.join(HERE, "contracts", n, "stamps.json"))]
TITLES = {"GKK": "Keys and Knowledge", "GSG": "Social Graph", "GDO": "Directed Overlay",
          "GSN": "Social Network", "GC": "Coins", "GB": "Bonds"}
VERSION = "4.32.0"
WIN = os.name == "nt"
DATA = os.environ.get("DATA") or os.path.join(HERE, "data")
LEAN_HOME = os.environ.get("LEAN_HOME") or os.path.join(DATA, f"lean-{VERSION}-{'windows' if WIN else 'linux'}")
LEAN_URL = (f"https://github.com/leanprover/lean4/releases/download/v{VERSION}/"
            f"lean-{VERSION}-windows.zip")

README_ZIP = """GCV: the Lean proofs of the stamps of contract {n}

Model.lean   the contract's speech-act schemas as a Lean transition system (St, Step, Reach)
C*.lean      one theorem pair per stamp: it holds initially (_init) and every step keeps it (_step)
Final.lean   Props (all stamps) and reach_props: every reachable state satisfies all stamps

Check it yourself (Lean {v}; elan installs it from lean-toolchain):
  1. install Lean: https://lean-lang.org/install/
  2. lake build                                   # Lean checks every proof
  3. lake env lean Axioms.lean                    # lists the axioms the final theorem uses
  4. lake env leanchecker --fresh {n}.Final       # replays everything through the kernel
"""

STATUS = {"lean": "not started", "contracts": {c: "waiting" for c in ORDER}, "log": []}
ENGINES: dict[str, Engine] = {}
VERIFY: dict[str, dict] = {}
JOBS: dict[str, dict] = {}
JOBQ: queue.Queue = queue.Queue()
LOCK = threading.Lock()


def log(msg):
    line = time.strftime("%H:%M:%S ") + msg
    print(line, flush=True)
    STATUS["log"] = (STATUS["log"] + [line])[-40:]


def lake_path():
    exe = "lake.exe" if WIN else "lake"
    p = os.path.join(LEAN_HOME, "bin", exe)
    return p if os.path.exists(p) else shutil.which("lake")


def lean_env():
    env = dict(os.environ)
    env["PATH"] = os.path.join(LEAN_HOME, "bin") + os.pathsep + env.get("PATH", "")
    return env


# ------------------------------------------------------------------ warm-up

def ensure_lean():
    if lake_path():
        STATUS["lean"] = "ready"
        return True
    if not WIN:
        STATUS["lean"] = "missing (install Lean 4.32 and set LEAN_HOME)"
        return False
    os.makedirs(DATA, exist_ok=True)
    z = os.path.join(DATA, "lean.zip")
    STATUS["lean"] = "downloading Lean"
    log(f"downloading {LEAN_URL}")
    tmp = z + ".part"
    with urllib.request.urlopen(LEAN_URL, timeout=600) as r, open(tmp, "wb") as f:
        while True:
            b = r.read(1 << 20)
            if not b:
                break
            f.write(b)
    os.replace(tmp, z)
    STATUS["lean"] = "unpacking Lean"
    log("unpacking Lean")
    with zipfile.ZipFile(z) as zf:
        zf.extractall(DATA)
    os.remove(z)
    ok = bool(lake_path())
    STATUS["lean"] = "ready" if ok else "unpacked, but lake not found"
    log(STATUS["lean"])
    return ok


def build_contract(name):
    src = os.path.join(HERE, "contracts", name)
    dst = os.path.join(DATA, "contracts", name)
    stamp = open(os.path.join(src, "stamps.json"), encoding="utf-8").read() + \
        open(os.path.join(src, "proj", name, "Final.lean"), encoding="utf-8").read()
    mark = os.path.join(DATA, "contracts", f"{name}.built")
    if not (os.path.exists(mark) and open(mark, encoding="utf-8").read() == stamp):
        if os.path.exists(dst):
            shutil.rmtree(dst, ignore_errors=True)
        shutil.copytree(src, dst)
        STATUS["contracts"][name] = "Lean is checking the stamps"
        log(f"{name}: lake build")
        t = time.time()
        p = subprocess.run([lake_path(), "build"], cwd=os.path.join(dst, "proj"), capture_output=True,
                           text=True, encoding="utf-8", errors="replace", env=lean_env())
        if p.returncode != 0:
            STATUS["contracts"][name] = "Lean build failed"
            log(f"{name}: build failed\n{(p.stdout + p.stderr)[-1500:]}")
            return
        open(mark, "w", encoding="utf-8").write(stamp)
        log(f"{name}: stamps checked by Lean ({time.time() - t:.0f}s)")
    e = Engine(dst, name, lake=lake_path(), lean_env=lean_env())
    ENGINES[name] = e
    VERIFY.setdefault(name, {})
    try:
        ax = os.path.join(dst, "proj", "Axioms.lean")
        open(ax, "w", encoding="utf-8").write(f"import {name}.Final\n#print axioms {name}.reach_props\n")
        p = subprocess.run([lake_path(), "env", "lean", "Axioms.lean"], cwd=os.path.join(dst, "proj"),
                           capture_output=True, text=True, encoding="utf-8", errors="replace", env=lean_env())
        out = (p.stdout + p.stderr).strip()
        VERIFY[name]["axioms"] = out[out.find("["):].strip("[] \n").split(", ") if "[" in out else out
    except Exception:
        VERIFY[name]["axioms"] = "could not list"
    STATUS["contracts"][name] = "ready"


def recheck(name):
    """Replay every declaration, Lean's core included, through the kernel (leanchecker --fresh)."""
    dst = os.path.join(DATA, "contracts", name, "proj")
    VERIFY.setdefault(name, {})["replay"] = "running"
    t = time.time()
    try:
        p = subprocess.run([lake_path(), "env", "leanchecker", "--fresh", f"{name}.Final"], cwd=dst,
                           capture_output=True, text=True, encoding="utf-8", errors="replace", env=lean_env(),
                           timeout=3600)
        ok = p.returncode == 0
        VERIFY[name]["replay"] = "ok" if ok else "failed"
        VERIFY[name]["replay_seconds"] = round(time.time() - t)
        if not ok:
            log(f"{name}: leanchecker: {(p.stdout + p.stderr)[-600:]}")
    except Exception as ex:
        VERIFY[name]["replay"] = f"not run ({ex.__class__.__name__})"


def warmup():
    try:
        if not ensure_lean():
            return
        for name in ORDER:
            try:
                build_contract(name)
            except Exception:
                STATUS["contracts"][name] = "error"
                log(f"{name}: {traceback.format_exc()[-800:]}")
        try:
            build_generic()
        except Exception:
            GENERIC["state"] = "failed"
            log(traceback.format_exc()[-600:])
        for name in ORDER:
            if name in ENGINES:
                recheck(name)
                log(f"{name}: leanchecker --fresh: {VERIFY[name].get('replay')}")
    except Exception:
        STATUS["lean"] = "error"
        log(traceback.format_exc()[-1500:])


# ------------------------------------------------------------------ questions

def asked_path(name):
    os.makedirs(os.path.join(DATA, "asked"), exist_ok=True)
    return os.path.join(DATA, "asked", f"{name}.json")


def load_asked(name):
    try:
        return json.load(open(asked_path(name), encoding="utf-8"))
    except Exception:
        return []


def worker():
    while True:
        jid = JOBQ.get()
        job = JOBS[jid]
        job["state"] = "running"
        try:
            e = ENGINES[job["contract"]]
            r = e.ask(job["property"], jid)
            job["result"] = r
            if r.get("verdict") in ("proved", "refuted") and "stamp" not in r:
                with LOCK:
                    a = load_asked(job["contract"])
                    if not any(x["formal"] == r["formal"] for x in a):
                        a.append({"formal": r["formal"], "english": r["english"], "verdict": r["verdict"],
                                  "when": time.strftime("%Y-%m-%d")})
                        json.dump(a, open(asked_path(job["contract"]), "w", encoding="utf-8"),
                                  indent=1, ensure_ascii=False)
        except Exception:
            job["result"] = {"verdict": "error", "message": traceback.format_exc()[-600:]}
        job["state"] = "done"


# ------------------------------------------------------------------ HTTP

def contract_info(name):
    src = os.path.join(HERE, "contracts", name)
    stamps = json.load(open(os.path.join(src, "stamps.json"), encoding="utf-8"))
    out = {"name": name, "title": TITLES.get(name, name), "status": STATUS["contracts"].get(name),
           "text": open(os.path.join(src, "contract.txt"), encoding="utf-8").read(),
           "stamps": stamps, "asked": load_asked(name),
           "glossary": json.load(open(os.path.join(src, "glossary.json"), encoding="utf-8"))}
    e = ENGINES.get(name)
    if e is None:
        from parse import parse_contract
        c = parse_contract(open(os.path.join(src, "schemas.txt"), encoding="utf-8").read(), name)
    else:
        c = e.c
    out["facts"] = c.sorts
    out["schemas"] = open(os.path.join(src, "schemas.txt"), encoding="utf-8").read()
    model = open(os.path.join(src, "proj", name, "Model.lean"), encoding="utf-8").read()
    out["pairs"] = schema_pairs(out["schemas"], model)
    out["model_head"] = model.split("inductive Step")[0].strip()
    out["modules"] = sorted(f for f in os.listdir(os.path.join(src, "proj", name)) if f.endswith(".lean"))
    out["verify"] = {**VERIFY.get(name, {}), "lean": VERSION}
    out["generic"] = generic_for(name)
    return out


GENERIC_EN = {
    "records": "If someone holds a fact that names another person, then the two are linked by a chain of acts they took part in: records never cross communities.",
    "closure": "Every act that can be taken either stays within one community, or each person in it shares a community with someone whose will the act needs.",
}


def generic_for(name):
    """The theorems proved once for all contracts of a simple form, as they apply to this contract."""
    f = os.path.join(HERE, "..", "generic", "GSCA", "Stamps.lean")
    if not os.path.exists(f) or GENERIC.get("state") != "ok":
        return []
    txt = open(f, encoding="utf-8").read()
    out = []
    for kind in ("records", "closure"):
        key = f"theorem {name.lower()}_{kind} "
        if key in txt:
            body = txt.split(key, 1)[1].split("\n\n", 1)[0]
            out.append({"english": GENERIC_EN[kind], "lean": (key + body).strip()})
    return out


GENERIC = {"state": "waiting"}


def build_generic():
    src = os.path.join(HERE, "..", "generic")
    dst = os.path.join(DATA, "generic")
    shutil.rmtree(dst, ignore_errors=True)
    shutil.copytree(src, dst, ignore=shutil.ignore_patterns(".lake"))
    p = subprocess.run([lake_path(), "build"], cwd=dst, capture_output=True, text=True, encoding="utf-8",
                       errors="replace", env=lean_env())
    GENERIC["state"] = "ok" if p.returncode == 0 else "failed"
    log(f"generic theorems: {GENERIC['state']}")


def schema_pairs(schemas, model):
    """[(schema name, schema text, Lean constructor text)] in schema order."""
    blocks, cur = [], []
    for ln in schemas.splitlines():
        if ln.startswith("%") or ln.startswith("Environment predicates") or ln.startswith("Reflexive"):
            continue
        if ln and not ln.startswith(" ") and ":" in ln.split("<-")[0]:
            if cur:
                blocks.append("\n".join(cur).strip())
            cur = [ln]
        elif ln.strip():
            cur.append(ln)
    if cur:
        blocks.append("\n".join(cur).strip())
    step = model.split("inductive Step")[1].split("inductive Reach")[0]
    ctors = {}
    for part in step.split("  /-- ")[1:]:
        nm = part.split(";")[0].split(":")[0].strip()
        ctors[nm] = ("/-- " + part).rstrip()
    out = []
    for b in blocks:
        nm = b.split(":")[0].strip()
        out.append({"name": nm, "schema": b, "lean": ctors.get(nm, "")})
    for nm, txt in ctors.items():
        if nm.startswith("environment"):
            out.append({"name": "environment", "schema": "(kept current by the platform)", "lean": txt})
    return out


class H(BaseHTTPRequestHandler):
    def log_message(self, *a):
        pass

    def send(self, code, body, ctype="application/json; charset=utf-8"):
        if not isinstance(body, (bytes, bytearray)):
            body = (json.dumps(body, ensure_ascii=False) if "json" in ctype else body).encode("utf-8")
        self.send_response(code)
        self.send_header("Content-Type", ctype)
        self.send_header("Content-Length", str(len(body)))
        self.send_header("Cache-Control", "no-store")
        self.end_headers()
        self.wfile.write(body)

    def do_GET(self):
        p = self.path.split("?")[0]
        try:
            if p in ("/", "/index.html"):
                return self.send(200, open(os.path.join(HERE, "index.html"), encoding="utf-8").read(),
                                 "text/html; charset=utf-8")
            if p == "/api/contracts":
                return self.send(200, [{"name": n, "title": TITLES.get(n, n),
                                        "status": STATUS["contracts"].get(n),
                                        "stamps": len(json.load(open(os.path.join(HERE, "contracts", n, "stamps.json"),
                                                                     encoding="utf-8")))}
                                       for n in ORDER])
            if p.startswith("/api/contract/"):
                n = p.rsplit("/", 1)[1]
                if n not in ORDER:
                    return self.send(404, {"error": "no such contract"})
                return self.send(200, contract_info(n))
            if p == "/api/status":
                return self.send(200, {**STATUS, "queue": JOBQ.qsize()})
            if p.startswith("/api/job/"):
                j = JOBS.get(p.rsplit("/", 1)[1])
                return self.send(200, j) if j else self.send(404, {"error": "no such job"})
            if p.startswith("/api/zip/"):
                n = p.rsplit("/", 1)[1].replace(".zip", "")
                if n not in ORDER:
                    return self.send(404, {"error": "no such contract"})
                import io
                buf = io.BytesIO()
                root = os.path.join(HERE, "contracts", n, "proj")
                with zipfile.ZipFile(buf, "w", zipfile.ZIP_DEFLATED) as zf:
                    for dp, dn, fn in os.walk(root):
                        dn[:] = [d for d in dn if d != ".lake"]
                        for f in fn:
                            if f.startswith(("Query_", "Refute_")):
                                continue
                            fp = os.path.join(dp, f)
                            zf.write(fp, os.path.join(f"GCV-{n}", os.path.relpath(fp, root)))
                    zf.writestr(f"GCV-{n}/Axioms.lean", f"import {n}.Final\n#print axioms {n}.reach_props\n")
                    zf.writestr(f"GCV-{n}/README.txt", README_ZIP.format(n=n, v=VERSION))
                data = buf.getvalue()
                self.send_response(200)
                self.send_header("Content-Type", "application/zip")
                self.send_header("Content-Disposition", f'attachment; filename="GCV-{n}.zip"')
                self.send_header("Content-Length", str(len(data)))
                self.end_headers()
                self.wfile.write(data)
                return
            if p.startswith("/api/lean/"):
                _, _, _, n, f = p.split("/", 4)
                if n in ORDER and f.replace(".lean", "").isalnum():
                    fp = os.path.join(HERE, "contracts", n, "proj", n, f)
                    if os.path.exists(fp):
                        return self.send(200, open(fp, encoding="utf-8").read(), "text/plain; charset=utf-8")
                return self.send(404, {"error": "no such file"})
            return self.send(404, {"error": "not found"})
        except Exception:
            return self.send(500, {"error": traceback.format_exc()[-500:]})

    def do_POST(self):
        p = self.path.split("?")[0]
        try:
            n = int(self.headers.get("Content-Length") or 0)
            body = json.loads(self.rfile.read(min(n, 20000)) or b"{}")
            name, line = body.get("contract"), (body.get("property") or "")[:500]
            if name not in ORDER:
                return self.send(400, {"error": "no such contract"})
            if p == "/api/render":
                e = ENGINES.get(name)
                if e is None:
                    return self.send(200, {"ok": False, "message": "Lean is still warming up for this contract."})
                try:
                    cd, fl, en = e.render(line)
                    return self.send(200, {"ok": True, "formal": fl, "english": en})
                except PropError as err:
                    return self.send(200, {"ok": False, "message": str(err)})
            if p == "/api/ask":
                if name not in ENGINES:
                    return self.send(200, {"error": "Lean is still checking this contract's stamps; try again soon."})
                if JOBQ.qsize() > 20:
                    return self.send(200, {"error": "Too many questions waiting; try again in a minute."})
                jid = f"{int(time.time() * 1000) % 10**9:09d}"
                JOBS[jid] = {"id": jid, "contract": name, "property": line, "state": "queued"}
                JOBQ.put(jid)
                return self.send(200, {"job": jid})
            return self.send(404, {"error": "not found"})
        except Exception:
            return self.send(500, {"error": traceback.format_exc()[-500:]})


def main():
    port = int(sys.argv[1]) if len(sys.argv) > 1 else int(os.environ.get("PORT", "4901"))
    os.makedirs(DATA, exist_ok=True)
    threading.Thread(target=warmup, daemon=True).start()
    threading.Thread(target=worker, daemon=True).start()
    log(f"GCV on 127.0.0.1:{port}, data in {DATA}")
    ThreadingHTTPServer(("127.0.0.1", port), H).serve_forever()


if __name__ == "__main__":
    main()
