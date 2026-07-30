#!/usr/bin/env python3
"""flt-loop-fs.py -- the loop simulator, with state on a REAL filesystem.

The design claim is that the automaton's next step depends entirely on state
that lives on disk. `flt-loop-viz.py` asserts that; this one *tests* it, by
reloading the whole state from the directory before every single evaluation.
Nothing survives a tick in memory. If the claim were false, the machine would
lose its place.

It also exercises the two disciplines the real loop depends on and that are
easy to get subtly wrong on paper:

  * every write is `.tmp` -> fsync -> os.replace, so a crash never leaves a
    half-written file;
  * the state directory is a git repo, so `git log --oneline` IS the
    transition trace and a repair agent can diff its way back to the tick
    that broke things.

Run:  python3 flt-loop-fs.py [--dir /tmp/flt-loop-sim] [--port 8771]
"""
import argparse
import json
import os
import pathlib
import random
import shutil
import subprocess
from http.server import BaseHTTPRequestHandler, HTTPServer

DIR = pathlib.Path("/tmp/flt-loop-sim")


# --------------------------------------------------------------------------
# atomic primitives
# --------------------------------------------------------------------------
def wr(path, text):
    """Atomic write. The whole crash-safety story rests on this one function."""
    path = pathlib.Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp = path.with_suffix(path.suffix + ".tmp")
    with open(tmp, "w") as fh:
        fh.write(text)
        fh.flush()
        os.fsync(fh.fileno())
    os.replace(tmp, path)


def rd(path, default=None):
    try:
        return pathlib.Path(path).read_text()
    except FileNotFoundError:
        return default


def rm(path):
    try:
        pathlib.Path(path).unlink()
    except FileNotFoundError:
        pass


def git(*args):
    return subprocess.run(
        ["git", "-C", str(DIR), "-c", "user.email=loop@flt", "-c", "user.name=flt-loop"]
        + list(args), capture_output=True, text=True)


# --------------------------------------------------------------------------
# on-disk layout  <-> in-memory dict
# --------------------------------------------------------------------------
#   main              current release sha (stands in for `git rev-parse main`)
#   rebaselined       sha already reacted to
#   queue1            "AUDITED: <sha|none>" header, then one task per line
#   queue2            one task per line
#   batch             one branch per line
#   inflight          one branch per line   (absent = no claim outstanding)
#   snapshot.json     {"sha": ...}          (absent = no snapshot)
#   workers           "<wt> <state>" for NON-derivable states only
#   healthy/ancestor  "<wt> 0|1"
#   STOP              presence halts
#   jobs/<n>.json     the record;  .started / .sentinel written by the job
#   email.log         one line per notification


def seed():
    if DIR.exists():
        shutil.rmtree(DIR)
    DIR.mkdir(parents=True)
    git("init", "-q")
    wr(DIR / "main", "r19")
    wr(DIR / "rebaselined", "r19")
    wr(DIR / "queue1", "AUDITED: r19\nexists_diffCharScalar\nexists_nat_eq_sum_breaks\n")
    wr(DIR / "queue2", "")
    wr(DIR / "batch", "flt-lean-7\n")
    wr(DIR / "snapshot.json", json.dumps({"sha": "r19"}))
    wr(DIR / "workers", "")
    wr(DIR / "healthy", "flt-lean-1 1\nflt-lean-2 1\nflt-lean-3 1\n")
    wr(DIR / "ancestor", "flt-lean-1 1\nflt-lean-2 1\nflt-lean-3 1\n")
    wr(DIR / "email.log", "")
    (DIR / "jobs").mkdir()
    git("add", "-A")
    git("commit", "-q", "-m", "seed")


def _pairs(name):
    out = {}
    for ln in (rd(DIR / name, "") or "").splitlines():
        if ln.strip():
            k, v = ln.split()
            out[k] = v
    return out


def load():
    """Rebuild the ENTIRE state from disk. Called before every evaluation."""
    q1 = (rd(DIR / "queue1", "AUDITED: none\n") or "").splitlines()
    aud = None
    if q1 and q1[0].startswith("AUDITED:"):
        v = q1[0].split(":", 1)[1].strip()
        aud = None if v == "none" else v
        q1 = q1[1:]
    jobs = {}
    for f in sorted((DIR / "jobs").glob("*.json")):
        j = json.loads(f.read_text())
        n = f.stem
        j["started"] = (DIR / "jobs" / (n + ".started")).exists()
        # a marker whose token does not match the record is NOT a marker
        st = rd(DIR / "jobs" / (n + ".started"), "")
        if j["started"] and st.strip() != j["token"]:
            j["started"] = False
        sen = rd(DIR / "jobs" / (n + ".sentinel"))
        j["sentinel"] = None
        if sen:
            try:
                d = json.loads(sen)
                if d.get("token") == j["token"]:
                    j["sentinel"] = d
            except json.JSONDecodeError:
                j["sentinel"] = None          # truncated sentinel = not finished
        j["alive"] = (DIR / "jobs" / (n + ".alive")).exists()
        j.setdefault("retries", 0)
        jobs[n] = j
    snap = rd(DIR / "snapshot.json")
    return {
        "stop": (DIR / "STOP").exists(),
        "main": (rd(DIR / "main", "") or "").strip(),
        "rebaselined": (rd(DIR / "rebaselined", "") or "").strip(),
        "snapshot": json.loads(snap) if snap else None,
        "queue1": {"audited": aud, "tasks": [t for t in q1 if t.strip()]},
        "queue2": [t for t in (rd(DIR / "queue2", "") or "").splitlines() if t.strip()],
        "batch": [b for b in (rd(DIR / "batch", "") or "").splitlines() if b.strip()],
        "inflight": ([b for b in (rd(DIR / "inflight") or "").splitlines() if b.strip()]
                     if (DIR / "inflight").exists() else None),
        "jobs": jobs,
        "workers": {w: (_pairs("workers").get(w) or None)
                    for w in _pairs("healthy")},
        "healthy": {k: v == "1" for k, v in _pairs("healthy").items()},
        "ancestor": {k: v == "1" for k, v in _pairs("ancestor").items()},
        "log": [], "git": [], "email": [],
    }


def save(s):
    wr(DIR / "main", s["main"])
    wr(DIR / "rebaselined", s["rebaselined"])
    wr(DIR / "queue1", "AUDITED: %s\n%s" % (s["queue1"]["audited"] or "none",
                                            "".join(t + "\n" for t in s["queue1"]["tasks"])))
    wr(DIR / "queue2", "".join(t + "\n" for t in s["queue2"]))
    wr(DIR / "batch", "".join(b + "\n" for b in s["batch"]))
    if s["inflight"] is None:
        rm(DIR / "inflight")
    else:
        wr(DIR / "inflight", "".join(b + "\n" for b in s["inflight"]))
    if s["snapshot"] is None:
        rm(DIR / "snapshot.json")
    else:
        wr(DIR / "snapshot.json", json.dumps(s["snapshot"]))
    wr(DIR / "workers", "".join(f"{w} {st}\n" for w, st in s["workers"].items() if st))
    wr(DIR / "ancestor", "".join("%s %d\n" % (k, v) for k, v in s["ancestor"].items()))
    if s["stop"]:
        wr(DIR / "STOP", "halted\n")
    live = set()
    for n, j in s["jobs"].items():
        live |= {n}
        rec = {k: j[k] for k in ("kind", "worktree", "payload", "token", "retries")}
        wr(DIR / "jobs" / (n + ".json"), json.dumps(rec, indent=1))
        if j["started"]:
            wr(DIR / "jobs" / (n + ".started"), j["token"])
        if j["alive"]:
            wr(DIR / "jobs" / (n + ".alive"), j["token"])
        else:
            rm(DIR / "jobs" / (n + ".alive"))
        if j["sentinel"] is not None:
            d = dict(j["sentinel"]); d["token"] = j["token"]
            wr(DIR / "jobs" / (n + ".sentinel"), json.dumps(d))
    for f in (DIR / "jobs").glob("*"):
        stem = f.name.split(".")[0]
        if stem not in live:
            rm(f)


def commit_fs(msg):
    git("add", "-A")
    git("commit", "-q", "-m", msg)


def gitlog(n=60):
    r = git("log", "--oneline", "-%d" % n)
    return [l for l in r.stdout.splitlines() if l.strip()]


# --------------------------------------------------------------------------
# rows -- identical logic to flt-loop-viz.py
# --------------------------------------------------------------------------
from flt_loop_rows import *          # noqa: F401,F403  -- the single source of truth
import flt_loop_rows as _R
evaluate, ROWS, mutate = _R.evaluate, _R.ROWS, _R.mutate


def tick():
    """load -> evaluate -> act -> save -> commit. Nothing persists in memory."""
    s = load()
    rows, firing = evaluate(s)
    label = ""
    for rid, lbl, _, action in ROWS:
        if rid == firing:
            label = lbl
            action(s)
            break
    for e in s["email"]:
        with open(DIR / "email.log", "a") as fh:
            fh.write(e + "\n")
    save(s)
    # Only IDLE is silent -- a history of "nothing happened" would bury the
    # history of what did. Everything else commits, PANIC especially: its
    # message is written by the row itself and must reach git before the
    # medic touches anything.
    if firing != 18:
        commit_fs(s["git"][0] if s["git"] else f"row {firing}: {label}")
    return firing, s


def mutate_fs(job, what):
    s = load()
    mutate(s, job, what)
    save(s)
    if s["git"]:
        commit_fs(s["git"][0])
    else:
        commit_fs("inject: %s%s" % (what, f" ({job})" if job else ""))


# --------------------------------------------------------------------------
# server
# --------------------------------------------------------------------------
PAGE = r"""<!doctype html><html><head><meta charset="utf-8">
<title>flt-loop (filesystem)</title><style>
:root{--bg:#0f1115;--fg:#d8dee9;--dim:#5b6270;--ok:#7fd88f;--fire:#ffcc66;
      --bad:#e06c75;--card:#171a21;--line:#242833}
*{box-sizing:border-box}body{margin:0;background:var(--bg);color:var(--fg);
 font:13px/1.55 ui-monospace,Menlo,monospace}
header{padding:9px 15px;border-bottom:1px solid var(--line);display:flex;gap:10px;
 align-items:center;flex-wrap:wrap}
h1{font-size:13px;margin:0;font-weight:600}
button{background:#232833;color:var(--fg);border:1px solid var(--line);border-radius:5px;
 padding:4px 10px;cursor:pointer;font:inherit;font-size:12px}
button:hover{background:#2c3341}button.p{background:#2f4f3a;border-color:#3d6b4d}
.wrap{display:grid;grid-template-columns:280px 1fr 270px;gap:10px;padding:10px;align-items:start}
.card{background:var(--card);border:1px solid var(--line);border-radius:6px;padding:10px;margin-bottom:10px}
.card h2{font-size:10px;margin:0 0 8px;color:var(--dim);text-transform:uppercase;letter-spacing:.09em}
.row{display:flex;justify-content:space-between;gap:6px;padding:1px 0}
.k{color:var(--dim)}.v{text-align:right;word-break:break-all}
table{width:100%;border-collapse:collapse}td{padding:4px 5px;vertical-align:top;border-top:1px solid var(--line)}
tr.no{color:var(--dim)}tr.yes td{color:var(--ok)}
tr.fire td{background:#3a3016;color:var(--fire);font-weight:600}
.id{width:24px;text-align:right;color:var(--dim)}
.why{font-size:10.5px;color:var(--dim);font-style:italic}
.log div{padding:1px 0;border-bottom:1px solid var(--line);font-size:11px}
.chip{display:inline-block;padding:1px 5px;border-radius:4px;background:#232833;margin:1px 2px 1px 0;font-size:11px}
.chip.claimed{background:#2b3550;color:#9db4ff}
.chip.awaiting_merge{background:#4a3520;color:#e0a86c}
.chip.free{background:#26382c;color:#8fd8a0}
.j{border-top:1px solid var(--line);padding:4px 0;font-size:11px}
.j b{color:#9db4ff}.mut{color:var(--dim)}
.ctl{display:flex;gap:5px;align-items:center;padding:2px 0;font-size:11px}
.ctl label{color:var(--dim);flex:1}
.fs{display:grid;grid-template-columns:230px 1fr;gap:10px}
.fl div{padding:2px 5px;cursor:pointer;border-radius:4px;font-size:11.5px}
.fl div:hover{background:#232833}.fl div.sel{background:#2b3550;color:#9db4ff}
pre{margin:0;white-space:pre-wrap;word-break:break-all;font-size:11.5px;color:#c8d0dc;
 max-height:340px;overflow:auto}
</style></head><body>
<header><h1>flt-loop &mdash; filesystem simulator</h1>
<button class="p" onclick="step()">step</button>
<button onclick="run()" id="runbtn">auto</button>
<button onclick="post('/api/seed')">reseed</button>
<span class="mut" id="tick"></span><span class="mut" id="dir"></span></header>
<div class="wrap">
 <div>
  <div class="card"><h2>state (read from disk)</h2><div id="state"></div></div>
  <div class="card"><h2>inject</h2><div id="inject"></div></div>
 </div>
 <div>
  <div class="card"><h2>rows &mdash; first match fires</h2><table id="rows"></table></div>
  <div class="card"><h2>state directory</h2><div class="fs">
    <div class="fl" id="files"></div><pre id="filebody">select a file</pre></div></div>
 </div>
 <div>
  <div class="card"><h2>workers</h2><div id="workers"></div></div>
  <div class="card"><h2>jobs</h2><div id="jobs"></div></div>
  <div class="card"><h2>git log</h2><div class="log" id="git"></div></div>
  <div class="card"><h2>email.log</h2><div class="log" id="email"></div></div>
 </div>
</div>
<script>
let T=0,timer=null,sel=null;
const $=i=>document.getElementById(i);
const api=(p,b)=>fetch(p,b?{method:'POST',headers:{'Content-Type':'application/json'},
  body:JSON.stringify(b)}:{}).then(r=>r.json());
const kv=(k,v)=>`<div class="row"><span class="k">${k}</span><span class="v">${v}</span></div>`;

function render(d){
 const s=d.state;
 $('dir').textContent=d.dir;
 $('state').innerHTML=kv('main',s.main)+
  kv('rebaselined',s.rebaselined+(s.rebaselined===s.main?'':' <span style="color:#e06c75">stale</span>'))+
  kv('snapshot',s.snapshot?s.snapshot.sha+(s.snapshot.sha===s.main?'':' <span style="color:#e06c75">stale</span>'):'<span style="color:#e06c75">none</span>')+
  kv('queue1 AUDITED',s.queue1.audited??'<span style="color:#e06c75">none</span>')+
  kv('queue1',s.queue1.tasks.length)+kv('queue2',s.queue2.length)+
  kv('batch',s.batch.length)+kv('.inflight',s.inflight?s.inflight.length:'&mdash;');
 $('rows').innerHTML=d.rows.map(r=>`<tr class="${r.fires?'fire':(r.matched?'yes':'no')}">
   <td class="id">${r.id}</td><td>${r.label}${r.matched?'':`<div class="why">${r.why}</div>`}</td></tr>`).join('');
 $('workers').innerHTML=Object.entries(s.workers).map(([w,st])=>
   `<div class="row"><span class="k">${w}</span><span class="chip ${st}">${st}</span></div>`).join('');
 const js=Object.entries(s.jobs);
 $('jobs').innerHTML=js.length?js.map(([n,j])=>`<div class="j"><b>${n}</b> <span class="mut">${j.kind}</span><br>
   <span class="mut">${j.token} &middot; retries ${j.retries}</span><br>
   ${j.started?'started':'<span class="mut">not started</span>'} &middot;
   ${j.alive?'alive':'<span class="mut">dead</span>'} &middot;
   ${j.sentinel?'sentinel':'<span class="mut">no sentinel</span>'}
   <div class="ctl"><button onclick="mut('${n}','finish')">finish</button>
   <button onclick="mut('${n}','die')">die</button></div></div>`).join('')
   :'<span class="mut">none</span>';
 $('git').innerHTML=d.gitlog.map(g=>`<div>${g}</div>`).join('');
 $('email').innerHTML=d.email.length?d.email.map(e=>`<div style="color:#e06c75">${e}</div>`).join('')
   :'<span class="mut">none</span>';
 $('files').innerHTML=d.files.map(f=>`<div class="${f===sel?'sel':''}" onclick="openf('${f}')">${f}</div>`).join('');
 $('tick').textContent='tick '+T+(d.firing?'  → row '+d.firing:'');
 if(sel) openf(sel,true);
}
async function openf(f,quiet){sel=f;const d=await api('/api/file?p='+encodeURIComponent(f));
 $('filebody').textContent=d.body; if(!quiet){document.querySelectorAll('.fl div')
 .forEach(e=>e.classList.toggle('sel',e.textContent===f));}}
async function step(){const d=await api('/api/step',{});T++;render(d);}
async function mut(j,w){render(await api('/api/mutate',{job:j,what:w}));}
async function post(p){const d=await api(p,{});T=0;render(d);}
function run(){if(timer){clearInterval(timer);timer=null;$('runbtn').textContent='auto';}
 else{timer=setInterval(step,700);$('runbtn').textContent='stop';}}
$('inject').innerHTML=`
 <div class="ctl"><label>release (main moves)</label><button onclick="mut(null,'release')">go</button></div>
 <div class="ctl"><label>merger dies (no sentinel)</label><button onclick="mut(null,'merger_die')">go</button></div>
 <div class="ctl"><label>merger reports OK, main unmoved (illegal)</label><button onclick="mut(null,'merger_noop')">go</button></div>
 <div class="ctl"><label>build fails</label><button onclick="mut(null,'build_fail')">go</button></div>
 <div class="ctl"><label>corrupt: orphan .inflight</label><button onclick="mut(null,'corrupt')">go</button></div>
 <div class="ctl"><label>medic GO</label><button onclick="mut(null,'medic_go')">go</button></div>
 <div class="ctl"><label>medic NO-GO</label><button onclick="mut(null,'medic_nogo')">go</button></div>
 <div class="ctl"><label>STOP file</label><button onclick="mut(null,'stop')">go</button></div>`;
api('/api/state').then(render);
</script></body></html>"""


def listing():
    out = []
    for f in sorted(DIR.rglob("*")):
        if ".git" in f.parts or f.is_dir() or f.name.endswith(".tmp"):
            continue
        out.append(str(f.relative_to(DIR)))
    return out


class H(BaseHTTPRequestHandler):
    def log_message(self, *a):
        pass

    def _send(self, body, ctype="application/json"):
        b = body.encode()
        self.send_response(200)
        self.send_header("Content-Type", ctype)
        self.send_header("Content-Length", str(len(b)))
        self.end_headers()
        self.wfile.write(b)

    def _payload(self, firing=None):
        s = load()
        rows, f = evaluate(s)
        return json.dumps({"state": s, "rows": rows, "firing": firing or f,
                           "gitlog": gitlog(), "files": listing(), "dir": str(DIR),
                           "email": [e for e in (rd(DIR / "email.log", "") or "").splitlines() if e]})

    def do_GET(self):
        if self.path.startswith("/api/file"):
            from urllib.parse import urlparse, parse_qs
            q = parse_qs(urlparse(self.path).query).get("p", [""])[0]
            tgt = (DIR / q).resolve()
            body = "(not found)"
            if str(tgt).startswith(str(DIR.resolve())) and tgt.is_file():
                body = tgt.read_text()
            self._send(json.dumps({"body": body}))
        elif self.path.startswith("/api/state"):
            self._send(self._payload())
        else:
            self._send(PAGE, "text/html; charset=utf-8")

    def do_POST(self):
        n = int(self.headers.get("Content-Length") or 0)
        body = json.loads(self.rfile.read(n) or "{}")
        if self.path.endswith("/step"):
            f, _ = tick()
            self._send(self._payload(f))
        elif self.path.endswith("/seed"):
            seed()
            self._send(self._payload())
        elif self.path.endswith("/mutate"):
            mutate_fs(body.get("job"), body.get("what"))
            self._send(self._payload())


def main():
    global DIR
    ap = argparse.ArgumentParser()
    ap.add_argument("--dir", default="/tmp/flt-loop-sim")
    ap.add_argument("--port", type=int, default=8771)
    ap.add_argument("--ticks", type=int, help="headless: run N ticks and exit")
    ap.add_argument("--reseed", action="store_true", help="wipe and reseed first")
    a = ap.parse_args()
    DIR = pathlib.Path(a.dir)
    # Seed ONLY if there is nothing there. A restart must resume from the
    # directory, not erase it -- the whole claim being tested is that the
    # state lives on disk, and a server that wipes on boot would refute it.
    if a.reseed or not (DIR / "main").exists():
        seed()
    else:
        print("resuming existing state in", DIR)
    if a.ticks:
        for _ in range(a.ticks):
            f, _ = tick()
            print("row", f)
        return
    print(f"flt-loop filesystem simulator on http://127.0.0.1:{a.port}   state: {DIR}")
    HTTPServer(("127.0.0.1", a.port), H).serve_forever()


main()
