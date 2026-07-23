#!/usr/bin/env python3
"""Generate the tree section of PROGRESS.md from progress-entries.json.

The flat entries file lists the Lean declarations we track (name, defining
module, prose, work-in-progress flag).  This driver:
  1. runs the census through the RESIDENT REPORT SERVER (Deyao's final
     design, 2026-07-23): `lake serve` run as the systemd user unit
     `flt-report-server.service`, its stdin/stdout wired to two FIFOs
     under `.report-server/` — no resident Python process, no wrapper
     scripts; the unit is the sole lifecycle mechanism. run_census()
     opens the FIFOs, speaks Content-Length-framed JSON-RPC, performs
     the LSP handshake itself when the session is fresh (the unit's
     ExecStartPre clears the state.json marker on every start, so the
     first client after a start/respawn sends initialize/initialized +
     didOpen — handshake is protocol, not lifecycle), refreshes
     `ProgressCensus.lean` in the live session (bumped-version
     didChange, or didClose+didOpen when sources changed), waits for
     diagnostics, and extracts the `#eval` census JSON. It reports each entry's status: missing /
     own-cone sorry / whole-cone sorry / dependency edges to other
     listed entries (BFS over used constants, stopping at listed
     names), plus the compiler-verified sorried-declaration list and
     root status, in ONE response;
  2. decides the mark for each entry:
       cross      — a `sorry` lives in the entry's exclusive cone;
       double     — no `sorryAx` anywhere in the cone (compiler-verified);
       single     — otherwise (own content complete, sorries behind
                    tracked children);
  3. renders the tree (roots = entries nobody else depends on) and splices
     it into the `## Tree` section of PROGRESS.md.

The census route is the ONLY route: `python3 progress-tree.py
--census` runs the same run_census() and prints the raw census JSON —
consumed by the Stop hook (`.claude/check-sorries.py`, which needs
sorried/root but not the tree render) and available to humans/Claude
for debugging. The census file's generated import header (every module
under Fermat/ except the root aggregator) and its baked-in input path
are REGENERATED on every run of this script, so newly added modules
are picked up automatically.

CONTRACT (Deyao, 2026-07-22/23, final): NO fallbacks, NO auto-spawn.
Either the census answers fully — every tracked entry reported,
sorried list and root status present — and PROGRESS.md is rendered
from that answer alone, or this script RAISES with the real error
(server not running: the message says to `systemctl --user start
flt-report-server` and the CALLER decides; missing entries; compiler
error diagnostics naming the module that does not compile), exits
nonzero, and leaves PROGRESS.md untouched. A broken repo must surface as a loud crash at
generation time, never as a silently rearranged tree.

STALENESS (investigated against the toolchain server source,
Lean/Server/Watchdog.lean + FileWorker*.lean, v4.32.0-rc1): the
language server CANNOT itself detect that dependencies of an open file
changed — `lake setup-file` (which rebuilds stale imports) runs only
at file-worker startup (didOpen / worker restart), imports are never
reloaded in a running worker, and the "imports out of date" diagnostic
is only emitted when a CLIENT notifies the watchdog (didSave of an
open dependency or workspace/didChangeWatchedFiles); the watchdog even
registers a **/*.lean file watcher WITH the client — file watching is
the client's job in this protocol. So run_census() does exactly that
client job, statelessly: it snapshots Fermat/**/*.lean (mtime+size;
sources only, NEVER .lake artifacts) into .report-server/state.json
and didClose+didOpens the census file when the snapshot (or the import
block) changed — making lake rebuild exactly the changed cones —
while an unchanged snapshot gets a bumped-version identity didChange,
which re-publishes diagnostics from cached elaboration snapshots in
seconds. A names/root input change alone changes the census file BODY
(the input fingerprint line in the generated block), so a didChange
re-elaborates the census against the new input without an import
reload.

Placement: dependency edges come from the compiled proof terms; an
entry the server reports but that no proof term places yet (a freshly
stated leaf whose consumer is still sorried) may carry a provisional
"parent" field in progress-entries.json (precedence: live edges >
"parent" > root). See main() for the exact rules.

This module is import-safe: generation happens only under `__main__`.
"""
import fcntl, hashlib, json, os, select, sys, time

ROOT = os.path.dirname(os.path.abspath(__file__))
CENSUS_LEAN = os.path.join(ROOT, "ProgressCensus.lean")
CENSUS_INPUT = os.path.join(ROOT, "progress-census-input.json")
_BEGIN = "-- BEGIN GENERATED IMPORTS"
_END = "-- END GENERATED IMPORTS"

# --- resident report server (systemd user unit flt-report-server) --------
SERVER_DIR = os.path.join(ROOT, ".report-server")
REQ_FIFO = os.path.join(SERVER_DIR, "req.fifo")
RESP_FIFO = os.path.join(SERVER_DIR, "resp.fifo")
STATE_FILE = os.path.join(SERVER_DIR, "state.json")
LOCK_FILE = os.path.join(SERVER_DIR, "lock")
QUERY_LOG = os.path.join(SERVER_DIR, "query.log")
CENSUS_URI = "file://" + CENSUS_LEAN
START_HINT = ("the report server is not running (or died) — it is the "
              "systemd user unit `flt-report-server`: start it with "
              "`systemctl --user start flt-report-server` (unit file "
              "flt-report-server.service at the repo root; logs: "
              "`journalctl --user -u flt-report-server`)")


# ------------------------------------------------------- the census runner

def scan_fermat_modules():
    """Every project module under Fermat/ (the root aggregator
    Fermat.lean lives at the repo root, not under Fermat/, so it is
    naturally excluded — its sorry gate fails by design)."""
    mods = []
    for dirpath, _dirs, files in os.walk(os.path.join(ROOT, "Fermat")):
        for name in files:
            if name.endswith(".lean"):
                rel = os.path.relpath(os.path.join(dirpath, name), ROOT)
                mods.append(rel[:-len(".lean")].replace(os.sep, "."))
    return sorted(mods)


def regenerate_census_header():
    """Rewrite the generated import block of ProgressCensus.lean (module
    list from the source scan + the baked-in input path + a fingerprint
    of the CURRENT census input file). Missing markers are a script/repo
    bug and crash loudly.

    The fingerprint line matters for the report server: the input json
    is read at ELABORATION time, so a names/root change with unchanged
    sources must still change the census file's BODY text — otherwise a
    bumped-version didChange would serve the previous input's cached
    elaboration. Callers therefore write CENSUS_INPUT BEFORE calling
    this function. The line sits after the imports, so it is body text
    (a change re-elaborates the census without an import reload)."""
    src = open(CENSUS_LEAN, encoding="utf-8").read()
    i = src.index(_BEGIN)
    j = src.index(_END)
    block = _BEGIN + "\n"
    for mod in scan_fermat_modules():
        block += f"import {mod}\n"
    block += f'def censusInputPath : System.FilePath := "{CENSUS_INPUT}"\n'
    if os.path.exists(CENSUS_INPUT):
        fp = hashlib.sha1(open(CENSUS_INPUT, "rb").read()).hexdigest()
    else:
        fp = "no-input"
    block += f"-- census-input fingerprint: {fp}\n"
    new = src[:i] + block + src[j:]
    if new != src:
        with open(CENSUS_LEAN, "w", encoding="utf-8") as fh:
            fh.write(new)


# ---------------------------------------------- report-server LSP client

class _PipeLsp:
    """Content-Length-framed JSON-RPC over the report server's FIFOs.

    One instance per client run; request ids are `<pid>.<seq>` — ids
    only need to be unique among IN-FLIGHT requests (the server keeps
    no memory of answered ids), so sequential client runs may reuse
    numbers freely. The server holds both FIFO ends O_RDWR (see
    flt-report-server.service), so opening/closing our ends never EOFs
    or SIGPIPEs it; the response stream position always sits on a
    message boundary because every client reads whole framed messages.
    Liveness probe: the O_WRONLY|O_NONBLOCK open of req.fifo fails with
    ENXIO exactly when no process holds a read end — i.e. the server is
    gone — and raises the systemctl start hint (no auto-spawn — the
    caller decides; Deyao, 2026-07-23)."""

    def __init__(self, timeout=3600):
        self.timeout = timeout
        try:
            self.wfd = os.open(REQ_FIFO, os.O_WRONLY | os.O_NONBLOCK)
        except OSError as exc:
            raise RuntimeError(f"{START_HINT} (request pipe: {exc})") from exc
        os.set_blocking(self.wfd, True)
        self.rfd = os.open(RESP_FIFO, os.O_RDONLY)
        self.buf = b""
        self.seq = 0
        self.diags = {}   # uri -> latest published diagnostics

    def close(self):
        for fd in (self.wfd, self.rfd):
            try:
                os.close(fd)
            except OSError:
                pass

    def _send(self, obj):
        data = json.dumps(obj).encode()
        msg = b"Content-Length: " + str(len(data)).encode() + b"\r\n\r\n" + data
        while msg:
            n = os.write(self.wfd, msg)
            msg = msg[n:]

    def _fill(self, deadline):
        wait = deadline - time.time()
        if wait <= 0:
            raise RuntimeError(
                f"report server did not respond within {self.timeout}s")
        r, _, _ = select.select([self.rfd], [], [], wait)
        if not r:
            raise RuntimeError(
                f"report server did not respond within {self.timeout}s")
        chunk = os.read(self.rfd, 1 << 16)
        if chunk == b"":
            raise RuntimeError(f"{START_HINT} (response pipe EOF)")
        self.buf += chunk

    def _read_msg(self, deadline):
        while b"\r\n\r\n" not in self.buf:
            self._fill(deadline)
        head, _, self.buf = self.buf.partition(b"\r\n\r\n")
        length = None
        for line in head.decode("ascii", "replace").split("\r\n"):
            if line.lower().startswith("content-length:"):
                length = int(line.split(":", 1)[1].strip())
        if length is None:
            raise RuntimeError(f"malformed LSP header from report server: "
                               f"{head!r}")
        while len(self.buf) < length:
            self._fill(deadline)
        body, self.buf = self.buf[:length], self.buf[length:]
        return json.loads(body)

    def _dispatch(self, msg):
        method = msg.get("method")
        if method == "textDocument/publishDiagnostics":
            p = msg["params"]
            self.diags[p["uri"]] = p["diagnostics"]
        elif method is not None and "id" in msg:
            # server->client request (e.g. client/registerCapability for
            # its **/*.lean file watcher): a minimal client answers null
            self._send({"jsonrpc": "2.0", "id": msg["id"], "result": None})

    def notify(self, method, params):
        self._send({"jsonrpc": "2.0", "method": method, "params": params})

    def request(self, method, params):
        self.seq += 1
        rid = f"{os.getpid()}.{self.seq}"
        self._send({"jsonrpc": "2.0", "id": rid,
                    "method": method, "params": params})
        deadline = time.time() + self.timeout
        while True:
            msg = self._read_msg(deadline)
            self._dispatch(msg)
            if msg.get("id") == rid and "method" not in msg:
                if "error" in msg:
                    raise RuntimeError(
                        f"report server: {method}: {msg['error']}")
                return msg.get("result")


def _source_snapshot():
    """mtime+size of every SOURCE the census depends on (Fermat/**/*.lean
    and the lake project files) — never anything under .lake. This is
    the client-side half of the LSP file-watching contract; see the
    module docstring's STALENESS section for why the server cannot
    answer this itself."""
    snap = {}
    for dirpath, _dirs, files in os.walk(os.path.join(ROOT, "Fermat")):
        for name in files:
            if name.endswith(".lean"):
                p = os.path.join(dirpath, name)
                st = os.stat(p)
                snap[os.path.relpath(p, ROOT)] = [st.st_mtime_ns, st.st_size]
    for name in ("lakefile.toml", "lakefile.lean", "lake-manifest.json",
                 "lean-toolchain"):
        p = os.path.join(ROOT, name)
        if os.path.exists(p):
            st = os.stat(p)
            snap[name] = [st.st_mtime_ns, st.st_size]
    return snap


def _imports_sha(text):
    return hashlib.sha1("\n".join(
        l for l in text.splitlines() if l.startswith("import ")
    ).encode()).hexdigest()


def _qlog(line):
    with open(QUERY_LOG, "a", encoding="utf-8") as fh:
        fh.write(f"[{time.strftime('%F %T')}] {line}\n")


def run_census(names, root="fermat_last_theorem", timeout=3600):
    """Run the census through the resident report server and return the
    parsed response dict ({"entries": ..., "sorried": ..., "root": ...}).

    NO fallbacks, NO auto-spawn (Deyao, 2026-07-22/23): a dead/absent
    server, a broken pipe, or compiler errors in the census RAISE with
    the real message (errors name the module that does not compile).
    Handshake is the CLIENT's job (protocol, not lifecycle — Deyao,
    2026-07-23): the unit's ExecStartPre removes state.json on every
    (re)start, so a missing state file means a fresh server session,
    and this client performs initialize/initialized + didOpen itself
    before querying. Otherwise, refresh protocol per the STALENESS
    section of the module docstring:
      * source snapshot or import block changed -> didClose+didOpen
        (lake setup-file rebuilds exactly the stale cones, imports are
        reloaded, the whole file re-elaborates);
      * census text changed only in the body (input fingerprint) ->
        bumped-version didChange, body re-elaborates, imports stay;
      * nothing changed -> bumped-version identity didChange, the
        server re-publishes diagnostics from cached elaboration
        snapshots (seconds).
    The flock serializes concurrent clients (generator vs Stop hook)
    over the single shared LSP session — a lock, not a fallback."""
    with open(CENSUS_INPUT, "w", encoding="utf-8") as fh:
        json.dump({"names": list(names), "root": root}, fh)
    regenerate_census_header()
    text = open(CENSUS_LEAN, encoding="utf-8").read()
    snap = _source_snapshot()
    text_sha = hashlib.sha1(text.encode()).hexdigest()
    imports_sha = _imports_sha(text)

    os.makedirs(SERVER_DIR, exist_ok=True)
    lockfd = os.open(LOCK_FILE, os.O_CREAT | os.O_RDWR)
    try:
        fcntl.flock(lockfd, fcntl.LOCK_EX)
        state = None
        if os.path.exists(STATE_FILE):
            state = json.load(open(STATE_FILE, encoding="utf-8"))
        version = (state or {}).get("version", 0) + 1
        if state is None:
            # fresh server session: the unit's ExecStartPre cleared the
            # marker on start/respawn — this client handshakes first
            mode = "handshake"
        elif (state.get("snapshot") != snap
                or state.get("imports_sha") != imports_sha):
            mode = "reopen"
        elif state.get("text_sha") != text_sha:
            mode = "didChange"
        else:
            mode = "warm"
        t0 = time.time()
        lsp = _PipeLsp(timeout)
        ok = False
        try:
            if mode == "handshake":
                lsp.request("initialize", {"processId": os.getpid(),
                                           "rootUri": "file://" + ROOT,
                                           "capabilities": {}})
                lsp.notify("initialized", {})
                lsp.notify("textDocument/didOpen", {"textDocument": {
                    "uri": CENSUS_URI, "languageId": "lean4",
                    "version": version, "text": text}})
            elif mode == "reopen":
                lsp.notify("textDocument/didClose",
                           {"textDocument": {"uri": CENSUS_URI}})
                lsp.notify("textDocument/didOpen", {"textDocument": {
                    "uri": CENSUS_URI, "languageId": "lean4",
                    "version": version, "text": text}})
            else:
                lsp.notify("textDocument/didChange", {
                    "textDocument": {"uri": CENSUS_URI, "version": version},
                    "contentChanges": [{"text": text}]})
            lsp.request("textDocument/waitForDiagnostics",
                        {"uri": CENSUS_URI, "version": version})
            diags = lsp.diags.get(CENSUS_URI, [])
            errors = [d for d in diags if d.get("severity") == 1]
            if errors:
                msgs = "\n".join(
                    f"{CENSUS_LEAN}:{d['range']['start']['line'] + 1}: "
                    f"{d['message']}" for d in errors[:10])
                raise RuntimeError(f"census elaboration failed ({mode}, "
                                   f"{time.time() - t0:.1f}s):\n{msgs}")
            resp = None
            for d in diags:
                msg = d.get("message", "")
                k = msg.find("{")
                if k < 0:
                    continue
                try:
                    cand = json.loads(msg[k:])
                except ValueError:
                    continue
                if isinstance(cand, dict) and "sorried" in cand:
                    resp = cand
            if resp is None:
                raise RuntimeError(
                    f"census produced no JSON payload ({mode}, "
                    f"{len(diags)} diagnostics, none parseable)")
            ok = True
        finally:
            lsp.close()
            # state is written on failure too, with a poisoned text_sha:
            # the next run then always re-elaborates instead of reading
            # a warm no-op against the failed version's diagnostics
            json.dump({"snapshot": snap,
                       "text_sha": text_sha if ok else "elaboration-failed",
                       "imports_sha": imports_sha, "version": version},
                      open(STATE_FILE, "w", encoding="utf-8"))
            _qlog(f"census: mode={mode} version={version} "
                  f"{time.time() - t0:.1f}s ok={ok}")
        return resp
    finally:
        os.close(lockfd)


# ------------------------------------------------------------- generation

def main():
    entries = json.load(open(f"{ROOT}/progress-entries.json"))
    names = [e.get("fullname", e["name"]) for e in entries]
    disp = {e.get("fullname", e["name"]): e["name"] for e in entries}
    by_name = {e.get("fullname", e["name"]): e for e in entries}

    # NO fallbacks (Deyao, 2026-07-22): the census must answer fully or
    # this run dies with the real error — run_census raises with the
    # lake output tail naming the module that does not compile. ONE
    # census per generation: the response carries entries, sorried, and
    # root together.
    resp = run_census(names)
    if "entries" not in resp:
        raise RuntimeError(f"malformed census response: "
                           f"{str(resp)[:500]}")

    deps = {n: [] for n in names}
    own = {}
    clean = {}
    for item in resp["entries"]:
        n = item["name"]
        if item.get("missing"):
            continue
        deps[n] = item["kids"]
        own[n] = item["own"]
        clean[n] = item["clean"]
    missing = [n for n in names if n not in clean]
    if missing:
        raise RuntimeError(
            "tracked entries missing from the compiled environment "
            "(renamed or not yet stated? fix progress-entries.json or "
            "the source): " + ", ".join(missing))

    # --------------------------------------------- compiler sorry count
    if not isinstance(resp.get("sorried"), list):
        raise RuntimeError(f"census response lacks the sorried list: "
                           f"{str(resp)[:500]}")
    sorried_names = [s["name"] for s in resp["sorried"]]
    sorry_count = len(sorried_names)

    # -------------------------------------------------------------- marks
    # cross  — a `sorry` lives in the node's EXCLUSIVE cone (reached
    #          without passing through any other tracked node): the
    #          node's own mathematical content is still open;
    # double — no sorryAx anywhere in the cone (compiler-certified);
    # single — otherwise: the node's own content is complete, the
    #          remaining sorries all sit behind tracked children.
    mark = {}
    for e in entries:
        n = e.get("fullname", e["name"])
        if clean[n]:
            mark[n] = "✅✅"
        elif own.get(n, False):
            mark[n] = "❌"
        else:
            mark[n] = "✅"

    # --------------------------------------------------------- build tree
    children = {n: [k for k in deps.get(n, []) if k in by_name]
                for n in names}

    # Provisional placement (Deyao, 2026-07-22): a freshly stated leaf
    # whose consumer is still sorried has no incoming proof-term edge
    # yet (a sorried body contributes no dependencies) and would float
    # to root level as a fake root. An entry may therefore carry an
    # optional "parent" field (the fullname of its decomposing parent,
    # recorded by the orchestrator at tracking time). Placement
    # precedence: live census edges > provisional "parent" > root —
    # the field is consulted ONLY for entries no live edge places, and
    # real edges take over automatically once the consumer's proof
    # skeleton lands. A provisional attachment is skipped (entry stays
    # a root, one-liner note) when the parent is unknown/self,
    # currently ✅✅ (its subtree is hidden — attaching would make the
    # open leaf invisible), or the edge would create a render cycle.
    placed = {k for n in names for k in children[n]}

    def _reaches(frm, to):
        seen, st = set(), [frm]
        while st:
            x = st.pop()
            if x == to:
                return True
            if x in seen:
                continue
            seen.add(x)
            st.extend(children.get(x, []))
        return False

    for e in entries:
        n = e.get("fullname", e["name"])
        p = e.get("parent")
        if not p or n in placed:
            continue
        if p == n or p not in by_name:
            print(f"note: provisional parent of {n} ignored "
                  f"(unknown or self: {p})", file=sys.stderr)
            continue
        if mark.get(p) == "✅✅":
            print(f"note: provisional parent of {n} ignored ({p} is "
                  "proven and hidden); entry stays at root",
                  file=sys.stderr)
            continue
        if _reaches(n, p):
            print(f"note: provisional parent of {n} ignored "
                  f"(edge {p} -> {n} would create a cycle)",
                  file=sys.stderr)
            continue
        children[p].append(n)
        placed.add(n)

    has_parent = {k for n in names for k in children[n]}
    roots = [n for n in names if n not in has_parent]

    lines_out = []

    def render(n, depth):
        # fully proven nodes are HIDDEN from the display entirely (Deyao,
        # 2026-07-17: the tree shows only the missing parts); the data
        # still lives in progress-entries.json / progress-tree.json.
        if mark[n] == "✅✅":
            return
        e = by_name[n]
        state = "🟪" if e.get("wip") else "·"
        # 4-space indentation per level: classic Markdown renderers
        # (Markdown.pl / python-markdown) flatten 2-space-nested lists,
        # which made every item look childless in such previews.
        # name + status only (Deyao, 2026-07-23): the per-entry prose
        # stays in progress-entries.json but is not rendered.
        lines_out.append(f"{'    ' * depth}- {mark[n]}{state} `{disp[n]}`")
        # a node with several dependents appears once under EACH of them,
        # with its full text and subtree duplicated (no "(see above)"
        # references — Deyao, 2026-07-17); the dependency graph is
        # acyclic, so this terminates.
        for k in sorted(children[n], key=lambda x: names.index(x)):
            render(k, depth + 1)

    for r in roots:
        render(r, 0)

    # --------------------------------------------- display invariant checks
    # 1. no single-tick item may be rendered without children (its
    #    remaining sorries must be visibly attributable to ❌ descendants);
    # 2. no double-tick item may be rendered with children (proven
    #    subtrees are trimmed).
    _items = [(i, l) for i, l in enumerate(lines_out)
              if l.lstrip().startswith("- ")]

    def _depth(l):
        return len(l) - len(l.lstrip())

    _viol = []
    for _j, (_i, _l) in enumerate(_items):
        _ls = _l.lstrip()
        _d = _depth(_l)
        _nxt = _items[_j + 1][1] if _j + 1 < len(_items) else None
        _haskids = _nxt is not None and _depth(_nxt) > _d
        if _ls.startswith("- ✅✅"):
            _viol.append(f"double-tick displayed at all: {_l.strip()[:80]}")
        elif _ls.startswith("- ✅"):
            if not _haskids:
                _viol.append(f"single-tick without children: {_l.strip()[:80]}")
    if _viol:
        # Every generation is fully compiler-backed (no fallbacks), so a
        # display-invariant violation is a real defect: die loudly
        # without touching PROGRESS.md.
        for _v in _viol:
            print("INVARIANT VIOLATION:", _v, file=sys.stderr)
        sys.exit(1)

    # --------------------------------------------------- splice + dump
    json.dump({"marks": mark, "children": children, "roots": roots,
               "sorried": sorried_names},
              open(f"{ROOT}/progress-tree.json", "w"),
              ensure_ascii=False, indent=1)

    md = open(f"{ROOT}/PROGRESS.md").read().split("\n")
    t0 = next(i for i, l in enumerate(md) if l.startswith("## Tree"))
    t1 = next(i for i in range(t0 + 1, len(md)) if md[i].startswith("## "))
    legend = [
        "## Tree (generated — do not edit by hand; run `python3 progress-tree.py`)",
        "",
        "The tree below is GENERATED from `progress-entries.json` (the flat list",
        "of tracked Lean declarations with their descriptions): the dependency",
        "structure is computed from the compiled proofs (which listed",
        "declarations each proof transitively uses), and the marks are computed",
        "by the Lean compiler — ❌ the declaration's own source still contains",
        "`sorry`; ✅ the source is a complete proof but its dependency cone",
        "still contains a `sorry`; ✅✅ the whole cone is sorry-free",
        "(`#print axioms` shows only propext/Classical.choice/Quot.sound).",
        "✅✅ nodes are HIDDEN from this display entirely — the tree shows",
        "only the open work (they remain in `progress-entries.json` and",
        "`progress-tree.json`). A node with several dependents is shown in",
        "full (text and subtree) under each dependent — no back references —",
        "so beneath every ✅ node the ❌ nodes its remaining sorries flow",
        "through are directly visible.",
        "Second symbol: `·` normal, `🟪` currently being worked on (from the",
        "entries file). To add/remove/annotate a node, edit",
        "`progress-entries.json` and re-run the generator.",
        "",
    ]
    if sorry_count is not None:
        legend += [
            f"**Sorried declarations (compiler-counted): {sorry_count}**"
            + (" — " + ", ".join(f"`{n.rsplit('.', 1)[-1]}`"
                                 for n in sorried_names)
               if sorried_names else ""),
            "",
        ]
    md = md[:t0] + legend + lines_out + [""] + md[t1:]
    open(f"{ROOT}/PROGRESS.md", "w").write("\n".join(md))
    print(f"entries: {len(entries)}  roots: {len(roots)}  "
          f"double: {sum(1 for v in mark.values() if v == '✅✅')}  "
          f"single: {sum(1 for v in mark.values() if v == '✅')}  "
          f"cross: {sum(1 for v in mark.values() if v == '❌')}  "
          f"sorried-decls: {sorry_count}")


if __name__ == "__main__":
    if "--census" in sys.argv:
        # print-json-only entry over the same run_census() route the
        # generator uses (regenerate the header, run `lake lean
        # ProgressCensus.lean`, print the census JSON verbatim).
        # Consumed by the Stop hook and invoked explicitly by
        # humans/Claude for debugging; NOT a fallback — nothing calls
        # it automatically, and it is the same single route main()
        # takes. Failures crash loudly out of run_census.
        _entries = json.load(open(f"{ROOT}/progress-entries.json"))
        print(json.dumps(run_census(
            [e.get("fullname", e["name"]) for e in _entries])))
    else:
        main()
