#!/usr/bin/env python3
"""Generate the tree section of PROGRESS.md from progress-entries.json.

The flat entries file lists the Lean declarations we track (name, defining
module, prose, work-in-progress flag).  This driver:
  1. runs the census as ONE COMMAND-LINE INVOCATION over ssh (Deyao,
     2026-07-25): `lake env lean ProgressCensus.lean`, on the host
     named by `~/.flt-worker-host/<worktree>`. See run_census().
     ProgressCensus.lean ends in an `#eval` that prints the census as
     one JSON line on stdout; run_census() scans stdout for it. The
     census reports each entry's status: missing / own-cone sorry /
     whole-cone sorry / dependency edges to other listed entries (BFS
     over used constants, stopping at listed names), plus the
     compiler-verified sorried-declaration list and root status;
  2. decides the mark for each entry:
       cross      — a `sorry` lives in the entry's exclusive cone;
       double     — no `sorryAx` anywhere in the cone (compiler-verified);
       single     — otherwise (own content complete, sorries behind
                    tracked children);
  3. renders the tree (roots = entries nobody else depends on) and splices
     it into the `## Tree` section of PROGRESS.md, stamped with the commit
     it describes (see stamp_line()).

`python3 progress-tree.py --census` runs the same run_census() and
prints the raw census JSON — consumed by the Stop hook
(`.claude/check-sorries.py`, which needs sorried/root but not the tree
render) and available to humans/Claude for debugging. The census
file's generated import header (every module under Fermat/ except the
root aggregator) and its baked-in input path are REGENERATED on every
run of this script, so newly added modules are picked up
automatically.

THERE IS NO RESIDENT SERVER. The report MCP, the `flt-report-server@`
/ `flt-lake-socket@` systemd units, the FIFOs under `.report-server/`
and its `state.json` staleness marker were all DELETED on 2026-07-25,
along with the LSP client and the file-watching/staleness bookkeeping
that used to live in this file. Every persistent-server failure this
project hit came from documents opened and never closed and from state
shared between clients — a stale `lake setup-file` failure replayed
with `verified: true`, a false clean from an unheard publish, four
rival elaborations of one file. A command-line invocation is a fresh
process that exits and returns its memory, so none of those can occur;
the fix is structural, not disciplinary.

Two consequences of that transport, both of which bite:
  * COST. Each run pays the IMPORT LOAD of the whole project cone
    (minutes). There is no warm/didChange fast path. Run the census
    once per bookkeeping cycle, never in a loop.
  * THE TREE MUST BE BUILT. This transport READS OLEANS; it does not
    elaborate the cone for you. A stale or broken build dies with
    `object file '….olean' does not exist`, and run_census() adds a
    hint saying to `lake build` first. A module that fails to build
    contributes NO declarations, so a partial census would also give a
    wrong floating answer — which is why there is no degraded mode.

CONTRACT (Deyao, 2026-07-22/23, reaffirmed 2026-07-25): NO fallbacks.
Either the census answers fully — every tracked entry reported,
sorried list and root status present — and PROGRESS.md is rendered
from that answer alone, or this script RAISES with the real error
(lake's own output, naming the module that does not compile; missing
entries), exits nonzero, and leaves PROGRESS.md untouched. A broken
repo must surface as a loud crash at generation time, never as a
silently rearranged tree.

Choosing WHICH COMMIT to census is not a fallback and is the caller's
business: when HEAD does not build, checking out the newest ancestor
that does and censusing THAT is honest — it describes a state of the
repository that actually existed. What the generated tree must never
do is describe one commit while claiming to be another, so the render
carries a stamp naming the commit it was computed from (stamp_line()),
and flags it when that is not the checked-out HEAD.

A caution learned the hard way (2026-07-25): this docstring described
the deleted FIFO design for a full day after the code stopped
implementing it, and that staleness is exactly how a reference to the
deleted `.report-server/` survived into a fatal code path — `_qlog`
was called on BOTH the success and the failure path of run_census(),
so its FileNotFoundError both killed successful runs and replaced the
RuntimeError carrying lake's real output. Keep this text describing
what the code below actually does.

Placement: dependency edges come from the compiled proof terms; an
entry the census reports but that no proof term places yet (a freshly
stated leaf whose consumer is still sorried) may carry a provisional
"parent" field in progress-entries.json (precedence: live edges >
"parent" > root). See main() for the exact rules.

This module is import-safe: generation happens only under `__main__`.
"""
import hashlib, json, os, shlex, subprocess, sys, time

ROOT = os.path.dirname(os.path.abspath(__file__))
CENSUS_LEAN = os.path.join(ROOT, "ProgressCensus.lean")
CENSUS_INPUT = os.path.join(ROOT, "progress-census-input.json")
_BEGIN = "-- BEGIN GENERATED IMPORTS"
_END = "-- END GENERATED IMPORTS"


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

    The fingerprint line ties the generated file to the input it was
    generated for: the input json is read at ELABORATION time, so
    without it a names/root change with unchanged sources would leave
    the census file byte-identical and give no evidence of which input
    a given ProgressCensus.lean belongs to. Callers therefore write
    CENSUS_INPUT BEFORE calling this function.

    (It was originally load-bearing for a different reason — the
    resident report server would otherwise have served the previous
    input's cached elaboration for a bumped-version didChange. That
    server is deleted and every run is now a fresh process, so nothing
    can be cached across runs; the line is kept because a generated
    file that records its own input is worth having.)"""
    src = open(CENSUS_LEAN, encoding="utf-8").read()
    i = src.index(_BEGIN)
    j = src.index(_END)
    block = _BEGIN + "\n"
    for mod in scan_fermat_modules():
        block += f"import {mod}\n"
    # RELATIVE path (Deyao's fleet, 2026-07-23): run_census() cd's to the
    # worktree ROOT before invoking `lake env lean ProgressCensus.lean`, so a
    # relative path resolves correctly, and — the reason it must stay relative
    # — the generated file then stays BYTE-IDENTICAL across every worktree at
    # the same commit. An absolute path here made each worktree's census
    # regeneration dirty its own ProgressCensus.lean, tripping the dispatch
    # pool-hook's clean-worktree guard.
    block += ('def censusInputPath : System.FilePath := '
              '"progress-census-input.json"\n')
    if os.path.exists(CENSUS_INPUT):
        fp = hashlib.sha1(open(CENSUS_INPUT, "rb").read()).hexdigest()
    else:
        fp = "no-input"
    block += f"-- census-input fingerprint: {fp}\n"
    new = src[:i] + block + src[j:]
    if new != src:
        with open(CENSUS_LEAN, "w", encoding="utf-8") as fh:
            fh.write(new)


def _git(*args):
    """Read-only git query in ROOT. Returns stripped stdout, or "" on any
    failure — this is used only to LABEL the output, never to decide
    anything, so it must not be able to break a census run."""
    try:
        p = subprocess.run(["git", "-C", ROOT, *args],
                           capture_output=True, text=True, timeout=30)
    except (OSError, subprocess.SubprocessError):
        return ""
    return p.stdout.strip() if p.returncode == 0 else ""


def stamp_line():
    """One line naming the commit this tree was computed from.

    WHY (Deyao's orchestrator, 2026-07-25). The census reads OLEANS, so it
    describes whatever source state was last BUILT — which need not be the
    checked-out HEAD, and when HEAD does not compile the honest move is to
    census the newest ancestor that does. That is a legitimate choice of
    input, not a fallback. What is NOT acceptable is a generated artifact
    that silently describes a different commit than the one checked out:
    the next reader has no way to tell. So the render always carries the
    commit it came from, and says so loudly when that is not HEAD.

    A dirty worktree is flagged too — an uncommitted edit means the tree
    describes something with no commit name at all."""
    head = _git("rev-parse", "--short", "HEAD")
    if not head:
        return "_Generated from an unknown commit (git unavailable)._"
    subj = _git("log", "-1", "--format=%s", head)
    when = _git("log", "-1", "--format=%cI", head)
    dirty = bool(_git("status", "--porcelain"))
    line = f"_Generated from `{head}`"
    if when:
        line += f" ({when})"
    if subj:
        line += f" — {subj}"
    line += "._"
    if dirty:
        line += ("\n\n_The worktree was DIRTY when this ran: uncommitted edits "
                 "are not described by the commit named above._")
    return line


def run_census(names, root="fermat_last_theorem", timeout=3600):
    """Run the census on the COMMAND LINE and return the parsed response
    dict ({"entries": ..., "sorried": ..., "root": ...}).

    Transport (Deyao, 2026-07-25 — replaces the resident report server,
    which is deleted along with the MCP, the FIFOs and state.json):
    one `lake env lean ProgressCensus.lean` subprocess. The census file
    ends in an `#eval` that writes its JSON with `IO.println`, so the
    payload arrives on stdout and elaboration errors on stderr; the
    process then exits and returns all its memory.

    NO fallbacks (Deyao, 2026-07-22/23): a census that fails to compile,
    or produces no JSON, RAISES with the real stderr — errors name the
    module that does not compile.

    Cost model: each call pays the IMPORT LOAD of the whole project cone
    (minutes), not re-elaboration, provided the oleans are current. There
    is no warm/didChange fast path any more and no staleness bookkeeping
    to get wrong — which is the trade this change makes deliberately, the
    per-document state being where every observed defect came from. Run
    it once per bookkeeping cycle, not in a loop, and give it a long
    timeout."""
    with open(CENSUS_INPUT, "w", encoding="utf-8") as fh:
        json.dump({"names": list(names), "root": root}, fh)
    regenerate_census_header()
    t0 = time.time()
    # THIS MACHINE RUNS ONLY CLAUDE CODE (Deyao, 2026-07-25). Lean runs on
    # the assigned remote host, named by the routing table, and we reach it
    # over ssh — never locally, however tempting, because a local run drags
    # every elaboration back onto a slice that is CPU-quota-capped at 24
    # cores and is meant to be idle.
    host_file = os.path.join(os.path.expanduser("~"), ".flt-worker-host",
                             os.path.basename(ROOT))
    try:
        host = open(host_file, encoding="utf-8").read().strip()
    except OSError as exc:
        raise RuntimeError(
            f"no routing entry for {os.path.basename(ROOT)}: {exc}. "
            f"{host_file} must name the host that serves this worktree "
            f"— the census cannot be run locally.") from exc
    if host in ("local", "mystique") or not host:
        raise RuntimeError(
            f"routing entry {host_file} says {host!r}; this machine runs "
            f"only Claude Code, so it must name a remote Lean host.")
    # elan is NOT on PATH in a non-interactive ssh session (the systemd
    # units used to supply it), so put it there explicitly — otherwise the
    # remote dies with a bare `lake: command not found`.
    remote = (f"export PATH=$HOME/.elan/bin:$PATH; cd {shlex.quote(ROOT)} && "
              f"lake env lean {shlex.quote(CENSUS_LEAN)}")
    proc = subprocess.run(
        ["ssh", "-o", "BatchMode=yes", host, remote],
        capture_output=True, text=True, timeout=timeout)
    # `#eval` writes the census JSON to stdout via IO.println; elaboration
    # errors go to stderr and are what a nonzero status means.
    resp = None
    for line in proc.stdout.splitlines():
        k = line.find("{")
        if k < 0:
            continue
        try:
            cand = json.loads(line[k:])
        except ValueError:
            continue
        if isinstance(cand, dict) and "sorried" in cand:
            resp = cand
    dt = time.time() - t0
    if resp is None:
        # `lake env lean` writes its DIAGNOSTICS TO STDOUT, not stderr —
        # reporting stderr alone yields a bare "(no stderr)" that hides the
        # real cause (observed 2026-07-25: a missing .olean read as silence).
        blob = ((proc.stdout or "") + (proc.stderr or "")).strip()
        detail = "\n".join(blob.splitlines()[:10]) or "(no output at all)"
        hint = ""
        if "does not exist" in blob and ".olean" in blob:
            hint = ("\nHINT: an .olean is missing — the build is stale. "
                    "Run `lake build` before the census; this transport "
                    "reads oleans, it does not elaborate the cone for you.")
        raise RuntimeError(
            f"census produced no JSON payload (rc={proc.returncode}, "
            f"{dt:.1f}s):\n{detail}{hint}")
    print(f"census: rc={proc.returncode} {dt:.1f}s ok", file=sys.stderr)
    return resp


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
        stamp_line(),
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
