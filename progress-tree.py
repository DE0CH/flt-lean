#!/usr/bin/env python3
"""Generate the tree section of PROGRESS.md from progress-entries.json.

The flat entries file lists the Lean declarations we track (name, defining
module, prose, work-in-progress flag).  This driver:
  1. asks the census server (`lean-daemon.py`, autostarted on demand —
     since 2026-07-22 a thin LSP client that keeps one `lake serve`
     alive and reopens `ProgressCensus.lean` per query; building and
     invalidation belong entirely to the language server) for each
     entry's status: missing / own-cone sorry / whole-cone sorry /
     dependency edges to other listed entries (BFS over used constants,
     stopping at listed names), plus the compiler-verified
     sorried-declaration list and root status, in ONE response;
  2. decides the mark for each entry:
       cross      — a `sorry` lives in the entry's exclusive cone;
       double     — no `sorryAx` anywhere in the cone (compiler-verified);
       single     — otherwise (own content complete, sorries behind
                    tracked children);
  3. renders the tree (roots = entries nobody else depends on) and splices
     it into the `## Tree` section of PROGRESS.md.

This file also owns the standalone one-shot census route,
`ProgressCensus.lean` (run as `lake lean ProgressCensus.lean`; also
available here as `python3 progress-tree.py --census`): the same
metaprogram without a resident server, lake building the import closure
incrementally. The census file's generated import header (every module
under Fermat/ except the root aggregator) and its baked-in input path
are REGENERATED on every run of this script, so newly added modules
are picked up automatically.

CONTRACT (Deyao, 2026-07-22, final): NO fallbacks. Either the server
answers fully — every tracked entry reported, sorried list and root
status present — and PROGRESS.md is rendered from that answer alone,
or this script RAISES with the real error (daemon error text, missing
entries, lake output tail naming the module that does not compile),
exits nonzero, and leaves PROGRESS.md untouched. A broken repo must
surface as a loud crash at generation time, never as a silently
rearranged tree.

Placement: dependency edges come from the compiled proof terms; an
entry the server reports but that no proof term places yet (a freshly
stated leaf whose consumer is still sorried) may carry a provisional
"parent" field in progress-entries.json (precedence: live edges >
"parent" > root). See main() for the exact rules.

This module is import-safe: generation happens only under `__main__`.
"""
import json, re, subprocess, sys, textwrap, unicodedata, os

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
    list from the source scan + the baked-in input path). Missing
    markers are a script/repo bug and crash loudly."""
    src = open(CENSUS_LEAN, encoding="utf-8").read()
    i = src.index(_BEGIN)
    j = src.index(_END)
    block = _BEGIN + "\n"
    for mod in scan_fermat_modules():
        block += f"import {mod}\n"
    block += f'def censusInputPath : System.FilePath := "{CENSUS_INPUT}"\n'
    new = src[:i] + block + src[j:]
    if new != src:
        with open(CENSUS_LEAN, "w", encoding="utf-8") as fh:
            fh.write(new)


def run_census(names, root="fermat_last_theorem", timeout=3600):
    """Regenerate the census header, write the input file, run
    `lake lean ProgressCensus.lean`, and return the parsed response
    dict ({"entries": ..., "sorried": ..., "root": ...}).

    NO fallbacks (Deyao, 2026-07-22): any compile/run failure RAISES
    with the lake output tail (which names the module that does not
    compile). A broken repo must crash the caller loudly."""
    regenerate_census_header()
    with open(CENSUS_INPUT, "w", encoding="utf-8") as fh:
        json.dump({"names": list(names), "root": root}, fh)
    res = subprocess.run(
        ["lake", "lean", CENSUS_LEAN],
        capture_output=True, text=True, cwd=ROOT, timeout=timeout)
    # The census JSON is the (last) stdout line holding one object with
    # the expected keys; lake build progress may precede it.
    resp = None
    for line in res.stdout.splitlines():
        k = line.find("{")
        if k < 0:
            continue
        try:
            cand = json.loads(line[k:])
        except ValueError:
            continue
        if isinstance(cand, dict) and "sorried" in cand:
            resp = cand
    if res.returncode != 0 or resp is None:
        tail = "\n".join(
            (res.stdout + "\n" + res.stderr).strip().splitlines()[-15:])
        raise RuntimeError(
            f"census failed (lake lean exit {res.returncode}):\n{tail}")
    return resp


# ------------------------------------------------------------- generation

def main():
    entries = json.load(open(f"{ROOT}/progress-entries.json"))
    names = [e.get("fullname", e["name"]) for e in entries]
    disp = {e.get("fullname", e["name"]): e["name"] for e in entries}
    by_name = {e.get("fullname", e["name"]): e for e in entries}

    # keep the standalone census file's generated header current
    regenerate_census_header()

    # NO fallbacks (Deyao, 2026-07-22): the server must answer fully or
    # this run dies with the real error. A daemon {"error": ...} carries
    # the lake output tail naming the module that does not compile.
    def daemon_query(request):
        res = subprocess.run(
            [sys.executable, f"{ROOT}/lean-daemon.py", "--query",
             json.dumps(request)],
            capture_output=True, text=True, cwd=ROOT, timeout=3600)
        if res.returncode != 0:
            raise RuntimeError(
                f"lean-daemon --query exited {res.returncode}: "
                f"{res.stderr.strip()[-2000:]}")
        resp = json.loads(res.stdout)
        if "error" in resp:
            raise RuntimeError(f"lean daemon: {resp['error']}")
        return resp

    # ONE query per generation: the census response carries entries,
    # sorried, and root together.
    resp = daemon_query({"cmd": "report", "names": names})
    if "entries" not in resp:
        raise RuntimeError(f"malformed daemon report response: "
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
        head = f"{'    ' * depth}- {mark[n]}{state} `{disp[n]}`"
        body = e["text"]
        # drop the leading name-echo from the prose if present
        body = re.sub(rf"^`?{re.escape(n)}`?\s*[—:-]?\s*", "", body)
        wrapped = textwrap.wrap(
            body, width=max(100 - 4 * depth - 2, 30)) if body else []
        lines_out.append(head + (" — " + wrapped[0] if wrapped else ""))
        for w in wrapped[1:]:
            lines_out.append(f"{'    ' * depth}  {w}")
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
        # one-shot lake-native census (no resident server): regenerate
        # the header, run `lake lean ProgressCensus.lean`, print the
        # JSON. The fallback route when the daemon misbehaves.
        _entries = json.load(open(f"{ROOT}/progress-entries.json"))
        _resp = run_census([e.get("fullname", e["name"]) for e in _entries])
        if _resp is None:
            sys.exit(1)
        print(json.dumps(_resp))
    else:
        main()
