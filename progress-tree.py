#!/usr/bin/env python3
"""Generate the tree section of PROGRESS.md from progress-entries.json.

The flat entries file lists the Lean declarations we track (name, defining
module, prose, work-in-progress flag).  This driver:
  1. asks the persistent Lean environment server (`lean-daemon.py`,
     autostarted on demand) for each entry's status: missing / own-cone
     sorry / whole-cone sorry / dependency edges to other listed entries
     (BFS over used constants, stopping at listed names);
  2. decides the mark for each entry:
       cross      — a `sorry` lives in the entry's exclusive cone;
       double     — no `sorryAx` anywhere in the cone (compiler-verified);
       single     — otherwise (own content complete, sorries behind
                    tracked children);
  3. renders the tree (roots = entries nobody else depends on) and splices
     it into the `## Tree` section of PROGRESS.md.

The daemon's environment reflects the last BUILT state of each module
(`stale_sources` in its response names modules edited since), and the
daemon SELF-MATERIALIZES its input: unbuilt/stale modules are built on
demand (targeted `lake build`) before the environment is imported, so
tracked entries are present in normal operation.

Generation NEVER refuses and never surfaces transient state (Deyao,
2026-07-22): a module that genuinely fails to build is the daemon's to
log (`.lean-daemon.log`, `failed_modules` in its responses); the
affected entries are rendered here from the previous generation's
cached marks/edges (`progress-tree.json`), keeping their last-known
subtree shape. Only a bug in the scripts themselves may crash this.
"""
import json, re, subprocess, sys, textwrap, unicodedata, os

ROOT = os.path.dirname(os.path.abspath(__file__))
entries = json.load(open(f"{ROOT}/progress-entries.json"))
names = [e.get("fullname", e["name"]) for e in entries]
disp = {e.get("fullname", e["name"]): e["name"] for e in entries}
by_name = {e.get("fullname", e["name"]): e for e in entries}

# ------------------------------------------------- query the lean daemon
# The previous generation's marks/edges: the fallback for any entry the
# daemon cannot report on right now (module genuinely failing to build,
# daemon unreachable). Merging from it keeps the last-known subtree
# shape instead of orphaning entries into fake flat roots.
try:
    _cache = json.load(open(f"{ROOT}/progress-tree.json"))
except (OSError, ValueError):
    _cache = {}
cache_marks = _cache.get("marks", {})
cache_children = _cache.get("children", {})

res = subprocess.run(
    [sys.executable, f"{ROOT}/lean-daemon.py", "--query",
     json.dumps({"cmd": "report", "names": names})],
    capture_output=True, text=True, cwd=ROOT, timeout=3600)
resp = {}
if res.returncode == 0:
    try:
        resp = json.loads(res.stdout)
    except ValueError:
        resp = {}
if "error" in resp or "entries" not in resp:
    # daemon unavailable/transient — fall back to cache for everything
    resp = {"entries": []}

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

# Entries the daemon could not report (module failed to build, or the
# daemon itself was unavailable): render from the cached previous
# generation. Silent by design — the daemon log carries the failure
# signal; PROGRESS.md and the operator see a complete tree either way.
fallback = [n for n in names if n not in clean]
fallback_mark = {}
for n in fallback:
    fallback_mark[n] = cache_marks.get(n, "❌")
    deps[n] = [k for k in cache_children.get(n, []) if k in by_name]
if fallback:
    print(f"note: {len(fallback)} entries rendered from cached previous "
          "generation", file=sys.stderr)

# ------------------------------------------------- compiler sorry count
sres = subprocess.run(
    [sys.executable, f"{ROOT}/lean-daemon.py", "--query",
     json.dumps({"cmd": "sorries"})],
    capture_output=True, text=True, cwd=ROOT, timeout=3600)
sorry_count = None
sorried_names = []
if sres.returncode == 0:
    try:
        sresp = json.loads(sres.stdout)
        # only trust an actual sorried list — a daemon {"error": ...}
        # response must NOT be rendered as "0 sorried declarations"
        if "error" not in sresp and isinstance(sresp.get("sorried"), list):
            sorried_names = [s["name"] for s in sresp["sorried"]]
            sorry_count = len(sorried_names)
    except Exception:
        pass

# ------------------------------------------------------------------ marks
# cross  — a `sorry` lives in the node's EXCLUSIVE cone (reached without
#          passing through any other tracked node): the node's own
#          mathematical content is still open;
# double — no sorryAx anywhere in the cone (compiler-certified);
# single — otherwise: the node's own content is complete, the remaining
#          sorries all sit behind tracked children.
mark = {}
for e in entries:
    n = e.get("fullname", e["name"])
    if n in fallback_mark:
        mark[n] = fallback_mark[n]
    elif clean[n]:
        mark[n] = "✅✅"
    elif own.get(n, False):
        mark[n] = "❌"
    else:
        mark[n] = "✅"

# --------------------------------------------------------------- build tree
children = {n: [k for k in deps.get(n, []) if k in by_name] for n in names}
has_parent = {k for n in names for k in children[n]}
roots = [n for n in names if n not in has_parent]

lines_out = []
def render(n, depth):
    # fully proven nodes are HIDDEN from the display entirely (Deyao,
    # 2026-07-17: the tree shows only the missing parts); the data still
    # lives in progress-entries.json / progress-tree.json.
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
    wrapped = textwrap.wrap(body, width=max(100 - 4 * depth - 2, 30)) if body else []
    lines_out.append(head + (" — " + wrapped[0] if wrapped else ""))
    for w in wrapped[1:]:
        lines_out.append(f"{'    ' * depth}  {w}")
    # a node with several dependents appears once under EACH of them, with
    # its full text and subtree duplicated (no "(see above)" references —
    # Deyao, 2026-07-17); the dependency graph is acyclic, so this
    # terminates.
    for k in sorted(children[n], key=lambda x: names.index(x)):
        render(k, depth + 1)

for r in roots:
    render(r, 0)

# ------------------------------------------------- display invariant checks
# 1. no single-tick item may be rendered without children (its remaining
#    sorries must be visibly attributable to ❌ descendants);
# 2. no double-tick item may be rendered with children (proven subtrees
#    are trimmed).
_items = [(i, l) for i, l in enumerate(lines_out) if l.lstrip().startswith("- ")]
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
    for _v in _viol:
        print("INVARIANT VIOLATION:", _v, file=sys.stderr)
    # Only a fully compiler-backed generation may be held to the display
    # invariants; a cache-merged one (some entries at their last-known
    # state) can transiently violate them and must still be written —
    # generation never refuses (Deyao, 2026-07-22).
    if not fallback:
        sys.exit(1)

# ------------------------------------------------------------- splice + dump
json.dump({"marks": mark, "children": children, "roots": roots},
          open(f"{ROOT}/progress-tree.json", "w"), ensure_ascii=False, indent=1)

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
                             for n in sorried_names) if sorried_names else ""),
        "",
    ]
md = md[:t0] + legend + lines_out + [""] + md[t1:]
open(f"{ROOT}/PROGRESS.md", "w").write("\n".join(md))
print(f"entries: {len(entries)}  roots: {len(roots)}  "
      f"double: {sum(1 for v in mark.values() if v == '✅✅')}  "
      f"single: {sum(1 for v in mark.values() if v == '✅')}  "
      f"cross: {sum(1 for v in mark.values() if v == '❌')}  "
      f"sorried-decls: {sorry_count}")
