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
(`stale_sources` in its response names modules edited since).
"""
import json, re, subprocess, sys, textwrap, unicodedata, os

ROOT = os.path.dirname(os.path.abspath(__file__))
entries = json.load(open(f"{ROOT}/progress-entries.json"))
names = [e.get("fullname", e["name"]) for e in entries]
disp = {e.get("fullname", e["name"]): e["name"] for e in entries}
by_name = {e.get("fullname", e["name"]): e for e in entries}

# ------------------------------------------------- query the lean daemon
res = subprocess.run(
    [sys.executable, f"{ROOT}/lean-daemon.py", "--query",
     json.dumps({"cmd": "report", "names": names})],
    capture_output=True, text=True, cwd=ROOT, timeout=3600)
if res.returncode != 0:
    print("DAEMON FAILED:", res.stderr[:500], file=sys.stderr)
    sys.exit(1)
resp = json.loads(res.stdout)
if "error" in resp:
    print("DAEMON ERROR:", resp["error"], file=sys.stderr)
    sys.exit(1)
for mod in resp.get("stale_sources", []):
    print(f"NOTE: {mod} edited since last build — status reflects the "
          "built state", file=sys.stderr)

deps = {n: [] for n in names}
own = {}
clean = {}
for item in resp["entries"]:
    n = item["name"]
    if item.get("missing"):
        print(f"LEAN: {n} MISSING", file=sys.stderr)
        continue
    deps[n] = item["kids"]
    own[n] = item["own"]
    clean[n] = item["clean"]

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
    if n not in clean:
        mark[n] = "❌"
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
md = md[:t0] + legend + lines_out + [""] + md[t1:]
open(f"{ROOT}/PROGRESS.md", "w").write("\n".join(md))
print(f"entries: {len(entries)}  roots: {len(roots)}  "
      f"double: {sum(1 for v in mark.values() if v == '✅✅')}  "
      f"single: {sum(1 for v in mark.values() if v == '✅')}  "
      f"cross: {sum(1 for v in mark.values() if v == '❌')}")
