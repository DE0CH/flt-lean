#!/usr/bin/env python3
"""Generate the tree section of PROGRESS.md from progress-entries.json.

The flat entries file lists the Lean declarations we track (name, defining
module, prose, work-in-progress flag).  This driver:
  1. emits a Lean scratch file that (a) `#print axioms` each entry and
     (b) runs a meta program computing, for each entry, which OTHER listed
     entries its proof depends on (BFS over used constants, stopping at
     listed names) — the dependency tree, filtered to the list;
  2. runs the Lean compiler once (`lake env lean`);
  3. decides the mark for each entry:
       cross      — the declaration's own source block contains `sorry`;
       double     — `#print axioms` shows no `sorryAx` (whole cone clean);
       single     — otherwise (own text complete, cone still has sorries);
  4. renders the tree (roots = entries nobody else depends on) and splices
     it into the `## Tree` section of PROGRESS.md; repeated subtrees are
     rendered once, later occurrences get a `(see above)` reference.
"""
import json, re, subprocess, sys, textwrap, unicodedata, os

ROOT = os.path.dirname(os.path.abspath(__file__))
entries = json.load(open(f"{ROOT}/progress-entries.json"))
names = [e.get("fullname", e["name"]) for e in entries]
disp = {e.get("fullname", e["name"]): e["name"] for e in entries}
by_name = {e.get("fullname", e["name"]): e for e in entries}

# ---------------------------------------------------------------- lean file
mods = sorted({e["module"] for e in entries})
lean = ["import " + m for m in mods]
lean.append("open Lean in")
lean.append("#eval show CoreM Unit from do")
lean.append("  let names : Array Name := #[" + ", ".join("`" + n for n in names) + "]")
lean.append("""  let listed : NameSet := names.foldl (fun s n => s.insert n) {}
  let env ← getEnv
  for root in names do
    match env.find? root with
    | none => IO.println s!"DEP\\t{root}\\tMISSING"
    | some ci =>
      let mut visited : NameSet := {}
      let mut kids : Array Name := #[]
      let mut ownSorry := false
      let mut stack : Array Name := ci.getUsedConstantsAsSet.toArray
      while !stack.isEmpty do
        let c := stack.back!
        stack := stack.pop
        if !(visited.contains c) then
          visited := visited.insert c
          if c == `sorryAx then
            ownSorry := true
          else if listed.contains c && c != root then
            kids := kids.push c
          else
            match env.find? c with
            | some ci' => stack := stack ++ ci'.getUsedConstantsAsSet.toArray
            | none => pure ()
      IO.println s!"DEP\\t{root}\\t{ownSorry}\\t{kids}"
""")
for n in names:
    q = "«%s»" % n if False else n
    lean.append(f"#print axioms {n}")
open(f"{ROOT}/.progress_status.lean", "w").write("\n".join(lean) + "\n")

# ------------------------------------------------------------------- run it
res = subprocess.run(["lake", "env", "lean", f"{ROOT}/.progress_status.lean"],
                     capture_output=True, text=True, cwd=ROOT, timeout=3600)
out = res.stdout + res.stderr
if "MISSING" in out or res.returncode not in (0,):
    # axioms lines still usable; report problems
    for l in out.splitlines():
        if "MISSING" in l or "error" in l:
            print("LEAN:", l[:200], file=sys.stderr)

# ------------------------------------------------------- parse deps + axioms
deps = {n: [] for n in names}
own = {}
clean = {}
for l in out.splitlines():
    if l.startswith("DEP\t"):
        _, root, osf, kids = l.split("\t")
        kids = kids.strip("#[] ")
        deps[root] = [k.strip() for k in kids.split(",") if k.strip()] if kids else []
        own[root] = (osf == "true")


for m in re.finditer(r"'([^\n]+)' depends on axioms: \[(.*?)\]", out, re.S):
    clean[m.group(1)] = "sorryAx" not in m.group(2)
for m in re.finditer(r"'([^']+)' does not depend on any axioms", out):
    clean[m.group(1)] = True

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
    head = f"{'  ' * depth}- {mark[n]}{state} `{disp[n]}`"
    body = e["text"]
    # drop the leading name-echo from the prose if present
    body = re.sub(rf"^`?{re.escape(n)}`?\s*[—:-]?\s*", "", body)
    wrapped = textwrap.wrap(body, width=72 - 2 * depth - 2) if body else []
    lines_out.append(head + (" — " + wrapped[0] if wrapped else ""))
    for w in wrapped[1:]:
        lines_out.append(f"{'  ' * depth}  {w}")
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
