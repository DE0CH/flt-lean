#!/usr/bin/env python3
"""Compiler-verified free-floating-code detection (Deyao, 2026-07-18).

A declaration in the project's own modules is *free-floating* if it is not
in the transitive used-constant cone of `fermat_last_theorem` — i.e. no
proof term reachable from the root actually uses it (a sorried body
contributes no edges, so material built bottom-up for a still-sorried
consumer shows up here until the consumer's proof skeleton is written).

Method (the Lean compiler does the work): generate a scratch file
importing every project module (except the root aggregator `Fermat`, which
deliberately fails on the sorry gate), run a metaprogram that (a) BFSes
the used-constant cone from the root, (b) sweeps every constant whose
defining module is a `Fermat.*` module, and (c) prints the ones outside
the cone. Results are cached in `free-floating.json` keyed by the max
mtime of the Lean sources, so repeated hook invocations are cheap.
"""

import json
import os
import subprocess
import sys

ROOT = os.path.dirname(os.path.abspath(__file__))
CACHE = os.path.join(ROOT, "free-floating.json")
ROOT_DECL = "fermat_last_theorem"


def source_key() -> str:
    # include this script's own mtime so detector refinements invalidate the cache
    latest = os.path.getmtime(os.path.abspath(__file__))
    # and the keep-list's, so allowlist changes invalidate it too
    keep_path = os.path.join(ROOT, "free-floating-keep.json")
    if os.path.exists(keep_path):
        latest = max(latest, os.path.getmtime(keep_path))
    for dirpath, _dirs, files in os.walk(os.path.join(ROOT, "Fermat")):
        for name in files:
            if name.endswith(".lean"):
                # a listed file vanishing mid-scan is unexpected: crash
                # (OSError) rather than compute a key from partial data
                latest = max(latest,
                             os.path.getmtime(os.path.join(dirpath, name)))
    return str(latest)


def modules() -> list[str]:
    mods = []
    base = os.path.join(ROOT, "Fermat")
    for dirpath, _dirs, files in os.walk(base):
        for name in sorted(files):
            if not name.endswith(".lean"):
                continue
            rel = os.path.relpath(os.path.join(dirpath, name), ROOT)
            mod = rel[:-5].replace(os.sep, ".")
            mods.append(mod)
    return mods


def main() -> int:
    key = source_key()
    if os.path.exists(CACHE):
        with open(CACHE) as fh:
            try:
                cached = json.load(fh)
            except ValueError as exc:
                raise RuntimeError(
                    f"corrupt cache {CACHE}: {exc} — delete the file and "
                    "rerun") from exc
        if cached.get("key") == key:
            print(json.dumps(cached))
            return 0

    lean = ["import " + m for m in modules()]
    lean.append("open Lean in")
    lean.append("#eval show CoreM Unit from do")
    lean.append(f"  let root : Name := `{ROOT_DECL}")
    lean.append("""  let env ← getEnv
  -- the transitive used-constant cone of the root
  let mut cone : NameSet := {}
  let mut stack : Array Name := #[root]
  while !stack.isEmpty do
    let c := stack.back!
    stack := stack.pop
    unless cone.contains c do
      cone := cone.insert c
      match env.find? c with
      | some ci => stack := stack ++ ci.getUsedConstantsAsSet.toArray
      | none => pure ()
  -- sweep every project-module declaration against the cone
  for (n, _) in env.constants.toList do
    if n.isInternalDetail then continue
    -- auto-generated structure/inductive members (rec, casesOn, mk, injEq,
    -- ext, congr_simp, ...) share their SOURCE LINES with the parent
    -- declaration; the free-floating criterion is line-based (every line
    -- transitively used from the root), so they are only reportable through
    -- their parent, never separately.
    let comps := n.componentsRev
    let isAutogen := match comps with
      | c :: _ =>
        let last := c.toString
        last ∈ ["rec", "recOn", "casesOn", "brecOn", "below", "ibelow",
          "binductionOn", "noConfusion", "noConfusionType", "mk", "injEq", "ctorIdx",
          "inj", "sizeOf_spec", "ext", "ext_iff", "congr_simp", "eq_def"] ||
        last.startsWith "eq_" || last.startsWith "match_" ||
        last.startsWith "proof_" || last.startsWith "_proof_"
      | _ => false
    if isAutogen then continue
    match env.getModuleIdxFor? n with
    | none => continue
    | some idx =>
      let mod := env.header.moduleNames[idx.toNat]!
      if mod.getRoot == `Fermat then
        unless cone.contains n do
          IO.println s!"FLOATING\\t{mod}\\t{n}"
""")
    scratch = os.path.join(ROOT, "FreeFloatingScratch.lean")
    with open(scratch, "w") as fh:
        fh.write("\n".join(lean) + "\n")
    try:
        proc = subprocess.run(
            ["lake", "env", "lean", scratch],
            cwd=ROOT, capture_output=True, text=True, timeout=1200,
        )
    finally:
        try:
            os.remove(scratch)
        except OSError:
            pass  # resource cleanup only — never affects the result
    if proc.returncode != 0:
        # do NOT cache or emit a partial analysis — a broken run must not
        # read as "zero floating declarations"; crash with the compiler's
        # own tail so the caller can see which module failed
        tail = "\n".join(
            (proc.stdout + "\n" + proc.stderr).strip().splitlines()[-30:])
        raise RuntimeError(
            f"free-floating analysis failed (lake env lean exit "
            f"{proc.returncode}); nothing cached:\n{tail}")
    # build-verified elaboration-invisible keepers: outside the term cone but
    # required by elaboration (deletion breaks the build); see
    # free-floating-keep.json and CLAUDE.md "Elaboration-invisible dependency
    # classes". Each entry names the failure that proved it.
    keep = {}
    keep_path = os.path.join(ROOT, "free-floating-keep.json")
    if os.path.exists(keep_path):
        with open(keep_path) as fh:
            try:
                keep_data = json.load(fh)
            except ValueError as exc:
                raise RuntimeError(
                    f"corrupt keep-list {keep_path}: {exc} — fix or delete "
                    "it and rerun") from exc
        keep = {k: v for k, v in keep_data.items() if not k.startswith("_")}
    floating = []
    kept_invisible = []
    for line in proc.stdout.splitlines():
        if line.startswith("FLOATING\t"):
            _tag, mod, name = line.split("\t")
            if name in keep:
                kept_invisible.append({"module": mod, "name": name})
            else:
                floating.append({"module": mod, "name": name})
    result = {"key": key, "returncode": proc.returncode,
              "kept_invisible": kept_invisible,
              "floating": floating}
    json.dump(result, open(CACHE, "w"), ensure_ascii=False, indent=1)
    print(json.dumps(result))
    return 0


if __name__ == "__main__":
    sys.exit(main())
