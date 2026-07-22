#!/usr/bin/env python3
"""Persistent Lean environment server for the FLT loop tooling.

Loading the full Fermat+mathlib environment costs minutes; paying it on
every `progress-tree.py` run and every Stop-hook check is what made both
slow. This daemon pays it ONCE: it keeps a `lake env lean` child alive
whose `#eval` loop holds the imported environment and answers queries
over a Unix socket, restarting the child only when the built `.olean`s
actually change.

  python3 lean-daemon.py --serve            # run the daemon (foreground)
  python3 lean-daemon.py --query '<json>'   # one query (autostarts daemon)
  python3 lean-daemon.py --stop             # shut the daemon down

Queries (JSON, one object per line over the socket):
  {"cmd": "report", "names": [...]}  -> per tracked declaration: missing /
      own (sorry in its exclusive cone) / clean (whole cone sorry-free) /
      kids (which other tracked declarations its proof uses); computed by
      BFS over `getUsedConstantsAsSet`, pruned to Fermat-module constants
      (mathlib cannot depend on the project, so every path to `sorryAx`
      or to a tracked name stays inside Fermat modules).
  {"cmd": "sorries"}  -> the compiler-verified list of project
      declarations whose proof term uses `sorryAx` directly (the same
      set the `declaration uses 'sorry'` build warnings mark), plus the
      root check for `fermat_last_theorem` (cone sorry + axiom
      whitelist over encountered axioms).

Every response is augmented by the daemon with freshness metadata:
  stale_sources    modules whose .lean source is newer than their .olean
                   (the environment reflects the LAST BUILD of those);
  unbuilt_modules  modules with no .olean at all (excluded from imports);
  failed_modules   modules whose last materialization attempt FAILED to
                   compile (the genuine dirty-input signal; retried when
                   their source or a project import's olean changes).

The daemon SELF-MATERIALIZES its input: before importing, it builds the
oleans of every unbuilt/stale project module with a targeted
`lake build <mod> ...` — the same on-demand behavior as the language
server compiling a file's imports when it is opened. Lake's content
hashing makes already-fresh modules free, so this is incremental. The
root aggregator module `Fermat` (the sorry gate, which fails by design)
is never a target: scan_modules never lists it and no bare `lake build`
is ever run.
"""

import json
import os
import re
import socket
import subprocess
import sys
import time

ROOT = os.path.dirname(os.path.abspath(__file__))
SOCK = os.path.join(ROOT, ".lean-daemon.sock")
LOG = os.path.join(ROOT, ".lean-daemon.log")
SERVER_LEAN = os.path.join(ROOT, ".lean-daemon-server.lean")
OLEAN_ROOT = os.path.join(ROOT, ".lake", "build", "lib", "lean")

# ------------------------------------------------------------ module scan


def scan_modules():
    """(module name, source path, olean path) for every project module
    under Fermat/ (the root aggregator Fermat.lean is excluded — its
    olean does not exist while the sorry gate fails)."""
    out = []
    src_root = os.path.join(ROOT, "Fermat")
    for dirpath, _dirs, files in os.walk(src_root):
        for name in sorted(files):
            if not name.endswith(".lean"):
                continue
            src = os.path.join(dirpath, name)
            rel = os.path.relpath(src, ROOT)[: -len(".lean")]
            mod = rel.replace(os.sep, ".")
            olean = os.path.join(OLEAN_ROOT, rel + ".olean")
            out.append((mod, src, olean))
    return out


_IMPORT_RE = re.compile(
    r"^(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?([A-Za-z_][\w.]*)")


def project_imports(src):
    """Project-internal imports of a module, parsed from its source
    header. Handles every variant in use ('import X', 'public import X',
    'public meta import X', 'import all X'), skips `/- ... -/` block
    comments (tracking nesting — the typical copyright/docstring header
    would otherwise end the scan before the imports), `--` line comments,
    and the header keywords `module`/`prelude`; stops at the first real
    declaration. Imports interleaved with comments or appearing after
    `module` are found."""
    imps = []
    depth = 0  # block-comment nesting depth
    try:
        with open(src, encoding="utf-8") as fh:
            for line in fh:
                s = line.strip()
                if depth > 0:
                    depth += s.count("/-") - s.count("-/")
                    if depth < 0:
                        depth = 0
                    continue
                if not s or s.startswith("--"):
                    continue
                if s.startswith("/-"):
                    depth = s.count("/-") - s.count("-/")
                    if depth < 0:
                        depth = 0
                    continue
                if s == "module" or s == "prelude":
                    continue
                m = _IMPORT_RE.match(s)
                if m:
                    if m.group(1).startswith("Fermat"):
                        imps.append(m.group(1))
                    continue
                # first real declaration ends the header
                break
    except OSError:
        pass
    return imps


def freshness(modules, force_bad=()):
    """Partition project modules; a module is importable only if its
    WHOLE project-internal import closure has oleans (a built olean
    whose transitive import is missing crashes importModules — the
    2026-07-22 daemon crash on a mid-edit module). `force_bad` names
    modules to treat as unbuilt regardless of the olean scan (used for
    modules that failed at import time — an agent's rebuild loop can
    delete/recreate an olean faster than we scan)."""
    have_olean = {}
    src_of = {}
    for mod, src, olean in modules:
        have_olean[mod] = os.path.exists(olean) and mod not in force_bad
        src_of[mod] = src
    # transitive closure of "imports a missing-olean module"
    imports = {mod: [i for i in project_imports(src_of[mod])
                     if i in have_olean] for mod, _s, _o in modules}
    bad = {mod for mod, ok in have_olean.items() if not ok}
    changed = True
    while changed:
        changed = False
        for mod, imps in imports.items():
            if mod not in bad and any(i in bad for i in imps):
                bad.add(mod)
                changed = True
    built, unbuilt, stale = [], [], []
    for mod, src, olean in modules:
        if mod in bad:
            unbuilt.append(mod)
            continue
        built.append((mod, src, olean))
        try:
            if os.path.getmtime(src) > os.path.getmtime(olean):
                stale.append(mod)
        except OSError:
            pass
    return built, unbuilt, stale


def olean_signature(built):
    sig = []
    for mod, _src, olean in built:
        try:
            sig.append((mod, os.path.getmtime(olean)))
        except OSError:
            sig.append((mod, 0.0))
    return tuple(sig)


# ------------------------------------------------------- Lean server file

LEAN_SERVER_BODY = r'''
open Lean

def main : IO Unit := do
  initSearchPath (← findSysroot)
  let env ← importModules (fermatModules.map (fun m => { module := m })) {}
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  let modNames := env.header.moduleNames
  let modData := env.header.moduleData
  let isFermatMod : Name → Bool := fun m => Name.isPrefixOf `Fermat m
  let expandable : Name → Bool := fun n =>
    match env.getModuleIdxFor? n with
    | some i => isFermatMod modNames[i.toNat]!
    | none => false
  let usedOf : Name → Array Name := fun n =>
    match env.find? n with
    | some ci => ci.getUsedConstantsAsSet.toArray
    | none => #[]
  let sorryName : Name := `sorryAx
  IO.println "DAEMON-READY"
  stdout.flush
  let mut done := false
  while !done do
    let line ← stdin.getLine
    if line.trimAscii.isEmpty then
      done := true
    else
      let mut out : Json := Json.null
      match Json.parse line with
      | .error e => out := Json.mkObj [("error", Json.str e)]
      | .ok req =>
        let cmd := (req.getObjValAs? String "cmd").toOption.getD ""
        if cmd == "quit" then
          done := true
        else if cmd == "report" then
          let nameJsons : Array Json :=
            ((req.getObjVal? "names").toOption.bind
              (fun j => j.getArr?.toOption)).getD #[]
          let listedArr : Array Name :=
            nameJsons.filterMap (fun j => j.getStr?.toOption.map String.toName)
          let listed : NameSet :=
            listedArr.foldl (fun s n => s.insert n) {}
          let mut items : Array Json := #[]
          for nm in listedArr do
            match env.find? nm with
            | none =>
              items := items.push (Json.mkObj
                [("name", Json.str nm.toString), ("missing", Json.bool true)])
            | some ci =>
              -- stopped BFS: dependency edges to other tracked names, and
              -- whether a sorry lives in the EXCLUSIVE cone (not behind a
              -- tracked child)
              let mut visited : NameSet := {}
              let mut kids : Array Name := #[]
              let mut own := false
              let mut stack : Array Name := ci.getUsedConstantsAsSet.toArray
              while !stack.isEmpty do
                let c := stack.back!
                stack := stack.pop
                if !(visited.contains c) then
                  visited := visited.insert c
                  if c == sorryName then own := true
                  else if listed.contains c && c != nm then
                    kids := kids.push c
                  else if expandable c then stack := stack ++ usedOf c
              -- full BFS: whole-cone sorry check (the `#print axioms`
              -- criterion, restricted to sorryAx)
              let mut visited2 : NameSet := {}
              let mut dirty := false
              let mut stack2 : Array Name := ci.getUsedConstantsAsSet.toArray
              while !stack2.isEmpty && !dirty do
                let c := stack2.back!
                stack2 := stack2.pop
                if !(visited2.contains c) then
                  visited2 := visited2.insert c
                  if c == sorryName then dirty := true
                  else if expandable c then stack2 := stack2 ++ usedOf c
              items := items.push (Json.mkObj [
                ("name", Json.str nm.toString),
                ("missing", Json.bool false),
                ("own", Json.bool own),
                ("clean", Json.bool (!dirty)),
                ("kids", Json.arr (kids.map (fun k => Json.str k.toString)))])
          out := Json.mkObj [("entries", Json.arr items)]
        else if cmd == "sorries" then
          -- the compiler-verified open-node list: project declarations
          -- whose own proof term uses sorryAx directly (the set the
          -- `declaration uses 'sorry'` warnings mark)
          let mut sorried : Array Json := #[]
          for i in [0:modNames.size] do
            if isFermatMod modNames[i]! then
              for nm in modData[i]!.constNames do
                if !nm.isInternal then
                  match env.find? nm with
                  | some ci =>
                    if ci.getUsedConstantsAsSet.contains sorryName then
                      sorried := sorried.push (Json.mkObj
                        [("name", Json.str nm.toString),
                         ("module", Json.str modNames[i]!.toString)])
                  | none => pure ()
          let rootStr :=
            (req.getObjValAs? String "root").toOption.getD "fermat_last_theorem"
          let mut rootJson := Json.mkObj [("missing", Json.bool true)]
          match env.find? rootStr.toName with
          | none => pure ()
          | some ci =>
            let mut visited : NameSet := {}
            let mut hasSorry := false
            let mut axs : Array Name := #[]
            let mut stack : Array Name := ci.getUsedConstantsAsSet.toArray
            while !stack.isEmpty do
              let c := stack.back!
              stack := stack.pop
              if !(visited.contains c) then
                visited := visited.insert c
                if c == sorryName then hasSorry := true
                else
                  match env.find? c with
                  | some (.axiomInfo _) => axs := axs.push c
                  | some ci' =>
                    if expandable c then
                      stack := stack ++ ci'.getUsedConstantsAsSet.toArray
                  | none => pure ()
            let whitelist : NameSet := ({} : NameSet)
              |>.insert `propext |>.insert `Classical.choice
              |>.insert `Quot.sound
            let bad := axs.filter (fun a => !whitelist.contains a)
            rootJson := Json.mkObj [
              ("missing", Json.bool false),
              ("coneSorry", Json.bool hasSorry),
              ("badAxioms", Json.arr (bad.map (fun a => Json.str a.toString)))]
          out := Json.mkObj [("sorried", Json.arr sorried), ("root", rootJson)]
        else
          out := Json.mkObj [("error", Json.str s!"unknown cmd {cmd}")]
      if !done then
        IO.println out.compress
        stdout.flush
'''


def write_server_lean(built):
    mods = ", ".join(f"`{mod}" for mod, _s, _o in built)
    with open(SERVER_LEAN, "w", encoding="utf-8") as fh:
        fh.write("-- GENERATED by lean-daemon.py; do not edit.\n")
        fh.write("import Lean\n")
        fh.write(f"def fermatModules : Array Lean.Name := #[{mods}]\n")
        fh.write(LEAN_SERVER_BODY)


# ----------------------------------------------------------------- daemon


class Daemon:
    def __init__(self):
        self.child = None
        self.sig = None
        # Modules that crashed importModules (olean vanished between scan
        # and import). Persisted ACROSS ensure_child calls so a failed
        # retry round does not forget its exclusions; pruned per call
        # when the olean reappears (module rebuilt -> re-admit).
        self.force_bad = set()
        # Modules whose last materialization attempt failed to COMPILE,
        # mapped to the fingerprint (source mtime + direct-import olean
        # mtimes) at failure time. Skipped by materialize() until the
        # fingerprint changes (source edited, or an import rebuilt) —
        # so a genuinely broken committed module costs one compile per
        # state, not one per query. Reported as `failed_modules`.
        self.build_failed = {}
        self.log = open(LOG, "a", encoding="utf-8")

    def _log(self, msg):
        self.log.write(f"[{time.strftime('%F %T')}] {msg}\n")
        self.log.flush()

    # ----------------------------------------------- self-materialization

    @staticmethod
    def _fingerprint(mod, src_of, olean_of):
        """Retry key for a failed module: its own source mtime plus the
        olean mtimes of its direct project imports. Changes when the
        module is edited or when a (possibly deep, via the dependents'
        own rebuild cascade) import gets rebuilt."""
        try:
            smt = os.path.getmtime(src_of[mod])
        except OSError:
            smt = 0.0
        imps = []
        for i in project_imports(src_of[mod]):
            if i in olean_of:
                try:
                    imps.append((i, os.path.getmtime(olean_of[i])))
                except OSError:
                    imps.append((i, 0.0))
        return (smt, tuple(sorted(imps)))

    @staticmethod
    def _needs_build(mod, src_of, olean_of):
        """True if the module has no olean or its source is newer."""
        o = olean_of[mod]
        if not os.path.exists(o):
            return True
        try:
            return os.path.getmtime(src_of[mod]) > os.path.getmtime(o)
        except OSError:
            return False

    def _lake_build(self, targets):
        """Targeted incremental build; returns (exit code, output tail)."""
        try:
            res = subprocess.run(
                ["lake", "build"] + targets, cwd=ROOT,
                stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                text=True, timeout=3600)
        except subprocess.TimeoutExpired:
            return 1, "lake build timed out after 3600s"
        except OSError as exc:
            return 1, f"lake could not be invoked: {exc}"
        tail = "\n".join(res.stdout.splitlines()[-15:])
        return res.returncode, tail

    def materialize(self):
        """Self-serve the daemon's input: build the oleans of every
        unbuilt/stale project module (never the root gate) before the
        import, exactly like the language server compiles imports for an
        opened file. A module that fails to compile is remembered in
        self.build_failed (fingerprinted, see above), its dependents are
        skipped via the import closure, and everything else proceeds —
        a broken module degrades only its own subtree, never the run."""
        modules = scan_modules()
        src_of = {m: s for m, s, _o in modules}
        olean_of = {m: o for m, _s, o in modules}
        # forget failures that vanished from the scan, got built by
        # someone else, or whose fingerprint changed (retry those)
        for m in list(self.build_failed):
            if (m not in src_of or not self._needs_build(m, src_of, olean_of)
                    or self.build_failed[m]
                    != self._fingerprint(m, src_of, olean_of)):
                del self.build_failed[m]
        need = [m for m, _s, _o in modules
                if self._needs_build(m, src_of, olean_of)]
        if not need:
            return
        # exclude known-failed modules AND their import-closure
        # dependents (building a dependent would just re-fail the compile
        # of its broken import on every query)
        skip = set(self.build_failed)
        imports = {m: [i for i in project_imports(src_of[m])
                       if i in src_of] for m in src_of}
        changed = True
        while changed:
            changed = False
            for m, imps in imports.items():
                if m not in skip and any(i in skip for i in imps):
                    skip.add(m)
                    changed = True
        targets = [m for m in need if m not in skip]
        if not targets:
            return
        self._log(f"materializing {len(targets)} modules: "
                  + " ".join(targets))
        t0 = time.time()
        code, tail = self._lake_build(targets)
        if code == 0:
            self._log(f"materialized {len(targets)} modules in "
                      f"{time.time() - t0:.1f}s")
            return
        self._log(f"batch materialization failed (exit {code}); "
                  f"attributing per module\n{tail}")
        # Per-module attribution: fresh modules are content-hash free,
        # so only genuinely broken ones (and their dependents, skipped
        # next round via the closure) pay a compile here.
        for mod in targets:
            if not self._needs_build(mod, src_of, olean_of):
                continue
            code, tail = self._lake_build([mod])
            if code != 0 and self._needs_build(mod, src_of, olean_of):
                self.build_failed[mod] = self._fingerprint(
                    mod, src_of, olean_of)
                self._log(f"MATERIALIZATION FAILED for {mod} "
                          f"(exit {code}):\n{tail}")
        ok = [m for m in targets if m not in self.build_failed
              and not self._needs_build(m, src_of, olean_of)]
        self._log(f"materialized {len(ok)}/{len(targets)} modules in "
                  f"{time.time() - t0:.1f}s; failed: "
                  + (" ".join(sorted(self.build_failed)) or "none"))

    def ensure_child(self, retries=5):
        # Oleans can vanish BETWEEN the scan and the import (a parallel
        # agent rebuilding its module deletes the target olean first) —
        # on a startup crash, rescan and retry: the vanished olean is
        # then seen as missing and the import-closure filter drops the
        # module and its dependents.
        last_exc = None
        # Self-serve the input first: build whatever is unbuilt/stale so
        # the import below sees a complete, current environment. Any
        # exception here must not kill the query path — materialization
        # is best-effort; freshness() below re-reads reality either way.
        try:
            self.materialize()
        except Exception as exc:
            self._log(f"materialize step crashed: {exc!r}")
        # Re-admit force_bad modules whose olean has reappeared (the
        # parallel agent finished rebuilding them). Modules failing
        # WITHIN this call's retries are re-added below and stay
        # excluded for the rest of the call even if the olean flickers
        # back mid-round.
        if self.force_bad:
            olean_of = {mod: olean for mod, _s, olean in scan_modules()}
            readmit = {m for m in self.force_bad
                       if os.path.exists(olean_of.get(m, ""))}
            for m in sorted(readmit):
                self._log(f"re-admitting {m}: olean reappeared")
            self.force_bad -= readmit
            # entries whose source vanished entirely drop out of the scan
            self.force_bad &= set(olean_of)
        for _attempt in range(retries):
            modules = scan_modules()
            built, unbuilt, stale = freshness(modules, self.force_bad)
            sig = olean_signature(built)
            if self.child is not None and self.child.poll() is not None:
                self._log("child died; restarting")
                self.child = None
            if self.child is not None and sig != self.sig:
                self._log("olean signature changed; restarting child")
                self.stop_child()
            if self.child is None:
                write_server_lean(built)
                self._log(f"starting child ({len(built)} modules)")
                t0 = time.time()
                errpath = os.path.join(ROOT, ".lean-daemon-child-stderr")
                errfh = open(errpath, "w", encoding="utf-8")
                try:
                    self.child = subprocess.Popen(
                        ["lake", "env", "lean", "--run", SERVER_LEAN],
                        cwd=ROOT,
                        stdin=subprocess.PIPE,
                        stdout=subprocess.PIPE,
                        stderr=errfh,
                        text=True,
                    )
                except Exception:
                    errfh.close()
                    raise
                # wait for the environment to finish importing
                try:
                    while True:
                        line = self.child.stdout.readline()
                        if line == "":
                            raise RuntimeError(
                                "lean child exited during startup; "
                                "see .lean-daemon.log"
                            )
                        if line.strip() == "DAEMON-READY":
                            break
                except Exception as exc:
                    last_exc = exc
                    errfh.close()
                    # reap the dead child (or kill a wedged one) — no
                    # zombie may survive into the next attempt
                    try:
                        self.child.kill()
                    except Exception:
                        pass
                    try:
                        self.child.wait(timeout=10)
                    except Exception:
                        pass
                    self.child = None
                    try:
                        errtxt = open(errpath, encoding="utf-8").read()
                    except OSError:
                        errtxt = ""
                    if errtxt:
                        self.log.write(errtxt)
                        self.log.flush()
                    # a module whose olean vanished at import time gets
                    # excluded — with its dependents, via the import
                    # closure in freshness() — on the next attempt
                    found = re.findall(
                        r"of module (\S+) does not exist", errtxt)
                    for m in found:
                        self.force_bad.add(m)
                        self._log(f"excluding {m} after import failure")
                    if not found:
                        self._log("startup failure without a recognizable "
                                  "missing-olean message; retrying as-is")
                    self._log(f"startup failed (attempt {_attempt + 1}"
                              f"/{retries}); rescanning")
                    time.sleep(2.0)
                    continue
                errfh.close()
                self.sig = sig
                self._log(f"child ready in {time.time() - t0:.1f}s")
            return unbuilt, stale
        raise RuntimeError(
            f"lean child failed to start after {retries} attempts: {last_exc}")

    def stop_child(self):
        if self.child is not None:
            try:
                self.child.stdin.write('{"cmd": "quit"}\n')
                self.child.stdin.flush()
                self.child.wait(timeout=10)
            except Exception:
                # kill AND reap — a bare kill() leaves a zombie
                try:
                    self.child.kill()
                except Exception:
                    pass
                try:
                    self.child.wait(timeout=10)
                except Exception:
                    pass
            self.child = None

    def handle(self, request):
        try:
            unbuilt, stale = self.ensure_child()
        except Exception as exc:
            return {"error": f"daemon could not start lean child: {exc}"}
        try:
            self.child.stdin.write(json.dumps(request) + "\n")
            self.child.stdin.flush()
            line = self.child.stdout.readline()
            if line == "":
                raise RuntimeError("lean child closed its stdout")
            resp = json.loads(line)
        except Exception as exc:
            self._log(f"query failed: {exc}")
            self.stop_child()
            return {"error": f"lean child query failed: {exc}"}
        resp["stale_sources"] = stale
        resp["unbuilt_modules"] = unbuilt
        resp["failed_modules"] = sorted(self.build_failed)
        return resp

    def serve(self):
        try:
            os.unlink(SOCK)
        except OSError:
            pass
        srv = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
        srv.bind(SOCK)
        srv.listen(4)
        self._log("daemon listening")
        while True:
            conn, _ = srv.accept()
            try:
                data = b""
                while not data.endswith(b"\n"):
                    chunk = conn.recv(65536)
                    if not chunk:
                        break
                    data += chunk
                if not data.strip():
                    continue
                request = json.loads(data)
                if request.get("cmd") == "shutdown":
                    conn.sendall(b'{"ok": true}\n')
                    conn.close()
                    break
                resp = self.handle(request)
                conn.sendall((json.dumps(resp) + "\n").encode())
            except Exception as exc:
                self._log(f"connection error: {exc}")
                try:
                    conn.sendall(
                        (json.dumps({"error": str(exc)}) + "\n").encode())
                except Exception:
                    pass
            finally:
                try:
                    conn.close()
                except Exception:
                    pass
        self.stop_child()
        try:
            os.unlink(SOCK)
        except OSError:
            pass
        self._log("daemon stopped")


# ----------------------------------------------------------------- client


def _connect(timeout):
    s = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
    s.settimeout(timeout)
    s.connect(SOCK)
    return s


def query(request, autostart=True, timeout=3600):
    """Send one request to the daemon, autostarting it if needed. The
    first query after a (re)start waits for the full environment import."""
    try:
        s = _connect(timeout)
    except OSError:
        if not autostart:
            raise
        subprocess.Popen(
            [sys.executable, os.path.abspath(__file__), "--serve"],
            cwd=ROOT,
            stdout=subprocess.DEVNULL,
            stderr=subprocess.DEVNULL,
            start_new_session=True,
        )
        deadline = time.time() + 60
        s = None
        while time.time() < deadline:
            try:
                s = _connect(timeout)
                break
            except OSError:
                time.sleep(0.5)
        if s is None:
            raise RuntimeError("could not start lean-daemon")
    with s:
        s.sendall((json.dumps(request) + "\n").encode())
        data = b""
        while not data.endswith(b"\n"):
            chunk = s.recv(65536)
            if not chunk:
                break
            data += chunk
    return json.loads(data)


def main():
    if "--serve" in sys.argv:
        Daemon().serve()
    elif "--stop" in sys.argv:
        try:
            print(json.dumps(query({"cmd": "shutdown"}, autostart=False)))
        except OSError:
            print('{"ok": false, "note": "daemon not running"}')
    elif "--query" in sys.argv:
        req = json.loads(sys.argv[sys.argv.index("--query") + 1])
        print(json.dumps(query(req)))
    else:
        print(__doc__)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
