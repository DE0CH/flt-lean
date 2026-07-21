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
  unbuilt_modules  modules with no .olean at all (excluded from imports).
"""

import json
import os
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


def freshness(modules):
    built, unbuilt, stale = [], [], []
    for mod, src, olean in modules:
        if not os.path.exists(olean):
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
        self.log = open(LOG, "a", encoding="utf-8")

    def _log(self, msg):
        self.log.write(f"[{time.strftime('%F %T')}] {msg}\n")
        self.log.flush()

    def ensure_child(self):
        modules = scan_modules()
        built, unbuilt, stale = freshness(modules)
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
            self.child = subprocess.Popen(
                ["lake", "env", "lean", "--run", SERVER_LEAN],
                cwd=ROOT,
                stdin=subprocess.PIPE,
                stdout=subprocess.PIPE,
                stderr=self.log,
                text=True,
            )
            # wait for the environment to finish importing
            while True:
                line = self.child.stdout.readline()
                if line == "":
                    raise RuntimeError(
                        "lean child exited during startup; see .lean-daemon.log"
                    )
                if line.strip() == "DAEMON-READY":
                    break
            self.sig = sig
            self._log(f"child ready in {time.time() - t0:.1f}s")
        return unbuilt, stale

    def stop_child(self):
        if self.child is not None:
            try:
                self.child.stdin.write('{"cmd": "quit"}\n')
                self.child.stdin.flush()
                self.child.wait(timeout=10)
            except Exception:
                self.child.kill()
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
