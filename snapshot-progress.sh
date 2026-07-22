#!/usr/bin/env bash
# snapshot-progress.sh — regenerate PROGRESS.md / progress-tree.json from the
# COMMITTED state, inside the secondary worktree /home/chend/flt-lean-snapshot,
# so uncommitted agent edits in the main worktree never pollute the tree.
#
# Contract (idempotent):
#   1. advance the snapshot worktree to main's current HEAD (detached).  The
#      snapshot is a LINKED worktree sharing main's object store, so the commit
#      is directly reachable — no fetch needed.  Main's own checkout is never
#      touched (all git commands run with -C $SNAP).
#   2. lake-build the tracked module set there — derived from the snapshot's
#      progress-entries.json — EXCLUDING the root gate module `Fermat`
#      (whose #assert_no_sorry fails by design mid-project).  lake keys on
#      content hashes, so this build is genuinely incremental.  A build
#      FAILURE degrades to a warning: a broken module keeps its previous
#      olean and is flagged stale by the daemon; progress-tree.py's own
#      missing-entry guard is the gate that decides publishability.
#   3. run the SNAPSHOT's progress-tree.py.  Its lean-daemon roots itself at
#      its own file's directory, so the snapshot daemon binds
#      $SNAP/.lean-daemon.sock — fully separate from main's daemon socket.
#   4. on success copy PROGRESS.md + progress-tree.json back into the main
#      worktree and print ONE summary line (commit + generator stats);
#      on any failure leave main untouched and exit nonzero.
set -euo pipefail

MAIN=/home/chend/flt-lean
SNAP=/home/chend/flt-lean-snapshot

# single-flight guard: concurrent runs would race on the worktree checkout
exec 9>"$SNAP/.snapshot.lock"
flock -n 9 || { echo "snapshot-progress: another run holds $SNAP/.snapshot.lock" >&2; exit 1; }

HEAD=$(git -C "$MAIN" rev-parse HEAD)

# -- 1. advance the snapshot ------------------------------------------------
# --force: the previous run's regenerated PROGRESS.md / progress-tree.json
# legitimately dirty the snapshot worktree; discard and re-derive.
git -C "$SNAP" checkout --detach --force "$HEAD" >&2
ACTUAL=$(git -C "$SNAP" rev-parse HEAD)
if [ "$ACTUAL" != "$HEAD" ]; then
  echo "snapshot-progress: snapshot HEAD $ACTUAL != main HEAD $HEAD after checkout" >&2
  exit 1
fi

# -- 2. build the tracked module set (root gate excluded) -------------------
mapfile -t MODULES < <(python3 - "$SNAP" <<'PYEOF'
import json, sys
snap = sys.argv[1]
entries = json.load(open(f"{snap}/progress-entries.json"))
mods = sorted({e["module"] for e in entries if e.get("module")})
for m in mods:
    if m != "Fermat":            # never the root gate module
        print(m)
PYEOF
)
if [ "${#MODULES[@]}" -eq 0 ]; then
  echo "snapshot-progress: no tracked modules derived from progress-entries.json" >&2
  exit 1
fi

# 9>&-: do NOT leak the lock fd into lake's children — an orphaned lean
# process from a killed run would otherwise hold the lock indefinitely.
BUILD_STATE=ok
( cd "$SNAP" && lake build "${MODULES[@]}" ) 9>&- || {
  BUILD_STATE=DEGRADED
  echo "snapshot-progress: WARNING — lake build of tracked modules failed;" \
       "broken modules keep their last-built olean (daemon flags them stale)." \
       "Continuing; progress-tree.py's missing-entry guard decides" \
       "publishability." >&2
}

# -- 3. regenerate the tree in the snapshot ---------------------------------
SUMMARY=$( cd "$SNAP" && python3 progress-tree.py 9>&- ) || {
  echo "snapshot-progress: progress-tree.py FAILED — main untouched" >&2
  exit 1
}

# -- 4. publish back to main ------------------------------------------------
cp "$SNAP/PROGRESS.md" "$MAIN/PROGRESS.md"
cp "$SNAP/progress-tree.json" "$MAIN/progress-tree.json"

echo "snapshot-progress: commit ${HEAD:0:12} [build $BUILD_STATE] — $SUMMARY"
