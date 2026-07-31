#!/bin/bash
# release 29 merge driver.  Same shape as release 26's domerge.sh, but pointing
# at the COMMITTED tools rather than /tmp copies, and recording a receipt for
# every branch (a merge or a deliberate decline) so nothing comes back next
# release for want of ancestry.
export PATH="$HOME/.elan/bin:$PATH"
cd ~/flt-staging || exit 1
T=tools/merge
for b in "$@"; do
  echo "########## $b"
  before=$(git rev-parse HEAD)
  git merge --no-commit --no-ff "$b" >/tmp/mergeout.txt 2>&1
  files=$(git diff --name-only --diff-filter=U)
  lean=""; other=""
  for f in $files; do case "$f" in *.lean) lean="$lean $f";; *) other="$other $f";; esac; done
  if [ -n "$lean" ];  then for f in $lean; do echo "  --- semmerge $f"; python3 $T/semmerge.py "$b" "$f"; done; fi
  if [ -n "$other" ]; then python3 $T/resolve_text.py $other && git add $other; fi
  if [ -n "$lean" ]; then git add $lean; fi
  # anything still unmerged (deletes, renames) -> report; the resolvers write the
  # working tree only, so this must be read AFTER the git add above or every
  # successfully-resolved file reports as unresolved.
  rest=$(git diff --name-only --diff-filter=U)
  if [ -n "$rest" ]; then echo "  !! UNRESOLVED: $rest"; fi
  if [ -n "$lean" ]; then
    python3 $T/checks.py check-comment $lean
    python3 $T/checks.py check-dup $lean
    python3 $T/checks.py check-branch "$b" $lean
  fi
  git add -A && git commit --no-edit -m "release 29: merge $b" >/dev/null 2>&1
  after=$(git rev-parse HEAD)
  if [ "$before" = "$after" ]; then
    echo "  -> NO COMMIT MADE (already up to date, or commit failed)"
  else
    echo "  -> $(git diff --stat HEAD^1 HEAD | tail -1)"
  fi
done
