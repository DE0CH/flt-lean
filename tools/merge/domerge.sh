#!/bin/bash
# release 26 merge driver
export PATH="$HOME/.elan/bin:$PATH"
cd ~/flt-staging || exit 1
for b in "$@"; do
  echo "########## $b"
  git merge --no-commit --no-ff "$b" >/dev/null 2>&1
  files=$(git diff --name-only --diff-filter=U)
  lean=""; other=""
  for f in $files; do case "$f" in *.lean) lean="$lean $f";; *) other="$other $f";; esac; done
  for f in $lean;  do python3 /tmp/semmerge.py "$b" "$f"; done
  for f in $other; do python3 /tmp/resolve.py "$f" >/dev/null; done
  if [ -n "$lean" ]; then
    python3 /tmp/checks.py check-comment $lean
    python3 /tmp/checks.py check-dup $lean
    python3 /tmp/checks.py check-branch "$b" $lean
  fi
  git add -A && git commit --no-edit -m "release 26: merge $b" >/dev/null 2>&1
  echo "   -> $(git diff --stat HEAD^1 HEAD | tail -1)"
done
