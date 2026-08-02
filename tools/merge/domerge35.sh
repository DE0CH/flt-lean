#!/bin/bash
# release 35 merge driver.  Same shape as release 29's, plus:
#   * a RECEIPT COMMIT for every branch, --allow-empty, so ancestry is recorded
#     even when the payload turns out already present or is declined;
#   * per-branch log files under /tmp/r35/logs so a 341-branch run is auditable.
export PATH="$HOME/.elan/bin:$PATH"
cd ~/flt-staging || exit 1
T=tools/merge
mkdir -p /tmp/r35/logs
for b in "$@"; do
  L=/tmp/r35/logs/$b.log
  echo "########## $b" | tee "$L"
  before=$(git rev-parse HEAD)
  git merge --no-commit --no-ff "$b" >>"$L" 2>&1
  files=$(git diff --name-only --diff-filter=U)
  lean=""; other=""
  for f in $files; do case "$f" in *.lean) lean="$lean $f";; *) other="$other $f";; esac; done
  if [ -n "$lean" ];  then for f in $lean; do echo "  --- semmerge $f" >>"$L"; python3 $T/semmerge.py "$b" "$f" >>"$L" 2>&1; done; fi
  if [ -n "$other" ]; then python3 $T/resolve_text.py $other >>"$L" 2>&1 && git add $other; fi
  if [ -n "$lean" ]; then git add $lean; fi
  rest=$(git diff --name-only --diff-filter=U)
  if [ -n "$rest" ]; then echo "  !! UNRESOLVED: $rest" | tee -a "$L"; fi
  if [ -n "$lean" ]; then
    python3 $T/checks.py check-comment $lean >>"$L" 2>&1
    python3 $T/checks.py check-dup $lean >>"$L" 2>&1
    python3 $T/checks.py check-branch "$b" $lean >>"$L" 2>&1
  fi
  git add -A
  git commit --no-edit --allow-empty -m "release 35: merge $b" >>"$L" 2>&1
  after=$(git rev-parse HEAD)
  if [ "$before" = "$after" ]; then
    echo "  -> NO COMMIT MADE" | tee -a "$L"
  else
    st=$(git diff --stat HEAD^1 HEAD | tail -1)
    [ -z "$st" ] && st="EMPTY-PAYLOAD"
    echo "  -> $st" | tee -a "$L"
  fi
  # a branch that is still not an ancestor means the merge did not record it
  git merge-base --is-ancestor "$b" HEAD || echo "  !! NOT ANCESTOR: $b" | tee -a "$L"
done
