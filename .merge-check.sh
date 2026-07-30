#!/bin/bash
# Post-merge audit for one merge commit. Usage: .merge-check.sh <branch>
# Checks: (1) payload non-empty (class six: dropped payload),
#         (2) names declared on the branch but absent from the resolved tree
#             yet still referenced (class seven: interface split).
set -u
B="$1"
cd /home/chend/flt-staging || exit 2

DECLRE='^(?:@\[[^]]*\]\s*)?(?:private |protected |noncomputable |partial )*(?:theorem|lemma|def|abbrev|instance|structure|inductive|class) \K[A-Za-z_][A-Za-z0-9_'"'"'.]*'

echo "--- payload (HEAD^1 -> HEAD) ---"
git diff --stat HEAD^1 HEAD | tail -5
n=$(git diff --name-only HEAD^1 HEAD | wc -l)
mb=$(git merge-base HEAD^1 HEAD^2)
bf=$(git diff --name-only "$mb" HEAD^2 | wc -l)
if [ "$n" -eq 0 ] && [ "$bf" -ne 0 ]; then
  echo "!!! DROPPED PAYLOAD: branch changed $bf files, merge carried 0"
  exit 1
fi

echo "--- class-seven: branch-declared names missing from resolved tree ---"
miss=0
for f in $(git diff --name-only "$mb" HEAD^2 | grep '\.lean$'); do
  [ -f "$f" ] || continue
  git show "HEAD^2:$f" 2>/dev/null | sed 's/\.{[^}]*}//' \
    | grep -oP "$DECLRE" | sort -u > /tmp/mc_b.txt
  sed 's/\.{[^}]*}//' "$f" | grep -oP "$DECLRE" | sort -u > /tmp/mc_r.txt
  for name in $(comm -23 /tmp/mc_b.txt /tmp/mc_r.txt); do
    # is the vanished name still referenced anywhere in the tree (comments stripped)?
    refs=$(grep -rlF "$name" --include=*.lean Fermat/ 2>/dev/null | wc -l)
    if [ "$refs" -gt 0 ]; then
      echo "  MISSING-BUT-REFERENCED: $name  (declared on $B in $f, referenced in $refs file(s))"
      miss=1
    else
      echo "  dropped, unreferenced (ok): $name  [$f]"
    fi
  done
done
[ "$miss" -eq 0 ] && echo "  (none referenced)"
echo "--- conflict markers in tree ---"
git grep -c '^<<<<<<<\|^>>>>>>>\|^|||||||' -- '*.lean' | head || echo "  none"
