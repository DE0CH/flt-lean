## TWO `lake build`s IN ONE WORKTREE PRODUCE FAILURES THAT ARE NOT IN ANY SOURCE FILE

(Same run.) `setsid --fork`ing a build and then, minutes later, forking another in the
same worktree leaves both alive writing the same `.olean`s. The symptom is a build that
ends

    Some required targets logged failures:
    - Fermat.FLT.ModularCurve.HyperellipticJacobian
    - Fermat.FLT.Modularity.AmpleSheaf
    error: build failed

with **`grep -c "^error"` equal to zero** — no module-level error text anywhere in the
log — and naming modules you have just verified GREEN individually. It reads as lake
replaying a cached failure, and it is not; it is the other build.

The doctrine's kill rule already says scope by cwd. The prevention is upstream of that:
**before forking a build, check the worktree has none running.**

    for p in $(pgrep -x lean; pgrep -x lake); do
      case "$(readlink /proc/$p/cwd 2>/dev/null)" in /home/chend/flt-lean-N*) echo "$p";; esac
    done

A poll loop that gives up on a timeout does NOT stop the build it was watching, so every
"poll, time out, fork another" cycle adds one. Three were live here at once.

