## RUN THE `merger` CHECK AS YOUR FIRST ACTION, NOT AS TRIAGE AFTERWARDS

(2026-07-31, `flt-lean-233`, measured.) The FIFTH invisibility class above already gives the
command and already says `merger` is where the answer lives. This is about WHEN to run it.

I was dispatched at three leaves in `ArtinConductor.lean`. I read the file, derived a proof of the
first, and committed it green — and only then ran

    git show merger:Fermat/FLT/Deformations/RepresentationTheory/ArtinConductor.lean | grep -n <name>

which showed **two of the three already PROVEN on `merger` the previous day**, one of them by an
essentially identical argument found independently. The whole run's Lean output had to be reverted
as a rival cut. The check costs one command and five seconds; running it after the work instead of
before cost an agent-run.

So: **before reading the target declaration, grep `merger` for every leaf named in your prompt** —
all of them, not just the one you intend to start with. A queue task is audited against `main` at
release time, and `main` is the frontier as of the last release; a task written a day ago can name
leaves that were closed hours later. Two of three is not an unusual hit rate for a file under
active work.

And when the answer comes back "already proven", the honest deliverable is the DECLINE, made by
you: revert your payload, name your own commit sha so the rival proof stays recoverable, and say
which tiebreak decided it. Leaving both proofs for the merge worker is a guaranteed name collision
on a file it must resolve blind.

