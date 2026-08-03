## `declaration uses \`sorry\`` IS SPELLED WITH BACKTICKS AT THIS TOOLCHAIN
(Same run, and it cost one confused minute that could have been an hour.) The warning Lean emits
is
    warning: Fermat/.../Family.lean:4312:8: declaration uses `sorry`
with BACKTICKS, not the `'sorry'` this file and a dozen docstrings quote. So the hand check every
agent reaches for —
    grep -c "declaration uses 'sorry'" /tmp/build.log      # returns 0 on a log full of them
— returns **zero**, which reads exactly like "no open leaves in this module" and is the most
confident possible wrong answer. `flt-buildfrontier.py` is safe (its regex is
`declaration uses .sorry.`), but nothing else that greps by hand is. Match `declaration uses` and
stop there, or use the dot.
