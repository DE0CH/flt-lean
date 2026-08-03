## `gp` SCRIPT FILES NEED `{}` AROUND A MULTI-LINE STATEMENT — AND THE FAILURE PRINTS A PLAUSIBLE ANSWER
(Same run, three wasted launches.)  `gp -q file.gp` parses a script
**statement by statement, not expression by expression**, so a `for(...)` whose
body spans lines is a syntax error unless the whole thing is wrapped in braces:
    {
    for(N=601, 1500,
      ...
    );
    }
Without them gp reports `syntax error, unexpected end of file, expecting )-> or
',' or ')'` pointing at the `for(` line, then `... skipping file`, **and then
carries on evaluating the remaining lines with the loop variable UNBOUND** — so
`N` is the polynomial `N`, `mfinit([N,2],0)` fails, and the script still prints
    levels screened: 1
    needing deep check: [N]
which reads as a completed run with one hit.  **A gp screen that reports a
suspiciously small number of levels has probably not looped at all**; require
the progress lines you printed yourself, exactly as a `lake` log requires its
`EXIT=`.
Two smaller ones from the same script.  `polissquarefree` is **not** a function
at this install (2.15.4) — use `poldegree(gcd(cp, deriv(cp))) > 0`; and
`getenv` is not available either, so parameterise a screen by writing the file,
not by exporting variables.
