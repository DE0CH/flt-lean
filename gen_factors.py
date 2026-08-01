#!/usr/bin/env python3
"""Regenerate `/tmp/fac-<tag>.txt`, the factorisation of each `H` that `gen_row.factors` reads.

These files used to be produced by hand in a `gp` session and left in `/tmp`, so they
evaporated and `gen_modules.py` could not be re-run at all.  The format is the one
`gen_row.factors` parses: the factor's polynomial (in `x`, one or more lines), then a line
`MULT <e>` giving its multiplicity — which must be `1`, since `H` is squarefree.

The factorisation is only a SEARCH: nothing downstream needs the factors to be irreducible,
only pairwise coprime and to multiply back to `H`, and `gen_factored.generate_row` asserts
exactly that.  So PARI is used here as an untrusted searcher, as the project doctrine
prescribes, and the Lean compiler re-checks the product identity.
"""
import os
import subprocess
import sys

from gen_all import ROWS, extract


def factor_lines(hsrc, q):
    src = " ".join(hsrc.split()).replace("X", "x")
    script = f"""default(parisize, 2000000000);
H = Mod(1,{q}) * ({src});
F = factormod(H, {q});
for (i = 1, matsize(F)[1], print(lift(lift(F[i,1]))); print("MULT ", F[i,2]));
"""
    out = subprocess.run(["gp", "-q"], input=script, capture_output=True,
                         text=True, timeout=1200)
    if out.returncode != 0:
        raise SystemExit("gp failed: " + out.stderr)
    return out.stdout


if __name__ == "__main__":
    dest = sys.argv[1] if len(sys.argv) > 1 else "/tmp"
    for tag, (hname, q, m) in ROWS.items():
        txt = factor_lines(extract(hname), q)
        path = os.path.join(dest, f"fac-{tag}.txt")
        with open(path, "w") as f:
            f.write(txt)
        print(tag, path, txt.count("MULT"), "factors")
