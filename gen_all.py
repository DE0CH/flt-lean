#!/usr/bin/env python3
"""Row table and source extraction for the `MazurNonCMFrobenius` certificate generators.

`SRC` is the module that HOLDS the four `hPoly*`.  They moved out of
`MazurNonCMCertificate.lean` on 2026-07-31 so the per-row certificate modules can see them;
if they move again, this is the one place to change.
"""
import io
import sys

from gen_frobenius import pari_check

SRC = "Fermat/FLT/EllipticCurve/MazurNonCMFrobenius.lean"

#  tag -> (name of `H`, the prime `ℓ`, the exponent `m` in `H ∣ X ^ (ℓ ^ m) - X`)
ROWS = {
    "ElevenA": ("hPolyElevenA", 23, 11),
    "ElevenB": ("hPolyElevenB", 23, 11),
    "SeventeenA": ("hPolySeventeenA", 67, 34),
    "SeventeenB": ("hPolySeventeenB", 67, 34),
}


def extract(name, path=SRC):
    s = open(path).read()
    i = s.index("def " + name + " :")
    j = s.index("\n\n", i)
    return s[i:j].split(":=", 1)[1].strip()


if __name__ == "__main__":
    # `--pari` re-checks every certificate against PARI/GP, independently of the Python
    # arithmetic that generates the Lean.  Two implementations, one answer.
    for tag, (hname, q, m) in ROWS.items():
        k = 2 if q == 67 else None
        out, err = pari_check(extract(hname), q, m, k)
        print(tag, out.replace("\n", " | "))
