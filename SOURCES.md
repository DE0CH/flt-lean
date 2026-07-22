# Downloaded reference sources

Sources live in `sources/` at the repo root (gitignored — large
binaries stay out of git; re-obtain as described below if lost).
Populated 2026-07-22 on the shared-terminal machine.

## Present in `sources/`

- `silverman2009aec.txt` — Silverman, *The Arithmetic of Elliptic
  Curves*, 2nd ed. (GTM 106). Clean text edition. §III.8 = the Weil
  pairing (for `hleg1`–`hleg6`), §III.8 computing + X.5 etc.
  (Anna's md5 `ac908404c6fa0dac1120192cebf9d8ca`.)
- `silverman1994ataec.djvu` / `.txt` — Silverman, *Advanced Topics in
  the Arithmetic of Elliptic Curves* (GTM 151; Tate curve /
  uniformization). Recovered from the dissertation repo's git history
  (`~/dissertation`, commit `b4452f8`, `Books/silverman1994ataec.*`).
- `diamondshurman2005mf.pdf` / `.txt` — Diamond–Shurman, *A First
  Course in Modular Forms* (GTM 228). Clean text layer.
  (md5 `7ea26e0fc15cbaf820da12b47edc76c7`.)
- `css1997mfflt.pdf` / `.txt` — Cornell–Silverman–Stevens, *Modular
  Forms and Fermat's Last Theorem*. Scanned; OCR-quality text layer —
  formulas are rough, re-OCR specific chapters if needed.
  (md5 `33324a29860440c9c73fc031eda45746`.)
- `neukirch1999ant.pdf` / `.txt` — Neukirch, *Algebraic Number
  Theory* (Grundlehren 322). Clean text layer.
  (md5 `6f69e8276623e871b9bad9779ed3e075`.)
- `mazur1977eisenstein.pdf` — Mazur, *Modular curves and the
  Eisenstein ideal*, Publ. IHÉS 47. Open access from Numdam
  (`PMIHES_1977__47__33_0.pdf`). Has a text layer from Numdam.
- `mazur1978isogenies.pdf` / `-ocr.pdf` / `.txt` — Mazur, *Rational
  isogenies of prime degree*, Invent. Math. 44. From GDZ Göttingen
  (`PPN356556735_0044`, `LOG_0015`); scan OCR'd locally (eng).
- `duke54-1-1987.pdf` — full scanned issue Duke Math. J. 54(1), 1987.
  (md5 `7ac9e26e01bd4c3709d0a3246a20c912`.) Journal page = PDF page − 6.
- `serre1987duke.pdf` / `-ocr.pdf` / `.txt` — Serre, *Sur les
  représentations modulaires de degré 2 de Gal(Q̄/Q)*, Duke 54 (1987)
  179–230 (§4.1 = Frey-curve conditions). Pages 185–236 of the issue
  scan, OCR'd locally (fra+eng).

## Other reference material

- `~/cs/FLT` — the reference Lean FLT project (same mathlib pin),
  mined for vendorable sorry-free material. Shallow clone
  (depth 50) on this machine; deepen with `git fetch --unshallow`
  if history is needed.
- `~/dissertation` — the pre-split dissertation repo checkout; its
  git history contains the FLT work pre-split plus
  `Books/silverman1994ataec.*`. Other Books/ belong to the
  W*-category dissertation, not this project.

## Re-downloading

Use the Anna's Archive MCP / CLI (`annas-mcp.py`; key in `.env`,
loaded via `.mcp.json` or `set -a; source .env`). Quota counts
distinct md5s per day; same-md5 mirror retries are free. On a TLS
error retry the same md5 with a different `--domain-index` (index 2
worked reliably here); keep certificate verification ON. OCR without
docker: `ocrmypdf` in `.venv` + system tesseract
(`TESSDATA_PREFIX=~/.local/share/tessdata` has eng+fra+osd).
