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
  (md5 `6f69e8276623e871b9bad9779ed3e075`.) NOTE: Neukirch proves the
  global reciprocity law COHOMOLOGICALLY (VI §5, via local CFT + the
  class field axiom for idele classes); for **Artin's own proof**
  (Artin's Lemma and the cyclotomic descent) use Childress below.
- `childress2009cft.pdf` / `.txt` — Childress, *Class Field Theory*
  (Universitext, Springer 2009). Clean text layer. The classical,
  ideal-theoretic proof of Artin Reciprocity: Theorem 5.2.1 (statement,
  with clause (ii) — the modulus may be taken divisible only by the
  ramified primes), Proposition 5.2.2 (`ker A ⊆ P⁺·N`), Lemmas
  5.2.3–5.2.7 (Van der Waerden's auxiliary-prime lemmas), Lemma 5.2.8
  (**Artin's Lemma**), and ch. 5 §1 p. 107 (the conductor is not
  divisible by any unramified prime). This is the reference cited by the
  reciprocity leaves in `ModThree.lean`.
  (md5 `3900c4cf249e1bd00b326f4632dfb02f`; downloaded 2026-07-26 —
  domain_index 0 gave a self-signed-certificate TLS error, index 2
  worked.)
- `katzmazur1985ameq.pdf` — Katz & Mazur, *Arithmetic Moduli of
  Elliptic Curves*, Annals of Math. Studies 108 (1985).  (md5
  `62957af02d03e4ff13459c92e05cda93`; downloaded 2026-07-27 —
  domain_index 0 gave a self-signed-certificate TLS error and index 1
  returned a non-https URL, index 2 worked.)  **No text layer**, and it
  is a 2-up scan: 263 PDF pages for a ~520-page book, so
  `pdftotext` returns 263 bytes of nothing.  OCR page by page with
  `pdftoppm -r 200 -png -f A -l B … && tesseract` — `ocrmypdf`/docker are
  not available on this host, but `tesseract` is.  **Page map**: book page
  `P` ≈ PDF page `6.5 + P/2`; the front matter runs i–xiv over PDF pages
  1–6.  Sections consumed so far: 4.7 (PDF 64), 5.1 (PDF 70), 5.2
  (PDF 71), 6.6 (PDF 89), 8.1 (PDF 118).
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

- `schmidt1976eqff.djvu` / `.txt` — W. M. Schmidt, *Equations over
  Finite Fields: An Elementary Approach*, Lecture Notes in Mathematics
  536 (Springer, 1976). md5 `98e627e92286763bc7e9e4a116453457`,
  fetched with `domain_index: 2` (indices 0 and 1 gave a self-signed
  cert chain and an `http://` URL respectively). Text extracted with
  `djvutxt` — clean, no OCR needed.

  This is the reference for the **Stepanov–Bombieri route** to the Weil
  bound in `Modularity/KhareWintenberger.lean` (the Lang–Weil subtree
  under `exists_bound_forall_zmodSolvable_of_irreducibleFibre`).
  Chapter III §§1–6 is all that item 2 needs — §§7 ff. exist only to
  remove the restriction to prime `q`, which this development never
  needs. Chapter V is the plane-curve → hypersurface step and Chapter
  VI §7 the induction on dimension. Landmarks in the extracted text:
  III §1 Reduction ≈ line 3160, (4.3)/(4.5) ≈ 3300, Lemma 4A ≈ 3541,
  Lemma 5A ≈ 3689, §6 ≈ 3751; V Thm 4C ≈ 6639, Thm 5A ≈ 6709;
  VI Thm 7A / Lemmas 7B, 7C ≈ 8157.

  (Downloaded 2026-07-27. A task prompt of that date asserted the book
  was already here and told agents to check this file before
  re-downloading — it was not, and this entry is what that check
  should have found.)

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
