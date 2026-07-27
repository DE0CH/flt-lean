# Downloaded reference sources

Sources live in `sources/` at the repo root (gitignored — large
binaries stay out of git; re-obtain as described below if lost).
Populated 2026-07-22 on the shared-terminal machine.

**Where they actually are: `/home/chend/flt-lean/sources/` — the MAIN
repo only.** `sources/` is gitignored, so it exists in no worktree:
`ls sources/` from `~/flt-lean-N` returns nothing and that is not
evidence a book is missing. Always read them by absolute path
(`/home/chend/flt-lean/sources/<file>`), and note they live on the
Claude-Code host (mystique), not on the remote build hosts.

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
- `mazur1977eisenstein.pdf` — Mazur, *Modular curves and the
  Eisenstein ideal*, Publ. IHÉS 47. Open access from Numdam
  (`PMIHES_1977__47__33_0.pdf`). Has a text layer from Numdam.
- `mazur1978isogenies.pdf` / `-ocr.pdf` / `.txt` — Mazur, *Rational
  isogenies of prime degree*, Invent. Math. 44. From GDZ Göttingen
  (`PPN356556735_0044`, `LOG_0015`); scan OCR'd locally (eng).
- `oorttate1970.pdf` / `.txt` — Tate–Oort, *Group schemes of prime
  order*, Ann. Sci. ÉNS (4) 3 (1970) 1–21. Open access from Numdam
  (`ASENS_1970_4_3_1_1_0`); clean Numdam text layer.
- `raynaud1974pgroups.pdf` / `.txt` — Raynaud, *Schémas en groupes de
  type (p,…,p)*, Bull. SMF 102 (1974) 241–280. Open access from Numdam
  (`BSMF_1974__102__241_0`); clean Numdam text layer.
  (These two were downloaded 2026-07-25 and were never listed here;
  entries added 2026-07-27 by the agent that noticed. They are the
  references for the finite-flat-group-scheme / prolongation leaves.)
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

### The two moduli-of-elliptic-curves references (added 2026-07-27)

Both were cited by open leaves and neither was present. They are the
references for the whole `X0.lean` / integral-model / cusp cluster —
`exists_cuspResidueIndexing`, `exists_unique_specialFibre_universal`,
`geometricallyConnected_of_gamma0Atlas`, `exists_x0IntegralModel`,
`exists_gamma0AtlasData_pullbackSpecial`.

- `lnm349mfov2.djvu` / `.txt` — the whole volume: *Modular Functions of
  One Variable II*, Springer Lecture Notes in Mathematics **349**
  (Antwerp 1972, ed. Deligne–Kuyk, 1973). 600 djvu pages, embedded OCR
  text layer extracted with `djvutxt`.
  (md5 `07501ea02ad30d618e4258fabb81bcd3`; `domain_index: 0` gave a
  self-signed-certificate TLS error, index 2 worked.)
  **djvu page = printed volume page + 2.** Contains, besides
  Deligne–Rapoport: Deligne, *Formes modulaires et représentations de
  GL(2)* (p. 55); Casselman, *On representations of GL_n and the
  arithmetic of modular curves* (p. 107); Langlands, *Modular forms and
  ℓ-adic representations* (p. 361); Deligne, *Les constantes des
  équations fonctionnelles des fonctions L* (p. 501).

- `delignerapoport1973scme.txt` — **Deligne–Rapoport, *Les schémas de
  modules de courbes elliptiques*** (the article, LNM 349 pp. 143–316),
  re-OCR'd locally from the djvu at 300 dpi with `tesseract -l fra+eng`.
  This is markedly cleaner than the volume's embedded 1970s text layer
  (accents and subscripts survive) — prefer it; `lnm349mfov2.txt` keeps
  the embedded version if you want a second opinion on a garbled formula.
  Page markers are `[[DeRa  LNM349 p. N  |  DeRa-M  |  djvu page K]]`,
  where `DeRa-M` is the article's own running pagination (`M = N − 142`).
  **Grep caveat**: OCR frequently turns the period in a numbered
  statement into a comma (`Construction 5,3`, `6.4,`), so search with
  `grep -E 'Construction 5[.,]3'` rather than a literal dot.
  Landmarks, by LINE in `delignerapoport1973scme.txt`:

  | § | what | line | LNM p. |
  |---|---|---|---|
  | — | Sommaire (full table of contents) | 18 | 144 |
  | I.8 | Schémas grossiers de modules | 935 | 171 |
  | **III.1** | Un théorème de proreprésentabilité; **Thm 1.2** at 1876 | **1868** | 197 |
  | IV.1 | Contractions | 2149 | 205 |
  | IV.2 | Structures de niveau n | 2326 | 209 |
  | IV.3 | Structures de niveau H | 2403 | 211 |
  | IV.5 | Théorie transcendante (rappels) | 2979 | 226 |
  | **IV.5.5** | **Cor. 5.5**: fibres géom. de (3.20.4) connexes en toute caractéristique (5.6 = irréductibles si `p ∤ n`) | **3029** | 227 |
  | IV.6 | Structures de niveau H : étude à l'infini | 3039 | 228 |
  | V | Réduction modulo p | 3263 | 234 |
  | VI | Schémas grossiers de modules | 4613 | 267 |
  | **VI.5** | **L'action de Galois sur les pointes**; Construction 5.3 at 5218 | **5191** | 282 |
  | **VI.6** | Étude de `M_{Γ₀(n)}`; Thm 6.6 = Eichler–Shimura congruence at 5319 | **5220** | 283 |
  | **VI.6.7** | **Prop. 6.7** (H ⊆ GL(2,ℤ/n), K its inverse image) | **5346** | 285 |
  | VI.6.9 | Thm 6.9 + the local equation `(6.9.1) 𝒪[x,y]/(xy−p)` at 5405 | 5386 | 286 |
  | VII.1 | Construction de la courbe de Tate sur ℤ[[q]] | 5564 | 291 |
  | VII.2 | Application : structure à l'infini de `M_H` | 5881 | 298 |

  **For the cusp leaves specifically**: the ℚ-structure of the cusps is
  **VI.5**, not VI.6 — Construction 5.3 (line 5218) states
  `M^∞_H[1/n] = H \ Isom_{ℤ[1/n]}(μ_n × ℤ/n, (ℤ/n)²) / ±U`
  as an isomorphism of *Galois* schemes, which is exactly where the
  residue fields `ℚ(ζ_{gcd(d, N/d)})` and the action `σ_t : a ↦ t⁻¹a`
  come from. VI.6 / VI.6.7 are the `Γ₀(n)` coarse-scheme and
  Eichler–Shimura material. The orbit count itself (one class per
  `d ∣ N`, size `φ(gcd(d, N/d))`) stays in Diamond–Shurman §3.8
  (`diamondshurman2005mf.txt` ≈ line 5630); DR supplies the arithmetic
  half only.

- `katzmazur1985ame.pdf` / `.txt` — **Katz–Mazur, *Arithmetic Moduli of
  Elliptic Curves*, Annals of Mathematics Studies 108** (Princeton,
  1985). (md5 `62957af02d03e4ff13459c92e05cda93`; `domain_index: 0`
  gave the same self-signed-cert TLS error, index 2 worked.)
  The PDF is a **2-up image-only scan**, 263 PDF pages carrying book
  pages 2–515 — `pdftotext` returns 263 *bytes*, i.e. nothing. The
  `.txt` was produced locally: `pdftoppm -r 300 -gray -png`, each page
  split into left/right halves with ImageMagick, then
  `tesseract --psm 6 -l eng`. (Docker is not available on this machine,
  so the `ocrmypdf` recipe in CLAUDE.md cannot be used.)
  Page markers are `[[KM  pdf NNNx  |  book p. N]]`; the mapping is
  **PDF page = ⌊book page / 2⌋ + 6**, half `a` = even book page (left),
  half `b` = odd (right). Landmarks, by LINE in `katzmazur1985ame.txt`:

  | § | what | line | book p. |
  |---|---|---|---|
  | — | Table of contents (full, with page numbers) | 40 | v–viii |
  | 1.1 | Review of relative Cartier divisors | 531 | 3 |
  | 1.4 | Points of "exact order N" and cyclic subgroups | 1018 | 17 |
  | 1.12 | Roots of unity | 2427 | 55 |
  | 2 | Review of elliptic curves | 2692 | 63 |
  | **2.3.1** | **Thm 2.3.1**: `[N] : E → E` finite locally free of rank `N²`; `E[N]` étale-locally `ℤ/N × ℤ/N` when `N` invertible (§2.3 header at 3180) | **3181** | 73 |
  | 2.8 | Pairings | 3668 | 87 |
  | 2.9 | Deformation theory | 3806 | 91 |
  | 5.1 | Regularity: First Main Theorem (5.1.1 at 5156) | 5148 | 129 |
  | 6.1 | Cyclicity: The Main Theorem | 6138 | 152 |
  | 8 | Coarse moduli schemes, cusps, and compactification | 8700 | 224 |
  | **8.1.1** | **Coarse moduli scheme** `M(P) = M(P,𝒮)/G`; Lemma 8.1.2 normality; 8.1.3 classifying map | **8705** | 224 |
  | **8.2** | **The j-line as a coarse moduli scheme** | **8848** | 228 |
  | 8.4 | j-invariant as fine modulus; coarse = fine (!) | 9046 | 234 |
  | 8.6 | Cusps by normalization near infinity; `Cusps(P)` defined at (8.6.3.2), line 9518 | 9469 | 246 |
  | **8.6.8** | **Thm 8.6.8** (R excellent noetherian regular): the compactified coarse moduli scheme | **9640** | 249 |
  | 8.7 | Interlude: the groups `T[N]` and `T` | 9677 | 251 |
  | 8.8 | Relation to the Tate curve | 9973 | 258 |
  | 8.11 | Computation of `Cusps(P)` via the Tate curve; Lemma 8.11.2 at 10266 | 10248 | 266 |
  | 10.6 | Cusp-labels and component-labels | 11166 | 295 |
  | 10.9 | Application to the four basic moduli problems | 11366 | 301 |
  | 13 | Reductions mod p of the basic moduli problems | 14429 | 389 |

  OCR quality is good for prose and section headers and rough on
  displayed formulas (a scanned 1985 typescript). Chapter and section
  numbers survive reliably, so locate by `(8.6.3.2)`-style tags rather
  than by page. If a specific displayed formula matters, re-OCR that
  page from the PDF at higher resolution rather than trusting the `.txt`.
  Chapters 10 and 13 (cusp/component labels, reduction mod p) are the
  other parts this project keeps needing; they are in the same file.

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
worked reliably here); keep certificate verification ON.

**OCR without docker.** `docker` is NOT installed on this machine, so
CLAUDE.md's `jbarlow83/ocrmypdf` recipe cannot run. Use the native
route, which is what produced `katzmazur1985ame.txt` and
`delignerapoport1973scme.txt` (263-page book: 6 min to rasterize,
under 2 min to OCR at `-P 12`):

    # PDF
    pdftoppm -r 300 -gray -png book.pdf p            # -> p-001.png …
    # 2-up scan only: split each page into halves first
    convert p-001.png -crop 50%x100%+0+0   +repage p-001a.png
    convert p-001.png -crop 50%x100%+W/2+0 +repage p-001b.png
    ls p-*.png | xargs -P 12 -n 1 -I{} \
      env TESSDATA_PREFIX=$HOME/.local/share/tessdata \
      tesseract {} {} --psm 6 -l eng

    # DjVu — try `djvutxt` first (embedded layer); re-OCR if it is bad
    ddjvu -format=tiff -page=N -scale=300 book.djvu d-N.tif
    TESSDATA_PREFIX=$HOME/.local/share/tessdata \
      tesseract d-N.tif d-N --psm 6 -l fra+eng

`TESSDATA_PREFIX=~/.local/share/tessdata` has **eng + fra + osd**; the
system `/usr/share/tesseract-ocr/5/tessdata` has only eng+osd, so the
prefix is required for anything French (all of Deligne–Rapoport).
Assemble the per-page `.txt`s in reading order with a page marker per
page — the markers are what make a 19k-line OCR text navigable, and
both new entries above document their marker format. Work in
`/scratch/chend-flt/<name>-ocr/`, not `$HOME` (the rasterized pages of
one book are ~200 MB and the home volume is tight).
