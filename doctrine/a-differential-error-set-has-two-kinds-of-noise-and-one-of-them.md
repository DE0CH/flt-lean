## A DIFFERENTIAL ERROR SET HAS TWO KINDS OF NOISE, AND ONE OF THEM LOOKS LIKE A REGRESSION

(Same release, and it is the practical companion to the "VERIFY DIFFERENTIALLY"
section above.)  Keying errors on `(column, message)` and diffing multisets works,
and the report is not clean even when the edit is:

* **`?_uniq.NNNNNNN` metavariable ids are a global counter.**  One edit anywhere
  shifts every later one, so a single unchanged error shows up as one GONE and one
  NEW with different digits.  Truncate the message before the id, or read the pair
  as cancelling.
* **A repair can TRADE one error for another at the same site** and that is
  progress, not a wash.  My first `genY_classify` fix replaced two
  `Fields missing` errors with one `Type mismatch` at the same declaration —
  i.e. the field was accepted and only my derivation of it was wrong, which is
  what told me the named bridge `IsX0CurveModel.classify_genericOpen` was the
  thing to reach for.  A raw count would have called that "one fixed, one
  introduced".

Read the GONE list against what you intended to fix, name by name, before
believing either total.

