module
public import Fermat.FLT.FreyCurve.MazurTorsion
@[expose] public section
example {M : Type} [AddCommGroup M] (f : AddMonoid.End M) (n : ℕ) (P : M) :
    (f * f + (n : AddMonoid.End M)) P = f (f P) + n • P := by
  show (f * f) P + (n : AddMonoid.End M) P = _
  congr 1
