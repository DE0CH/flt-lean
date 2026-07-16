import Fermat.Basic
import Fermat.FLT.FreyCurve.Mazur
import Fermat.FLT.GaloisRepresentation.HardlyRamified.Frey
import Fermat.FLT.GaloisRepresentation.HardlyRamified.Defs
import Fermat.FLT.GaloisRepresentation.HardlyRamified.Threeadic
import Fermat.FLT.GaloisRepresentation.Chebotarev
import Fermat.FLT.GaloisRepresentation.BrauerNesbitt
import Fermat.FLT.EllipticCurve.TorsionCard
import Fermat.FLT.KnownIn1980s.EllipticCurves.GoodReduction
import Fermat.FLT.KnownIn1980s.EllipticCurves.Flat
import Fermat.SorryGate

/-!
The sorry gate (see `Fermat/SorryGate.lean`): this root module FAILS to
compile while any node of the dependency tree is open, so `lake build`
reports an error — the signal to continue the loop — until
`fermat_last_theorem` is sorry-free with the standard axioms only.
-/

#assert_no_sorry fermat_last_theorem
