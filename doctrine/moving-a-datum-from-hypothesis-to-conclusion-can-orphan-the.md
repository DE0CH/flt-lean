## MOVING A DATUM FROM HYPOTHESIS TO CONCLUSION CAN ORPHAN THE SUBTREE THAT PRODUCED IT — PASS THE **EXISTENTIAL**, NOT THE WITNESS

(2026-07-31, same repair.) The obvious way to make a leaf produce its datum is to give it
the raw nonemptiness witness `(𝒟₀ : AuxDeformationDatum …)` and delete the consumer's call
to the theorem that used to build the weakly universal one. That call was the ONLY thing
keeping `exists_isWeaklyUniversal_auxDeformationDatum` — and the whole Schlessinger clause
subtree beneath it — in the root's used-constant cone, and **a sorried body contributes no
dependency edges**, so the leaf's intended proof does not hold it there. The change would
have silently made a large proven subtree free-floating.

The fix costs one character of design: hand the leaf the EXISTENTIAL

    hwu : ∃ 𝒟 : AuxDeformationDatum … , 𝒟.IsWeaklyUniversal

which the consumer discharges with the same call it already made. The leaf still chooses
its own datum, and the producer stays in the cone. **Any time a repair deletes a call from
a proven proof, ask what else that call was holding up.**

