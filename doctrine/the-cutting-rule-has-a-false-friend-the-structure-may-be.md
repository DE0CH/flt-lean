## THE CUTTING RULE HAS A FALSE FRIEND: the structure may be supplying a NUMBER
(2026-07-31, `X0.lean`.) The discriminator this file gives for a good cut — *the residual
statement stops mentioning the project's own vocabulary* — is right, and it has one failure
mode that produces a FALSE leaf while looking like the textbook application of the rule.
**Deleting the structure from a statement can delete a NUMERICAL constraint that no
hypothesis then expresses.**
Cutting `IsRelPicZeroOf.exists_flatSurj_ajListSum` leaves the divisor half: fppf-locally,
`L ⊗ ⊗ᵢ𝒪(−yᵢ) ∼ 𝒪(−o)^{⊗d}` with `d = #{yᵢ}`. For `L = P.sheaf p` that is relative
Riemann–Roch and TRUE. Generalised to *an arbitrary invertible `L`* — which is exactly what
the rule seems to ask for, since it deletes `P` — it is **FALSE**, in one line: over
`S = T = Spec k` with `deg L = m`, the `RelPicEquiv` twist `π^*N` has fibre degree `0`, so
comparing degrees gives `m − d = −d`, i.e. `m = 0`. `P` was the only object in scope carrying
"relative degree zero", and this pin has no degree theory in which to state it as a hypothesis.
**The check is mechanical and costs a minute: read a numerical invariant off both sides of the
conclusion** — fibre degree, rank, list length, dimension — and ask whether the generalised
hypotheses still force it to balance. The tell here was a repeated `l.length`: it counted the
sections AND the copies of `𝒪(−o)`. Relaxing those to two independent numbers restores truth
for arbitrary `L` and destroys usefulness, because the assembly's induction produces equal
lengths by construction and can no longer close.
So the seam to prefer is not "delete the structure" but **"delete the parts of the structure the
residual proof does not use"** — here the group law, `aj` and `inj` all went and only `P.sheaf`
stayed, which is a real cut by any measure. And write the refutation of the tempting
generalisation into the leaf's docstring: it is the only thing that stops the next agent from
"simplifying" the statement into a false one.
Throughput note from the same task, because it is the difference between one iteration and
twenty: to develop against a leaf inside an 80k-line module, **import that module's PARENT and
hand-copy the two or three declarations from the module itself that your proof names.**
`lake build …ModularCurve.X0` is ~40 minutes; a scratch importing `RelativePicard` plus inlined
copies of `IsSmoothProperCurve` and `AbelianSchemeStruct.listSum` verified the whole 130-line
development in **90 seconds**, first try, and transplanted unchanged. Also: a
`setsid nohup` build survives the session teardowns that kill every `run_in_background` waiter,
so launch the build detached and the waiter separately.
