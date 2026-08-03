## AN "AXIS NOT AVAILABLE BECAUSE THE CONSUMER NEEDS X" CLAIM IS REFUTABLE BY A COMPILE
(Same run, and it is the cheapest audit in this file.) An `AXES SEARCHED` paragraph that
rules an axis out **on the strength of what a consumer needs** is not a mathematical claim at
all — it is a claim about a proof that is sitting in the same file, and it can be settled in
ten minutes instead of argued about.
This leaf's read: *"the BIJECTION-vs-INJECTION axis is NOT available here … the consumer needs
only an injection, but an injection of GEOMETRIC points would not let the degree-one points be
separated, since two distinct cusps of the same degree are distinguished only by the fibre
structure a bijection records."* Plausible, specific, and FALSE: the consumer separates two
cusps with `Subtype.ext (congrArg Sigma.fst (Φ.injective (Subtype.ext hab)))`, which is
`Function.Injective Φ` and nothing else.
**The check: restate the CONSUMER in a scratch, with the weakened form of the leaf as an
explicit hypothesis, and elaborate it.** If it compiles, the axis is available. Do not read
the proof and reason about it — a proof that "uses the `Equiv`" is exactly what an injection
also provides, and that is the confusion the claim was built on.
**Then decide, and record the decision rather than the option.** I did not take the axis:
surjectivity here is "the model has no cusps beyond `Γ_1(N)∖ℙ¹(ℚ)`", which falls out of the
same Deligne–Rapoport construction as injectivity, so weakening buys a successor almost
nothing and gives up the form a future exact count would need. That is a judgement, so the
docstring says what would reverse it — *a successor who finds the completeness half genuinely
separable should weaken the `≃` to `Function.Injective`; every consumer compiles unchanged.*
An axis paragraph that records a checked-and-declined option is worth more than one that
records a wrong reason for never checking.
