## A HELPER WRITTEN FOR THE `ℚ` SIDE WILL BE STATED AT `ℚ`, AND THE `𝔽_p` TWIN CANNOT USE IT
(Same task, and it is the half the task prompt got wrong.) The prompt asserted that the
q-expansion principle's two commutative-algebra lemmas — `isAlgebraic_of_quotient_isMaximal`
and `injective_of_not_isAlgebraic_apply` — were "PROVEN and stated over an ARBITRARY base
field `k`, precisely so this leaf would not have to write them again". They were stated
over **`ℚ`**, in the same file, and no instantiation of a `ℚ`-only statement reaches
`ZMod p`.
The generalisation was free, and the reason is the thing to check: **the only property of
`ℚ` either proof used was that it is JACOBSON**, which mathlib gives every field through
`IsArtinianRing R → IsJacobsonRing R`. So `ℚ` → `{k : Type} [Field k]` is a letter change,
the `ℚ` call site is undisturbed (it instantiates `k := ℚ`), and one declaration now serves
both sides instead of two being kept in step.
So, before transcribing a `ℚ`-side helper for an `𝔽_p` leaf: **grep the proof for where the
base is actually spent.** If every use extracts one named property (Jacobson, perfect,
characteristic zero used only via `(n : k) ≠ 0`, infinite), generalise in place. This is
the same discipline as *FOLLOW THE HYPOTHESIS* below, applied to a base rather than to a
morphism, and it is worth running on any lemma whose docstring says "for an arbitrary field
target" while its binders say otherwise — that mismatch between prose and signature is the
tell, and it was present here.
**And do not believe a task prompt's account of a declaration's SIGNATURE.** A prompt is
written from an intention or from another branch; the signature is two seconds away
(`grep -n "^theorem <name>" -A6`). Same rule as the line-number checksum, one level down.
