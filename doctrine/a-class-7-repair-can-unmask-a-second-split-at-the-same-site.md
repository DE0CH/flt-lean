# A class-7 repair can UNMASK a second split at the same site — budget a round per layer

(Release 36, 2026-08-03, `HyperellipticJacobian.lean`.) A call of
`vanishesAt_or_of_mul` that predated the lemma's new `0 ≤ ord` hypotheses
failed inside `exists_pt_of_ord_pos`; once that argument-drift was repaired,
the SAME proofs errored again — their closing steps referenced
`eq_pt_affine_of_chart` / `eq_pt_infinite_of_chart`, declared 6 600 lines
BELOW. The first failure had aborted elaboration of the tactic block, so the
declaration-order split behind it produced no diagnostic at all in rounds 1–2.

This composes with the release-35 lesson that `maxErrors` caps the list: not
only can errors hide BEHIND the cap and BELOW the failing module, they can
hide INSIDE an already-reported failing proof. One broken declaration can
carry one damage layer per proof step. So after repairing an error inside a
proof body, re-read the WHOLE body against the current tree — grep every
identifier it uses for its declaration line — instead of rebuilding on hope.

Second lesson, same site: the file carried TWO PROVEN rival uniqueness pairs —
`eq_pt_{affine,infinite}_of_chartValue` (ord_injective route, hsep-free at
infinity) and `eq_pt_{affine,infinite}_of_chart` (eq_of_ord_nonneg_imp route)
— same statements up to binder order, different names, both landed by the
merge. The consumers sat above BOTH copies. Repair: move the pair whose
dependency cone is entirely above the consumers (the chartValue pair), and
retarget; the loser pair (`eq_pt_affine_of_chart`, `eq_pt_infinite_of_chart`,
plus its private suppliers `eq_of_ord_nonneg_imp`, `ord_nonneg_of_localDenom`)
is left consumerless and queued for deletion rather than deleted mid-release —
a proven orphan cannot turn the build red, and every extra build round during
a release costs the whole fleet dispatch time.
