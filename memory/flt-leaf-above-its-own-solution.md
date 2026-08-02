---
name: flt-leaf-above-its-own-solution
description: "A leaf declared above the theorem that would close it acquires a permanent \"missing mathematics\" verdict; grep its docstring's cited names and compare LINE NUMBERS."
metadata: 
  node_type: memory
  type: project
  originSessionId: ab11faf7-7d5a-4e47-8ce3-599d46d18322
  modified: 2026-08-01T23:14:13.670Z
---

A `sorry` leaf declared ABOVE the theorem that closes it cannot be closed where
it stands, so every prover reads its (correct, dated) "this is the ONE genuinely
missing piece of mathematics" verdict, confirms the tree still lacks the theory
it names, and correctly moves on. The verdict then hardens.

Instance (2026-08-01, flt-lean-389): `det_nTorsion_eq_cyclotomicExponent` in
`Modularity/MoretBailly.lean` sat 78 lines ABOVE `exists_weilPairing_mu_charZero`,
which became PROVEN a few hours after the leaf was cut. With the pairing in hand
the leaf is the discrete-logarithm proof of `det_nTorsion_eq_neg_one_of_conj_inv`
below it with `−1` replaced by `c`. Relocating the leaf DOWN past the pairing and
pasting that proof closed it first try, 9 s in a scratch.

**Why:** the leaf's docstring cites names. Grep each cited name's `^theorem`
line and compare with the leaf's own line. A PROVEN name BELOW you is why the
leaf is open — not the mathematics.

**Related:** a decline that reasons "doing this would orphan X" is indexed to a
leaf's STATUS, not its statement, and inverts the moment that leaf is proven by
the route in question. Re-read every such decline when anything in its chain
closes. See [[flt-declaration-order-leaves]], [[flt-cycle-verdict-expires]],
[[flt-audit-scoped-to-declaration-it-read]].
