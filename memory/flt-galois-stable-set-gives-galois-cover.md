---
name: flt-galois-stable-set-gives-galois-cover
description: A leaf about ONE point's non-normal field of definition becomes a leaf about a Galois cover for free, if the point lies in a Γ-stable finite set
metadata:
  type: project
---

A leaf stated about `geomPtField ab y` — the field of definition of a SINGLE
geometric point — looks like it needs a normal-closure argument before any
Galois-theoretic dictionary (`IsGalois` is a hypothesis of every inertia ⟹
unramified ⟹ `q ∤ discr` lemma in this tree) can be applied to it. It does not,
whenever `y` lies in a finite set that `Γ_ℚ` PERMUTES.

Here (`X0.lean`, 2026-07-31) the set was `{z | p·z = ratToGeom P}`, the
`p`-division set of a RATIONAL point. Two facts make it work and both are
already in the file:

* Γ-stability is `galSMul_ratToGeom` — `σ(ratToGeom P) = ratToGeom P` — plus
  `map_nsmul`. It is exactly the rationality of `P`.
* Finiteness is the torsor injection `z ↦ z − y` into `A[p]`, over
  `finite_torsion_geomPt_of_abelianScheme`.

Then `H := ⋂_{z} Stab(z)` is open (finite intersection, each `Stab(z)` contains
a `fixingSubgroup` of a finite extension) and NORMAL (conjugation permutes the
set), and `InfiniteGalois.isOpen_and_normal_iff_finite_and_isGalois` converts
"open and normal" into "finite-dimensional and Galois" in ONE step. The Galois
cover `L = fixedField H` comes out with `L.fixingSubgroup = H` exactly, so a
leaf about a single inertia subgroup at `q` transports to the whole cover for
free, and `NumberField.discr_dvd_discr` carries `q ∤ discr L` down to the
non-normal subfield the consumer actually names.

**Why to look for this shape:** it converted `exists_ramificationSet_geomPtField`
from an opaque discriminant leaf into a purely geometric one
(`exists_inertiaSet_geomPt`, inertia fixes division points) with ~200 lines of
PROVEN Galois bookkeeping in between. See [[flt-two-leaves-may-be-one]] and
[[flt-reduce-to-an-open-leaf-not-a-proof]] for neighbouring moves.

**The enabling half was a HOIST, not a theorem** — see
[[flt-hoist-above-the-consumer-not-a-new-theorem]].
