## COUNT BOTH DIRECTIONS BEFORE DOING DECLARATION-ORDER SURGERY
Same leaf, same day, and it is the reason the leaf was reachable at all. Its docstring
recorded the blockage correctly — "a declaration-order artifact and nothing else",
`exists_gamma0GITPresentationOver_zmod` proves the `p ∤ N` case verbatim ~2300 lines
below — and prescribed the fix as **hoisting the producer UP**: the whole `𝔽_ℓ`
rigidification chain, ~2000 lines, in an 82 000-line concurrently-edited module. Two
successive task prompts repeated that as the plan.
**Moving the CONSUMERS DOWN was six declarations and ~430 lines.** The producer's
dependency cone is usually much larger than the consumer's, so the obvious direction is
usually the expensive one. Count both before cutting; the cheap direction is found by
grepping what sits BETWEEN the two positions and consumes the block (here: nothing — the
furthest-reaching of the six is next used ~700 lines below the destination).
**And a block move can be made SAFE in a contended file, which is what makes this
tractable at all.** Do it with a script that slices line ranges, then verify the result is
a PURE PERMUTATION of the original lines:
    python3 - <<'PY'
    from collections import Counter
    a=Counter(open('/tmp/X0.before').read().split('\n'))
    b=Counter(open('Fermat/.../X0.lean').read().split('\n'))
    print("added:",dict(b-a)); print("removed:",dict(a-b))
    PY
Anything in `removed` is a bug in your slice indices; `added` must contain exactly the
section/`open`/blank lines you meant to insert. That check costs a second and is stronger
than reading the diff, because a 1200-line reordering diff is unreadable. Leave a
breadcrumb at BOTH positions — the old one saying what left and where to, the new one
saying what arrived and why — since the next reader of either site will otherwise
rediscover the blockage.
