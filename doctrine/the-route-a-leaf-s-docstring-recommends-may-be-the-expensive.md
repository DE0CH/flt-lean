## THE ROUTE A LEAF'S DOCSTRING RECOMMENDS MAY BE THE EXPENSIVE ONE — PRICE THE FALLBACK FIRST

(2026-07-31, same leaf.) The docstring listed two routes and recommended the first:
establish the filtered-colimit formula `(Lan M)(V) = colim_{U ⊇ h(V)} M(U) ⊗ Γ(W,V)`, show
the index poset is codirected, and use "tensor commutes with filtered colimits". It listed
the *generators* argument as the alternative "if the pin gives no usable formula".

The generators route needed **no new mathematics at all** — every ingredient is already an
instance in the pin:

* `Adjunction.leftAdjointOplaxMonoidal` turns "the right adjoint is lax monoidal" into the
  comparison map `δ` with naturality in both variables, for free;
* `Limits.isIso_app_coconePt_of_preservesColimit` is the closure step;
* `PresheafOfModules.isColimitFreeYonedaCoproductsCokernelCofork` is the presentation;
* `PreservesColimitsOfSize` on `tensorLeft`/`tensorRight` and
  `Adjunction.leftAdjoint_preservesColimits` are the two preservation facts.

The colimit formula the docstring recommended is never used, and the codirectedness it
spent a paragraph on collapses to the single fact that `Opens.map` preserves `⊓`. The whole
dévissage is ~40 lines. **A route recommendation in a docstring is a guess made before
anyone tried; the fallback is not the fallback until you have priced both.**

