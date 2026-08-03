## `Mono (kernel.ι f)` can fail instance search even where `Abelian` is available
Same day, and it cost a cycle. `sectionIdeal σ` is `kernel (…)`, elaborated in one file with
whatever `HasKernel` instance was found there; a later `mono_comp` in another file reconstructs a
DEFEQ BUT NOT SYNTACTICALLY EQUAL instance, and the search for `Mono (kernel.ι …)` fails — while
the abstract `example {C} [Abelian C] (f : X ⟶ Y) : Mono (kernel.ι f) := by infer_instance`
succeeds, which is what makes it look impossible. Supplying the term via `haveI` does NOT help,
for the same reason: the `haveI`'s own statement elaborates at the other instantiation.
The fix is to force the instantiation from the goal rather than from a fresh elaboration:
    refine @mono_comp _ _ _ _ _ _ ?_ _ (mono_of_the_second_factor)
    exact equalizer.ι_mono          -- `?_` is at the goal's own instantiation
General shape: when an instance search fails on a term that came out of another module's `def`,
stop trying to name the instance and open a hole the goal will instantiate for you.
