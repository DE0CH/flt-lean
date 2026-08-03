## SIBLING LEAVES COSTED AT DIFFERENT DEPTHS MAY BE ONE LEAF — test it before costing either

(2026-07-31, `flt-lean-204`, on the two halves of strong multiplicity one in
`Modularity/Interface.lean`.)

A cut had split one leaf into two and written a careful paragraph explaining that they "want
different machinery and are of different depth": one was inside the Atkin–Lehner theory the
file was already building and "could plausibly be closed without new analysis"; the other
needed Rankin–Selberg or the adelic dictionary, "an input this pin lacks entirely", and
"anyone attacking this leaf should expect to BUILD one of the two missing analytic theories".

**Both were the same leaf.** Each is two lines over one statement — newform block independence
at a common level — instantiated at a different common multiple of the two levels. The
asymmetry was an artefact of reading each leaf's hypothesis at face value: the "deep" one
looked deep because its agreement set was smaller, and the smaller set really does defeat the
obvious attack (Hecke recursion never reaches a NEW prime — that part of the old note was
correct). But the route that closes the sibling does not use recursion; it changes level, and
at the larger level the weaker hypothesis is already enough.

**The general test, and it is cheap.** When a cut leaves siblings, take the machinery named as
missing for the EASY one and ask whether it also discharges the HARD one. Here that was five
minutes of reading and a 10-second scratch verify. Two leaves became one, three declarations
became glue, and — the point that outlives the instance — nobody will now be dispatched to
build Rankin–Selberg for a node that does not need it.

**And the reverse reading matters just as much:** a leaf documented as CHEAP because it sits
inside theory the file already has is suspect the moment its cheap route also proves a sibling
documented as expensive. Either the cheap verdict is wrong or the expensive one is. Say which
in the docstring; do not leave the pair contradicting each other, because the next agent will
believe whichever docstring it opens first.

