## TWO LEAVES IN IMPORT-INCOMPARABLE MODULES CANNOT SEE EACH OTHER — AND THE SHARED HOME IS THE ONE THING TO FIX FIRST
(2026-08-02, `flt-lean-9`, fusing `Fermat.exists_projGroupLaw_relPointAddEquiv_field`
(`ModularCurve/EllipticScheme.lean`) with
`…Modularity.exists_projMulOverField_geomFibreAddEquiv` (`Modularity/MoretBailly.lean`).)
This file already records that two leaves may be one theorem in two vocabularies, and that
the cure is to grep the file's docstrings for the classical statement. **That cure is
scoped to ONE file, and the commonest expensive instance is not.** Here the two leaves were
in two modules that are IMPORT-INCOMPARABLE — neither reaches the other, verified by walking
both closures — so no grep either agent could run from inside its own module would have
found the other, and neither could have consumed the other's copy even after finding it.
Each carried a 6677-line port estimate for the same work.
**The tell, and it is in the STATEMENTS rather than in the prose: two leaves whose
conclusions share a long verbatim prefix and differ only in a trailing conjunct.** Both
asked for the same `m` with the same four axioms in the same `ofMul` shape; one hung the
GEOMETRIC point dictionary off it and the other the RATIONAL one. Diff the two statements
before costing either.
**The repair is architectural and it is cheap, because it moves a STATEMENT and not a
proof.** Find the common ancestor module — here `ProjectiveModelOverField.lean`, which both
already imported — and put ONE leaf there carrying BOTH trailing conjuncts as a conjunction.
Both consumers become short assemblies. Frontier 2 → 1, no mathematics done, and the port
now has one target and one home instead of two rival ones.
Four things that made it go through in a day, each of which is the thing to check:
* **The common ancestor may be reachable for free.** The statement needed
  `AbelianSchemeStruct`, `RelPoint`, `GeomFibrePt`, `specAlgClos` and `galSMul`, all in
  `Modularity/AbelianScheme.lean` — which imports **no `Fermat.*` module at all**, so the
  new `public import` added exactly one module to the closure. Check the candidate's own
  import list before assuming a statement cannot be expressed upstream.
* **The bridge to each consumer is usually DEFINITIONAL, because the geometric inputs are
  `Prop`s.** `ProjGroupLaw.toAbelianSchemeStructField`,
  `ProjGroupLawOverField.ofMul (…).toAbelianSchemeStruct` and the new shared
  `abelianSchemeStructOfMul` are all `AbelianSchemeStruct.ofMorphisms` on the same data,
  differing only in the `IsProper`/`Smooth`/`GeometricallyConnected` arguments — so
  proof irrelevance makes them defeq and each consumer's proof is one `exact`. Do NOT build
  a transport; try `exact` first.
* **A `DecidableEq` that a consumer HAS must be an instance binder on the shared leaf, not
  a `Classical.typeDecidableEq` inside its statement.** `WeierstrassCurve.Affine.Point`'s
  `AddCommGroup` is declared under `[DecidableEq F]`, so baking in a classical instance
  gives a group structure that does not match the consumer's syntactically and the `≃+`
  will not typecheck. The `F̄` side had no such consumer, so there the internal
  `Classical.typeDecidableEq` is right — and copying MoretBailly's spelling character for
  character is what made its assembly a one-liner.
* **The leaf's own hoisted prerequisites may already be duplicated downstream.** Building
  the shared structure needed `IsProper (projToSpec E)` over a field, which existed as
  `isProper_projToSpec_field` and `isProper_projToSpecOverField` — two independent,
  character-for-character identical proofs in the two consumers, neither of which can see
  the other. It is now proven once upstream.
### RE-MEASURE A PORT BEFORE QUOTING ITS SIZE: subtract what has already landed in the target module
Every docstring in that cluster quoted **6677 lines**, honestly measured when written. The
true remaining figure was **2518 lines / 73 declarations**, because eighteen declarations of
the closure (986 lines) had since been ported into the very module the port was destined
for, and because `Fermat.ProjCoords` — the chart interface the estimate leads with — is
already stated over `{F : Type u} [Field F]` and needs no porting at all.
The measurement is one script and it is worth running before any port is dispatched:
    # transitive in-file dependency closure of the port's top declaration,
    # over COMMENT-STRIPPED source, attributing each token to its enclosing declaration;
    # then keep the ones whose header mentions the thing being varied (`ℚ`, `Scheme.{0}`);
    # then SUBTRACT the names already present in the destination module.
A port's advertised size is measured once, at the moment it is declined, and is never
re-measured while the fleet ports pieces of it. Expect it to be an over-estimate by a
factor of two in any cluster that has had two releases of attention.
### AND THE DESTINATION DECIDES THE SHAPE: a port that must land UPSTREAM cannot be done in place
The cheap-looking route — "generalise `ℚ` to `F` IN PLACE where the proofs already are, and
recover the old development as `F := ℚ`" — is right whenever the generalised declarations
end up somewhere the consumer can see. Here it is WRONG and the reason is one line of import
graph: `EllipticScheme.lean` is DOWNSTREAM of the module the shared leaf lives in, so an `m`
proved there could never discharge it. Copying the 2518 lines upstream is also wrong: it
leaves the chain in the tree twice. The correct shape is a **MOVE** — relocate the chain
upstream, generalised, and leave the `ℚ` declarations as `F := ℚ` instantiations, under
which every existing consumer keeps compiling unchanged and nothing is duplicated.
**So before choosing between "generalise in place" and "port", compute where the RESULT has
to be visible from.** That is a property of the import graph, not of the mathematics, and it
is the only input that decides the question.
