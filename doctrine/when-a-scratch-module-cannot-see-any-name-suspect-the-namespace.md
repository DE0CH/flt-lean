## WHEN A SCRATCH MODULE CANNOT SEE ANY NAME, SUSPECT THE NAMESPACE BEFORE THE OLEANS
Same day, same worktree, and it cost two elaboration cycles. A scratch module importing a
freshly-built project module reported `Unknown identifier` for **every** name it used, plus
autoImplicit's misleading "Function expected at `gammaTwo` but this term has type `?m.1`". Every
instinct in this file points at stale or inconsistent `.lake` artifacts — and they were fine. The
cause was that `namespace Heegner` is nested inside `namespace BinaryQuadraticForm`, so the real
prefix is `Fermat.BinaryQuadraticForm.Heegner`, three components where the file's own docstrings
say "`Heegner.foo`" throughout.
The one-line discriminator, before touching anything else:
    #check @Some.Name.You.Are.Sure.Of     -- a top-level name from that module
If that resolves, the module is imported and current and the problem is your namespace path; if it
does not, then suspect the build. `grep -n "^namespace \|^end "` on the target file gives the true
prefix in one call — the docstrings do not, because they quote the name as an agent would type it
from inside the namespace.
