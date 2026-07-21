import Lake
open Lake DSL

package "fermat" where
  version := v!"0.1.0"
  -- Open sorry nodes emit Lean's standard warning and the build proceeds.
  -- The completeness check is the root sorry gate (`Fermat/SorryGate.lean`):
  -- `#assert_no_sorry fermat_last_theorem` fails `lake build` while any
  -- `sorryAx` remains in the top theorem's cone.

-- Pinned to the exact mathlib rev pinned by the FLT project
-- (ImperialCollegeLondon/FLT), from which several files are vendored.
require "leanprover-community" / "mathlib" @ git "a3364faec42918fcd84a03a255b50570129f9ead"

@[default_target]
lean_lib «Fermat» where
