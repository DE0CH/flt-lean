import Lake
open Lake DSL

package "fermat" where
  version := v!"0.1.0"

-- Pinned to the exact mathlib rev pinned by the FLT project
-- (ImperialCollegeLondon/FLT), from which several files are vendored.
require "leanprover-community" / "mathlib" @ git "a3364faec42918fcd84a03a255b50570129f9ead"

@[default_target]
lean_lib «Fermat» where
