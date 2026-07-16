import Lake
open Lake DSL

package "fermat" where
  version := v!"0.1.0"

require "leanprover-community" / "mathlib" @ git "v4.32.0-rc1"

@[default_target]
lean_lib «Fermat» where
