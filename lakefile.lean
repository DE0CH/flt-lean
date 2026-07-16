import Lake
open Lake DSL

package "fermat" where
  version := v!"0.1.0"
  -- Warnings are hard errors (Deyao, 2026-07-16): an accidental `sorry`
  -- (or any stray warning) fails the build outright. The deliberate,
  -- tracked sorry nodes of the dependency tree opt out one by one with
  -- `set_option warn.sorry false in`; the root sorry gate
  -- (`Fermat/SorryGate.lean`) still fails `lake build` while any node is
  -- open, so a failing build remains the continue-signal.
  leanOptions := #[⟨`warningAsError, true⟩]

-- Pinned to the exact mathlib rev pinned by the FLT project
-- (ImperialCollegeLondon/FLT), from which several files are vendored.
require "leanprover-community" / "mathlib" @ git "a3364faec42918fcd84a03a255b50570129f9ead"

@[default_target]
lean_lib «Fermat» where
