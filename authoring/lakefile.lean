import Lake
open Lake DSL

package Tex2lean where
  leanOptions := #[⟨`autoImplicit, false⟩]

@[default_target]
lean_lib Tex2lean where
  srcDir := "."

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.33.0"
