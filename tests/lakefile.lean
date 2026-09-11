import Lake
open Lake DSL

package Tex2lean where
  leanOptions := #[⟨`autoImplicit, false⟩]

@[default_target]
lean_lib Tex2lean where
  srcDir := "."

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "db584cd6d46c92f209a44c0f1c829460d327499d"
