import Lake
open Lake DSL

package «lean-rough-paths» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @
  "16b5a1bae01ff8aadfe0e4bcf490c12a66a965c3"

@[default_target]
lean_lib «HopfAlgebras» where
  srcDir := "."

@[default_target]
lean_lib «RoughPaths» where
  srcDir := "."
