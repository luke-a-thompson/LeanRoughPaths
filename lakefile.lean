import Lake
open Lake DSL

package «lean-rough-paths» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @
  "c52f5fc15e8361912fba11513a3070f698eb56f8"

@[default_target]
lean_lib «HopfAlgebras» where
  srcDir := "."

@[default_target]
lean_lib «RoughPaths» where
  srcDir := "."
