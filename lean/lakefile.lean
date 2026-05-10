import Lake
open Lake DSL

package «meir_moser» where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩
  ]
  moreServerOptions := #[
    ⟨`maxHeartbeats, (1000000 : Nat)⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.15.0"

@[default_target]
lean_lib MeirMoser where
  globs := #[.andSubmodules `MeirMoser]
