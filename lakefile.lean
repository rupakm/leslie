import Lake
open Lake DSL

require lintLlmProofs from git
  "https://github.com/jessealama/lint-llm-proofs" @ "main"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.29.1"

package «leslie» where
  -- Settings applied to both builds and interactive editing
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩, -- pretty-prints `fun a ↦ b`
    ⟨`pp.proofs.withType, false⟩
  ]
  -- add any additional package configuration options here

@[default_target]
lean_lib «Leslie» where
  -- add any library configuration options here

@[default_target]
lean_lib «Leslie_LTS» where
  -- LTS framework and examples

require checkdecls from git "https://github.com/PatrickMassot/checkdecls.git"

meta if get_config? env = some "dev" then
require «doc-gen4» from git
  "https://github.com/leanprover/doc-gen4" @ "main"