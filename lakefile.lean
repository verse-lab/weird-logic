import Lake
open Lake DSL

package «weird-logic» where
  -- Settings applied to both builds and interactive editing
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩ -- pretty-prints `fun a ↦ b`
  ]
  -- add any additional package configuration options here

@[default_target]
lean_lib WeirdLogic {
  roots := #[`WeirdLogic]
  globs := #[Glob.submodules `WeirdLogic]
}

require batteries from
    git "https://github.com/leanprover-community/batteries" @ "v4.20.0"

require mathlib from
    git "https://github.com/leanprover-community/mathlib4.git" @ "v4.20.0"

require ssreflect from
    git "https://github.com/verse-lab/lean-ssr.git" @ "v4.20.0"

require lgtm from
    git "https://github.com/verse-lab/irl.git" @ "oopsla26-artefact"

-- @[default_target]
-- lean_lib «WeirdLogic» where
  -- add any library configuration options here
