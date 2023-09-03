import Lake

open Lake DSL

package talk

@[default_target]
lean_lib Talk {
  globs := #[.submodules "Talk"]
}

require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "master"
