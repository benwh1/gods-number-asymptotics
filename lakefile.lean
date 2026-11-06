import Lake

open Lake DSL

package cubegod where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩]

require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "v4.35.0"

@[default_target]
lean_lib CubeGod

/-- The statements of the main theorems, for `lake comparator`. -/
lean_lib Challenge

/-- Build the library, then print the final theorems and the axioms they depend on, failing unless
those are only `propext`, `Classical.choice` and `Quot.sound`. Run it with `lake run`. -/
@[default_script]
script axioms do
  let lake ← getLake
  let build ← IO.Process.spawn { cmd := lake.toString, args := #["build"] }
  let code ← build.wait
  if code != 0 then return code
  let check ← IO.Process.spawn
    { cmd := lake.toString, args := #["env", "lean", "--run", "scripts/Axioms.lean"] }
  check.wait
