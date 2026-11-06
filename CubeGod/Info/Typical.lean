import CubeGod.Info.Entropy

/-!
# Typical lists

A list of `c` values is `ε`-typical for `P` if it looks like `c` draws from `P`: each value `v` appears
between `(1-ε)cP(v)` and `(1+ε)cP(v)` times. This is the multiplicative form, so values of probability
zero never appear.
-/

open Finset Real

set_option linter.unusedSectionVars false

namespace CubeGod

variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] {c : ℕ}

/-- How many times `v` appears in the list `x`. -/
def count (x : Fin c → α) (v : α) : ℕ := #{k | x k = v}

/-- `x` is `ε`-typical for `P`. -/
def Typical (ε : ℝ) (P : α → ℝ) (x : Fin c → α) : Prop :=
  ∀ v, (1 - ε) * c * P v ≤ count x v ∧ (count x v : ℝ) ≤ (1 + ε) * c * P v

end CubeGod
