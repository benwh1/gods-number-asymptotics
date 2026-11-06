import CubeGod.Spec

/-!
# The comparator challenge

The statements of the four main theorems of `CubeGod.Main`, for the cube of `CubeGod.Spec`, with
the proofs left out. `lake comparator` checks that the theorems of the same names in `CubeGod.Main`
(the solution) have exactly these statements, that their proofs use only the standard axioms, and
that the kernel accepts them.

The definitions, in `CubeGod.Spec`, are the trusted part: read that file to see what is claimed.
Run it with `lake comparator`; the configuration is `comparator.json`.
-/

open Filter Topology Real Asymptotics Nat

namespace CubeGod

/-- **Lower bound.** For all sufficiently large `n`,
`D(n) ≥ ¼·log(24!/4!⁶)·n²/log n − log(24!/4!⁶)·(log 13/4 + 3)·n²/(log n)²`. -/
theorem lower_bound : ∀ᶠ n : ℕ in atTop,
    (godsNumber n : ℝ) ≥ Real.log (24 ! / 4 ! ^ 6 : ℕ) / 4 * n ^ 2 / Real.log n -
      Real.log (24 ! / 4 ! ^ 6 : ℕ) * (Real.log 13 / 4 + 3) * n ^ 2 / Real.log n ^ 2 := by
  sorry

/-- **Upper bound.** For some `K` and all sufficiently large `n`,
`D(n) ≤ ¼·log(24!/4!⁶)·n²/log n + K·n²·log log n/(log n)²`. -/
theorem upper_bound : ∃ K : ℝ, ∀ᶠ n : ℕ in atTop,
    (godsNumber n : ℝ) ≤ Real.log (24 ! / 4 ! ^ 6 : ℕ) / 4 * n ^ 2 / Real.log n +
      K * (n ^ 2 * Real.log (Real.log n) / Real.log n ^ 2) := by
  sorry

/-- **The theorem.** As `n → ∞`,
`D(n) = ¼·log(24!/4!⁶)·n²/log n + O(n²·log log n/(log n)²)`. -/
theorem godsNumber_asymptotic :
    (fun n : ℕ ↦ (godsNumber n : ℝ) - Real.log (24 ! / 4 ! ^ 6 : ℕ) / 4 * n ^ 2 / Real.log n)
      =O[atTop] fun n : ℕ ↦ (n : ℝ) ^ 2 * Real.log (Real.log n) / Real.log n ^ 2 := by
  sorry

/-- The limit: `D(n)·log n/n² → ¼·log(24!/4!⁶)`. -/
theorem godsNumber_tendsto :
    Tendsto (fun n : ℕ ↦ (godsNumber n : ℝ) * Real.log n / n ^ 2) atTop
      (𝓝 (Real.log (24 ! / 4 ! ^ 6 : ℕ) / 4)) := by
  sorry

end CubeGod
