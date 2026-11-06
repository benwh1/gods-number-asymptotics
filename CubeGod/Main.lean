import CubeGod.Method.Explicit

/-!
# The theorems

The main theorems, for the cube of `CubeGod.Spec`, with `log` the
natural logarithm:

1. `lower_bound`: for all large `n`,
   `D(n) ≥ ¼·log(24!/4!⁶)·n²/log n − log(24!/4!⁶)·(log 13/4 + 3)·n²/(log n)²`;
2. `upper_bound`: for some `K` and all large `n`,
   `D(n) ≤ ¼·log(24!/4!⁶)·n²/log n + K·n²·log log n/(log n)²`;
3. `godsNumber_asymptotic`: `D(n) = ¼·log(24!/4!⁶)·n²/log n + O(n²·log log n/(log n)²)`.

The main term doesn't depend on the base of the logarithm. They come from `lower_bound_explicit` and
`method_explicit`. The limit `godsNumber_tendsto` follows from 3.
-/

open Filter Topology Real Asymptotics Nat

namespace CubeGod

/-- A bound on the moves needed for every solvable state bounds God's number. -/
theorem godsNumber_le_of {n : ℕ} {B : ℝ}
    (h : ∀ s : State n, Solvable s → ∃ w, act w s = solved n ∧ (w.length : ℝ) ≤ B) :
    (godsNumber n : ℝ) ≤ B := by
  set S : Set ℕ := {k | ∃ s : State n, Solvable s ∧ dist s = k} with hS
  have hdist : ∀ k ∈ S, (k : ℝ) ≤ B := by
    rintro k ⟨s, hs, rfl⟩
    obtain ⟨w, hw, hle⟩ := h s hs
    have : dist s ≤ w.length := Nat.sInf_le ⟨w, rfl, hw⟩
    exact (Nat.cast_le.mpr this).trans hle
  have hne : S.Nonempty := ⟨dist (solved n), solved n, ⟨[], rfl⟩, rfl⟩
  have hbdd : BddAbove S := by
    refine ⟨⌈B⌉₊, fun k hk ↦ ?_⟩
    exact Nat.cast_le.mp ((hdist k hk).trans (Nat.le_ceil B))
  exact hdist _ (Nat.sSup_mem hne hbdd)

theorem patternCount_eq : ((24 ! / 4 ! ^ 6 : ℕ) : ℝ) = patternCount := rfl

/-- **Lower bound.** For all sufficiently large `n`,
`D(n) ≥ ¼·log(24!/4!⁶)·n²/log n − log(24!/4!⁶)·(log 13/4 + 3)·n²/(log n)²`. -/
theorem lower_bound : ∀ᶠ n : ℕ in atTop,
    (godsNumber n : ℝ) ≥ Real.log (24 ! / 4 ! ^ 6 : ℕ) / 4 * n ^ 2 / Real.log n -
      Real.log (24 ! / 4 ! ^ 6 : ℕ) * (Real.log 13 / 4 + 3) * n ^ 2 / Real.log n ^ 2 := by
  filter_upwards [eventually_ge_atTop 12] with n hn
  exact lower_bound_explicit hn

/-- **Upper bound.** For some `K` and all sufficiently large `n`,
`D(n) ≤ ¼·log(24!/4!⁶)·n²/log n + K·n²·log log n/(log n)²`. -/
theorem upper_bound : ∃ K : ℝ, ∀ᶠ n : ℕ in atTop,
    (godsNumber n : ℝ) ≤ Real.log (24 ! / 4 ! ^ 6 : ℕ) / 4 * n ^ 2 / Real.log n +
      K * (n ^ 2 * Real.log (Real.log n) / Real.log n ^ 2) := by
  obtain ⟨K, hK⟩ := method_explicit
  exact ⟨K, by filter_upwards [hK] with n hn using godsNumber_le_of hn⟩

/-- **The theorem.** As `n → ∞`,
`D(n) = ¼·log(24!/4!⁶)·n²/log n + O(n²·log log n/(log n)²)`. -/
theorem godsNumber_asymptotic :
    (fun n : ℕ ↦ (godsNumber n : ℝ) - Real.log (24 ! / 4 ! ^ 6 : ℕ) / 4 * n ^ 2 / Real.log n)
      =O[atTop] fun n : ℕ ↦ (n : ℝ) ^ 2 * Real.log (Real.log n) / Real.log n ^ 2 := by
  obtain ⟨K, hK⟩ := upper_bound
  set c := Real.log (24 ! / 4 ! ^ 6 : ℕ) * (Real.log 13 / 4 + 3) with hc
  have hc0 : 0 ≤ c := by
    have h₁ : 0 ≤ Real.log (24 ! / 4 ! ^ 6 : ℕ) := by
      rw [patternCount_eq]; exact Real.log_nonneg (by exact_mod_cast patternCount_ge_one)
    have h₂ : 0 ≤ Real.log 13 := Real.log_nonneg (by norm_num)
    rw [hc]; positivity
  refine IsBigO.of_bound (|K| + c) ?_
  filter_upwards [hK, lower_bound, tendsto_log_log.eventually_ge_atTop 1] with n hup hlo hll
  set ℓ := Real.log n with hℓ
  have hℓ1 : 1 < ℓ := by have := two_le_log hll; linarith
  set E := (n : ℝ) ^ 2 * Real.log ℓ / ℓ ^ 2 with hE
  have hE0 : 0 ≤ E := by rw [hE]; positivity
  -- The lower error is at most `E`.
  have hlow : (n : ℝ) ^ 2 / ℓ ^ 2 ≤ E := by
    rw [hE]
    exact div_le_div_of_nonneg_right (le_mul_of_one_le_right (sq_nonneg _) hll) (by positivity)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hE0, abs_le]
  constructor
  · have : c * (n ^ 2 / ℓ ^ 2) ≤ c * E := mul_le_mul_of_nonneg_left hlow hc0
    have e : c * (n : ℝ) ^ 2 / ℓ ^ 2 = c * (n ^ 2 / ℓ ^ 2) := by ring
    have := mul_le_mul_of_nonneg_right (le_abs_self K) hE0
    have := mul_nonneg (abs_nonneg K) hE0
    rw [ge_iff_le, ← hc, e] at hlo
    nlinarith
  · have := mul_le_mul_of_nonneg_right (le_abs_self K) hE0
    have := mul_nonneg hc0 hE0
    nlinarith

/-- The limit: `D(n)·log n/n² → ¼·log(24!/4!⁶)`. -/
theorem godsNumber_tendsto :
    Tendsto (fun n : ℕ ↦ (godsNumber n : ℝ) * Real.log n / n ^ 2) atTop
      (𝓝 (Real.log (24 ! / 4 ! ^ 6 : ℕ) / 4)) := by
  set A := Real.log (24 ! / 4 ! ^ 6 : ℕ)
  have hℓ : Tendsto (fun n : ℕ ↦ Real.log n) atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  -- The error is `o(n²/log n)`, since `log x = o(x)`.
  have hsmall : (fun n : ℕ ↦ (n : ℝ) ^ 2 * Real.log (Real.log n) / Real.log n ^ 2)
      =o[atTop] fun n : ℕ ↦ (n : ℝ) ^ 2 / Real.log n := by
    refine IsLittleO.of_bound fun ε hε ↦ ?_
    have hlogx : ∀ᶠ x : ℝ in atTop, Real.log x ≤ ε * x := by
      filter_upwards [Real.isLittleO_log_id_atTop.bound hε, eventually_gt_atTop 1] with x hx hx₁
      simp only [Real.norm_eq_abs, id] at hx
      rw [abs_of_pos (Real.log_pos hx₁), abs_of_pos (by linarith)] at hx
      exact hx
    filter_upwards [hℓ.eventually hlogx, hℓ.eventually_gt_atTop 1] with n hn hℓ1
    set ℓ := Real.log n
    have hℓ0 : 0 < ℓ := by linarith
    have hl0 : 0 ≤ Real.log ℓ := Real.log_nonneg hℓ1.le
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity),
      abs_of_nonneg (by positivity)]
    calc (n : ℝ) ^ 2 * Real.log ℓ / ℓ ^ 2 ≤ (n : ℝ) ^ 2 * (ε * ℓ) / ℓ ^ 2 := by gcongr
      _ = ε * ((n : ℝ) ^ 2 / ℓ) := by field_simp
  have h := (godsNumber_asymptotic.trans_isLittleO hsmall).tendsto_div_nhds_zero
  have h' := h.add_const (A / 4)
  rw [zero_add] at h'
  refine h'.congr' ?_
  filter_upwards [hℓ.eventually_gt_atTop 0, eventually_gt_atTop 0] with n hℓ0 hn0
  have : (n : ℝ) ≠ 0 := by exact_mod_cast hn0.ne'
  field_simp
  ring

end CubeGod
