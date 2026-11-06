import CubeGod.Method.Books
import CubeGod.Method.Counting

/-!
# The upper bound with an explicit error

With `N = n/2 - 1` and `ℓ = ⌊log₂ N⌋`, take `c = ℓ - 6⌊log₂ℓ⌋`, so `2^c·ℓ⁶ < 64·2^ℓ`, and
`a = c·⌊N/(ℓ²c²)⌋`, a multiple of `c`, and `h = ⌊N/(ac)⌋`. Each kind's schedule comes from
`exists_sched`: at most `c·log₂C/2 + P₀ + P₁·ln c` steps, with codebooks of at most `2^c` lists. Every
step costs at most `(N/c)²(1 + 1/ℓ)` moves, so Stage 2 costs at most
`(N/c)²(1 + 1/ℓ)(c·log₂C + O(log c))`, which is `¼·log₂C·n²/L + O(n² log L/L²)` with `L = log₂ n`.
The tolerance of the twist is the constant `¼`, so a bad row has chance `exp(−Ω(c))`.

These are base 2: `c` is about `log₂ n`, codebooks hold up to `2^c` lists, and information is in
bits. Only the final bound, `method_explicit`, is stated with the natural logarithm, by `error_le`.
-/

open Finset Real Filter Topology

namespace CubeGod

variable {n h a c : ℕ}

/-- `c` as a function of `ℓ`. -/
def cOf (l : ℕ) : ℕ := l - 6 * Nat.log 2 l

/-- `12⌊log₂ ℓ⌋ ≤ ℓ` once `ℓ ≥ 128`. -/
theorem twelve_log_le {l : ℕ} (hl : 128 ≤ l) : 12 * Nat.log 2 l ≤ l := by
  set m := Nat.log 2 l with hm
  have h₁ : 2 ^ m ≤ l := Nat.pow_log_le_self 2 (by omega)
  by_cases hm7 : m < 7
  · omega
  · push Not at hm7
    -- `12m ≤ 2^m` for `m ≥ 7`.
    have h₂ : 12 * m ≤ 2 ^ m := by
      obtain ⟨k, hk⟩ : ∃ k, m = k + 7 := ⟨m - 7, by omega⟩
      have h₃ : k + 1 ≤ 2 ^ k := Nat.lt_two_pow_self
      rw [hk, pow_add]
      norm_num
      omega
    omega

/-- `2^c·ℓ⁶ ≤ 64·2^ℓ`. -/
theorem two_pow_cOf_mul (l : ℕ) (hl : 6 * Nat.log 2 l ≤ l) :
    (2 : ℝ) ^ cOf l * (l : ℝ) ^ 6 ≤ 64 * 2 ^ l := by
  set m := Nat.log 2 l with hm
  have hsplit : (2 : ℝ) ^ cOf l * 2 ^ (6 * m) = 2 ^ l := by
    rw [← pow_add]; congr 1; unfold cOf; have := hl; omega
  have hlt : l < 2 ^ (m + 1) := Nat.lt_pow_succ_log_self (by norm_num) l
  have hltr : (l : ℝ) ≤ 2 ^ (m + 1) := by exact_mod_cast hlt.le
  have h6 : (l : ℝ) ^ 6 ≤ 64 * 2 ^ (6 * m) := by
    calc (l : ℝ) ^ 6 ≤ (2 ^ (m + 1)) ^ 6 := pow_le_pow_left₀ (by positivity) hltr 6
      _ = 64 * 2 ^ (6 * m) := by rw [← pow_mul]; ring
  calc (2 : ℝ) ^ cOf l * (l : ℝ) ^ 6 ≤ 2 ^ cOf l * (64 * 2 ^ (6 * m)) :=
        mul_le_mul_of_nonneg_left h6 (by positivity)
    _ = 64 * 2 ^ l := by rw [← hsplit]; ring

theorem cOf_ge {l : ℕ} (hl : 128 ≤ l) : (l : ℝ) / 2 ≤ cOf l := by
  have := twelve_log_le hl
  have h : l ≤ 2 * cOf l := by unfold cOf; omega
  have : (l : ℝ) ≤ 2 * cOf l := by exact_mod_cast h
  linarith

theorem cOf_le (l : ℕ) : cOf l ≤ l := Nat.sub_le _ _

theorem sub_cOf_le (l : ℕ) : (l : ℝ) - cOf l ≤ 6 * logb 2 l := by
  have h₁ : (Nat.log 2 l : ℝ) ≤ logb 2 l := by
    have := Real.natLog_le_logb l 2
    exact_mod_cast this
  have h₂ : (cOf l : ℝ) ≥ l - 6 * Nat.log 2 l := by
    unfold cOf
    rcases le_total (6 * Nat.log 2 l) l with h | h
    · rw [Nat.cast_sub h]; push_cast; linarith
    · rw [Nat.sub_eq_zero_of_le h]; push_cast
      have : (l : ℝ) ≤ 6 * Nat.log 2 l := by exact_mod_cast h
      linarith
  linarith

/-! ### The parameters, as functions of `n` -/

/-- `N = n/2 - 1`, the number of layers in `I`. -/
def Nof (n : ℕ) : ℕ := n / 2 - 1

/-- `ℓ = ⌊log₂ N⌋`. -/
def lOf (n : ℕ) : ℕ := Nat.log 2 (Nof n)

theorem tendsto_lOf : Tendsto lOf atTop atTop := by
  exact tendsto_logN

/-- The relations between `n`, `N`, `ℓ` and `L = log₂ n`, for `n ≥ 16`. -/
theorem lOf_bounds {n : ℕ} (hn : 16 ≤ n) :
    (2 : ℝ) ^ lOf n ≤ Nof n ∧ (Nof n : ℝ) < 2 ^ (lOf n + 1) ∧ (Nof n : ℝ) ≤ n / 2 ∧
      (n : ℝ) ≤ 5 * Nof n ∧ logb 2 n - 4 ≤ lOf n ∧ (lOf n : ℝ) ≤ logb 2 n := by
  have hN0 : Nof n ≠ 0 := by unfold Nof; omega
  have h₁ : 2 ^ lOf n ≤ Nof n := Nat.pow_log_le_self 2 hN0
  have h₂ : Nof n < 2 ^ (lOf n + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
  have h₁r : (2 : ℝ) ^ lOf n ≤ Nof n := by exact_mod_cast h₁
  have h₂r : (Nof n : ℝ) < 2 ^ (lOf n + 1) := by exact_mod_cast h₂
  have h₃ : (Nof n : ℝ) ≤ n / 2 := by
    have : 2 * Nof n ≤ n := by unfold Nof; omega
    have : (2 : ℝ) * Nof n ≤ n := by exact_mod_cast this
    linarith
  have h₄ : (n : ℝ) ≤ 5 * Nof n := by
    have : n ≤ 5 * Nof n := by unfold Nof; omega
    exact_mod_cast this
  have hn₀ : (0 : ℝ) < n := by positivity
  refine ⟨h₁r, h₂r, h₃, h₄, ?_, ?_⟩
  · -- `n ≤ 5N < 5·2^(ℓ+1) ≤ 2^(ℓ+4)`.
    have : (n : ℝ) < 2 ^ ((lOf n : ℝ) + 4) := by
      have e : (2 : ℝ) ^ ((lOf n : ℝ) + 4) = 16 * 2 ^ lOf n := by
        rw [Real.rpow_add (by norm_num), Real.rpow_natCast]; norm_num; ring
      rw [e]
      have : (2 : ℝ) ^ (lOf n + 1) = 2 * 2 ^ lOf n := by ring
      linarith
    have := (Real.logb_lt_iff_lt_rpow (by norm_num) hn₀).mpr this
    linarith
  · -- `2^ℓ ≤ N ≤ n`.
    have : (2 : ℝ) ^ (lOf n : ℝ) ≤ n := by
      rw [Real.rpow_natCast]; linarith
    exact (Real.le_logb_iff_rpow_le (by norm_num) hn₀).mpr this

theorem tendsto_cOf : Tendsto cOf atTop atTop := by
  refine tendsto_atTop_atTop.mpr fun b ↦ ⟨max 128 (2 * b), fun l hl ↦ ?_⟩
  have h := cOf_ge (le_of_max_le_left hl)
  have : (2 * b : ℝ) ≤ l := by exact_mod_cast le_of_max_le_right hl
  have : (b : ℝ) ≤ cOf l := by linarith
  exact_mod_cast this

/-- The bound on the bad fraction from `typical_chernoff_explicit`, with tolerance `ε₀/2`. -/
noncomputable def betaOf (nX ε : ℝ) (c : ℕ) : ℝ := 2 * nX * exp (-((ε / 2) ^ 2 * nX⁻¹ ^ 2 / 4)) ^ c

/-! ### From `log₂` to `log` -/

theorem tendsto_log_log :
    Tendsto (fun n : ℕ ↦ Real.log (Real.log n)) atTop atTop :=
  tendsto_log_atTop.comp (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)

theorem two_le_log {n : ℕ} (h : 1 ≤ Real.log (Real.log n)) : 2 ≤ Real.log n := by
  have h0 : 0 ≤ Real.log n := Real.log_natCast_nonneg n
  rcases h0.eq_or_lt with h0 | h0
  · rw [← h0, Real.log_zero] at h; linarith
  · have := Real.log_le_sub_one_of_pos h0; linarith

/-- The error term with `log₂` is at most twice the one with `log`. -/
theorem error_le {n : ℕ} (hll : 1 ≤ Real.log (Real.log n)) :
    (n : ℝ) ^ 2 * logb 2 (logb 2 n) / logb 2 n ^ 2 ≤
      2 * ((n : ℝ) ^ 2 * Real.log (Real.log n) / Real.log n ^ 2) := by
  set ℓ := Real.log n with hℓdef
  set l2 := Real.log 2 with hl2def
  set y := Real.log ℓ with hy
  have hl2 : 1 / 2 < l2 := by have := Real.log_two_gt_d9; rw [hl2def]; linarith
  have hl2' : l2 < 1 := by have := Real.log_two_lt_d9; rw [hl2def]; linarith
  have hℓ : 1 < ℓ := by have := two_le_log hll; linarith
  have hℓ0 : 0 < ℓ := by linarith
  -- `log₂(log₂ n)·log 2 = y − log(log 2) ≤ y + 1 ≤ 2y`.
  have hx : logb 2 (logb 2 (n : ℝ)) * l2 = y - Real.log l2 := by
    show Real.log (ℓ / l2) / l2 * l2 = _
    rw [div_mul_cancel₀ _ (by linarith), Real.log_div hℓ0.ne' (by linarith)]
  have hxl : -Real.log l2 ≤ 1 := by
    have := Real.one_sub_inv_le_log_of_pos (show 0 < l2 by linarith)
    have h₂ : l2⁻¹ ≤ 2 := by rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
    linarith
  have hL : logb 2 (n : ℝ) = ℓ / l2 := rfl
  rw [hL]
  have hn2 : (0 : ℝ) ≤ (n : ℝ) ^ 2 := sq_nonneg _
  have hu : logb 2 (ℓ / l2) ≤ 2 * y / l2 := by
    rw [show logb 2 (ℓ / l2) = (logb 2 (ℓ / l2) * l2) / l2 by field_simp, ← hL, hx]
    exact div_le_div_of_nonneg_right (by linarith) (by linarith)
  rw [div_pow, div_le_iff₀ (by positivity)]
  have e : 2 * ((n : ℝ) ^ 2 * y / ℓ ^ 2) * (ℓ ^ 2 / l2 ^ 2) = 2 * (n : ℝ) ^ 2 * y / l2 ^ 2 := by
    field_simp
  rw [e]
  calc (n : ℝ) ^ 2 * logb 2 (ℓ / l2) ≤ (n : ℝ) ^ 2 * (2 * y / l2) := mul_le_mul_of_nonneg_left hu hn2
    _ = 2 * (n : ℝ) ^ 2 * y / l2 := by ring
    _ ≤ 2 * (n : ℝ) ^ 2 * y / l2 ^ 2 := by
        apply div_le_div_of_nonneg_left (by positivity) (by positivity)
        nlinarith

/-- **The final arithmetic** of the explicit bound, with `L = log₂ n` and `u = log₂ L`. -/
theorem final_sq {A K₂ P n N l c L S len : ℝ} (hA : 0 ≤ A) (hK₂ : 0 ≤ K₂) (hP : 0 ≤ P)
    (hL16 : 16 ≤ L) (hu₁ : 1 ≤ logb 2 L)
    (hl₁ : L - 4 ≤ l) (hl₂ : l ≤ L) (hcl : l - 6 * logb 2 l ≤ c) (hc₂ : l / 2 ≤ c)
    (hN₀ : 0 ≤ N) (hN : N ≤ n / 2)
    (hlen : len ≤ S + N ^ 2 / c ^ 2 * (1 + 1 / l) * (c * A + P * logb 2 L) + K₂ * (4 * N ^ 2 / l ^ 2))
    (hS : S ≤ N ^ 2 / l ^ 2) :
    len ≤ A / 4 * n ^ 2 / L + (12 * A + 8 * P + 1 + 4 * K₂) * (n ^ 2 * logb 2 L / L ^ 2) := by
  set u := logb 2 L with hu
  have hL₀ : 0 < L := by linarith
  have hl8 : L / 2 ≤ l := by linarith
  have hl₀ : 0 < l := by linarith
  have hl1 : 1 ≤ l := by linarith
  have hlogl : logb 2 l ≤ u := Real.logb_le_logb_of_le (by norm_num) hl₀ hl₂
  have hc₀ : L / 4 ≤ c := by linarith
  have hcpos : 0 < c := by linarith
  have hn2 : N ^ 2 ≤ n ^ 2 / 4 := by
    have : N ^ 2 ≤ (n / 2) ^ 2 := pow_le_pow_left₀ hN₀ hN 2
    linarith
  set t := n ^ 2 * u / L ^ 2 with ht
  have hn0 : 0 ≤ n ^ 2 := sq_nonneg n
  have ht0 : 0 ≤ t := by rw [ht]; positivity
  have hNl : N ^ 2 / l ^ 2 ≤ t := by
    have h₁ : L ^ 2 / 4 ≤ l ^ 2 := by
      have := pow_le_pow_left₀ (by positivity) hl8 2
      linarith
    calc N ^ 2 / l ^ 2 ≤ (n ^ 2 / 4) / (L ^ 2 / 4) := div_le_div₀ (by positivity) hn2
          (by positivity) h₁
      _ = n ^ 2 / L ^ 2 := by field_simp
      _ ≤ t := by
          rw [ht]; exact div_le_div_of_nonneg_right (le_mul_of_one_le_right hn0 hu₁) (by positivity)
  -- `(1 + 1/ℓ)/c ≤ 1/L + 48u/L²`.
  have hfrac : (1 + 1 / l) / c ≤ 1 / L + 48 * u / L ^ 2 := by
    have hnum : L * (1 + 1 / l) ≤ c + 12 * u := by
      have : L * (1 / l) ≤ 2 := by
        rw [mul_div_assoc', mul_one, div_le_iff₀ hl₀]; linarith
      have : L - c ≤ 4 + 6 * u := by linarith
      nlinarith
    rw [div_le_iff₀ hcpos]
    calc 1 + 1 / l ≤ (c + 12 * u) / L := by rw [le_div_iff₀ hL₀]; linarith
      _ = c / L + 12 * u / L := by ring
      _ ≤ c / L + 48 * u * c / L ^ 2 := by
          have : 12 * u / L ≤ 48 * u * c / L ^ 2 := by
            rw [div_le_div_iff₀ hL₀ (by positivity)]
            have hu0 : 0 ≤ u := by linarith
            calc 12 * u * L ^ 2 = (12 * u * L) * L := by ring
              _ ≤ (12 * u * L) * (4 * c) :=
                  mul_le_mul_of_nonneg_left (by linarith) (by positivity)
              _ = 48 * u * c * L := by ring
          linarith
      _ = (1 / L + 48 * u / L ^ 2) * c := by ring
  -- The main term.
  have hmain : N ^ 2 / c ^ 2 * (1 + 1 / l) * (c * A) ≤ A / 4 * n ^ 2 / L + 12 * A * t := by
    have e : N ^ 2 / c ^ 2 * (1 + 1 / l) * (c * A) = N ^ 2 * ((1 + 1 / l) / c) * A := by
      field_simp
    rw [e]
    have hq₀ : 0 ≤ (1 + 1 / l) / c := by positivity
    have h₁ : N ^ 2 * ((1 + 1 / l) / c) * A ≤ n ^ 2 / 4 * (1 / L + 48 * u / L ^ 2) * A := by
      apply mul_le_mul_of_nonneg_right _ hA
      exact mul_le_mul hn2 hfrac hq₀ (by positivity)
    have e₁ : n ^ 2 / 4 * (1 / L + 48 * u / L ^ 2) * A = A / 4 * n ^ 2 / L + 12 * A * t := by
      rw [ht]; ring
    linarith
  -- The excess.
  have hexc : N ^ 2 / c ^ 2 * (1 + 1 / l) * (P * u) ≤ 8 * P * t := by
    have h₁ : N ^ 2 / c ^ 2 ≤ (n ^ 2 / 4) * (16 / L ^ 2) := by
      have : 1 / c ^ 2 ≤ 16 / L ^ 2 := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        have := pow_le_pow_left₀ (by positivity) hc₀ 2
        nlinarith
      calc N ^ 2 / c ^ 2 = N ^ 2 * (1 / c ^ 2) := by ring
        _ ≤ (n ^ 2 / 4) * (16 / L ^ 2) := mul_le_mul hn2 this (by positivity) (by positivity)
    have h₂ : 1 + 1 / l ≤ 2 := by
      have : 1 / l ≤ 1 := by rw [div_le_one hl₀]; exact hl1
      linarith
    have hPu : 0 ≤ P * u := by positivity
    calc N ^ 2 / c ^ 2 * (1 + 1 / l) * (P * u) ≤ (n ^ 2 / 4) * (16 / L ^ 2) * 2 * (P * u) :=
          mul_le_mul_of_nonneg_right (mul_le_mul h₁ h₂ (by positivity) (by positivity)) hPu
      _ = 8 * P * t := by rw [ht]; ring
  have hsmall : S + K₂ * (4 * N ^ 2 / l ^ 2) ≤ (1 + 4 * K₂) * t := by
    have : S + K₂ * (4 * N ^ 2 / l ^ 2) ≤ (1 + 4 * K₂) * (N ^ 2 / l ^ 2) := by
      have e : K₂ * (4 * N ^ 2 / l ^ 2) = 4 * K₂ * (N ^ 2 / l ^ 2) := by ring
      linarith
    exact this.trans (mul_le_mul_of_nonneg_left hNl (by positivity))
  have e : N ^ 2 / c ^ 2 * (1 + 1 / l) * (c * A + P * u) =
      N ^ 2 / c ^ 2 * (1 + 1 / l) * (c * A) + N ^ 2 / c ^ 2 * (1 + 1 / l) * (P * u) := by ring
  rw [e] at hlen
  have e₂ : (12 * A + 8 * P + 1 + 4 * K₂) * t = 12 * A * t + 8 * P * t + (1 + 4 * K₂) * t := by
    ring
  linarith

/-! ### The grid -/

/-- The sizes of the grid with `a = c·⌊N/(ℓ²c²)⌋`. -/
theorem sq_grid_bounds {N l c : ℕ} (hc₁ : 1 ≤ c) (hcl : c ≤ l) (hl : 1 ≤ l)
    (hN : 2 * (l : ℝ) ^ 4 ≤ N) :
    0 < N / (l ^ 2 * (c * c)) ∧
      ((c * (N / (l ^ 2 * (c * c))) : ℕ) : ℝ) * c * (l : ℝ) ^ 2 ≤ N ∧
      (N : ℝ) ≤ 2 * (l : ℝ) ^ 2 * (((c * (N / (l ^ 2 * (c * c))) : ℕ) : ℝ) * c) := by
  have hdiv : 0 < l ^ 2 * (c * c) := by positivity
  set a' := N / (l ^ 2 * (c * c)) with ha'
  have ha₁ : a' * (l ^ 2 * (c * c)) ≤ N := Nat.div_mul_le_self _ _
  have ha₂ : N < (a' + 1) * (l ^ 2 * (c * c)) := by
    have := Nat.lt_mul_div_succ N hdiv
    rw [Nat.mul_comm] at this
    exact this
  have ha₁r : (a' : ℝ) * ((l : ℝ) ^ 2 * (c * c)) ≤ N := by exact_mod_cast ha₁
  have ha₂r : (N : ℝ) ≤ ((a' : ℝ) + 1) * ((l : ℝ) ^ 2 * (c * c)) := by exact_mod_cast ha₂.le
  have hl' : (1 : ℝ) ≤ l := by exact_mod_cast hl
  have hclr : (c : ℝ) ≤ l := by exact_mod_cast hcl
  have hc' : (1 : ℝ) ≤ c := by exact_mod_cast hc₁
  have hlc : 2 * ((l : ℝ) ^ 2 * (c * c)) ≤ N := by
    have h₁ : (l : ℝ) ^ 2 * (c * c) ≤ (l : ℝ) ^ 4 := by
      have : (c : ℝ) * c ≤ (l : ℝ) ^ 2 := by nlinarith
      nlinarith [sq_nonneg (l : ℝ)]
    linarith
  have hpos : 0 < a' := by
    by_contra h0
    have ha0 : a' = 0 := Nat.le_zero.mp (not_lt.mp h0)
    rw [ha0] at ha₂r
    have : (0 : ℝ) < (l : ℝ) ^ 2 * (c * c) := by positivity
    simp at ha₂r
    linarith
  have ha'r : (1 : ℝ) ≤ a' := by exact_mod_cast hpos
  refine ⟨hpos, ?_, ?_⟩
  · push_cast; nlinarith
  · push_cast
    have : ((a' : ℝ) + 1) ≤ 2 * a' := by linarith
    nlinarith [mul_le_mul_of_nonneg_right this (show (0 : ℝ) ≤ (l : ℝ) ^ 2 * (c * c) by positivity)]

/-- `2^c·8c²·ℓ ≤ ac` when `ac ≥ N/(2ℓ²)`. -/
theorem two_pow_le_ac {N l c : ℕ} {ac : ℝ} (hl : 1024 ≤ l) (hcl : c ≤ l)
    (h2c : (2 : ℝ) ^ c * (l : ℝ) ^ 6 ≤ 64 * 2 ^ l) (hN : (2 : ℝ) ^ l ≤ N)
    (hac : (N : ℝ) ≤ 2 * (l : ℝ) ^ 2 * ac) :
    (2 : ℝ) ^ c * (8 * ((c : ℝ) * c)) * l ≤ ac := by
  have hl' : (1024 : ℝ) ≤ l := by exact_mod_cast hl
  have hl₀ : (0 : ℝ) < l := by linarith
  have hclr : (c : ℝ) ≤ l := by exact_mod_cast hcl
  have h₁ : (2 : ℝ) ^ c * (8 * ((c : ℝ) * c)) * l ≤ 2 ^ c * (8 * (l : ℝ) ^ 3) := by
    have : (c : ℝ) * c * l ≤ (l : ℝ) ^ 3 := by
      have : (c : ℝ) * c ≤ l * l := mul_le_mul hclr hclr (by positivity) (by positivity)
      nlinarith
    nlinarith [pow_pos (show (0 : ℝ) < 2 by norm_num) c]
  have h₂ : (2 : ℝ) ^ c * (8 * (l : ℝ) ^ 3) * (l : ℝ) ^ 3 ≤ 512 * 2 ^ l := by nlinarith
  have h₃ : (512 : ℝ) * 2 ^ l ≤ ac * (l : ℝ) ^ 3 := by
    have : (N : ℝ) * l ≤ 2 * (l : ℝ) ^ 3 * ac := by nlinarith
    have : (2 : ℝ) ^ l * 1024 ≤ (2 : ℝ) ^ l * l := mul_le_mul_of_nonneg_left hl' (by positivity)
    nlinarith
  have : (2 : ℝ) ^ c * (8 * (l : ℝ) ^ 3) ≤ ac :=
    le_of_mul_le_mul_right (h₂.trans h₃) (by positivity)
  linarith

/-- A step of Stage 2 with square blocks costs at most `(N/c)²(1 + 1/ℓ)` moves. -/
theorem sqLen_le {N l : ℝ} (hN : (h : ℝ) * (a * c) ≤ N) (hca : c ∣ a) (hc : 0 < c) (hl : 1 ≤ l)
    (h₂ : (2 : ℝ) ^ c * (8 * ((c : ℝ) * c)) * l ≤ a * c) :
    (Layout.sqLen h a c (2 ^ c) : ℝ) ≤ (N / c) ^ 2 * (1 + 1 / l) := by
  have hc' : (0 : ℝ) < c := by exact_mod_cast hc
  have hl₀ : (0 : ℝ) < l := by linarith
  have hP : (2 : ℝ) * (groupPairs h).length ≤ (h : ℝ) ^ 2 := by
    have := two_length_groupPairs h
    have h' : ((2 * (groupPairs h).length + h : ℕ) : ℝ) = ((h ^ 2 : ℕ) : ℝ) := by rw [this]
    push_cast at h'
    have : (0 : ℝ) ≤ h := by positivity
    linarith
  obtain ⟨a', rfl⟩ := hca
  have hdiv : c * a' / c = a' := Nat.mul_div_cancel_left _ hc
  unfold Layout.sqLen
  rw [hdiv]
  push_cast
  set P : ℝ := ((groupPairs h).length : ℝ)
  have hP₀ : 0 ≤ P := by positivity
  have hY : 2 * (2 ^ c * (8 * ((c : ℝ) * c)) + c * a' * c) ≤ 2 * ((1 + 1 / l) * (c * a' * c)) := by
    have : (2 : ℝ) ^ c * (8 * ((c : ℝ) * c)) ≤ (c * a' * c) / l := by
      rw [le_div_iff₀ hl₀]; push_cast at h₂; linarith
    have e : (1 + 1 / l) * ((c : ℝ) * a' * c) = c * a' * c + c * a' * c / l := by ring
    linarith
  have hsq : ((h : ℝ) * (c * a')) ^ 2 ≤ (N / c) ^ 2 := by
    apply pow_le_pow_left₀ (by positivity)
    rw [le_div_iff₀ hc']; push_cast at hN; linarith
  calc P * a' * (2 * (2 ^ c * (8 * ((c : ℝ) * c)) + c * a' * c)) ≤
        P * a' * (2 * ((1 + 1 / l) * (c * a' * c))) :=
        mul_le_mul_of_nonneg_left hY (by positivity)
    _ = (2 * P) * ((c * a') ^ 2) * (1 + 1 / l) := by ring
    _ ≤ (h : ℝ) ^ 2 * ((c * a') ^ 2) * (1 + 1 / l) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_right hP (by positivity)
    _ = ((h : ℝ) * (c * a')) ^ 2 * (1 + 1 / l) := by ring
    _ ≤ (N / c) ^ 2 * (1 + 1 / l) := mul_le_mul_of_nonneg_right hsq (by positivity)

/-! ### The bad fraction -/

/-- `c·β·(2c)² ≤ 1` eventually, for the twist's tolerance `¼`. -/
theorem eventually_beta (nX : ℝ) (hnX : 1 ≤ nX) :
    ∀ᶠ c : ℕ in atTop, (c : ℝ) * betaOf nX (1 / 2) c * (2 * c) ^ 2 ≤ 1 := by
  set r := exp (-((1 / 2 / 2) ^ 2 * nX⁻¹ ^ 2 / 4)) with hr
  have hr₀ : 0 < r := Real.exp_pos _
  have hr₁ : r < 1 := by
    have : 0 < (1 / 2 / 2 : ℝ) ^ 2 * nX⁻¹ ^ 2 / 4 := by positivity
    have h := Real.exp_lt_exp.mpr (show -((1 / 2 / 2 : ℝ) ^ 2 * nX⁻¹ ^ 2 / 4) < 0 by linarith)
    rwa [Real.exp_zero] at h
  have hlim := tendsto_pow_const_mul_const_pow_of_abs_lt_one 3 (r := r)
    (by rw [abs_of_pos hr₀]; exact hr₁)
  filter_upwards [hlim.eventually (gt_mem_nhds (show (0 : ℝ) < 1 / (8 * nX) by positivity))]
    with c hc
  unfold betaOf
  rw [← hr]
  have e : (c : ℝ) * (2 * nX * r ^ c) * (2 * c) ^ 2 = 8 * nX * ((c : ℝ) ^ 3 * r ^ c) := by ring
  rw [e]
  have : (c : ℝ) ^ 3 * r ^ c ≤ 1 / (8 * nX) := hc.le
  calc 8 * nX * ((c : ℝ) ^ 3 * r ^ c) ≤ 8 * nX * (1 / (8 * nX)) :=
        mul_le_mul_of_nonneg_left this (by positivity)
    _ = 1 := by field_simp

/-! ### The Method, with an explicit error -/

set_option maxHeartbeats 1000000 in
/-- **The upper bound with an explicit error.** For large `n`, every solvable state can be solved in
at most `¼·log C·n²/log n + K·n² log log n/(log n)²` moves. The proof works with `L = log₂ n`, since
the blocks are about `log₂ n` layers, and changes to `log` at the end. -/
theorem method_explicit : ∃ K : ℝ, ∀ᶠ n : ℕ in atTop, ∀ s : State n, Solvable s →
    ∃ w, act w s = solved n ∧ (w.length : ℝ) ≤ log patternCount / 4 * n ^ 2 / log n +
      K * (n ^ 2 * log (log n) / log n ^ 2) := by
  classical
  set A := logb 2 patternCount with hA
  have hC : (1 : ℝ) ≤ patternCount := by exact_mod_cast patternCount_ge_one
  have hA₀ : 0 ≤ A := logb_nonneg (by norm_num) hC
  set nX : ℝ := (patternCount : ℝ) with hnX
  have hcardX : ∀ q, (Fintype.card (OState q) : ℝ) = nX := fun q ↦ by rw [card_oState]
  obtain ⟨P₀t, P₁t, hSt⟩ := exists_sched true
  obtain ⟨P₀f, P₁f, hSf⟩ := exists_sched false
  set P : ℝ := |P₀t| + |P₁t| + |P₀f| + |P₁f| with hP
  have hP₀ : 0 ≤ P := by positivity
  obtain ⟨K₁, hK₁⟩ := factP1
  obtain ⟨K₂, hK₂⟩ := factP2_oblique
  obtain ⟨Lg, hL⟩ := exists_cycle_lists
  set Gs := allCycles.length with hGs
  set Cp : ℝ := 5 * K₁ + 136 * (Lg * Gs) + 2 with hCp
  have hK₂0 : (0 : ℝ) ≤ K₂ := by positivity
  have hK0 : 0 ≤ 12 * A + 8 * P + 1 + 4 * K₂ := by positivity
  refine ⟨2 * (12 * A + 8 * P + 1 + 4 * K₂), ?_⟩
  -- What we need of `L = log₂ n`.
  have hLtend : Tendsto (fun n : ℕ ↦ logb 2 (n : ℝ)) atTop atTop :=
    (tendsto_logb_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  have evL : ∀ᶠ n : ℕ in atTop, 16 ≤ logb 2 (n : ℝ) ∧ 1 ≤ logb 2 (logb 2 (n : ℝ)) ∧
      4 * logb 2 (logb 2 (n : ℝ)) ≤ logb 2 (n : ℝ) := by
    have h₁ : ∀ᶠ x : ℝ in atTop, 16 ≤ x ∧ 1 ≤ logb 2 x ∧ 4 * logb 2 x ≤ x := by
      have hb := Real.isLittleO_log_id_atTop.bound (show (0 : ℝ) < log 2 / 4 by positivity)
      filter_upwards [hb, eventually_ge_atTop 16] with x hx h16
      have hx₀ : 0 < x := by linarith
      refine ⟨h16, ?_, ?_⟩
      · rw [Real.le_logb_iff_rpow_le (by norm_num) hx₀]; norm_num; linarith
      · simp only [Real.norm_eq_abs, id] at hx
        rw [abs_of_pos hx₀, abs_of_pos (log_pos (by linarith))] at hx
        rw [Real.logb, mul_div_assoc', div_le_iff₀ (log_pos (by norm_num))]
        linarith
    exact hLtend.eventually h₁
  -- What we need of `ℓ`.
  have evl : ∀ᶠ l : ℕ in atTop, 4096 ≤ l ∧ Cp * (l : ℝ) ^ 5 ≤ 2 ^ l ∧
      (cOf l : ℝ) * betaOf nX (1 / 2) (cOf l) * (2 * cOf l) ^ 2 ≤ 1 ∧
      (∃ S : Sched true (cOf l), S.Solves (1 / 4) ∧ S.M = 2 ^ cOf l ∧
        (S.T : ℝ) ≤ cOf l * A / 2 + P₀t + P₁t * log (cOf l)) ∧
      (∃ S : Sched false (cOf l), S.Solves (1 / 4) ∧ S.M = 2 ^ cOf l ∧
        (S.T : ℝ) ≤ cOf l * A / 2 + P₀f + P₁f * log (cOf l)) := by
    filter_upwards [eventually_ge_atTop 4096, (eventually_poly_le Cp 5 one_pos),
      tendsto_cOf.eventually (eventually_beta nX hC), tendsto_cOf.eventually hSt,
      tendsto_cOf.eventually hSf] with l h₁ h₂ h₃ h₄ h₅
    refine ⟨h₁, ?_, h₃, h₄, h₅⟩
    rwa [one_mul, Real.rpow_natCast] at h₂
  filter_upwards [tendsto_lOf.eventually evl, eventually_ge_atTop 16, evL,
    tendsto_log_log.eventually_ge_atTop 1] with n hgood hn16 hLn hll s hs
  obtain ⟨hl4096, hpoly, hβl, hSt', hSf'⟩ := hgood
  obtain ⟨hL16, hu₁, hu₄⟩ := hLn
  obtain ⟨hN₁, hN₂, hNn, hnN, hlL₁, hlL₂⟩ := lOf_bounds hn16
  set N := Nof n with hN
  set l := lOf n with hl
  set c := cOf l with hc
  obtain ⟨St, hStsolve, hStM, hStT⟩ := hSt'
  obtain ⟨Sf, hSfsolve, hSfM, hSfT⟩ := hSf'
  -- Sizes.
  have hl128 : 128 ≤ l := by omega
  have hlr : (4096 : ℝ) ≤ l := by exact_mod_cast hl4096
  have hl₀ : (0 : ℝ) < l := by linarith
  have hcl2 : (l : ℝ) / 2 ≤ c := cOf_ge hl128
  have hcl : c ≤ l := cOf_le l
  have hclr : (c : ℝ) ≤ l := by exact_mod_cast hcl
  have hc₁ : 1 ≤ c := by
    have : (1 : ℝ) ≤ c := by linarith
    exact_mod_cast this
  have hcpos : (0 : ℝ) < c := by have : (1 : ℝ) ≤ c := by exact_mod_cast hc₁
                                 linarith
  have h2c : (2 : ℝ) ^ c * (l : ℝ) ^ 6 ≤ 64 * 2 ^ l :=
    two_pow_cOf_mul l (by have := twelve_log_le hl128; omega)
  have hNr₁ : (1 : ℝ) ≤ N := le_trans (one_le_pow₀ (by norm_num)) hN₁
  have hl5 : Cp * (l : ℝ) ^ 5 ≤ N := hpoly.trans hN₁
  have hCp2 : 2 ≤ Cp := by
    rw [hCp]; have : (0 : ℝ) ≤ 5 * K₁ + 136 * (Lg * Gs) := by positivity
    linarith
  -- The grid.
  have hl4 : 2 * (l : ℝ) ^ 4 ≤ N := by
    have : 2 * (l : ℝ) ^ 4 ≤ Cp * (l : ℝ) ^ 5 := by
      have h₁ : (l : ℝ) ^ 4 ≤ (l : ℝ) ^ 5 := pow_le_pow_right₀ (by linarith) (by norm_num)
      calc 2 * (l : ℝ) ^ 4 ≤ 2 * (l : ℝ) ^ 5 := by linarith
        _ ≤ Cp * (l : ℝ) ^ 5 := mul_le_mul_of_nonneg_right hCp2 (by positivity)
    linarith
  obtain ⟨ha'Pos, hgle', hgge⟩ := sq_grid_bounds (N := N) hc₁ hcl (by omega) hl4
  set a := c * (N / (l ^ 2 * (c * c))) with ha
  have haPos : 0 < a := Nat.mul_pos (by omega) ha'Pos
  have hca : c ∣ a := Dvd.intro _ rfl
  have haR : (0 : ℝ) < a := by exact_mod_cast haPos
  have hgPos : 0 < a * c := by positivity
  have hh₁ : (N / (a * c)) * (a * c) ≤ N := Nat.div_mul_le_self _ _
  have hh₂ : N < (N / (a * c) + 1) * (a * c) := by
    have := Nat.lt_mul_div_succ N hgPos
    rw [Nat.mul_comm] at this
    exact this
  set h := N / (a * c) with hh
  have hh₁r : (h : ℝ) * ((a : ℝ) * c) ≤ N := by exact_mod_cast hh₁
  have hh₂r : (N : ℝ) ≤ ((h : ℝ) + 1) * ((a : ℝ) * c) := by exact_mod_cast hh₂.le
  obtain ⟨Y⟩ := exists_layout (n := n) (h := h) (a := a) (c := c) hh₁
  have hn₀ : 0 < (n + 1) / 2 := by omega
  have haN : (N : ℝ) ≤ 2 * (l : ℝ) ^ 3 * a := by
    have : (a : ℝ) * c ≤ a * l := mul_le_mul_of_nonneg_left hclr haR.le
    calc (N : ℝ) ≤ 2 * (l : ℝ) ^ 2 * (a * c) := hgge
      _ ≤ 2 * (l : ℝ) ^ 2 * (a * l) := mul_le_mul_of_nonneg_left this (by positivity)
      _ = 2 * (l : ℝ) ^ 3 * a := by ring
  -- The schedules.
  let Sq : ∀ q, Sched q c := fun q ↦ match q with
    | true => St
    | false => Sf
  have hSqt : Sq true = St := rfl
  have hSqf : Sq false = Sf := rfl
  have hSqsolve : ∀ q, (Sq q).Solves (1 / 4) := fun q ↦ by
    cases q
    · rw [hSqf]; exact hSfsolve
    · rw [hSqt]; exact hStsolve
  -- The bad tuples.
  set β := betaOf nX (1 / 2) c with hβ
  have hβ₀ : 0 ≤ β := by rw [hβ]; unfold betaOf; positivity
  let Bad : ∀ q, Finset (Fin c → OState q) := fun q ↦
    univ.filter fun x ↦ ¬ Typical (1 / 4) (uniform (OState q)) x
  have hBadOk : ∀ q x, x ∉ Bad q → Typical (1 / 4) (uniform (OState q)) x := by
    intro q x hx
    by_contra hcon
    exact hx (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcon⟩)
  have hBadCard : ∀ q, (#(Bad q) : ℝ) ≤ β * (Fintype.card (OState q) : ℝ) ^ c := by
    intro q
    have := typical_chernoff_explicit (α := OState q) (τ := 1 / 4) (by norm_num) (by norm_num) c
    refine this.trans (le_of_eq ?_)
    rw [hβ]; unfold betaOf; rw [hcardX q]; norm_num
  have hK₂' : ∀ q : Oblique n, CanSolve K₂ q.name := fun q ↦
    hK₂ n _ _ q.name.2.1 q.name.2.2 (Finset.mem_offDiag.mp q.2).2.2
  obtain ⟨w, hw, hlen'⟩ := method_solves Y hn₀ haPos (by omega) hca (hK₁ n) hK₂' hL Sq hSqsolve
    Bad hBadOk hBadCard s hs
  refine ⟨w, hw, ?_⟩
  have hNr0 : (0 : ℝ) ≤ N := by positivity
  -- The twist.
  have htw := cycleLen_twist_le (h := h) (a := a) (c := c) hh₁r haPos (by omega)
  have hNa : (N : ℝ) ^ 2 / a ≤ 2 * (l : ℝ) ^ 3 * N := by
    rw [div_le_iff₀ haR]
    calc (N : ℝ) ^ 2 = N * N := by ring
      _ ≤ N * (2 * (l : ℝ) ^ 3 * a) := mul_le_mul_of_nonneg_left haN hNr0
      _ = 2 * (l : ℝ) ^ 3 * N * a := by ring
  -- Stage 2.
  have hac : (2 : ℝ) ^ c * (8 * ((c : ℝ) * c)) * l ≤ a * c :=
    two_pow_le_ac (by omega) hcl h2c hN₁ hgge
  have hstep := sqLen_le (N := (N : ℝ)) (l := (l : ℝ)) hh₁r hca (by omega) (by linarith) hac
  have hlogc : log (c : ℝ) ≤ logb 2 (logb 2 (n : ℝ)) := by
    have hcL : (c : ℝ) ≤ logb 2 n := hclr.trans hlL₂
    have h₂ : log (c : ℝ) ≤ log (logb 2 n) := log_le_log hcpos hcL
    have h₃ : log (logb 2 (n : ℝ)) ≤ logb 2 (logb 2 n) := by
      have hL1 : 0 ≤ log (logb 2 (n : ℝ)) := log_nonneg (by linarith only [hL16])
      have h21 : log 2 ≤ 1 := by have := Real.log_two_lt_d9; linarith only [this]
      have h2p : 0 < log 2 := log_pos (by norm_num)
      have : log (logb 2 (n : ℝ)) ≤ log (logb 2 (n : ℝ)) / log 2 := by
        rw [le_div_iff₀ h2p]
        have := mul_le_mul_of_nonneg_left h21 hL1
        linarith only [this]
      exact this
    linarith only [h₂, h₃]
  have hlogc₀ : 0 ≤ log (c : ℝ) := log_nonneg (by exact_mod_cast hc₁)
  have hTT : ((Sq true).T : ℝ) + (Sq false).T ≤ c * A + P * logb 2 (logb 2 (n : ℝ)) := by
    rw [hSqt, hSqf]
    have hu₀ : (0 : ℝ) ≤ logb 2 (logb 2 (n : ℝ)) := by linarith only [hu₁]
    have b₁ : P₀t ≤ |P₀t| * logb 2 (logb 2 (n : ℝ)) :=
      (le_abs_self _).trans (le_mul_of_one_le_right (abs_nonneg _) hu₁)
    have b₂ : P₀f ≤ |P₀f| * logb 2 (logb 2 (n : ℝ)) :=
      (le_abs_self _).trans (le_mul_of_one_le_right (abs_nonneg _) hu₁)
    have b₃ : P₁t * log c ≤ |P₁t| * logb 2 (logb 2 (n : ℝ)) :=
      (mul_le_mul_of_nonneg_right (le_abs_self _) hlogc₀).trans
        (mul_le_mul_of_nonneg_left hlogc (abs_nonneg _))
    have b₄ : P₁f * log c ≤ |P₁f| * logb 2 (logb 2 (n : ℝ)) :=
      (mul_le_mul_of_nonneg_right (le_abs_self _) hlogc₀).trans
        (mul_le_mul_of_nonneg_left hlogc (abs_nonneg _))
    rw [hP]
    linarith only [hStT, hSfT, b₁, b₂, b₃, b₄]
  have hst2 : (((Sq true).len h a + (Sq false).len h a : ℕ) : ℝ) ≤
      N ^ 2 / c ^ 2 * (1 + 1 / l) * (c * A + P * logb 2 (logb 2 (n : ℝ))) := by
    unfold Sched.len
    have hM₁ : (Sq true).M = 2 ^ c := by rw [hSqt]; exact hStM
    have hM₂ : (Sq false).M = 2 ^ c := by rw [hSqf]; exact hSfM
    rw [hM₁, hM₂]
    push_cast
    have e : (N : ℝ) ^ 2 / c ^ 2 * (1 + 1 / l) = (N / c) ^ 2 * (1 + 1 / l) := by ring
    rw [e]
    have hq₀ : 0 ≤ (N / (c : ℝ)) ^ 2 * (1 + 1 / l) := by positivity
    calc ((Sq true).T : ℝ) * (Layout.sqLen h a c (2 ^ c) : ℝ) +
          ((Sq false).T : ℝ) * (Layout.sqLen h a c (2 ^ c) : ℝ) =
          (((Sq true).T : ℝ) + (Sq false).T) * (Layout.sqLen h a c (2 ^ c) : ℝ) := by ring
      _ ≤ (((Sq true).T : ℝ) + (Sq false).T) * ((N / c) ^ 2 * (1 + 1 / l)) :=
          mul_le_mul_of_nonneg_left hstep (by positivity)
      _ ≤ (c * A + P * logb 2 (logb 2 (n : ℝ))) * ((N / c) ^ 2 * (1 + 1 / l)) :=
          mul_le_mul_of_nonneg_right hTT hq₀
      _ = (N / c) ^ 2 * (1 + 1 / l) * (c * A + P * logb 2 (logb 2 (n : ℝ))) := by ring
  -- Stage 3.
  have hacl : (a : ℝ) * c ≤ N / (l : ℝ) ^ 2 := by
    rw [le_div_iff₀ (by positivity)]; exact hgle'
  have hl2 : (1 : ℝ) ≤ (l : ℝ) ^ 2 := one_le_pow₀ (by linarith)
  have hacN : (a : ℝ) * c ≤ N := by
    have : (a : ℝ) * c * 1 ≤ a * c * (l : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_left hl2 (by positivity)
    linarith only [this, hgle']
  have hcβ₀ : 0 ≤ (c : ℝ) * β := by positivity
  have hst3 := stage3_le (h := h) (N := (N : ℝ)) (g := (a : ℝ) * c) (β := (c : ℝ) * β)
    (by positivity) hacN hcβ₀ hh₁r hh₂r
  have hβN : (c : ℝ) * β * (N : ℝ) ^ 2 ≤ N ^ 2 / (l : ℝ) ^ 2 := by
    rw [le_div_iff₀ (by positivity)]
    have hcl' : (l : ℝ) ^ 2 ≤ (2 * c) ^ 2 := pow_le_pow_left₀ (by positivity) (by linarith) 2
    have : (c : ℝ) * β * (l : ℝ) ^ 2 ≤ 1 :=
      (mul_le_mul_of_nonneg_left hcl' hcβ₀).trans hβl
    have := mul_le_mul_of_nonneg_left this (by positivity : (0 : ℝ) ≤ (N : ℝ) ^ 2)
    linarith only [this]
  have h3N : 3 * (N : ℝ) * (a * c) ≤ 3 * (N ^ 2 / (l : ℝ) ^ 2) := by
    have := mul_le_mul_of_nonneg_left hacl (by positivity : (0 : ℝ) ≤ 3 * N)
    have e : 3 * (N : ℝ) * (N / (l : ℝ) ^ 2) = 3 * (N ^ 2 / (l : ℝ) ^ 2) := by ring
    linarith only [this, e]
  have hstage3 : (K₂ : ℝ) * ((N : ℝ) ^ 2 -
      (1 - c * β) * (((h : ℝ) ^ 2 - h) * ((a : ℝ) * c) ^ 2)) ≤ K₂ * (4 * N ^ 2 / (l : ℝ) ^ 2) := by
    apply mul_le_mul_of_nonneg_left _ hK₂0
    have e : 4 * (N : ℝ) ^ 2 / (l : ℝ) ^ 2 = 3 * (N ^ 2 / (l : ℝ) ^ 2) + N ^ 2 / (l : ℝ) ^ 2 := by
      ring
    linarith only [hst3, hβN, h3N, e]
  -- The small terms.
  have hl3N : (1 : ℝ) ≤ (l : ℝ) ^ 3 * N := by
    have h₁ : (1 : ℝ) ≤ (l : ℝ) ^ 3 := one_le_pow₀ (by linarith)
    have := mul_le_mul h₁ hNr₁ zero_le_one (by positivity)
    linarith only [this]
  have hS : ((K₁ * n : ℕ) : ℝ) + ((2 * Lg * (Gs * cycleLen h c a 1 2) : ℕ) : ℝ) ≤
      N ^ 2 / (l : ℝ) ^ 2 := by
    push_cast
    have hK₁0 : (0 : ℝ) ≤ K₁ := by positivity
    have hLG : (0 : ℝ) ≤ Lg * Gs := by positivity
    have h₁ : (K₁ : ℝ) * n ≤ 5 * K₁ * N := by
      have := mul_le_mul_of_nonneg_left hnN hK₁0
      linarith only [this]
    have h₂ : 2 * (Lg : ℝ) * (Gs * cycleLen h c a 1 2) ≤ 136 * (Lg * Gs) * ((l : ℝ) ^ 3 * N) := by
      have : (cycleLen h c a 1 2 : ℝ) ≤ 68 * ((l : ℝ) ^ 3 * N) := by
        have e : 34 * (2 * (l : ℝ) ^ 3 * N) = 68 * ((l : ℝ) ^ 3 * N) := by ring
        nlinarith only [htw, hNa, e]
      have := mul_le_mul_of_nonneg_left this hLG
      linarith only [this]
    have hNN : (N : ℝ) ≤ (l : ℝ) ^ 3 * N := by
      have : (1 : ℝ) * N ≤ (l : ℝ) ^ 3 * N :=
        mul_le_mul_of_nonneg_right (one_le_pow₀ (by linarith)) hNr0
      linarith only [this]
    have hsum3 : (K₁ : ℝ) * n + 2 * Lg * (Gs * cycleLen h c a 1 2) ≤ Cp * ((l : ℝ) ^ 3 * N) := by
      have e₁ : 5 * (K₁ : ℝ) * N ≤ 5 * K₁ * ((l : ℝ) ^ 3 * N) := by
        have := mul_le_mul_of_nonneg_left hNN (by positivity : (0 : ℝ) ≤ 5 * K₁)
        linarith only [this]
      rw [hCp]
      linarith only [h₁, h₂, e₁, hl3N]
    have hfin : Cp * ((l : ℝ) ^ 3 * N) ≤ N ^ 2 / (l : ℝ) ^ 2 := by
      rw [le_div_iff₀ (by positivity)]
      have := mul_le_mul_of_nonneg_right hl5 hNr0
      have e : Cp * ((l : ℝ) ^ 3 * N) * (l : ℝ) ^ 2 = Cp * (l : ℝ) ^ 5 * N := by ring
      have e' : (N : ℝ) ^ 2 = N * N := by ring
      linarith only [this, e, e']
    linarith only [hsum3, hfin]
  -- Put it together.
  set L := logb 2 (n : ℝ) with hLdef
  have hlen : (w.length : ℝ) ≤ (((K₁ * n : ℕ) : ℝ) +
      ((2 * Lg * (Gs * cycleLen h c a 1 2) : ℕ) : ℝ)) +
      N ^ 2 / c ^ 2 * (1 + 1 / l) * (c * A + P * logb 2 L) + K₂ * (4 * N ^ 2 / (l : ℝ) ^ 2) := by
    have := hlen'
    rw [show ((n / 2 - 1 : ℕ) : ℝ) = (N : ℝ) from rfl] at this
    have e : ((2 * Lg * (allCycles.length * cycleLen h c a 1 2) : ℕ) : ℝ) =
        ((2 * Lg * (Gs * cycleLen h c a 1 2) : ℕ) : ℝ) := rfl
    linarith only [this, hst2, hstage3, e]
  have hsub : (l : ℝ) - 6 * logb 2 l ≤ c := by linarith only [sub_cOf_le l]
  have hfin := final_sq hA₀ hK₂0 hP₀ hL16 hu₁ hlL₁ hlL₂ hsub hcl2 hNr0 hNn hlen hS
  -- From `log₂` to `log`.
  have hℓ := two_le_log hll
  have hmain : A / 4 * n ^ 2 / L = log patternCount / 4 * n ^ 2 / log n := by
    have : log 2 ≠ 0 := (log_pos (by norm_num)).ne'
    have : log (n : ℝ) ≠ 0 := by linarith
    rw [hA, hLdef, hnX]
    simp only [Real.logb]
    field_simp
  have herr := mul_le_mul_of_nonneg_left (error_le hll) hK0
  rw [hmain] at hfin
  linarith

end CubeGod
