import CubeGod.Schedule.Core

/-!
# One step

The path of `Exact/Path.lean` is built from the end backward, one balanced two-point step at a time.
This file gives the steps.

- `H_mix_ge`, `H_mix_le` and `H_mix_le_sqrt` bound the entropy gained by mixing a
  distribution with a rearranged copy of itself, using that `-x log x` has second derivative between
  `-1/l` and `-1/h` on `[l, h]`.
- `gap_le` and `sqDist_uniform_le` compare the entropy gap with the distance to uniform.
- `exists_spectral_gap` uses compactness: some step moves every mean-zero function by a
  fixed fraction of its size. It comes from Fact T.
- `step_near` and `step_far` give, for each distribution, a rate `ρm`, at least `γ/150`
  times the gap near uniform and at least `farRate` far from it, such that every rate up to `ρm` is
  the rate of a balanced two-point step (`RatesUpTo`).
-/

open Finset Real Set

set_option linter.unusedSectionVars false

namespace CubeGod

/-! ### Strong concavity of `-x log x` on an interval -/

/-- `-x log x + x²/(2h)` is concave on `[0, h]`. -/
theorem concaveOn_negMulLog_add {h : ℝ} (hh : 0 < h) :
    ConcaveOn ℝ (Icc 0 h) (fun x ↦ negMulLog x + x ^ 2 / (2 * h)) := by
  refine concaveOn_of_hasDerivWithinAt2_nonpos (convex_Icc 0 h)
    (f' := fun x ↦ -log x - 1 + x / h) (f'' := fun x ↦ -x⁻¹ + 1 / h) ?_ ?_ ?_ ?_
  · exact (continuous_negMulLog.add (by fun_prop)).continuousOn
  · intro x hx
    rw [interior_Icc] at hx ⊢
    have hx0 : x ≠ 0 := hx.1.ne'
    have h₁ := hasDerivAt_negMulLog hx0
    have h₂ : HasDerivAt (fun x : ℝ ↦ x ^ 2 / (2 * h)) (x / h) x := by
      have := (hasDerivAt_pow 2 x).div_const (2 * h)
      convert this using 1
      push_cast
      field_simp
    exact (h₁.add h₂).hasDerivWithinAt
  · intro x hx
    rw [interior_Icc] at hx ⊢
    have hx0 : x ≠ 0 := hx.1.ne'
    have h₁ : HasDerivAt (fun y ↦ -log y - 1 + y / h) (-x⁻¹ + 1 / h) x := by
      have a : HasDerivAt (fun y ↦ -log y) (-x⁻¹) x := (hasDerivAt_log hx0).neg
      have b : HasDerivAt (fun y ↦ y / h) (1 / h) x := by
        simpa using (hasDerivAt_id x).div_const h
      exact (a.sub_const 1).add b
    exact h₁.hasDerivWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    have : 1 / h ≤ x⁻¹ := by
      rw [one_div]
      exact inv_anti₀ hx.1 hx.2.le
    linarith

/-- `-x log x + x²/(2l)` is convex on `[l, ∞)`. -/
theorem convexOn_negMulLog_add {l : ℝ} (hl : 0 < l) :
    ConvexOn ℝ (Ici l) (fun x ↦ negMulLog x + x ^ 2 / (2 * l)) := by
  refine convexOn_of_hasDerivWithinAt2_nonneg (convex_Ici l)
    (f' := fun x ↦ -log x - 1 + x / l) (f'' := fun x ↦ -x⁻¹ + 1 / l) ?_ ?_ ?_ ?_
  · exact (continuous_negMulLog.add (by fun_prop)).continuousOn
  · intro x hx
    rw [interior_Ici] at hx ⊢
    have hx0 : x ≠ 0 := (hl.trans hx).ne'
    have h₁ := hasDerivAt_negMulLog hx0
    have h₂ : HasDerivAt (fun x : ℝ ↦ x ^ 2 / (2 * l)) (x / l) x := by
      have := (hasDerivAt_pow 2 x).div_const (2 * l)
      convert this using 1
      push_cast
      field_simp
    exact (h₁.add h₂).hasDerivWithinAt
  · intro x hx
    rw [interior_Ici] at hx ⊢
    have hx0 : x ≠ 0 := (hl.trans hx).ne'
    have h₁ : HasDerivAt (fun y ↦ -log y - 1 + y / l) (-x⁻¹ + 1 / l) x := by
      have a : HasDerivAt (fun y ↦ -log y) (-x⁻¹) x := (hasDerivAt_log hx0).neg
      have b : HasDerivAt (fun y ↦ y / l) (1 / l) x := by
        simpa using (hasDerivAt_id x).div_const l
      exact (a.sub_const 1).add b
    exact h₁.hasDerivWithinAt
  · intro x hx
    rw [interior_Ici] at hx
    have : x⁻¹ ≤ 1 / l := by
      rw [one_div]
      exact inv_anti₀ hl hx.le
    linarith

/-- The algebra behind both bounds. -/
theorem mix_sq (x y t : ℝ) :
    (1 - t) * x ^ 2 + t * y ^ 2 - ((1 - t) * x + t * y) ^ 2 = t * (1 - t) * (x - y) ^ 2 := by
  ring

/-- Mixing gains at least `t(1-t)(x-y)²/(2h)` on `[0, h]`. -/
theorem negMulLog_mix_ge {h x y t : ℝ} (hh : 0 < h) (hx : x ∈ Icc 0 h) (hy : y ∈ Icc 0 h)
    (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) :
    (1 - t) * negMulLog x + t * negMulLog y + t * (1 - t) * (x - y) ^ 2 / (2 * h)
      ≤ negMulLog ((1 - t) * x + t * y) := by
  have := (concaveOn_negMulLog_add hh).2 hx hy (by linarith : 0 ≤ 1 - t) ht₀ (by ring)
  simp only [smul_eq_mul] at this
  have e := mix_sq x y t
  have : t * (1 - t) * (x - y) ^ 2 / (2 * h) =
      ((1 - t) * x ^ 2 + t * y ^ 2 - ((1 - t) * x + t * y) ^ 2) / (2 * h) := by rw [e]
  rw [this]
  field_simp at *
  linarith

/-- Mixing gains at most `t(1-t)(x-y)²/(2l)` on `[l, ∞)`. -/
theorem negMulLog_mix_le {l x y t : ℝ} (hl : 0 < l) (hx : l ≤ x) (hy : l ≤ y)
    (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) :
    negMulLog ((1 - t) * x + t * y)
      ≤ (1 - t) * negMulLog x + t * negMulLog y + t * (1 - t) * (x - y) ^ 2 / (2 * l) := by
  have := (convexOn_negMulLog_add hl).2 (mem_Ici.mpr hx) (mem_Ici.mpr hy)
    (by linarith : 0 ≤ 1 - t) ht₀ (by ring)
  simp only [smul_eq_mul] at this
  have e := mix_sq x y t
  have : t * (1 - t) * (x - y) ^ 2 / (2 * l) =
      ((1 - t) * x ^ 2 + t * y ^ 2 - ((1 - t) * x + t * y) ^ 2) / (2 * l) := by rw [e]
  rw [this]
  field_simp at *
  linarith

/-! ### Entropy of a mixture -/

variable {X : Type*} [Fintype X]

/-- The squared distance `∑ (V x - W x)²`. -/
def sqDist (V W : X → ℝ) : ℝ := ∑ x, (V x - W x) ^ 2

theorem sqDist_nonneg (V W : X → ℝ) : 0 ≤ sqDist V W :=
  Finset.sum_nonneg fun _ _ ↦ sq_nonneg _

/-- Every value of `W` is in `[l, h]`. -/
def InBand (l h : ℝ) (W : X → ℝ) : Prop := ∀ x, l ≤ W x ∧ W x ≤ h

omit [Fintype X] in
theorem InBand.mix {l h t : ℝ} {V W : X → ℝ} (hV : InBand l h V) (hW : InBand l h W)
    (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) : InBand l h (fun x ↦ (1 - t) * V x + t * W x) := by
  intro x
  obtain ⟨a, b⟩ := hV x
  obtain ⟨c, d⟩ := hW x
  constructor <;> nlinarith

omit [Fintype X] in
theorem InBand.comp {l h : ℝ} {W : X → ℝ} (hW : InBand l h W) (σ : Equiv.Perm X) :
    InBand l h (fun x ↦ W (σ x)) := fun x ↦ hW (σ x)

omit [Fintype X] in
theorem InBand.mono {l h l' h' : ℝ} {W : X → ℝ} (hW : InBand l h W) (hl : l' ≤ l) (hh : h ≤ h') :
    InBand l' h' W := fun x ↦ ⟨hl.trans (hW x).1, (hW x).2.trans hh⟩

/-- Mixing two distributions on `[0, h]` gains at least `t(1-t)·∑(V - W)²/(2h)` nats. -/
theorem H_mix_ge {h t : ℝ} (hh : 0 < h) {V W : X → ℝ} (hV : InBand 0 h V) (hW : InBand 0 h W)
    (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) :
    (1 - t) * H V + t * H W + t * (1 - t) * sqDist V W / (2 * h * log 2)
      ≤ H (fun x ↦ (1 - t) * V x + t * W x) := by
  have hs := Finset.sum_le_sum fun x (_ : x ∈ Finset.univ) ↦
    negMulLog_mix_ge hh (hV x) (hW x) ht₀ ht₁
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_div] at hs
  have hl := log_two_pos'
  unfold H sqDist
  have e : (1 - t) * ((∑ x, negMulLog (V x)) / log 2) + t * ((∑ x, negMulLog (W x)) / log 2) +
      t * (1 - t) * (∑ x, (V x - W x) ^ 2) / (2 * h * log 2) =
      ((1 - t) * (∑ x, negMulLog (V x)) + t * (∑ x, negMulLog (W x)) +
        t * (1 - t) * (∑ x, (V x - W x) ^ 2) / (2 * h)) / log 2 := by
    field_simp
  rw [e]
  exact div_le_div_of_nonneg_right hs hl.le

/-- Mixing two distributions on `[l, ∞)` gains at most `t(1-t)·∑(V - W)²/(2l)` nats. -/
theorem H_mix_le {l t : ℝ} (hl : 0 < l) {V W : X → ℝ} (hV : ∀ x, l ≤ V x) (hW : ∀ x, l ≤ W x)
    (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) :
    H (fun x ↦ (1 - t) * V x + t * W x)
      ≤ (1 - t) * H V + t * H W + t * (1 - t) * sqDist V W / (2 * l * log 2) := by
  have hs := Finset.sum_le_sum fun x (_ : x ∈ Finset.univ) ↦
    negMulLog_mix_le hl (hV x) (hW x) ht₀ ht₁
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_div] at hs
  have h2 := log_two_pos'
  unfold H sqDist
  have e : (1 - t) * ((∑ x, negMulLog (V x)) / log 2) + t * ((∑ x, negMulLog (W x)) / log 2) +
      t * (1 - t) * (∑ x, (V x - W x) ^ 2) / (2 * l * log 2) =
      ((1 - t) * (∑ x, negMulLog (V x)) + t * (∑ x, negMulLog (W x)) +
        t * (1 - t) * (∑ x, (V x - W x) ^ 2) / (2 * l)) / log 2 := by
    field_simp
  rw [e]
  exact div_le_div_of_nonneg_right hs h2.le

/-- `-(x + y) log (x + y) ≤ -x log x - y log y`. -/
theorem negMulLog_add_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    negMulLog (x + y) ≤ negMulLog x + negMulLog y := by
  rcases hx.eq_or_lt with rfl | hx'
  · simp
  have hxy : 0 < x + y := by linarith
  have h₁ : log x ≤ log (x + y) := log_le_log hx' (by linarith)
  have h₂ : y * log y ≤ y * log (x + y) := by
    rcases hy.eq_or_lt with rfl | hy'
    · simp
    exact mul_le_mul_of_nonneg_left (log_le_log hy' (by linarith)) hy
  simp only [negMulLog]
  nlinarith

/-- `-t log t ≤ 2√t`. -/
theorem negMulLog_le_two_sqrt {t : ℝ} (ht : 0 ≤ t) : negMulLog t ≤ 2 * Real.sqrt t := by
  rcases ht.eq_or_lt with rfl | ht'
  · simp
  have hs : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht'
  have hss : Real.sqrt t * Real.sqrt t = t := Real.mul_self_sqrt ht
  have hlog : log t = 2 * log (Real.sqrt t) := by
    rw [Real.log_sqrt ht]; ring
  have h₁ := one_sub_inv_le_log_of_pos hs
  rw [negMulLog, hlog]
  have : t * (Real.sqrt t)⁻¹ = Real.sqrt t := by
    calc t * (Real.sqrt t)⁻¹ = (Real.sqrt t * Real.sqrt t) * (Real.sqrt t)⁻¹ := by rw [hss]
      _ = Real.sqrt t := by field_simp
  nlinarith [Real.sqrt_nonneg t]

/-- Mixing gains at most `5√t` bits, always. -/
theorem H_mix_le_sqrt {t : ℝ} {V W : X → ℝ} (hV : IsDist V) (hW : IsDist W) (ht₀ : 0 ≤ t)
    (ht₁ : t ≤ 1) :
    H (fun x ↦ (1 - t) * V x + t * W x) ≤ (1 - t) * H V + t * H W + 5 * Real.sqrt t := by
  have hpt : ∀ x, negMulLog ((1 - t) * V x + t * W x) ≤
      V x * negMulLog (1 - t) + (1 - t) * negMulLog (V x) +
        (W x * negMulLog t + t * negMulLog (W x)) := by
    intro x
    have := negMulLog_add_le (mul_nonneg (by linarith : 0 ≤ 1 - t) (hV.nonneg x))
      (mul_nonneg ht₀ (hW.nonneg x))
    rw [negMulLog_mul, negMulLog_mul] at this
    linarith
  have hs := Finset.sum_le_sum fun x (_ : x ∈ Finset.univ) ↦ hpt x
  simp only [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum, hV.sum, hW.sum,
    one_mul] at hs
  have h₁ : negMulLog (1 - t) ≤ t := by
    have := negMulLog_le_one_sub_self (by linarith : 0 ≤ 1 - t); linarith
  have h₂ := negMulLog_le_two_sqrt ht₀
  have h₃ : t ≤ Real.sqrt t := by
    have := Real.sqrt_le_sqrt (show t * t ≤ t by nlinarith)
    rwa [Real.sqrt_mul_self ht₀] at this
  have hl := log_two_pos'
  have hl₁ : 3 / 5 ≤ log 2 := by have := Real.log_two_gt_d9; linarith
  unfold H
  rw [div_le_iff₀ hl]
  have e : ((1 - t) * ((∑ x, negMulLog (V x)) / log 2) + t * ((∑ x, negMulLog (W x)) / log 2) +
      5 * Real.sqrt t) * log 2 = (1 - t) * (∑ x, negMulLog (V x)) +
        t * (∑ x, negMulLog (W x)) + 5 * Real.sqrt t * log 2 := by
    field_simp
  rw [e]
  nlinarith [Real.sqrt_nonneg t]

theorem H_comp_perm (W : X → ℝ) (σ : Equiv.Perm X) : H (fun x ↦ W (σ x)) = H W :=
  H_comp_equiv W σ

theorem sqDist_comp_inv (W : X → ℝ) (σ : Equiv.Perm X) :
    sqDist W (fun x ↦ W (σ⁻¹ x)) = sqDist W (fun x ↦ W (σ x)) := by
  unfold sqDist
  rw [← Equiv.sum_comp σ]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  have : σ⁻¹ (σ x) = x := by simp
  simp only [this]
  ring

/-! ### The gap to uniform -/

/-- The gap to the largest entropy. -/
noncomputable def gap (W : X → ℝ) : ℝ := logb 2 (Fintype.card X) - H W

theorem gap_nonneg [Nonempty X] {W : X → ℝ} (hW : IsDist W) : 0 ≤ gap W := by
  have := H_le_log_card hW
  unfold gap
  linarith

theorem sqDist_uniform_eq [Nonempty X] {W : X → ℝ} (hW : IsDist W) :
    sqDist W (uniform X) = ∑ x, W x ^ 2 - (Fintype.card X : ℝ)⁻¹ := by
  have hn : (Fintype.card X : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  unfold sqDist uniform
  have : ∀ x, (W x - (Fintype.card X : ℝ)⁻¹) ^ 2 =
      W x ^ 2 - 2 * (Fintype.card X : ℝ)⁻¹ * W x + ((Fintype.card X : ℝ)⁻¹) ^ 2 := fun x ↦ by ring
  simp only [this, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hW.sum,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp
  ring

/-- The gap is at most `|X|·∑(W - U)²` nats. -/
theorem gap_le [Nonempty X] {W : X → ℝ} (hW : IsDist W) :
    gap W ≤ Fintype.card X * sqDist W (uniform X) / log 2 := by
  set n : ℝ := (Fintype.card X : ℝ) with hn
  have hn₀ : 0 < n := by rw [hn]; exact_mod_cast Fintype.card_pos
  have h2 := log_two_pos'
  have hpt : ∀ x, W x * log n - negMulLog (W x) ≤ W x * (n * W x - 1) := by
    intro x
    rcases (hW.nonneg x).eq_or_lt with h | h
    · rw [← h]; simp
    · have := log_le_sub_one_of_pos (mul_pos hn₀ h)
      rw [log_mul hn₀.ne' h.ne'] at this
      rw [negMulLog]
      nlinarith
  have hs := Finset.sum_le_sum fun x (_ : x ∈ Finset.univ) ↦ hpt x
  simp only [Finset.sum_sub_distrib, ← Finset.sum_mul, hW.sum, one_mul, mul_sub,
    mul_one] at hs
  have hsq : ∑ x, W x * (n * W x) = n * ∑ x, W x ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ ↦ by ring
  rw [hsq] at hs
  rw [sqDist_uniform_eq hW, gap, H, logb, ← hn]
  rw [div_sub_div_same, div_le_div_iff_of_pos_right h2]
  have : n * (∑ x, W x ^ 2 - n⁻¹) = n * ∑ x, W x ^ 2 - 1 := by
    field_simp
  rw [this]
  linarith

/-- The gap is at least `∑(W - U)²/4` nats. -/
theorem sqDist_uniform_le [Nonempty X] {W : X → ℝ} (hW : IsDist W) :
    sqDist W (uniform X) ≤ 4 * log 2 * gap W := by
  have hU := isDist_uniform (α := X)
  have hb : ∀ {V : X → ℝ}, IsDist V → InBand 0 1 V := fun hV x ↦ ⟨hV.nonneg x, hV.le_one x⟩
  have hmix := H_mix_ge one_pos (hb hW) (hb hU) (t := 1 / 2) (by norm_num) (by norm_num)
  have hle := H_le_log_card (hW.mix hU (t := 1 / 2) (by norm_num) (by norm_num))
  rw [H_uniform] at hmix
  have h2 := log_two_pos'
  unfold gap
  have e : 1 / 2 * (1 - 1 / 2) * sqDist W (uniform X) / (2 * 1 * log 2) =
      sqDist W (uniform X) / (8 * log 2) := by ring
  rw [e] at hmix
  have : sqDist W (uniform X) / (8 * log 2) ≤ (logb 2 (Fintype.card X) - H W) / 2 := by linarith
  rw [div_le_iff₀ (by positivity)] at this
  linarith

/-- A small gap puts `W` close to uniform at every point. -/
theorem sq_sub_uniform_le [Nonempty X] {W : X → ℝ} (hW : IsDist W) (x : X) :
    (W x - uniform X x) ^ 2 ≤ 4 * gap W := by
  have h₁ : (W x - uniform X x) ^ 2 ≤ sqDist W (uniform X) :=
    Finset.single_le_sum (f := fun x ↦ (W x - uniform X x) ^ 2) (fun _ _ ↦ sq_nonneg _)
      (Finset.mem_univ x)
  have h₂ := sqDist_uniform_le hW
  have h₃ : log 2 < 1 := by
    have := Real.log_two_lt_d9
    linarith
  have h₄ := gap_nonneg hW
  nlinarith

/-- With a gap of at most `1/(16|X|²)`, every value is within a factor of `1 ± ½` of uniform. -/
theorem inBand_of_gap [Nonempty X] {W : X → ℝ} (hW : IsDist W)
    (hg : gap W ≤ 1 / (16 * (Fintype.card X : ℝ) ^ 2)) :
    InBand (1 / (2 * Fintype.card X)) (3 / (2 * Fintype.card X)) W := by
  set n : ℝ := (Fintype.card X : ℝ) with hn
  have hn₀ : 0 < n := by rw [hn]; exact_mod_cast Fintype.card_pos
  intro x
  have h := (sq_sub_uniform_le hW x).trans (mul_le_mul_of_nonneg_left hg (by norm_num))
  have e : 4 * (1 / (16 * n ^ 2)) = (1 / (2 * n)) ^ 2 := by field_simp; ring
  rw [e, uniform, ← hn] at h
  have := abs_le_of_sq_le_sq' h (by positivity)
  have e₁ : n⁻¹ - 1 / (2 * n) = 1 / (2 * n) := by field_simp; ring
  have e₂ : n⁻¹ + 1 / (2 * n) = 3 / (2 * n) := by field_simp; ring
  constructor <;> linarith [this.1, this.2]

/-! ### The spectral gap -/

namespace CycleSystem

variable {A G : Type*} [DecidableEq X] [Fintype A] [DecidableEq A] [Zero A]
variable {Γ : CycleSystem X A G}

omit [Fintype X] [DecidableEq X] [Fintype A] [DecidableEq A] in
/-- A function that every step leaves alone is constant, by Fact T. -/
theorem const_of_invariant {v : X → ℝ} (hinv : ∀ g a x, v (Γ.e g a x) = v x) (x y : X) :
    v x = v y := by
  have hcomp : ∀ w ∈ Subgroup.closure (Set.range fun q : G × A ↦ Γ.e q.1 q.2), ∀ x, v (w x) = v x := by
    intro w hw
    induction hw using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨q, rfl⟩ := hx
      exact hinv q.1 q.2
    | one => intro x; rfl
    | mul x y _ _ hx hy => intro s; simpa using (hx (y s)).trans (hy s)
    | inv x _ hx => intro s; simpa using (hx (x⁻¹ s)).symm
  obtain ⟨w, hw, rfl⟩ := Γ.trans x y
  exact (hcomp w hw x).symm

omit [DecidableEq X] [Fintype A] [DecidableEq A] in
/-- The spectral gap: some step moves every mean-zero function by a fixed fraction of its size. -/
theorem exists_spectral_gap [Nonempty X] :
    ∃ γ > 0, ∀ v : X → ℝ, ∑ x, v x = 0 → v ≠ 0 →
      ∃ g a, γ * ∑ x, v x ^ 2 ≤ sqDist v (fun x ↦ v (Γ.e g a x)) := by
  -- The unit sphere of mean-zero functions is compact.
  set K : Set (X → ℝ) := {v | ∑ x, v x = 0} ∩ {v | ∑ x, v x ^ 2 = 1} with hKdef
  have hK : IsCompact K := by
    have hbox : IsCompact (Set.pi Set.univ fun _ : X ↦ Icc (-1 : ℝ) 1) :=
      isCompact_univ_pi fun _ ↦ isCompact_Icc
    refine hbox.of_isClosed_subset ?_ ?_
    · exact (isClosed_eq (by fun_prop) continuous_const).inter
        (isClosed_eq (by fun_prop) continuous_const)
    · intro v hv x _
      have h₁ : v x ^ 2 ≤ 1 := by
        rw [← hv.2]
        exact Finset.single_le_sum (f := fun x ↦ v x ^ 2) (fun _ _ ↦ sq_nonneg _)
          (Finset.mem_univ x)
      exact ⟨by nlinarith, by nlinarith⟩
  have hcont : ∀ g a, Continuous fun v : X → ℝ ↦ sqDist v (fun x ↦ v (Γ.e g a x)) := by
    intro g a
    unfold sqDist
    fun_prop
  -- Each point of the sphere is moved by some step, and so are its neighbours.
  have hloc : ∃ γ > 0, ∀ v ∈ K, ∃ g a, γ ≤ sqDist v (fun x ↦ v (Γ.e g a x)) := by
    refine hK.induction_on (p := fun s ↦ ∃ γ > 0, ∀ v ∈ s, ∃ g a,
      γ ≤ sqDist v (fun x ↦ v (Γ.e g a x))) ?_ ?_ ?_ ?_
    · exact ⟨1, one_pos, by simp⟩
    · rintro s t hst ⟨γ, hγ, h⟩
      exact ⟨γ, hγ, fun v hv ↦ h v (hst hv)⟩
    · rintro s t ⟨γ₁, h₁, hs⟩ ⟨γ₂, h₂, ht⟩
      refine ⟨min γ₁ γ₂, lt_min h₁ h₂, ?_⟩
      rintro v (hv | hv)
      · obtain ⟨g, a, h⟩ := hs v hv
        exact ⟨g, a, (min_le_left _ _).trans h⟩
      · obtain ⟨g, a, h⟩ := ht v hv
        exact ⟨g, a, (min_le_right _ _).trans h⟩
    · intro v₀ hv₀
      have hmove : ∃ g a, 0 < sqDist v₀ (fun x ↦ v₀ (Γ.e g a x)) := by
        by_contra hall
        push Not at hall
        have hinv : ∀ g a x, v₀ (Γ.e g a x) = v₀ x := by
          intro g a x
          have h0 : sqDist v₀ (fun x ↦ v₀ (Γ.e g a x)) = 0 :=
            le_antisymm (hall g a) (sqDist_nonneg _ _)
          have := (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ ↦ sq_nonneg _)).mp h0 x
            (Finset.mem_univ x)
          have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
          linarith
        obtain ⟨x₀⟩ := ‹Nonempty X›
        have hc := const_of_invariant hinv
        have hsum : ∑ x, v₀ x = 0 := hv₀.1
        simp only [hc _ x₀, Finset.sum_const, Finset.card_univ,
          nsmul_eq_mul] at hsum
        have hn : (Fintype.card X : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
        have h0 : v₀ x₀ = 0 := by
          rcases mul_eq_zero.mp hsum with h | h
          · exact absurd h hn
          · exact h
        have hsq : ∑ x, v₀ x ^ 2 = 1 := hv₀.2
        simp only [hc _ x₀, h0] at hsq
        simp at hsq
      obtain ⟨g, a, hpos⟩ := hmove
      have hev : ∀ᶠ v in nhds v₀, sqDist v₀ (fun x ↦ v₀ (Γ.e g a x)) / 2 <
          sqDist v (fun x ↦ v (Γ.e g a x)) :=
        (hcont g a).continuousAt.eventually (lt_mem_nhds (half_lt_self hpos))
      refine ⟨_, mem_nhdsWithin_of_mem_nhds hev, _, half_pos hpos, fun v hv ↦ ⟨g, a, hv.le⟩⟩
  obtain ⟨γ, hγ, h⟩ := hloc
  refine ⟨γ, hγ, fun v hv0 hne ↦ ?_⟩
  -- Scale `v` onto the sphere.
  set s := ∑ x, v x ^ 2 with hs
  have hs₀ : 0 < s := by
    obtain ⟨x, hx⟩ := Function.ne_iff.mp hne
    have hx' : v x ≠ 0 := hx
    have : 0 < v x ^ 2 := by positivity
    exact lt_of_lt_of_le this (Finset.single_le_sum (f := fun x ↦ v x ^ 2)
      (fun _ _ ↦ sq_nonneg _) (Finset.mem_univ x))
  set c := (Real.sqrt s)⁻¹ with hc
  have hc2 : c ^ 2 = s⁻¹ := by rw [hc, inv_pow, Real.sq_sqrt hs₀.le]
  have hw : (fun x ↦ c * v x) ∈ K := by
    refine ⟨?_, ?_⟩
    · show ∑ x, c * v x = 0
      rw [← Finset.mul_sum, hv0, mul_zero]
    · show ∑ x, (c * v x) ^ 2 = 1
      simp only [mul_pow, ← Finset.mul_sum, hc2]
      exact inv_mul_cancel₀ hs₀.ne'
  obtain ⟨g, a, hga⟩ := h _ hw
  refine ⟨g, a, ?_⟩
  have e : sqDist (fun x ↦ c * v x) (fun x ↦ c * v (Γ.e g a x)) =
      c ^ 2 * sqDist v (fun x ↦ v (Γ.e g a x)) := by
    unfold sqDist
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ ↦ by ring
  rw [e, hc2] at hga
  have := mul_le_mul_of_nonneg_left hga hs₀.le
  rwa [← mul_assoc, mul_inv_cancel₀ hs₀.ne', one_mul, mul_comm] at this

/-! ### Tools for one step -/

/-- `(a - b)² ≥ a²/2 - b²`. -/
theorem sq_sub_ge (a b : ℝ) : a ^ 2 / 2 - b ^ 2 ≤ (a - b) ^ 2 := by
  nlinarith [sq_nonneg (a - 2 * b)]

omit [DecidableEq X] in
/-- After the second firing, the first firing still has `‖Y - Y∘e‖²` between `D/4` and `2D`. -/
theorem sqDist_mixY (E : Equiv.Perm X) (W : X → ℝ) {β : ℝ} (hβ₀ : 0 ≤ β) (hβ₁ : β ≤ 1 / 8) :
    sqDist W (fun x ↦ W (E x)) / 4 ≤ sqDist (mixY E β W) (fun x ↦ mixY E β W (E x)) ∧
      sqDist (mixY E β W) (fun x ↦ mixY E β W (E x)) ≤ 2 * sqDist W (fun x ↦ W (E x)) := by
  set D := sqDist W (fun x ↦ W (E x)) with hD
  have e : ∀ x, mixY E β W x - mixY E β W (E x) =
      (1 - β) * (W x - W (E x)) - β * (W x - W (E⁻¹ x)) := by
    intro x
    have : E⁻¹ (E x) = x := by simp
    simp only [mixY, this]
    ring
  have e₂ : ∑ x, (W x - W (E⁻¹ x)) ^ 2 = D := by
    rw [hD, ← sqDist_comp_inv W E]
    rfl
  constructor
  · have hpt : ∀ x, (1 - β) ^ 2 / 2 * (W x - W (E x)) ^ 2 - β ^ 2 * (W x - W (E⁻¹ x)) ^ 2
        ≤ (mixY E β W x - mixY E β W (E x)) ^ 2 := by
      intro x
      rw [e]
      have := sq_sub_ge ((1 - β) * (W x - W (E x))) (β * (W x - W (E⁻¹ x)))
      nlinarith
    have hs := Finset.sum_le_sum fun x (_ : x ∈ Finset.univ) ↦ hpt x
    have e₁ : ∑ x, (W x - W (E x)) ^ 2 = D := rfl
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, e₁, e₂] at hs
    have hD₀ : 0 ≤ D := sqDist_nonneg _ _
    have hc : 1 / 4 ≤ (1 - β) ^ 2 / 2 - β ^ 2 := by nlinarith
    have : D / 4 ≤ (1 - β) ^ 2 / 2 * D - β ^ 2 * D := by
      nlinarith [mul_le_mul_of_nonneg_right hc hD₀]
    exact this.trans hs
  · have hpt : ∀ x, (mixY E β W x - mixY E β W (E x)) ^ 2 ≤
        2 * (1 - β) ^ 2 * (W x - W (E x)) ^ 2 + 2 * β ^ 2 * (W x - W (E⁻¹ x)) ^ 2 := by
      intro x
      rw [e]
      nlinarith [sq_nonneg ((1 - β) * (W x - W (E x)) + β * (W x - W (E⁻¹ x)))]
    have hs := Finset.sum_le_sum fun x (_ : x ∈ Finset.univ) ↦ hpt x
    have e₁ : ∑ x, (W x - W (E x)) ^ 2 = D := rfl
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, e₁, e₂] at hs
    have hD₀ : 0 ≤ D := sqDist_nonneg _ _
    have hc : (1 - β) ^ 2 + β ^ 2 ≤ 1 := by nlinarith
    have : 2 * (1 - β) ^ 2 * D + 2 * β ^ 2 * D ≤ 2 * D := by
      nlinarith [mul_le_mul_of_nonneg_right hc hD₀]
    exact hs.trans this

omit [DecidableEq X] in
/-- The intermediate value theorem, twice: if the second firing never gains more than the first can at
`α = ½`, then every rate up to `gainB bm` is the rate of a balanced two-point step. -/
theorem exists_balanced_rate (E : Equiv.Perm X) (W : X → ℝ) {bm : ℝ} (hbm : 0 ≤ bm)
    (hle : ∀ β ∈ Icc 0 bm, gainB E W β ≤ gainA E W (1 / 2) β) {ρ : ℝ} (hρ₀ : 0 ≤ ρ)
    (hρ : ρ ≤ gainB E W bm) :
    ∃ β ∈ Icc 0 bm, ∃ α ∈ Icc (0 : ℝ) (1 / 2), gainB E W β = ρ ∧ gainA E W α β = ρ := by
  have hB : ContinuousOn (fun β ↦ gainB E W β) (Icc 0 bm) :=
    (continuous_gainB' E continuous_const continuous_id).continuousOn
  have hmem : ρ ∈ Icc (gainB E W 0) (gainB E W bm) := by
    rw [gainB_zero]; exact ⟨hρ₀, hρ⟩
  obtain ⟨β, hβ, hβρ⟩ := intermediate_value_Icc hbm hB hmem
  have hA : ContinuousOn (fun α ↦ gainA E W α β) (Icc 0 (1 / 2)) :=
    (continuous_gainA' E continuous_const continuous_id continuous_const).continuousOn
  have hmem' : ρ ∈ Icc (gainA E W 0 β) (gainA E W (1 / 2) β) := by
    rw [gainA_zero]
    exact ⟨hρ₀, hβρ ▸ hle β hβ⟩
  obtain ⟨α, hα, hαρ⟩ := intermediate_value_Icc (by norm_num) hA hmem'
  exact ⟨β, hβ, α, hα, hβρ, hαρ⟩

omit [DecidableEq X] in
theorem isDist_mixY {E : Equiv.Perm X} {W : X → ℝ} (hW : IsDist W) {β : ℝ}
    (h₀ : 0 ≤ β) (h₁ : β ≤ 1) : IsDist (mixY E β W) :=
  hW.mix (hW.comp_equiv E⁻¹) h₀ h₁

/-- What a step lemma gives: for every rate up to `ρm`, a two-point step at `W` with that rate at
both firings. -/
def RatesUpTo (Γ : CycleSystem X A G) (W : X → ℝ) (ρm : ℝ) : Prop :=
  ∀ ρ, 0 ≤ ρ → ρ ≤ ρm → ∃ g a, ∃ α β : ℝ, 0 ≤ α ∧ α ≤ 1 ∧ 0 ≤ β ∧ β ≤ 1 ∧
    gainA (Γ.e g a) W α β = ρ ∧ gainB (Γ.e g a) W β = ρ

/-! ### The step lemma -/

/-- Below this gap, `W` is within a factor `1 ± ½` of uniform. -/
noncomputable def etaNear (X : Type*) [Fintype X] : ℝ := 1 / (16 * (Fintype.card X : ℝ) ^ 2)

theorem etaNear_pos (X : Type*) [Fintype X] [Nonempty X] : 0 < etaNear X := by
  have : (0 : ℝ) < Fintype.card X := by exact_mod_cast Fintype.card_pos
  unfold etaNear; positivity

/-- The spectral gap property of `γ`. -/
def SpectralGap (Γ : CycleSystem X A G) (γ : ℝ) : Prop :=
  ∀ v : X → ℝ, ∑ x, v x = 0 → v ≠ 0 → ∃ g a, γ * ∑ x, v x ^ 2 ≤ sqDist v (fun x ↦ v (Γ.e g a x))

omit [DecidableEq X] [Fintype A] [DecidableEq A] in
/-- The step of the spectral gap, applied to `W - U`. -/
theorem exists_mover [Nonempty X] {γ : ℝ} (hspec : Γ.SpectralGap γ) {W : X → ℝ} (hW : IsDist W)
    (hne : W ≠ uniform X) :
    ∃ g a, γ * sqDist W (uniform X) ≤ sqDist W (fun x ↦ W (Γ.e g a x)) := by
  set v : X → ℝ := fun x ↦ W x - uniform X x with hv
  have hv0 : ∑ x, v x = 0 := by
    simp only [hv, Finset.sum_sub_distrib, hW.sum, (isDist_uniform (α := X)).sum, sub_self]
  have hvne : v ≠ 0 := by
    intro h
    apply hne
    funext x
    have := congrFun h x
    simp only [hv, Pi.zero_apply] at this
    linarith
  obtain ⟨g, a, hga⟩ := hspec v hv0 hvne
  refine ⟨g, a, ?_⟩
  have e₂ : sqDist v (fun x ↦ v (Γ.e g a x)) = sqDist W (fun x ↦ W (Γ.e g a x)) := by
    unfold sqDist
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    simp only [hv, uniform]
    ring
  rw [← e₂]
  exact hga

omit [DecidableEq X] in
theorem sqDist_pos_of_ne {V W : X → ℝ} (h : V ≠ W) : 0 < sqDist V W := by
  obtain ⟨x, hx⟩ := Function.ne_iff.mp h
  have : 0 < (V x - W x) ^ 2 := by
    have : V x - W x ≠ 0 := sub_ne_zero.mpr hx
    positivity
  exact lt_of_lt_of_le this (Finset.single_le_sum (f := fun x ↦ (V x - W x) ^ 2)
    (fun _ _ ↦ sq_nonneg _) (Finset.mem_univ x))

omit [DecidableEq X] in
/-- `‖W - U‖² ≥ gap·ln 2/|X|`. -/
theorem sqDist_ge_gap [Nonempty X] {W : X → ℝ} (hW : IsDist W) :
    gap W * log 2 / Fintype.card X ≤ sqDist W (uniform X) := by
  have hn₀ : (0 : ℝ) < Fintype.card X := by exact_mod_cast Fintype.card_pos
  have h := gap_le hW
  rw [div_le_iff₀ hn₀]
  rw [le_div_iff₀ log_two_pos'] at h
  linarith

omit [DecidableEq X] [Fintype A] [DecidableEq A] in
/-- The step lemma, near uniform. -/
theorem step_near [Nonempty X] {γ : ℝ} (hγ : 0 < γ) (hspec : Γ.SpectralGap γ) {W : X → ℝ}
    (hW : IsDist W) (hgap : gap W ≤ etaNear X) (hne : W ≠ uniform X) :
    ∃ ρm : ℝ, 0 < ρm ∧ ρm ≤ 1 ∧ γ / 150 * gap W ≤ ρm ∧ Γ.RatesUpTo W ρm := by
  set n : ℝ := (Fintype.card X : ℝ) with hn
  have hn₀ : 0 < n := by rw [hn]; exact_mod_cast Fintype.card_pos
  have h2 := log_two_pos'
  set l : ℝ := 1 / (2 * n) with hl
  have hl₀ : 0 < l := by positivity
  have hb : InBand l (3 * l) W :=
    (inBand_of_gap hW hgap).mono le_rfl (le_of_eq (by rw [hl, ← hn]; ring))
  have hb₀ : InBand 0 (3 * l) W := hb.mono hl₀.le le_rfl
  obtain ⟨g, a, hga⟩ := exists_mover hspec hW hne
  set E := Γ.e g a with hE
  set D := sqDist W (fun x ↦ W (E x)) with hD
  have hgD : γ * (gap W * log 2 / n) ≤ D :=
    (mul_le_mul_of_nonneg_left (sqDist_ge_gap hW) hγ.le).trans hga
  have hD₀ : 0 < D := lt_of_lt_of_le (mul_pos hγ (sqDist_pos_of_ne hne)) hga
  set K : ℝ := D / (l * log 2) with hK
  have hK₀ : 0 < K := by positivity
  have hKg : 2 * γ * gap W ≤ K := by
    rw [hK, le_div_iff₀ (by positivity), hl]
    have : γ * (gap W * log 2 / n) = 2 * γ * gap W * (1 / (2 * n) * log 2) := by
      field_simp
    linarith
  -- The four bounds, in terms of `K`.
  have hY : ∀ β, 0 ≤ β → β ≤ 1 → InBand l (3 * l) (mixY E β W) := fun β h₀ h₁ ↦
    hb.mix (hb.comp E⁻¹) h₀ h₁
  have hBle : ∀ β, 0 ≤ β → β ≤ 1 → gainB E W β ≤ β * K / 2 := by
    intro β h₀ h₁
    have := H_mix_le hl₀ (fun x ↦ (hb x).1) (fun x ↦ (hb (E⁻¹ x)).1) (t := β) h₀ h₁
    rw [H_comp_perm, sqDist_comp_inv] at this
    have hc : β * (1 - β) * D / (2 * l * log 2) ≤ β * K / 2 := by
      have e : β * K / 2 = β * D / (2 * l * log 2) := by rw [hK]; field_simp
      rw [e]
      apply div_le_div_of_nonneg_right _ (by positivity)
      have : 0 ≤ β * D := by positivity
      nlinarith
    unfold gainB
    have e : mixY E β W = fun x ↦ (1 - β) * W x + β * W (E⁻¹ x) := rfl
    rw [e]
    linarith
  have hBge : ∀ β, 0 ≤ β → β ≤ 1 → β * (1 - β) * K / 6 ≤ gainB E W β := by
    intro β h₀ h₁
    have := H_mix_ge (by positivity : 0 < 3 * l) hb₀ (hb₀.comp E⁻¹) (t := β) h₀ h₁
    rw [H_comp_perm, sqDist_comp_inv] at this
    have hc : β * (1 - β) * K / 6 = β * (1 - β) * D / (2 * (3 * l) * log 2) := by
      rw [hK]; field_simp; ring
    unfold gainB
    have e : mixY E β W = fun x ↦ (1 - β) * W x + β * W (E⁻¹ x) := rfl
    rw [e, hc]
    linarith
  have hAge : ∀ β, 0 ≤ β → β ≤ 1 / 8 → K / 96 ≤ gainA E W (1 / 2) β := by
    intro β h₀ h₁
    have hYb := hY β h₀ (by linarith)
    have hYb₀ : InBand 0 (3 * l) (mixY E β W) := hYb.mono hl₀.le le_rfl
    have := H_mix_ge (by positivity : 0 < 3 * l) hYb₀ (hYb₀.comp E) (t := 1 / 2) (by norm_num)
      (by norm_num)
    rw [H_comp_perm] at this
    have hsq := (sqDist_mixY E W h₀ h₁).1
    have hc : K / 96 ≤ 1 / 2 * (1 - 1 / 2) * sqDist (mixY E β W) (fun x ↦ mixY E β W (E x)) /
        (2 * (3 * l) * log 2) := by
      have e₁ : K / 96 = (D / 4) / (24 * l * log 2) := by rw [hK]; field_simp; ring
      have e₂ : 1 / 2 * (1 - 1 / 2) * sqDist (mixY E β W) (fun x ↦ mixY E β W (E x)) /
          (2 * (3 * l) * log 2) =
          sqDist (mixY E β W) (fun x ↦ mixY E β W (E x)) / (24 * l * log 2) := by
        field_simp; ring
      rw [e₁, e₂]
      exact div_le_div_of_nonneg_right hsq (by positivity)
    unfold gainA
    have e : mixZ E (1 / 2) (mixY E β W) =
        fun x ↦ (1 - 1 / 2) * mixY E β W x + 1 / 2 * mixY E β W (E x) := rfl
    rw [e]
    linarith
  have hAle : ∀ α β, 0 ≤ α → α ≤ 1 → 0 ≤ β → β ≤ 1 / 8 → gainA E W α β ≤ α * K := by
    intro α β hα₀ hα₁ h₀ h₁
    have hYb := hY β h₀ (by linarith)
    have := H_mix_le hl₀ (fun x ↦ (hYb x).1) (fun x ↦ (hYb (E x)).1) (t := α) hα₀ hα₁
    rw [H_comp_perm] at this
    have hsq := (sqDist_mixY E W h₀ h₁).2
    have hc : α * (1 - α) * sqDist (mixY E β W) (fun x ↦ mixY E β W (E x)) / (2 * l * log 2)
        ≤ α * K := by
      have e : α * K = α * (2 * D) / (2 * l * log 2) := by rw [hK]; field_simp
      rw [e]
      apply div_le_div_of_nonneg_right _ (by positivity)
      have hα' : α * (1 - α) ≤ α := by nlinarith
      have hs₀ := sqDist_nonneg (mixY E β W) (fun x ↦ mixY E β W (E x))
      have := mul_le_mul hα' hsq hs₀ hα₀
      linarith
    unfold gainA
    have e : mixZ E α (mixY E β W) = fun x ↦ (1 - α) * mixY E β W x + α * mixY E β W (E x) :=
      rfl
    rw [e]
    linarith
  -- The step.
  have hle : ∀ β ∈ Icc 0 (1 / 48 : ℝ), gainB E W β ≤ gainA E W (1 / 2) β := by
    rintro β ⟨h₀, h₁⟩
    have := hBle β h₀ (by linarith)
    have := hAge β h₀ (by linarith)
    nlinarith
  set ρm := gainB E W (1 / 48) with hρm
  have hρm₁ : 47 / 13824 * K ≤ ρm := by
    have := hBge (1 / 48) (by norm_num) (by norm_num)
    linarith
  refine ⟨ρm, by linarith, ?_, ?_, fun ρ hρ₁ hρ₂ ↦ ?_⟩
  · have := H_mix_le_sqrt hW (hW.comp_equiv E⁻¹) (t := 1 / 48) (by norm_num) (by norm_num)
    rw [H_comp_equiv] at this
    have hs : Real.sqrt (1 / 48) ≤ 1 / 5 := by
      rw [Real.sqrt_le_left (by norm_num)]; norm_num
    rw [hρm]
    unfold gainB
    have e : mixY E (1 / 48) W = fun x ↦ (1 - 1 / 48) * W x + 1 / 48 * (W ∘ ⇑E⁻¹) x := rfl
    rw [e]
    linarith
  · nlinarith
  · obtain ⟨β, ⟨hβ₀, hβ₁⟩, α, ⟨hα₀, hα₁⟩, hB, hA⟩ :=
      exists_balanced_rate E W (by norm_num) hle hρ₁ hρ₂
    exact ⟨g, a, α, β, hα₀, by linarith, hβ₀, by linarith, hA, hB⟩

/-- The least rate far from uniform. -/
noncomputable def farRate (γ : ℝ) (X : Type*) [Fintype X] : ℝ :=
  (γ * etaNear X * log 2 / Fintype.card X) ^ 3 / 102400

omit [DecidableEq X] in
theorem gap_uniform [Nonempty X] : gap (uniform X) = 0 := by
  rw [gap, H_uniform, sub_self]

omit [DecidableEq X] [Fintype A] [DecidableEq A] in
/-- The step lemma, far from uniform. -/
theorem step_far [Nonempty X] {γ : ℝ} (hγ : 0 < γ) (hspec : Γ.SpectralGap γ) {W : X → ℝ}
    (hW : IsDist W) (hgap : etaNear X < gap W) :
    ∃ ρm : ℝ, farRate γ X ≤ ρm ∧ ρm ≤ 1 ∧ Γ.RatesUpTo W ρm := by
  set n : ℝ := (Fintype.card X : ℝ) with hn
  have hn₀ : 0 < n := by rw [hn]; exact_mod_cast Fintype.card_pos
  have h2 := log_two_pos'
  have h21 : log 2 ≤ 1 := by have := Real.log_two_lt_d9; linarith
  have hη := etaNear_pos X
  have hne : W ≠ uniform X := by
    intro h; rw [h, gap_uniform] at hgap; linarith
  obtain ⟨g, a, hga⟩ := exists_mover hspec hW hne
  set E := Γ.e g a with hE
  set D := sqDist W (fun x ↦ W (E x)) with hD
  set D₀ : ℝ := γ * etaNear X * log 2 / n with hD₀
  have hD₀pos : 0 < D₀ := by positivity
  have hD₀D : D₀ < D := by
    have h₁ := sqDist_ge_gap hW
    rw [← hn] at h₁
    have h₂ : etaNear X * log 2 / n < gap W * log 2 / n := by
      apply div_lt_div_of_pos_right _ hn₀
      exact mul_lt_mul_of_pos_right hgap h2
    have h₃ : D₀ = γ * (etaNear X * log 2 / n) := by rw [hD₀]; ring
    rw [h₃]
    calc γ * (etaNear X * log 2 / n) < γ * (gap W * log 2 / n) := mul_lt_mul_of_pos_left h₂ hγ
      _ ≤ γ * sqDist W (uniform X) := mul_le_mul_of_nonneg_left h₁ hγ.le
      _ ≤ D := hga
  have hD4 : D ≤ 4 := by
    have hpt : ∀ x, (W x - W (E x)) ^ 2 ≤ 2 * W x + 2 * W (E x) := by
      intro x
      have h₁ := hW.nonneg x; have h₂ := hW.nonneg (E x)
      have h₃ := hW.le_one x; have h₄ := hW.le_one (E x)
      nlinarith
    have hs := Finset.sum_le_sum fun x (_ : x ∈ Finset.univ) ↦ hpt x
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hW.sum,
      Equiv.sum_comp E W, hW.sum] at hs
    have : D = ∑ x, (W x - W (E x)) ^ 2 := rfl
    linarith
  have hD0 : 0 ≤ D := hD₀pos.le.trans hD₀D.le
  have hb₁ : ∀ {V : X → ℝ}, IsDist V → InBand 0 1 V := fun hV x ↦ ⟨hV.nonneg x, hV.le_one x⟩
  -- The four bounds.
  have hBle : ∀ β, 0 ≤ β → β ≤ 1 → gainB E W β ≤ 5 * Real.sqrt β := by
    intro β h₀ h₁
    have := H_mix_le_sqrt hW (hW.comp_equiv E⁻¹) h₀ h₁
    rw [H_comp_equiv] at this
    unfold gainB
    have e : mixY E β W = fun x ↦ (1 - β) * W x + β * (W ∘ ⇑E⁻¹) x := rfl
    rw [e]
    linarith
  have hBge : ∀ β, 0 ≤ β → β ≤ 1 → β * (1 - β) * D / (2 * 1 * log 2) ≤ gainB E W β := by
    intro β h₀ h₁
    have := H_mix_ge one_pos (hb₁ hW) ((hb₁ hW).comp E⁻¹) (t := β) h₀ h₁
    rw [H_comp_perm, sqDist_comp_inv] at this
    unfold gainB
    have e : mixY E β W = fun x ↦ (1 - β) * W x + β * W (E⁻¹ x) := rfl
    rw [e]
    linarith
  have hAge : ∀ β, 0 ≤ β → β ≤ 1 / 8 → D / 32 ≤ gainA E W (1 / 2) β := by
    intro β h₀ h₁
    have hYd : IsDist (mixY E β W) := isDist_mixY hW h₀ (by linarith)
    have := H_mix_ge one_pos (hb₁ hYd) ((hb₁ hYd).comp E) (t := 1 / 2) (by norm_num)
      (by norm_num)
    rw [H_comp_perm] at this
    have hsq := (sqDist_mixY E W h₀ h₁).1
    have hc : D / 32 ≤ 1 / 2 * (1 - 1 / 2) * sqDist (mixY E β W) (fun x ↦ mixY E β W (E x)) /
        (2 * 1 * log 2) := by
      rw [le_div_iff₀ (by positivity)]
      nlinarith
    unfold gainA
    have e : mixZ E (1 / 2) (mixY E β W) =
        fun x ↦ (1 - 1 / 2) * mixY E β W x + 1 / 2 * mixY E β W (E x) := rfl
    rw [e]
    linarith
  have hAle : ∀ α β, 0 ≤ α → α ≤ 1 → 0 ≤ β → β ≤ 1 → gainA E W α β ≤ 5 * Real.sqrt α := by
    intro α β hα₀ hα₁ h₀ h₁
    have hYd : IsDist (mixY E β W) := isDist_mixY hW h₀ h₁
    have := H_mix_le_sqrt hYd (hYd.comp_equiv E) hα₀ hα₁
    rw [H_comp_equiv] at this
    unfold gainA
    have e : mixZ E α (mixY E β W) = fun x ↦ (1 - α) * mixY E β W x + α * (mixY E β W ∘ ⇑E) x :=
      rfl
    rw [e]
    linarith
  -- The step.
  set bm : ℝ := (D / 160) ^ 2 with hbm
  have hbm₀ : 0 ≤ bm := sq_nonneg _
  have hbm₁ : bm ≤ 1 / 8 := by rw [hbm]; nlinarith
  have hsbm : Real.sqrt bm = D / 160 := by rw [hbm]; exact Real.sqrt_sq (by positivity)
  have hle : ∀ β ∈ Icc 0 bm, gainB E W β ≤ gainA E W (1 / 2) β := by
    rintro β ⟨h₀, h₁⟩
    have h₂ := hBle β h₀ (by linarith)
    have h₃ := hAge β h₀ (by linarith)
    have h₄ : Real.sqrt β ≤ D / 160 := hsbm ▸ Real.sqrt_le_sqrt h₁
    linarith
  set ρm := gainB E W bm with hρm
  have hρm₁ : D ^ 3 / 102400 ≤ ρm := by
    have := hBge bm hbm₀ (by linarith)
    have hc : D ^ 3 / 102400 ≤ bm * (1 - bm) * D / (2 * 1 * log 2) := by
      rw [le_div_iff₀ (by positivity), hbm]
      have : (1 : ℝ) / 2 ≤ 1 - (D / 160) ^ 2 := by rw [← hbm]; linarith
      have h3 : 0 ≤ (D / 160) ^ 2 * D := by positivity
      nlinarith [mul_le_mul_of_nonneg_left this h3]
    linarith
  have hfar : farRate γ X ≤ ρm := by
    refine le_trans ?_ hρm₁
    unfold farRate
    rw [← hn, ← hD₀]
    exact div_le_div_of_nonneg_right (pow_le_pow_left₀ hD₀pos.le hD₀D.le 3) (by norm_num)
  have hρm1 : ρm ≤ 1 := by
    have := hBle bm hbm₀ (by linarith)
    rw [hsbm] at this
    linarith
  refine ⟨ρm, hfar, hρm1, fun ρ hρ₁ hρ₂ ↦ ?_⟩
  obtain ⟨β, ⟨hβ₀, hβ₁⟩, α, ⟨hα₀, hα₁⟩, hB, hA⟩ :=
    exists_balanced_rate E W hbm₀ hle hρ₁ hρ₂
  exact ⟨g, a, α, β, hα₀, by linarith, hβ₀, by linarith, hA, hB⟩

/-! ### Gaps -/

omit [DecidableEq X] [Fintype A] [DecidableEq A] in
theorem SpectralGap.mono {γ γ' : ℝ} (h : Γ.SpectralGap γ) (hγ : γ' ≤ γ) : Γ.SpectralGap γ' := by
  intro v h₁ h₂
  obtain ⟨g, a, h⟩ := h v h₁ h₂
  exact ⟨g, a, le_trans (mul_le_mul_of_nonneg_right hγ
    (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)) h⟩

end CycleSystem

end CubeGod
