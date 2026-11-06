import CubeGod.Method.Method

/-!
# The schedule of each kind, for each `c`

For a super-tuple of `m = c²` pairs, take

* the rounding loss `e′ = roundErr` and the covering loss `ω = omegaOf C m`, both
  `O(log c/c²)` (`sq_mul_roundErr_le`, `sq_mul_omegaOf_le`);
* the full rate `ρ_full = 1/c − ω − e′`, so that an exact codebook for a firing of rate at most
  `ρ_full + e′` has exactly at most `2^c` lists (`coverBound_full`);
* `r₀ = ⌈2 ln c/ln(1/λ)⌉` blind rounds, so that `λ^r₀ ≤ 1/c²`, and the twist's tolerance `¼`.

Then for every large `c` the codebooks of `exists_books` give a schedule `Sched q c` of at most
`c·log₂C/2 + P₀ + P₁·ln c` steps, each codebook of at most `2^c` lists, that solves every list of
`c × c` patterns within `¼·c²/C` of `c²/C` (`exists_sched`).
-/

open Finset Real Filter Topology

namespace CubeGod

instance (q : Bool) : Nonempty (SideCycle q) := by
  cases q
  · exact ⟨⟨cyclesL.head (by simp [cyclesL]), pure_L _ (List.head_mem _)⟩⟩
  · exact ⟨⟨cyclesR.head (by simp [cyclesR]), pure_R _ (List.head_mem _)⟩⟩

/-! ### Growth -/

/-- `K₀ + K₁·ln x ≤ ε·x` eventually. -/
theorem eventually_lin_log_le (K₀ K₁ : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, K₀ + K₁ * log x ≤ ε * x := by
  have hb := Real.isLittleO_log_id_atTop.bound (show (0 : ℝ) < ε / (2 * (|K₁| + 1)) by positivity)
  filter_upwards [hb, eventually_ge_atTop (2 * |K₀| / ε), eventually_ge_atTop 1] with x hx hx₀ hx₁
  simp only [Real.norm_eq_abs, id] at hx
  rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ x)] at hx
  have h₁ : K₁ * log x ≤ |K₁| * |log x| := by rw [← abs_mul]; exact le_abs_self _
  have h₂ : |K₁| * |log x| ≤ |K₁| * (ε / (2 * (|K₁| + 1)) * x) :=
    mul_le_mul_of_nonneg_left hx (abs_nonneg _)
  have h₃ : |K₁| * (ε / (2 * (|K₁| + 1)) * x) ≤ ε * x / 2 := by
    rw [show |K₁| * (ε / (2 * (|K₁| + 1)) * x) = (|K₁| / (|K₁| + 1)) * (ε * x / 2) by
      field_simp]
    have : |K₁| / (|K₁| + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith
    have : 0 ≤ ε * x / 2 := by positivity
    nlinarith
  have h₄ : K₀ ≤ ε * x / 2 := by
    have := le_abs_self K₀
    rw [div_le_iff₀ hε] at hx₀
    linarith
  linarith

theorem eventually_nat {P : ℝ → Prop} (h : ∀ᶠ x : ℝ in atTop, P x) : ∀ᶠ c : ℕ in atTop, P c :=
  tendsto_natCast_atTop_atTop.eventually h

/-! ### The losses -/

theorem inv_log_two_le : 1 / log 2 ≤ 2 := by
  have := Real.log_two_gt_d9
  rw [div_le_iff₀ (by linarith)]; linarith

/-- `contErr M t ≤ 2t(ln M + ln(1/t) + 1)`. -/
theorem contErr_le {M t : ℝ} (ht₀ : 0 < t) (ht : t ≤ M) :
    contErr M t ≤ 2 * (t * (log M + log (1 / t) + 1)) := by
  unfold contErr
  have hM : 0 < M := lt_of_lt_of_le ht₀ ht
  have e : log (M / t) = log M + log (1 / t) := by
    rw [div_eq_mul_one_div, log_mul hM.ne' (by positivity)]
  rw [e]
  have h₀ : 0 ≤ t * (log M + log (1 / t)) + t := by
    rw [← e]
    have : 0 ≤ log (M / t) := log_nonneg (by rw [le_div_iff₀ ht₀]; linarith)
    positivity
  have := inv_log_two_le
  calc (t * (log M + log (1 / t)) + t) / log 2 = (t * (log M + log (1 / t)) + t) * (1 / log 2) := by
        ring
    _ ≤ (t * (log M + log (1 / t)) + t) * 2 := mul_le_mul_of_nonneg_left this h₀
    _ = 2 * (t * (log M + log (1 / t) + 1)) := by ring

theorem contErr_nonneg {M t : ℝ} (ht₀ : 0 < t) (ht : t ≤ M) : 0 ≤ contErr M t := by
  unfold contErr
  have : 0 ≤ log (M / t) := log_nonneg (by rw [le_div_iff₀ ht₀]; linarith)
  have := log_two_pos'
  positivity

/-- **The rounding loss is `O(log c/c²)`.** -/
theorem sq_mul_roundErr_le (X : Type*) [Fintype X] [Nonempty X] {c : ℕ}
    (hc : 4 * Fintype.card X ≤ c * c) :
    (c : ℝ) ^ 2 * roundErr X (c * c) ≤
      24 * Fintype.card X * (log (2 * Fintype.card X) + 1) +
        48 * Fintype.card X * log c := by
  set C : ℝ := (Fintype.card X : ℝ) with hC
  have hC₁ : (1 : ℝ) ≤ C := by rw [hC]; exact_mod_cast Fintype.card_pos (α := X)
  have hcc : (4 * C : ℝ) ≤ (c : ℝ) ^ 2 := by
    have : ((4 * Fintype.card X : ℕ) : ℝ) ≤ ((c * c : ℕ) : ℝ) := by exact_mod_cast hc
    push_cast at this; nlinarith
  have hc₀ : (0 : ℝ) < c := by
    have : (0 : ℝ) < (c : ℝ) ^ 2 := by linarith
    rcases (Nat.cast_nonneg c : (0 : ℝ) ≤ c).eq_or_lt with h | h
    · rw [← h] at this; simp at this
    · exact h
  set t : ℝ := 4 * C / ((c * c : ℕ) : ℝ) with ht
  have htc : t = 4 * C / (c : ℝ) ^ 2 := by rw [ht]; push_cast; ring
  have ht₀ : 0 < t := by rw [htc]; positivity
  have ht₁ : t ≤ 1 := by rw [htc, div_le_one (by positivity)]; exact hcc
  have hlog : log (1 / t) ≤ 2 * log c := by
    rw [htc, one_div_div, ← Real.log_rpow hc₀, Real.rpow_two]
    apply log_le_log (by positivity)
    rw [div_le_iff₀ (by positivity)]
    nlinarith [sq_nonneg (c : ℝ)]
  have hM : ∀ M : ℝ, 1 ≤ M → M ≤ 2 * C →
      contErr M t ≤ 2 * (t * (log (2 * C) + 2 * log c + 1)) := by
    intro M h₁ h₂
    refine (contErr_le ht₀ (by linarith)).trans ?_
    have : log M ≤ log (2 * C) := log_le_log (by linarith) h₂
    have : 0 ≤ t := ht₀.le
    nlinarith
  unfold roundErr miErr
  rw [← hC]
  have h₁ := hM C hC₁ (by linarith)
  have h₂ := hM 2 (by norm_num) (by linarith)
  have h₃ := hM (C * 2) (by nlinarith) (by linarith)
  have hsum : contErr C t + contErr 2 t + contErr (C * 2) t ≤
      6 * (t * (log (2 * C) + 2 * log c + 1)) := by linarith
  have e : (c : ℝ) ^ 2 * (6 * (t * (log (2 * C) + 2 * log c + 1))) =
      24 * C * (log (2 * C) + 1) + 48 * C * log c := by
    rw [htc]; field_simp; ring
  calc (c : ℝ) ^ 2 * (contErr C t + contErr 2 t + contErr (C * 2) t)
      ≤ (c : ℝ) ^ 2 * (6 * (t * (log (2 * C) + 2 * log c + 1))) :=
        mul_le_mul_of_nonneg_left hsum (sq_nonneg _)
    _ = _ := e

/-- The rounding loss is at least `4C/c²`. -/
theorem roundErr_ge (X : Type*) [Fintype X] [Nonempty X] {c : ℕ}
    (hc : 4 * Fintype.card X ≤ c * c) :
    4 * (Fintype.card X : ℝ) / (c : ℝ) ^ 2 ≤ roundErr X (c * c) := by
  set C : ℝ := (Fintype.card X : ℝ) with hC
  have hC₁ : (1 : ℝ) ≤ C := by rw [hC]; exact_mod_cast Fintype.card_pos (α := X)
  have hcc : (4 * C : ℝ) ≤ (c : ℝ) ^ 2 := by
    have : ((4 * Fintype.card X : ℕ) : ℝ) ≤ ((c * c : ℕ) : ℝ) := by exact_mod_cast hc
    push_cast at this; nlinarith
  have hc2 : (0 : ℝ) < (c : ℝ) ^ 2 := by linarith
  set t : ℝ := 4 * C / ((c * c : ℕ) : ℝ) with ht
  have htc : t = 4 * C / (c : ℝ) ^ 2 := by rw [ht]; push_cast; ring
  have ht₀ : 0 < t := by rw [htc]; positivity
  have ht₁ : t ≤ 1 := by rw [htc, div_le_one hc2]; exact hcc
  unfold roundErr miErr
  rw [← hC, ← htc]
  have h₁ : t ≤ contErr C t := by
    unfold contErr
    have hl : 0 ≤ log (C / t) := log_nonneg (by rw [le_div_iff₀ ht₀]; linarith)
    have := log_two_pos'
    have h21 : log 2 ≤ 1 := by have := Real.log_two_lt_d9; linarith
    rw [le_div_iff₀ this]
    nlinarith
  have h₂ := contErr_nonneg ht₀ (show t ≤ 2 by linarith)
  have h₃ := contErr_nonneg ht₀ (show t ≤ C * 2 by nlinarith)
  linarith

/-- The covering loss for `m` entries and `C` patterns. -/
noncomputable def omegaOf (C m : ℕ) : ℝ :=
  logb 2 (((m : ℝ) * log C + 2) * ((m : ℝ) + 1) ^ C) / m

/-- **The covering loss is `O(log c/c²)`.** -/
theorem sq_mul_omegaOf_le (C : ℕ) (hC : 1 ≤ C) {c : ℕ} (hc : 1 ≤ c) :
    (c : ℝ) ^ 2 * omegaOf C (c * c) ≤
      (C + 1) * (2 * log (log C + 2)) + 4 * (C + 1) * log c := by
  have hC' : (1 : ℝ) ≤ C := by exact_mod_cast hC
  have hc' : (1 : ℝ) ≤ c := by exact_mod_cast hc
  have hlC : 0 ≤ log (C : ℝ) := log_nonneg hC'
  set m : ℝ := ((c * c : ℕ) : ℝ) with hm
  have hmc : m = (c : ℝ) ^ 2 := by rw [hm]; push_cast; ring
  have hm₁ : 1 ≤ m := by rw [hmc]; nlinarith
  set B : ℝ := (c : ℝ) ^ 2 * (log C + 2) with hB
  have hB₁ : 1 ≤ B := by rw [hB]; nlinarith
  have hP : (m * log C + 2) * (m + 1) ^ C ≤ B ^ (C + 1) := by
    have h₁ : m * log C + 2 ≤ B := by rw [hB, hmc]; nlinarith
    have h₂ : m + 1 ≤ B := by rw [hB, hmc]; nlinarith
    rw [pow_succ, mul_comm (B ^ C)]
    exact mul_le_mul h₁ (pow_le_pow_left₀ (by linarith) h₂ C) (by positivity) (by positivity)
  have hPpos : 0 < (m * log C + 2) * (m + 1) ^ C := by positivity
  unfold omegaOf
  rw [← hm, mul_div_assoc', hmc, mul_div_cancel_left₀ _ (by positivity), ← hmc]
  calc logb 2 ((m * log C + 2) * (m + 1) ^ C) ≤ logb 2 (B ^ (C + 1)) :=
        logb_le_logb_of_le (by norm_num) hPpos hP
    _ = (C + 1) * logb 2 B := by rw [Real.logb_pow]; push_cast; ring
    _ = (C + 1) * (log B / log 2) := rfl
    _ ≤ (C + 1) * (2 * log B) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        have := inv_log_two_le
        have hlB : 0 ≤ log B := log_nonneg hB₁
        rw [div_eq_mul_one_div]; nlinarith
    _ = (C + 1) * (2 * log (log C + 2)) + 4 * (C + 1) * log c := by
        rw [hB, log_mul (by positivity) (by positivity), Real.log_pow]; push_cast; ring

/-- The full rate makes an exact codebook exactly `2^c` lists. -/
theorem coverBound_full (C : ℕ) (hC : 1 ≤ C) {c : ℕ} (hc : 1 ≤ c) :
    coverBound ((c * c : ℕ) : ℝ) C (1 / (c : ℝ) - omegaOf C (c * c)) = 2 ^ c := by
  have hC' : (1 : ℝ) ≤ C := by exact_mod_cast hC
  have hc' : (1 : ℝ) ≤ c := by exact_mod_cast hc
  set m : ℝ := ((c * c : ℕ) : ℝ) with hm
  have hmc : m = (c : ℝ) * c := by rw [hm]; push_cast; ring
  have hm₀ : 0 < m := by rw [hmc]; positivity
  set P := (m * log C + 2) * (m + 1) ^ C with hP
  have hPpos : 0 < P := by have := log_nonneg hC'; positivity
  unfold coverBound omegaOf
  rw [← hm, ← hP]
  have e : m * (1 / (c : ℝ) - logb 2 P / m) = c - logb 2 P := by
    rw [hmc]; field_simp
  rw [e, Real.rpow_sub (by norm_num), Real.rpow_natCast, Real.rpow_logb (by norm_num) (by norm_num)
    hPpos]
  field_simp

theorem omegaOf_nonneg (C : ℕ) (hC : 1 ≤ C) (m : ℕ) : 0 ≤ omegaOf C m := by
  unfold omegaOf
  have hC' : (1 : ℝ) ≤ C := by exact_mod_cast hC
  have : 0 ≤ log (C : ℝ) := log_nonneg hC'
  have h₁ : (1 : ℝ) ≤ ((m : ℝ) * log C + 2) * ((m : ℝ) + 1) ^ C := by
    have h₃ : (1 : ℝ) ≤ ((m : ℝ) + 1) ^ C :=
      one_le_pow₀ (by linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)])
    have h₂ : (2 : ℝ) ≤ (m : ℝ) * log C + 2 := by
      have := mul_nonneg (Nat.cast_nonneg m : (0 : ℝ) ≤ m) this
      linarith
    nlinarith
  exact div_nonneg (logb_nonneg (by norm_num) h₁) (Nat.cast_nonneg _)

/-- `(C₁ + C₂ ln x)² ≤ ε x` eventually. -/
theorem eventually_sq_log_le (C₁ C₂ : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, (C₁ + C₂ * log x) ^ 2 ≤ ε * x := by
  have h₁ := tendsto_pow_log_div_mul_add_atTop 1 0 2 one_ne_zero
  simp only [one_mul, add_zero] at h₁
  have hpos : 0 < ε / (4 * (C₂ ^ 2 + 1)) := by positivity
  filter_upwards [h₁.eventually (gt_mem_nhds hpos), eventually_gt_atTop (0 : ℝ),
    eventually_ge_atTop (4 * C₁ ^ 2 / ε)] with x hx hx₀ hx₁
  rw [div_lt_iff₀ hx₀] at hx
  have h₂ : (C₁ + C₂ * log x) ^ 2 ≤ 2 * C₁ ^ 2 + 2 * C₂ ^ 2 * log x ^ 2 := by
    nlinarith [sq_nonneg (C₁ - C₂ * log x)]
  have h₃ : 2 * C₂ ^ 2 * log x ^ 2 ≤ ε * x / 2 := by
    have : C₂ ^ 2 * log x ^ 2 ≤ (C₂ ^ 2 + 1) * log x ^ 2 := by nlinarith [sq_nonneg (log x)]
    have h₄ : (C₂ ^ 2 + 1) * log x ^ 2 ≤ (C₂ ^ 2 + 1) * (ε / (4 * (C₂ ^ 2 + 1)) * x) :=
      mul_le_mul_of_nonneg_left hx.le (by positivity)
    have h₅ : (C₂ ^ 2 + 1) * (ε / (4 * (C₂ ^ 2 + 1)) * x) = ε * x / 4 := by
      field_simp
    linarith
  have h₄ : 2 * C₁ ^ 2 ≤ ε * x / 2 := by
    rw [div_le_iff₀ hε] at hx₁; linarith
  linarith

theorem patternCount_gt_one : 1 < patternCount := by
  unfold patternCount
  norm_num [Nat.factorial]

theorem ceil_le_max_add_one (x : ℝ) : (⌈x⌉₊ : ℝ) ≤ max x 0 + 1 := by
  rcases le_total x 0 with h | h
  · rw [Nat.ceil_eq_zero.mpr h]; have := le_max_right x 0; push_cast; linarith
  · have := Nat.ceil_lt_add_one h
    rw [max_eq_left h]; linarith

/-! ### The parameters -/

/-- The number of blind rounds: `⌈2 ln c/ln(1/λ')⌉`, with `λ' = max λ ½`. -/
noncomputable def r0Of (lam : ℝ) (c : ℕ) : ℕ := ⌈2 * log (c : ℝ) / log (1 / max lam (1 / 2))⌉₊

/-- The full rate `1/c − ω − e′`. -/
noncomputable def rhoOf (X : Type*) [Fintype X] (c : ℕ) : ℝ :=
  1 / (c : ℝ) - omegaOf (Fintype.card X) (c * c) - roundErr X (c * c)

theorem lam_pow_le {lam : ℝ} (hlam₀ : 0 ≤ lam) (hlam₁ : lam < 1) {c : ℕ} (hc : 1 ≤ c) :
    lam ^ r0Of lam c ≤ 1 / (c : ℝ) ^ 2 := by
  set lam' := max lam (1 / 2) with hlam'
  have hlam'₀ : 0 < lam' := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  have hlam'₁ : lam' < 1 := max_lt hlam₁ (by norm_num)
  set lg := log (1 / lam') with hlg
  have hlg₀ : 0 < lg := log_pos (by rw [lt_div_iff₀ hlam'₀]; linarith)
  have hc₀ : (0 : ℝ) < c := by exact_mod_cast hc
  set r₀ := r0Of lam c with hr₀
  have h₁ : lam ^ r₀ ≤ lam' ^ r₀ := pow_le_pow_left₀ hlam₀ (le_max_left _ _) _
  have h₂ : lam' ^ r₀ = exp (-(r₀ * lg)) := by
    rw [hlg, one_div, log_inv, ← Real.exp_log (pow_pos hlam'₀ r₀), Real.log_pow]; ring_nf
  have h₃ : 2 * log (c : ℝ) ≤ r₀ * lg := by
    have := Nat.le_ceil (2 * log (c : ℝ) / lg)
    rw [div_le_iff₀ hlg₀] at this
    have e : r₀ = ⌈2 * log (c : ℝ) / lg⌉₊ := rfl
    rw [e]; linarith
  have h₄ : exp (-(r₀ * lg)) ≤ 1 / (c : ℝ) ^ 2 := by
    have e : 1 / (c : ℝ) ^ 2 = exp (-(2 * log c)) := by
      rw [Real.exp_neg, show 2 * log (c : ℝ) = log ((c : ℝ) ^ 2) by rw [Real.log_pow]; push_cast; ring,
        Real.exp_log (by positivity), one_div]
    rw [e]
    exact Real.exp_le_exp.mpr (by linarith)
  linarith

theorem r0Of_le {lam : ℝ} (hlam₁ : lam < 1) {c : ℕ} (hc : 1 ≤ c) :
    (r0Of lam c : ℝ) ≤ 2 / log (1 / max lam (1 / 2)) * log c + 1 := by
  have hlam'₀ : 0 < max lam (1 / 2) := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  have hlam'₁ : max lam (1 / 2) < 1 := max_lt hlam₁ (by norm_num)
  have hlg₀ : 0 < log (1 / max lam (1 / 2)) := log_pos (by rw [lt_div_iff₀ hlam'₀]; linarith)
  have hlogc : 0 ≤ log (c : ℝ) := log_nonneg (by exact_mod_cast hc)
  have := Nat.ceil_lt_add_one (show 0 ≤ 2 * log (c : ℝ) / log (1 / max lam (1 / 2)) by positivity)
  unfold r0Of
  have e : 2 * log (c : ℝ) / log (1 / max lam (1 / 2)) = 2 / log (1 / max lam (1 / 2)) * log c := by
    ring
  rw [e] at this ⊢
  linarith

/-! ### The arithmetic, step by step -/

/-- The constants of the rounding loss. -/
noncomputable def lossE₀ (C : ℝ) : ℝ := 24 * C * (log (2 * C) + 1)
/-- The constants of the rounding loss. -/
noncomputable def lossE₁ (C : ℝ) : ℝ := 48 * C
/-- The constants of the covering loss. -/
noncomputable def lossW₀ (C : ℝ) : ℝ := (C + 1) * (2 * log (log C + 2))
/-- The constants of the covering loss. -/
noncomputable def lossW₁ (C : ℝ) : ℝ := 4 * (C + 1)

section Numbers

variable (X : Type*) [Fintype X] [Nonempty X] {c : ℕ}

theorem rho_facts (hc4 : 4 * Fintype.card X ≤ c * c) (hc₁ : 1 ≤ c)
    (hev : lossW₀ (Fintype.card X) + 5 * lossE₀ (Fintype.card X) +
      (lossW₁ (Fintype.card X) + 5 * lossE₁ (Fintype.card X)) * log c ≤ 1 / 2 * c) :
    omegaOf (Fintype.card X) (c * c) + 5 * roundErr X (c * c) ≤ 1 / (2 * c) ∧
      0 < rhoOf X c ∧ roundErr X (c * c) ≤ rhoOf X c / 4 ∧ rhoOf X c ≤ 1 / c := by
  have hcr : (1 : ℝ) ≤ c := by exact_mod_cast hc₁
  have hc₀ : (0 : ℝ) < c := by linarith
  have he := sq_mul_roundErr_le X hc4
  have hω := sq_mul_omegaOf_le (Fintype.card X) Fintype.card_pos hc₁
  have he₀ := roundErr_pos X (show 0 < c * c by positivity) hc4
  have hω₀ := omegaOf_nonneg (Fintype.card X) Fintype.card_pos (c * c)
  set e := roundErr X (c * c)
  set ω := omegaOf (Fintype.card X) (c * c)
  unfold lossW₀ lossW₁ lossE₀ lossE₁ at hev
  have h₁ : (c : ℝ) ^ 2 * (ω + 5 * e) ≤ 1 / 2 * c := by
    have : (c : ℝ) ^ 2 * (ω + 5 * e) = (c : ℝ) ^ 2 * ω + 5 * ((c : ℝ) ^ 2 * e) := by ring
    linarith
  have h₂ : ω + 5 * e ≤ 1 / (2 * c) := by
    rw [le_div_iff₀ (by positivity)]
    have : (c : ℝ) ^ 2 * (ω + 5 * e) = (ω + 5 * e) * (2 * c) * (c / 2) := by ring
    rw [this] at h₁
    have h₃ : (ω + 5 * e) * (2 * c) * (c / 2) ≤ 1 * (c / 2) := by linarith
    exact le_of_mul_le_mul_right h₃ (by positivity)
  have h₄ : 1 / (2 * (c : ℝ)) < 1 / c := by
    rw [div_lt_div_iff₀ (by positivity) hc₀]; linarith
  unfold rhoOf
  refine ⟨h₂, by linarith, by linarith, by linarith⟩

theorem dev_le {lam : ℝ} {r₀ F : ℕ} (hlamr : lam ^ r₀ ≤ 1 / (c : ℝ) ^ 2)
    (hc₁ : 1 ≤ c) (hF : (F : ℝ) ≤ c) :
    mergeDev (Fintype.card X) lam (1 / 4) r₀ F (c * c) ≤ c := by
  set C : ℝ := (Fintype.card X : ℝ) with hC
  have hC₁ : (1 : ℝ) ≤ C := by rw [hC]; exact_mod_cast Fintype.card_pos (α := X)
  have hc₀ : (0 : ℝ) < c := by exact_mod_cast hc₁
  unfold mergeDev
  rw [← hC, show ((c * c : ℕ) : ℝ) = (c : ℝ) ^ 2 by push_cast; ring]
  have hs : Real.sqrt (lam ^ r₀ * C) ≤ Real.sqrt C / c := by
    rw [show Real.sqrt C / c = Real.sqrt (C / (c : ℝ) ^ 2) by
      rw [Real.sqrt_div' _ (by positivity), Real.sqrt_sq hc₀.le]]
    apply Real.sqrt_le_sqrt
    rw [div_eq_mul_one_div, mul_comm C]
    exact mul_le_mul_of_nonneg_right hlamr (by positivity)
  have hsC : Real.sqrt C ≤ C := by
    rw [Real.sqrt_le_left (by positivity)]; nlinarith
  have h₁ : Real.sqrt (lam ^ r₀ * C) * (1 / 4 * (c : ℝ) ^ 2 / C) ≤ c / 4 := by
    calc Real.sqrt (lam ^ r₀ * C) * (1 / 4 * (c : ℝ) ^ 2 / C) ≤
          Real.sqrt C / c * (1 / 4 * (c : ℝ) ^ 2 / C) :=
          mul_le_mul_of_nonneg_right hs (by positivity)
      _ = Real.sqrt C / C * (c / 4) := by field_simp
      _ ≤ 1 * (c / 4) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          rw [div_le_one (by positivity)]; exact hsC
      _ = c / 4 := one_mul _
  linarith

theorem epsStar_le {γ : ℝ} (hγ : 0 < γ) (hc4 : 4 * Fintype.card X ≤ c * c) (hc₁ : 1 ≤ c) :
    (c : ℝ) * epsStar X γ (c * c) ≤ 2 * Fintype.card X * (2 * (1 + 2 * (lossE₀ (Fintype.card X) +
      lossE₁ (Fintype.card X) * log c) / (γ / 150))) := by
  have hc₀ : (0 : ℝ) < c := by exact_mod_cast hc₁
  have he := sq_mul_roundErr_le X hc4
  have he₀ := roundErr_pos X (show 0 < c * c by positivity) hc4
  set e := roundErr X (c * c)
  set κ := γ / 150 with hκ
  have hκ₀ : 0 < κ := by positivity
  unfold epsStar
  rw [← hκ]
  have hy : (c : ℝ) * Real.sqrt (2 * e / κ) ≤
      1 + 2 * (lossE₀ (Fintype.card X) + lossE₁ (Fintype.card X) * log c) / κ := by
    rw [show (c : ℝ) * Real.sqrt (2 * e / κ) = Real.sqrt ((c : ℝ) ^ 2 * (2 * e / κ)) by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hc₀.le]]
    have hz : (c : ℝ) ^ 2 * (2 * e / κ) ≤
        2 * (lossE₀ (Fintype.card X) + lossE₁ (Fintype.card X) * log c) / κ := by
      rw [show (c : ℝ) ^ 2 * (2 * e / κ) = 2 * ((c : ℝ) ^ 2 * e) / κ by ring]
      unfold lossE₀ lossE₁
      exact div_le_div_of_nonneg_right (by linarith) hκ₀.le
    have hsq : ∀ y : ℝ, 0 ≤ y → Real.sqrt y ≤ 1 + y := fun y hy ↦ by
      rw [Real.sqrt_le_left (by positivity)]; nlinarith
    exact (hsq _ (by positivity)).trans (by linarith)
  have e₁ : (c : ℝ) * ((Fintype.card X : ℝ) * (2 * Real.sqrt (2 * e / κ))) =
      2 * Fintype.card X * ((c : ℝ) * Real.sqrt (2 * e / κ)) := by ring
  rw [e₁]
  have : (1 : ℝ) + 2 * (lossE₀ (Fintype.card X) + lossE₁ (Fintype.card X) * log c) / κ ≤
      2 * (1 + 2 * (lossE₀ (Fintype.card X) + lossE₁ (Fintype.card X) * log c) / κ) := by
    have : 0 ≤ (1 : ℝ) + 2 * (lossE₀ (Fintype.card X) + lossE₁ (Fintype.card X) * log c) / κ :=
      le_trans (by positivity) hy
    linarith
  exact mul_le_mul_of_nonneg_left (hy.trans this) (by positivity)

theorem cmu_le {Dc εs : ℝ} (hc₁ : 1 ≤ c) (hDc : Dc ≤ c) :
    (c : ℝ) * mergeMu (Fintype.card X) (c * c) Dc εs ≤
      2 * Fintype.card X + 2 * (Fintype.card X : ℝ) ^ 2 + 2 * Fintype.card X * (c * εs) := by
  set C : ℝ := (Fintype.card X : ℝ) with hC
  have hC₁ : (1 : ℝ) ≤ C := by rw [hC]; exact_mod_cast Fintype.card_pos (α := X)
  have hc₀ : (0 : ℝ) < c := by exact_mod_cast hc₁
  unfold mergeMu
  rw [← hC, show ((c * c : ℕ) : ℝ) = (c : ℝ) ^ 2 by push_cast; ring]
  have e₁ : (c : ℝ) * ((C + C * Dc + 2 * C * εs * (c : ℝ) ^ 2 + 2 * C ^ 2 * Dc) / (c : ℝ) ^ 2) =
      (C + C * Dc + 2 * C ^ 2 * Dc) / c + 2 * C * (c * εs) := by
    field_simp; ring
  rw [e₁]
  have h₁ : (C + C * Dc + 2 * C ^ 2 * Dc) / c ≤ 2 * C + 2 * C ^ 2 := by
    rw [div_le_iff₀ hc₀]
    have : C * Dc ≤ C * c := mul_le_mul_of_nonneg_left hDc (by positivity)
    have : C ^ 2 * Dc ≤ C ^ 2 * c := mul_le_mul_of_nonneg_left hDc (by positivity)
    have hcr : (1 : ℝ) ≤ c := by exact_mod_cast hc₁
    have : C * 1 ≤ C * c := mul_le_mul_of_nonneg_left hcr (by positivity)
    linarith
  linarith

end Numbers

/-- The merge's codebooks fit in `2^c` lists. -/
theorem cover_merge_le (C : ℕ) (hC : 1 ≤ C) {c : ℕ} (hc₁ : 1 ≤ c) {μ B : ℝ} (hμ₀ : 0 ≤ μ)
    (hμB : (c : ℝ) * μ ≤ B) (h71 : 71 * (4 * (C : ℝ) ^ 2 + B ^ 2) ≤ c / 2)
    (hQ : log (log C + 2) + 2 * C * log 2 + (2 + 4 * C) * log c ≤ log 2 / 2 * c) :
    (((c * c : ℕ) : ℝ) + 1) ^ C * coverBound ((c * c : ℕ) : ℝ) C
      (71 * max ((2 * (C : ℝ) / ((c * c : ℕ) : ℝ)) ^ 2) (μ ^ 2)) ≤ 2 ^ c := by
  have hC' : (1 : ℝ) ≤ C := by exact_mod_cast hC
  have hcr : (1 : ℝ) ≤ c := by exact_mod_cast hc₁
  have hc₀ : (0 : ℝ) < c := by linarith
  set m : ℝ := ((c * c : ℕ) : ℝ) with hm
  have hmc : m = (c : ℝ) ^ 2 := by rw [hm]; push_cast; ring
  have hm₁ : 1 ≤ m := by rw [hmc]; nlinarith
  have hlC : 0 ≤ log (C : ℝ) := log_nonneg hC'
  -- The exponent.
  set r := 71 * max ((2 * (C : ℝ) / m) ^ 2) (μ ^ 2) with hr
  have hmr : m * r ≤ c / 2 := by
    have h₁ : m * (2 * (C : ℝ) / m) ^ 2 ≤ 4 * (C : ℝ) ^ 2 := by
      have e : m * (2 * (C : ℝ) / m) ^ 2 = 4 * (C : ℝ) ^ 2 / m := by field_simp; ring
      rw [e]
      exact div_le_self (by positivity) hm₁
    have h₂ : m * μ ^ 2 ≤ B ^ 2 := by
      rw [hmc, show (c : ℝ) ^ 2 * μ ^ 2 = ((c : ℝ) * μ) ^ 2 by ring]
      exact pow_le_pow_left₀ (by positivity) hμB 2
    have hmax : m * max ((2 * (C : ℝ) / m) ^ 2) (μ ^ 2) ≤ 4 * (C : ℝ) ^ 2 + B ^ 2 := by
      rcases le_total ((2 * (C : ℝ) / m) ^ 2) (μ ^ 2) with h | h
      · rw [max_eq_right h]; nlinarith [sq_nonneg (C : ℝ)]
      · rw [max_eq_left h]; nlinarith [sq_nonneg B]
    rw [hr, show m * (71 * max ((2 * (C : ℝ) / m) ^ 2) (μ ^ 2)) =
      71 * (m * max ((2 * (C : ℝ) / m) ^ 2) (μ ^ 2)) by ring]
    linarith
  -- The polynomial factor.
  have hP : (m + 1) ^ C * ((m * log C + 2) * (m + 1) ^ C) ≤ (2 : ℝ) ^ ((c : ℝ) / 2) := by
    have hpos : 0 < (m + 1) ^ C * ((m * log C + 2) * (m + 1) ^ C) := by positivity
    rw [← Real.exp_log hpos, Real.rpow_def_of_pos (by norm_num)]
    apply Real.exp_le_exp.mpr
    rw [show (m + 1) ^ C * ((m * log C + 2) * (m + 1) ^ C) = (m * log C + 2) * ((m + 1) ^ C) ^ 2 by
      ring, log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
    have h₁ : log (m * log C + 2) ≤ log (log C + 2) + 2 * log c := by
      have : m * log C + 2 ≤ (c : ℝ) ^ 2 * (log C + 2) := by rw [hmc]; nlinarith
      calc log (m * log C + 2) ≤ log ((c : ℝ) ^ 2 * (log C + 2)) := log_le_log (by positivity) this
        _ = log (log C + 2) + 2 * log c := by
            rw [log_mul (by positivity) (by positivity), Real.log_pow]; push_cast; ring
    have h₂ : log (m + 1) ≤ log 2 + 2 * log c := by
      have : m + 1 ≤ 2 * (c : ℝ) ^ 2 := by rw [hmc]; nlinarith
      calc log (m + 1) ≤ log (2 * (c : ℝ) ^ 2) := log_le_log (by positivity) this
        _ = log 2 + 2 * log c := by
            rw [log_mul (by norm_num) (by positivity), Real.log_pow]; push_cast; ring
    have h₃ : (2 : ℝ) * (C * log (m + 1)) ≤ 2 * (C * (log 2 + 2 * log c)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h₂ (by positivity)) (by norm_num)
    push_cast
    nlinarith
  unfold coverBound
  have h2 : (2 : ℝ) ^ (m * r) ≤ 2 ^ ((c : ℝ) / 2) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hmr
  calc (m + 1) ^ C * ((m * log C + 2) * (m + 1) ^ C * 2 ^ (m * r)) =
        ((m + 1) ^ C * ((m * log C + 2) * (m + 1) ^ C)) * 2 ^ (m * r) := by ring
    _ ≤ (2 : ℝ) ^ ((c : ℝ) / 2) * 2 ^ ((c : ℝ) / 2) :=
        mul_le_mul hP h2 (by positivity) (by positivity)
    _ = 2 ^ c := by
        rw [← Real.rpow_add (by norm_num), add_halves, Real.rpow_natCast]

/-- The length of the path. -/
theorem pathLen_le (X : Type*) [Fintype X] [Nonempty X] {γ : ℝ} (hγ : 0 < γ) {c : ℕ}
    (hc4 : 4 * Fintype.card X ≤ c * c) (hc₁ : 1 ≤ c) (hA : 0 < logb 2 (Fintype.card X))
    (hsum : omegaOf (Fintype.card X) (c * c) + 5 * roundErr X (c * c) ≤ 1 / (2 * c)) :
    (pathLen X γ (rhoOf X c) (c * c) : ℝ) ≤ c * logb 2 (Fintype.card X) / 2 +
      (logb 2 (Fintype.card X) * (lossW₀ (Fintype.card X) + 3 / 2 * lossE₀ (Fintype.card X)) + 2 +
        |log (logb 2 (Fintype.card X) * (γ / 150) / (8 * Fintype.card X))| / (3 / 2 * (γ / 150))) +
      (logb 2 (Fintype.card X) * (lossW₁ (Fintype.card X) + 3 / 2 * lossE₁ (Fintype.card X)) +
        2 / (3 / 2 * (γ / 150))) * log c := by
  set C : ℝ := (Fintype.card X : ℝ) with hC
  set A := logb 2 C with hAdef
  have hcr : (1 : ℝ) ≤ c := by exact_mod_cast hc₁
  have hc₀ : (0 : ℝ) < c := by linarith
  have hlogc : 0 ≤ log (c : ℝ) := log_nonneg hcr
  have he := sq_mul_roundErr_le X hc4
  have hω := sq_mul_omegaOf_le (Fintype.card X) Fintype.card_pos hc₁
  have he_lo := roundErr_ge X hc4
  have hω₀ := omegaOf_nonneg (Fintype.card X) Fintype.card_pos (c * c)
  rw [← hC] at he hω he_lo
  set e := roundErr X (c * c) with hedef
  set ω := omegaOf (Fintype.card X) (c * c) with hωdef
  set κ := γ / 150 with hκ
  have hκ₀ : 0 < κ := by positivity
  set b := 3 / 2 * κ with hb
  have hb₀ : 0 < b := by positivity
  have he₀ : 0 < e := lt_of_lt_of_le (by positivity) he_lo
  unfold pathLen pot
  rw [← hC, ← hAdef, ← hedef, ← hκ, ← hb]
  have hρ : 2 * rhoOf X c - e = 2 / c * (1 - c * (ω + 3 / 2 * e)) := by
    unfold rhoOf; rw [← hedef, ← hωdef]; field_simp; ring
  set y := (c : ℝ) * (ω + 3 / 2 * e) with hy
  have hy₀ : 0 ≤ y := by positivity
  have hy₁ : y ≤ 1 / 2 := by
    have : ω + 3 / 2 * e ≤ 1 / (2 * c) := by linarith
    rw [hy]
    calc (c : ℝ) * (ω + 3 / 2 * e) ≤ c * (1 / (2 * c)) := mul_le_mul_of_nonneg_left this hc₀.le
      _ = 1 / 2 := by field_simp
  -- The full steps.
  have hfull : (⌈A / (2 * rhoOf X c - e)⌉₊ : ℝ) ≤ c * A / 2 + A * (lossW₀ C + 3 / 2 * lossE₀ C) + 1 +
      A * (lossW₁ C + 3 / 2 * lossE₁ C) * log c := by
    rw [hρ]
    have hpos : 0 < 2 / (c : ℝ) * (1 - y) := by
      have : 0 < 1 - y := by linarith
      positivity
    have h₁ : A / (2 / (c : ℝ) * (1 - y)) ≤ c * A / 2 * (1 + 2 * y) := by
      rw [div_le_iff₀ hpos]
      have : c * A / 2 * (1 + 2 * y) * (2 / c * (1 - y)) = A * ((1 + 2 * y) * (1 - y)) := by
        field_simp
      rw [this]
      have : 1 ≤ (1 + 2 * y) * (1 - y) := by nlinarith
      nlinarith
    have h₂ : c * A / 2 * (1 + 2 * y) = c * A / 2 + A * ((c : ℝ) ^ 2 * (ω + 3 / 2 * e)) := by
      rw [hy]; ring
    have h₃ : (c : ℝ) ^ 2 * (ω + 3 / 2 * e) ≤ lossW₀ C + 3 / 2 * lossE₀ C +
        (lossW₁ C + 3 / 2 * lossE₁ C) * log c := by
      unfold lossW₀ lossW₁ lossE₀ lossE₁
      have : (c : ℝ) ^ 2 * (ω + 3 / 2 * e) = (c : ℝ) ^ 2 * ω + 3 / 2 * ((c : ℝ) ^ 2 * e) := by ring
      linarith
    have h₄ := Nat.ceil_lt_add_one (show 0 ≤ A / (2 / (c : ℝ) * (1 - y)) by positivity)
    have h₅ := mul_le_mul_of_nonneg_left h₃ hA.le
    linarith
  -- The bridge steps.
  have hbridge : (⌈log (A / (2 * e / κ)) / b⌉₊ : ℝ) ≤ 1 + |log (A * κ / (8 * C))| / b +
      2 / b * log c := by
    refine (ceil_le_max_add_one _).trans ?_
    have hθ : 8 * C / (κ * (c : ℝ) ^ 2) ≤ 2 * e / κ := by
      rw [div_le_div_iff₀ (by positivity) hκ₀]
      have h4 : 4 * C ≤ e * (c : ℝ) ^ 2 := (div_le_iff₀ (by positivity)).mp he_lo
      have := mul_le_mul_of_nonneg_left h4 (show 0 ≤ 2 * κ by positivity)
      linarith
    have hl : log (A / (2 * e / κ)) ≤ log (A * κ / (8 * C)) + 2 * log c := by
      calc log (A / (2 * e / κ)) ≤ log (A / (8 * C / (κ * (c : ℝ) ^ 2))) :=
            log_le_log (by positivity) (div_le_div_of_nonneg_left hA.le (by positivity) hθ)
        _ = log (A * κ / (8 * C)) + 2 * log c := by
            rw [show A / (8 * C / (κ * (c : ℝ) ^ 2)) = A * κ / (8 * C) * (c : ℝ) ^ 2 by
              field_simp, log_mul (by positivity) (by positivity), Real.log_pow]; push_cast; ring
    have hmax : max (log (A / (2 * e / κ)) / b) 0 ≤ |log (A * κ / (8 * C))| / b + 2 / b * log c := by
      apply max_le
      · rw [div_le_iff₀ hb₀]
        have : |log (A * κ / (8 * C))| / b * b = |log (A * κ / (8 * C))| := by field_simp
        have : 2 / b * log c * b = 2 * log c := by field_simp
        have := le_abs_self (log (A * κ / (8 * C)))
        nlinarith
      · positivity
    linarith
  push_cast
  linarith

/-! ### The schedule of each kind -/

/-- **The schedule of each kind.** For every large `c`, a schedule of at most
`c·log₂C/2 + P₀ + P₁·ln c` steps, with codebooks of at most `2^c` lists of `c × c` bits, solves
every list of `c × c` patterns within `¼·c²/C` of `c²/C`. -/
theorem exists_sched (q : Bool) : ∃ P₀ P₁ : ℝ, ∀ᶠ c : ℕ in atTop, ∃ S : Sched q c,
    S.Solves (1 / 4) ∧ S.M = 2 ^ c ∧
      (S.T : ℝ) ≤ c * logb 2 patternCount / 2 + P₀ + P₁ * log c := by
  classical
  obtain ⟨γ, lam, L₀, hγ, -, hlam₀, hlam₁, hbooks⟩ := (cubeSys q).exists_books
  have hcardX : Fintype.card (OState q) = patternCount := card_oState q
  have hA : 0 < logb 2 (Fintype.card (OState q) : ℝ) := by
    rw [hcardX]; exact Real.logb_pos (by norm_num) (by exact_mod_cast patternCount_gt_one)
  have hlg₀ : 0 < log (1 / max lam (1 / 2)) := by
    have h₀ : 0 < max lam (1 / 2) := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
    exact log_pos (by rw [lt_div_iff₀ h₀]; linarith [max_lt hlam₁ (show (1 / 2 : ℝ) < 1 by norm_num)])
  have hfar : 0 < CycleSystem.farRate γ (OState q) := by
    unfold CycleSystem.farRate; have := CycleSystem.etaNear_pos (OState q); positivity
  -- The constants.
  obtain ⟨C, hC⟩ : ∃ C : ℝ, C = (Fintype.card (OState q) : ℝ) := ⟨_, rfl⟩
  have hC₁ : (1 : ℝ) ≤ C := by rw [hC]; exact_mod_cast Fintype.card_pos (α := OState q)
  obtain ⟨M₀, hM₀⟩ : ∃ M₀ : ℝ,
      M₀ = 2 * C + 2 * C ^ 2 + 2 * C * (2 * C * (2 * (1 + 2 * lossE₀ C / (γ / 150)))) := ⟨_, rfl⟩
  obtain ⟨M₁, hM₁⟩ : ∃ M₁ : ℝ, M₁ = 2 * C * (2 * C * (2 * (2 * lossE₁ C / (γ / 150)))) :=
    ⟨_, rfl⟩
  set ng := (allG (SideCycle q)).length with hng
  set len := CycleSystem.roundLen (SideCycle q) with hlen
  set lg := log (1 / max lam (1 / 2)) with hlg
  set A := logb 2 (Fintype.card (OState q) : ℝ) with hAdef
  refine ⟨(1 + L₀) * ng + (A * (lossW₀ C + 3 / 2 * lossE₀ C) + 2 +
      |log (A * (γ / 150) / (8 * C))| / (3 / 2 * (γ / 150))),
    2 / lg * ng + (A * (lossW₁ C + 3 / 2 * lossE₁ C) + 2 / (3 / 2 * (γ / 150))), ?_⟩
  filter_upwards [eventually_ge_atTop (4 * Fintype.card (OState q)),
    eventually_nat (eventually_lin_log_le (lossW₀ C + 5 * lossE₀ C) (lossW₁ C + 5 * lossE₁ C)
      (show (0 : ℝ) < 1 / 2 by norm_num)),
    eventually_nat (eventually_ge_atTop (1 / CycleSystem.farRate γ (OState q))),
    eventually_nat (eventually_lin_log_le ((1 + L₀) * len) (2 / lg * len) one_pos),
    eventually_nat (eventually_lin_log_le M₀ M₁ (show (0 : ℝ) < 1 / 2 by norm_num)),
    eventually_nat (eventually_sq_log_le M₀ M₁ (show (0 : ℝ) < 1 / 284 by norm_num)),
    eventually_nat (eventually_ge_atTop (4 * 284 * C ^ 2)),
    eventually_nat (eventually_lin_log_le (log (log C + 2) + 2 * C * log 2) (2 + 4 * C)
      (show (0 : ℝ) < log 2 / 2 by have := log_two_pos'; positivity))]
    with c hc4 hev₁ hev₂ hev₃ hev₄ hev₅ hev₆ hev₇
  have hc₁ : 1 ≤ c := le_trans (by have := Fintype.card_pos (α := OState q); omega) hc4
  have hcr : (1 : ℝ) ≤ c := by exact_mod_cast hc₁
  have hc₀ : (0 : ℝ) < c := by linarith
  have hlogc : 0 ≤ log (c : ℝ) := log_nonneg hcr
  have hcC : 4 * C ≤ c := by rw [hC]; exact_mod_cast hc4
  have hcc4 : 4 * Fintype.card (OState q) ≤ c * c := le_trans hc4 (Nat.le_mul_of_pos_left c (by omega))
  have hι : Fintype.card (Fin c × Fin c) = c * c := by simp
  obtain ⟨hsum, hρ₀, he4, hρle⟩ := rho_facts (OState q) hcc4 hc₁ (by rw [← hC]; exact hev₁)
  -- The merge.
  set r₀ := r0Of lam c with hr₀
  have hFc : (((r₀ + L₀) * len : ℕ) : ℝ) ≤ c := by
    have := r0Of_le hlam₁ hc₁
    push_cast
    have h₁ : ((r₀ : ℝ) + L₀) * len ≤ (2 / lg * log c + 1 + L₀) * len :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    have e₁ : (2 / lg * log (c : ℝ) + 1 + L₀) * len = (1 + L₀) * len + 2 / lg * len * log c := by ring
    linarith
  have hlamr := lam_pow_le hlam₀ hlam₁ hc₁
  have hDc := dev_le (OState q) hlamr hc₁ hFc
  have hDc₀ : 0 ≤ mergeDev (Fintype.card (OState q)) lam (1 / 4) r₀ ((r₀ + L₀) * len) (c * c) := by
    unfold mergeDev; positivity
  have hεs := epsStar_le (OState q) hγ hcc4 hc₁
  have hεs₀ : 0 ≤ epsStar (OState q) γ (c * c) := by unfold epsStar; positivity
  have hcμ := cmu_le (OState q) (εs := epsStar (OState q) γ (c * c)) hc₁ hDc
  rw [← hC] at hεs hcμ
  have hcμB : (c : ℝ) * mergeMu (Fintype.card (OState q)) (c * c)
      (mergeDev (Fintype.card (OState q)) lam (1 / 4) r₀ ((r₀ + L₀) * len) (c * c))
      (epsStar (OState q) γ (c * c)) ≤ M₀ + M₁ * log c := by
    have h₂ := mul_le_mul_of_nonneg_left hεs (show (0 : ℝ) ≤ 2 * C by positivity)
    rw [hM₀, hM₁]
    have e₁ : 2 * C * (2 * C * (2 * (1 + 2 * (lossE₀ C + lossE₁ C * log c) / (γ / 150)))) =
        2 * C * (2 * C * (2 * (1 + 2 * lossE₀ C / (γ / 150)))) +
          2 * C * (2 * C * (2 * (2 * lossE₁ C / (γ / 150)))) * log c := by ring
    linarith
  have hμ₀ : 0 ≤ mergeMu (Fintype.card (OState q)) (c * c)
      (mergeDev (Fintype.card (OState q)) lam (1 / 4) r₀ ((r₀ + L₀) * len) (c * c))
      (epsStar (OState q) γ (c * c)) := by
    unfold mergeMu; positivity
  have hμ : mergeMu (Fintype.card (OState q)) (c * c)
      (mergeDev (Fintype.card (OState q)) lam (1 / 4) r₀ ((r₀ + L₀) * len) (c * c))
      (epsStar (OState q) γ (c * c)) ≤ 1 / 2 := by
    have := hcμB.trans hev₄
    rw [show (1 / 2 : ℝ) * c = c * (1 / 2) by ring] at this
    exact le_of_mul_le_mul_left this hc₀
  have h71 : 71 * (4 * (Fintype.card (OState q) : ℝ) ^ 2 + (M₀ + M₁ * log c) ^ 2) ≤ c / 2 := by
    rw [← hC]; linarith
  have hcov₁ := cover_merge_le (Fintype.card (OState q)) Fintype.card_pos hc₁ hμ₀ hcμB h71
    (by rw [← hC]; exact hev₇)
  have hcov₂ : coverBound ((c * c : ℕ) : ℝ) (Fintype.card (OState q))
      (rhoOf (OState q) c + roundErr (OState q) (c * c)) ≤ 2 ^ c := by
    rw [show rhoOf (OState q) c + roundErr (OState q) (c * c) =
      1 / (c : ℝ) - omegaOf (Fintype.card (OState q)) (c * c) by unfold rhoOf; ring,
      coverBound_full _ Fintype.card_pos hc₁]
  have hpos : (1 / 4 : ℝ) * ((c * c : ℕ) : ℝ) / (Fintype.card (OState q) : ℝ) +
      (((r₀ + L₀) * len : ℕ) : ℝ) / 2 ≤ ((c * c : ℕ) : ℝ) / (2 * Fintype.card (OState q)) := by
    rw [← hC, show ((c * c : ℕ) : ℝ) = (c : ℝ) ^ 2 by push_cast; ring]
    have h₁ : (c : ℝ) / 2 ≤ (c : ℝ) ^ 2 / (4 * C) := by
      rw [div_le_div_iff₀ (by norm_num) (by positivity)]; nlinarith
    have e₁ : (c : ℝ) ^ 2 / (2 * C) = 1 / 4 * (c : ℝ) ^ 2 / C + (c : ℝ) ^ 2 / (4 * C) := by
      field_simp; ring
    linarith
  -- The codebooks.
  obtain ⟨T, g, B₁, B₂, hT, hB, hsolve⟩ := hbooks (Fin c × Fin c) c r₀ (1 / 4) (rhoOf (OState q) c)
    (by rw [hι]; positivity) (by rw [hι]; exact hcc4) (by norm_num) hρ₀
    (by have h₁ : 1 / (c : ℝ) ≤ CycleSystem.farRate γ (OState q) := by
          rw [div_le_iff₀ hc₀]; rw [div_le_iff₀ hfar] at hev₂; linarith
        linarith)
    (by rw [hι]; exact he4) (by rw [hι]; exact hpos) (by rw [hι]; exact hμ)
    (by rw [hι]; exact hcov₁) (by rw [hι]; exact hcov₂)
  refine ⟨⟨T, g, 2 ^ c, B₁, B₂, fun t ↦ ⟨(hB t).1, (hB t).2.1⟩, fun t ↦ (hB t).2.2.1,
    fun t ↦ (hB t).2.2.2⟩, fun s hs ↦ ?_, rfl, ?_⟩
  · obtain ⟨a, b, hab, hrun⟩ := hsolve s (by rw [hι]; exact hs)
    exact ⟨a, b, hab, hrun⟩
  · -- The number of steps.
    have hTr : (T : ℝ) ≤ (((r₀ + L₀) * ng : ℕ) : ℝ) + pathLen (OState q) γ (rhoOf (OState q) c)
        (c * c) := by
      have := hT; rw [hι] at this; exact_mod_cast this
    have hP := pathLen_le (OState q) hγ hcc4 hc₁ hA hsum
    have hM : (((r₀ + L₀) * ng : ℕ) : ℝ) ≤ (1 + L₀) * ng + 2 / lg * ng * log c := by
      have hr := r0Of_le hlam₁ hc₁
      push_cast
      have h₁ : ((r₀ : ℝ) + L₀) * ng ≤ (2 / lg * log c + 1 + L₀) * ng :=
        mul_le_mul_of_nonneg_right (by linarith only [hr]) (by positivity)
      linarith only [h₁]
    have hAeq : A = logb 2 (patternCount : ℝ) := by rw [hAdef, hcardX]
    rw [← hAeq]
    subst hC
    linarith only [hTr, hP, hM]

end CubeGod
