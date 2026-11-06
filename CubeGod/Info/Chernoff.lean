import CubeGod.Info.Typical

/-!
# A Chernoff bound for lists of independent draws

We don't use measure theory. A list of `c` independent draws is a list `y : Fin c → β` with weight
`∏ k, q k (y k)`, and all the arguments are finite sums.
-/

open Finset Real

set_option linter.unusedSectionVars false

namespace CubeGod

variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] {c : ℕ}

/-- The chance of the list `y`, for independent draws from `q k`. -/
def prodW (q : Fin c → β → ℝ) (y : Fin c → β) : ℝ := ∏ k, q k (y k)

omit [DecidableEq β] in
theorem prodW_nonneg {q : Fin c → β → ℝ} (hq : ∀ k, IsDist (q k)) (y : Fin c → β) :
    0 ≤ prodW q y :=
  Finset.prod_nonneg fun k _ ↦ (hq k).nonneg _

omit [DecidableEq β] in
/-- Sums of products over lists factor. -/
theorem sum_prod_list (g : Fin c → β → ℝ) :
    ∑ y : Fin c → β, ∏ k, g k (y k) = ∏ k, ∑ b, g k b := by
  have := (Finset.prod_univ_sum (fun _ : Fin c ↦ (univ : Finset β)) g).symm
  simpa [Fintype.piFinset_univ] using this

omit [DecidableEq β] in
theorem sum_prodW {q : Fin c → β → ℝ} (hq : ∀ k, IsDist (q k)) : ∑ y, prodW q y = 1 := by
  simp only [prodW]
  rw [sum_prod_list]
  simp [(hq _).sum]

omit [DecidableEq β] in
/-- `exp (λ·N)` has mean at most `exp (μ·(e^λ - 1))`, when `N` is a sum of 0-1 values. -/
theorem sum_prodW_exp {q : Fin c → β → ℝ} (hq : ∀ k, IsDist (q k)) {f : Fin c → β → ℝ}
    (hf : ∀ k b, f k b = 0 ∨ f k b = 1) (l : ℝ) :
    ∑ y, prodW q y * exp (l * ∑ k, f k (y k)) ≤
      exp ((∑ k, ∑ b, q k b * f k b) * (exp l - 1)) := by
  have hrewrite : ∀ y : Fin c → β, prodW q y * exp (l * ∑ k, f k (y k)) =
      ∏ k, (q k (y k) * exp (l * f k (y k))) := by
    intro y
    rw [Finset.mul_sum, Real.exp_sum, prodW, Finset.prod_mul_distrib]
  simp only [hrewrite]
  rw [sum_prod_list (fun k b ↦ q k b * exp (l * f k b)), Finset.sum_mul, Real.exp_sum]
  refine Finset.prod_le_prod₀ (fun k _ ↦ ?_) fun k _ ↦ ?_
  · exact Finset.sum_nonneg fun b _ ↦ mul_nonneg ((hq k).nonneg b) (exp_pos _).le
  · -- `E exp(l f) = 1 + m (e^l - 1) ≤ exp (m (e^l - 1))`.
    have h : ∑ b, q k b * exp (l * f k b) = 1 + (∑ b, q k b * f k b) * (exp l - 1) := by
      have hb : ∀ b, q k b * exp (l * f k b) = q k b + q k b * f k b * (exp l - 1) := by
        intro b
        rcases hf k b with h | h
        · simp [h]
        · simp [h]
          ring
      simp only [hb, Finset.sum_add_distrib, (hq k).sum, Finset.sum_mul]
    rw [h]
    linarith [add_one_le_exp ((∑ b, q k b * f k b) * (exp l - 1))]

/-- The mean of a sum of 0-1 values. -/
def meanN (q : Fin c → β → ℝ) (f : Fin c → β → ℝ) : ℝ := ∑ k, ∑ b, q k b * f k b

omit [DecidableEq β] in
theorem meanN_nonneg {q : Fin c → β → ℝ} (hq : ∀ k, IsDist (q k)) {f : Fin c → β → ℝ}
    (hf : ∀ k b, f k b = 0 ∨ f k b = 1) : 0 ≤ meanN q f := by
  refine Finset.sum_nonneg fun k _ ↦ Finset.sum_nonneg fun b _ ↦ ?_
  rcases hf k b with h | h <;> simp [h, (hq k).nonneg b]

omit [DecidableEq β] in
theorem meanN_le {q : Fin c → β → ℝ} (hq : ∀ k, IsDist (q k)) {f : Fin c → β → ℝ}
    (hf : ∀ k b, f k b = 0 ∨ f k b = 1) : meanN q f ≤ c := by
  have : ∀ k, ∑ b, q k b * f k b ≤ 1 := by
    intro k
    rw [← (hq k).sum]
    refine Finset.sum_le_sum fun b _ ↦ ?_
    rcases hf k b with h | h <;> simp [h, (hq k).nonneg b]
  calc meanN q f ≤ ∑ _k : Fin c, (1 : ℝ) := Finset.sum_le_sum fun k _ ↦ this k
    _ = c := by simp

open Classical in
omit [DecidableEq β] in
/-- The chance that a sum of 0-1 values is at least `t` above its mean. -/
theorem chernoff_upper {q : Fin c → β → ℝ} (hq : ∀ k, IsDist (q k)) {f : Fin c → β → ℝ}
    (hf : ∀ k b, f k b = 0 ∨ f k b = 1) {l : ℝ} (t : ℝ) (hl₀ : 0 ≤ l) (hl₁ : l ≤ 1) :
    ∑ y with meanN q f + t ≤ ∑ k, f k (y k), prodW q y ≤ exp (-(l * t) + c * l ^ 2) := by
  set μ := meanN q f with hμ
  have hstep : ∀ y, (if μ + t ≤ ∑ k, f k (y k) then prodW q y else 0) ≤
      prodW q y * (exp (l * ∑ k, f k (y k)) * exp (-(l * (μ + t)))) := by
    intro y
    have hw := prodW_nonneg hq y
    split_ifs with h
    · have : 1 ≤ exp (l * ∑ k, f k (y k)) * exp (-(l * (μ + t))) := by
        rw [← Real.exp_add]
        apply Real.one_le_exp
        nlinarith
      nlinarith
    · positivity
  rw [Finset.sum_filter]
  refine (Finset.sum_le_sum fun y _ ↦ hstep y).trans ?_
  simp only [← mul_assoc]
  rw [← Finset.sum_mul]
  refine (mul_le_mul_of_nonneg_right (sum_prodW_exp hq hf l) (exp_pos _).le).trans ?_
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h₁ := abs_le.mp (Real.abs_exp_sub_one_sub_id_le (x := l) (by rw [abs_le]; constructor <;> linarith))
  have hμ₀ : 0 ≤ μ := meanN_nonneg hq hf
  have hμ₁ : μ ≤ c := meanN_le hq hf
  have h₂ : μ * (exp l - 1 - l) ≤ c * l ^ 2 := by
    calc μ * (exp l - 1 - l) ≤ μ * l ^ 2 := mul_le_mul_of_nonneg_left h₁.2 hμ₀
      _ ≤ c * l ^ 2 := mul_le_mul_of_nonneg_right hμ₁ (by positivity)
  have : (∑ k, ∑ b, q k b * f k b) = μ := rfl
  rw [this]
  nlinarith

open Classical in
omit [DecidableEq β] in
/-- The chance that a sum of 0-1 values is at least `t` below its mean. -/
theorem chernoff_lower {q : Fin c → β → ℝ} (hq : ∀ k, IsDist (q k)) {f : Fin c → β → ℝ}
    (hf : ∀ k b, f k b = 0 ∨ f k b = 1) {l : ℝ} (t : ℝ) (hl₀ : 0 ≤ l) (hl₁ : l ≤ 1) :
    ∑ y with ∑ k, f k (y k) ≤ meanN q f - t, prodW q y ≤ exp (-(l * t) + c * l ^ 2) := by
  set μ := meanN q f with hμ
  have hstep : ∀ y, (if ∑ k, f k (y k) ≤ μ - t then prodW q y else 0) ≤
      prodW q y * (exp ((-l) * ∑ k, f k (y k)) * exp (l * (μ - t))) := by
    intro y
    have hw := prodW_nonneg hq y
    split_ifs with h
    · have : 1 ≤ exp ((-l) * ∑ k, f k (y k)) * exp (l * (μ - t)) := by
        rw [← Real.exp_add]
        apply Real.one_le_exp
        nlinarith
      nlinarith
    · positivity
  rw [Finset.sum_filter]
  refine (Finset.sum_le_sum fun y _ ↦ hstep y).trans ?_
  simp only [← mul_assoc]
  rw [← Finset.sum_mul]
  refine (mul_le_mul_of_nonneg_right (sum_prodW_exp hq hf (-l)) (exp_pos _).le).trans ?_
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h₁ := abs_le.mp (Real.abs_exp_sub_one_sub_id_le (x := -l) (by rw [abs_le]; constructor <;> linarith))
  have hμ₀ : 0 ≤ μ := meanN_nonneg hq hf
  have hμ₁ : μ ≤ c := meanN_le hq hf
  have h₂ : μ * (exp (-l) - 1 - (-l)) ≤ c * l ^ 2 := by
    have : (-l) ^ 2 = l ^ 2 := by ring
    calc μ * (exp (-l) - 1 - (-l)) ≤ μ * l ^ 2 := mul_le_mul_of_nonneg_left (this ▸ h₁.2) hμ₀
      _ ≤ c * l ^ 2 := mul_le_mul_of_nonneg_right hμ₁ (by positivity)
  have : (∑ k, ∑ b, q k b * f k b) = μ := rfl
  rw [this]
  nlinarith

omit [Fintype α] in
/-- The number of times a value appears, as a sum of 0-1 values. -/
theorem count_eq_sum (x : Fin c → α) (v : α) :
    (count x v : ℝ) = ∑ k, if x k = v then (1 : ℝ) else 0 := by
  simp only [count, Finset.card_filter]
  push_cast
  rfl

open Classical in
/-- A list of `c` uniform draws is typical, except with chance exponentially small
in `c`. Counted: at most `2|α|·exp(-τ²/(4|α|²))^c·|α|^c` lists aren't typical. -/
theorem typical_chernoff_explicit [Nonempty α] {τ : ℝ} (hτ₀ : 0 < τ) (hτ₁ : τ ≤ 1) (c : ℕ) :
    (#{x : Fin c → α | ¬ Typical τ (uniform α) x} : ℝ) ≤
      (2 * Fintype.card α) * exp (-(τ ^ 2 * (Fintype.card α : ℝ)⁻¹ ^ 2 / 4)) ^ c *
        (Fintype.card α : ℝ) ^ c := by
  have hcard : (0 : ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos
  have hcard1 : (1 : ℝ) ≤ Fintype.card α := by exact_mod_cast Fintype.card_pos
  set u : ℝ := (Fintype.card α : ℝ)⁻¹ with hu
  have hu₀ : 0 < u := by positivity
  have hu₁ : u ≤ 1 := by
    rw [hu]; exact inv_le_one_of_one_le₀ hcard1
  set l : ℝ := τ * u / 2 with hl
  have hl₀ : 0 ≤ l := by positivity
  have hl₁ : l ≤ 1 := by
    rw [hl]; nlinarith
  -- Fix `c`. Each list has weight `u^c`.
  set q : Fin c → α → ℝ := fun _ ↦ uniform α with hq
  have hqd : ∀ k, IsDist (q k) := fun _ ↦ isDist_uniform
  have hw : ∀ y : Fin c → α, prodW q y = u ^ c := by
    intro y
    simp [prodW, hq, uniform, hu]
  set t : ℝ := τ * c * u with ht
  -- The two tails for one value.
  have htail : ∀ v : α, (∑ y : Fin c → α, if t ≤ |(count y v : ℝ) - c * u| then u ^ c else 0)
      ≤ 2 * exp (-(τ ^ 2 * u ^ 2 / 4)) ^ c := by
    intro v
    set f : Fin c → α → ℝ := fun _ b ↦ if b = v then 1 else 0 with hf
    have hf01 : ∀ k b, f k b = 0 ∨ f k b = 1 := by
      intro k b
      simp only [hf]
      split_ifs <;> simp
    have hmean : meanN q f = c * u := by
      simp [meanN, hq, hf, uniform, hu]
    have hcount : ∀ y : Fin c → α, (count y v : ℝ) = ∑ k, f k (y k) := fun y ↦ count_eq_sum y v
    have hU := chernoff_upper hqd hf01 t hl₀ hl₁
    have hL := chernoff_lower hqd hf01 t hl₀ hl₁
    rw [Finset.sum_filter] at hU hL
    have he : exp (-(l * t) + c * l ^ 2) = exp (-(τ ^ 2 * u ^ 2 / 4)) ^ c := by
      rw [← Real.exp_nat_mul]
      congr 1
      rw [hl, ht]
      ring
    rw [he] at hU hL
    have key : (∑ y : Fin c → α, if t ≤ |(count y v : ℝ) - c * u| then u ^ c else 0) ≤
        (∑ a : Fin c → α, if meanN q f + t ≤ ∑ k, f k (a k) then prodW q a else 0) +
        (∑ a : Fin c → α, if ∑ k, f k (a k) ≤ meanN q f - t then prodW q a else 0) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun y _ ↦ ?_
      simp only [hw, hmean, ← hcount]
      have hupow : 0 ≤ u ^ c := by positivity
      by_cases h : t ≤ |(count y v : ℝ) - c * u|
      · rw [ite_eq_left h]
        rcases le_abs.mp h with h' | h'
        · rw [ite_eq_left (show c * u + t ≤ (count y v : ℝ) by linarith)]
          split_ifs <;> linarith
        · rw [ite_eq_left (show (count y v : ℝ) ≤ c * u - t by linarith)]
          split_ifs <;> linarith
      · rw [ite_eq_right h]
        split_ifs <;> linarith
    linarith
  -- Each non-typical list is in a tail of some value.
  have hbad : ∀ y : Fin c → α, ¬ Typical τ (uniform α) y →
      ∃ v, t ≤ |(count y v : ℝ) - c * u| := by
    intro y hy
    by_contra hall
    push Not at hall
    apply hy
    intro v
    have := abs_lt.mp (hall v)
    have hun : uniform α v = u := rfl
    rw [hun]
    constructor
    · rw [ht] at this; nlinarith [this.1]
    · rw [ht] at this; nlinarith [this.2]
  -- Add over the values.
  have hsum : (#{x : Fin c → α | ¬ Typical τ (uniform α) x} : ℝ) * u ^ c ≤
      ∑ v : α, ∑ y : Fin c → α, if t ≤ |(count y v : ℝ) - c * u| then u ^ c else 0 := by
    have hupow : 0 ≤ u ^ c := by positivity
    have hnn : ∀ (y : Fin c → α) (v : α),
        0 ≤ if t ≤ |(count y v : ℝ) - c * u| then u ^ c else 0 := by
      intro y v
      split_ifs <;> simp [hupow]
    rw [Finset.sum_comm]
    calc (#{x : Fin c → α | ¬ Typical τ (uniform α) x} : ℝ) * u ^ c
        = ∑ _y ∈ univ.filter fun x : Fin c → α ↦ ¬ Typical τ (uniform α) x, u ^ c := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ y ∈ univ.filter fun x : Fin c → α ↦ ¬ Typical τ (uniform α) x,
            ∑ v : α, if t ≤ |(count y v : ℝ) - c * u| then u ^ c else 0 := by
          refine Finset.sum_le_sum fun y hy ↦ ?_
          obtain ⟨v, hv⟩ := hbad y (Finset.mem_filter.mp hy).2
          calc u ^ c = if t ≤ |(count y v : ℝ) - c * u| then u ^ c else 0 := by
                rw [ite_eq_left hv]
            _ ≤ _ := Finset.single_le_sum (f := fun v ↦
                if t ≤ |(count y v : ℝ) - c * u| then u ^ c else 0) (fun v _ ↦ hnn y v) (mem_univ v)
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          fun y _ _ ↦ Finset.sum_nonneg fun v _ ↦ hnn y v
  have hfinal := hsum.trans (Finset.sum_le_sum fun v _ ↦ htail v)
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hfinal
  have hpow : u ^ c * (Fintype.card α : ℝ) ^ c = 1 := by
    rw [← mul_pow, hu, inv_mul_cancel₀ hcard.ne', one_pow]
  calc (#{x : Fin c → α | ¬ Typical τ (uniform α) x} : ℝ)
      = (#{x : Fin c → α | ¬ Typical τ (uniform α) x} : ℝ) * (u ^ c * (Fintype.card α : ℝ) ^ c) := by
        rw [hpow, mul_one]
    _ = ((#{x : Fin c → α | ¬ Typical τ (uniform α) x} : ℝ) * u ^ c) * (Fintype.card α : ℝ) ^ c := by
        ring
    _ ≤ ((Fintype.card α : ℝ) * (2 * exp (-(τ ^ 2 * u ^ 2 / 4)) ^ c)) * (Fintype.card α : ℝ) ^ c :=
        mul_le_mul_of_nonneg_right hfinal (by positivity)
    _ = _ := by ring

end CubeGod
