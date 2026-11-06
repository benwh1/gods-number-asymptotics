import Mathlib

/-!
# Entropy on a finite set

A distribution is a nonnegative function with sum 1. Entropy is in bits.
-/

open Finset Real

namespace CubeGod

variable {α β : Type*} [Fintype α] [Fintype β]

/-- `p` is a probability distribution on `α`. -/
structure IsDist (p : α → ℝ) : Prop where
  nonneg : ∀ a, 0 ≤ p a
  sum : ∑ a, p a = 1

theorem IsDist.le_one {p : α → ℝ} (h : IsDist p) (a : α) : p a ≤ 1 := by
  rw [← h.sum]
  exact Finset.single_le_sum (fun i _ ↦ h.nonneg i) (mem_univ a)

/-- The entropy of `p`, in bits. -/
noncomputable def H (p : α → ℝ) : ℝ := (∑ a, negMulLog (p a)) / log 2

theorem log_two_pos' : 0 < log 2 := log_pos (by norm_num)

theorem continuous_H : Continuous (H : (α → ℝ) → ℝ) := by
  unfold H
  fun_prop

/-- Entropy doesn't change when the points are relabelled. -/
theorem H_comp_equiv (p : α → ℝ) (σ : β ≃ α) : H (p ∘ σ) = H p := by
  unfold H
  congr 1
  exact Equiv.sum_comp σ (fun a ↦ negMulLog (p a))

/-- The entropy of a product of two distributions is the sum of their entropies. -/
theorem H_prod {p : α → ℝ} {q : β → ℝ} (hp : IsDist p) (hq : IsDist q) :
    H (fun x : α × β ↦ p x.1 * q x.2) = H p + H q := by
  unfold H
  rw [← add_div]
  congr 1
  rw [Fintype.sum_prod_type]
  simp only [negMulLog_mul]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul, hp.sum, hq.sum]
  simp

/-- Entropy is largest for the uniform distribution. -/
theorem H_le_log_card [Nonempty α] {p : α → ℝ} (h : IsDist p) :
    H p ≤ logb 2 (Fintype.card α) := by
  have hcard : (0 : ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos
  set N : ℝ := (Fintype.card α : ℝ) with hN
  -- Concavity of `negMulLog`, at the average of the `p a`.
  have hj := concaveOn_negMulLog.le_map_sum (t := (univ : Finset α))
    (w := fun _ ↦ N⁻¹) (p := p)
    (fun _ _ ↦ by positivity)
    (by simp [N, Finset.card_univ, hcard.ne'])
    (fun a _ ↦ h.nonneg a)
  simp only [smul_eq_mul, ← Finset.mul_sum, h.sum, mul_one] at hj
  have hval : negMulLog N⁻¹ = N⁻¹ * log N := by
    simp [negMulLog, Real.log_inv]
  rw [hval] at hj
  have : ∑ a, negMulLog (p a) ≤ log N := by
    have := mul_le_mul_of_nonneg_left hj hcard.le
    field_simp at this
    linarith
  unfold H
  rw [logb, div_le_div_iff_of_pos_right log_two_pos']
  exact this

/-- The mutual information of the two parts of a joint distribution. -/
noncomputable def mi (P : α × β → ℝ) : ℝ :=
  H (fun a ↦ ∑ b, P (a, b)) + H (fun b ↦ ∑ a, P (a, b)) - H P

/-- A mixture of distributions is a distribution. -/
theorem IsDist.mix {p q : α → ℝ} (hp : IsDist p) (hq : IsDist q) {t : ℝ} (h₀ : 0 ≤ t) (h₁ : t ≤ 1) :
    IsDist (fun a ↦ (1 - t) * p a + t * q a) := by
  constructor
  · intro a
    have := hp.nonneg a; have := hq.nonneg a
    have : 0 ≤ 1 - t := by linarith
    positivity
  · simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hp.sum, hq.sum]
    ring

/-- Relabelling a distribution gives a distribution. -/
theorem IsDist.comp_equiv {p : α → ℝ} (hp : IsDist p) (σ : β ≃ α) : IsDist (p ∘ σ) :=
  ⟨fun _ ↦ hp.nonneg _, (Equiv.sum_comp σ p).trans hp.sum⟩

/-- The product of two distributions is a distribution. -/
theorem IsDist.prod {p : α → ℝ} {q : β → ℝ} (hp : IsDist p) (hq : IsDist q) :
    IsDist (fun x : α × β ↦ p x.1 * q x.2) := by
  refine ⟨fun x ↦ mul_nonneg (hp.nonneg _) (hq.nonneg _), ?_⟩
  rw [Fintype.sum_prod_type]
  simp only [← Finset.mul_sum, hq.sum, mul_one, hp.sum]

/-- The uniform distribution. -/
noncomputable def uniform (α : Type*) [Fintype α] : α → ℝ := fun _ ↦ (Fintype.card α : ℝ)⁻¹

theorem isDist_uniform [Nonempty α] : IsDist (uniform α) := by
  have h : (Fintype.card α : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  refine ⟨fun _ ↦ by unfold uniform; positivity, ?_⟩
  simp [uniform, Finset.card_univ, h]

theorem H_uniform [Nonempty α] : H (uniform α) = logb 2 (Fintype.card α) := by
  have h : (Fintype.card α : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  unfold H uniform logb
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  congr 1
  simp only [negMulLog, Real.log_inv]
  field_simp

end CubeGod
