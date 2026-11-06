import CubeGod.Info.Chernoff

/-!
# Joint distributions

Marginals of a joint distribution `P` on `α × β`, the fact that mutual information is nonnegative,
and the entropy sums behind it.
-/

open Finset Real

set_option linter.unusedSectionVars false

namespace CubeGod

variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

/-- The marginal on `α`. -/
def fstD (P : α × β → ℝ) (a : α) : ℝ := ∑ b, P (a, b)

/-- The marginal on `β`. -/
def sndD (P : α × β → ℝ) (b : β) : ℝ := ∑ a, P (a, b)

variable {P : α × β → ℝ}

omit [DecidableEq α] [DecidableEq β] in
theorem isDist_fstD (hP : IsDist P) : IsDist (fstD P) := by
  refine ⟨fun a ↦ Finset.sum_nonneg fun b _ ↦ hP.nonneg _, ?_⟩
  rw [← hP.sum, Fintype.sum_prod_type]
  rfl

omit [DecidableEq α] [DecidableEq β] in
theorem isDist_sndD (hP : IsDist P) : IsDist (sndD P) := by
  refine ⟨fun b ↦ Finset.sum_nonneg fun a _ ↦ hP.nonneg _, ?_⟩
  rw [← hP.sum, Fintype.sum_prod_type_right]
  rfl

omit [DecidableEq α] [DecidableEq β] in
theorem le_fstD (hP : IsDist P) (x : α × β) : P x ≤ fstD P x.1 :=
  Finset.single_le_sum (f := fun b ↦ P (x.1, b)) (fun _ _ ↦ hP.nonneg _) (mem_univ x.2)

omit [DecidableEq α] [DecidableEq β] in
theorem le_sndD (hP : IsDist P) (x : α × β) : P x ≤ sndD P x.2 :=
  Finset.single_le_sum (f := fun a ↦ P (a, x.2)) (fun _ _ ↦ hP.nonneg _) (mem_univ x.1)

omit [DecidableEq α] [DecidableEq β] in
/-- `∑ P log(marginal)` is minus the entropy of the marginal, on the `β` side. -/
theorem sum_log_snd (P : α × β → ℝ) :
    ∑ v, P v * log (sndD P v.2) = -∑ b, negMulLog (sndD P b) := by
  rw [Fintype.sum_prod_type_right]
  simp only [negMulLog, neg_mul, Finset.sum_neg_distrib, neg_neg]
  refine Finset.sum_congr rfl fun b _ ↦ ?_
  rw [← Finset.sum_mul]
  rfl

omit [DecidableEq α] [DecidableEq β] in
/-- `∑ P log(marginal)` is minus the entropy of the marginal, on the `α` side. -/
theorem sum_log_fst (P : α × β → ℝ) :
    ∑ v, P v * log (fstD P v.1) = -∑ a, negMulLog (fstD P a) := by
  rw [Fintype.sum_prod_type]
  simp only [negMulLog, neg_mul, Finset.sum_neg_distrib, neg_neg]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [← Finset.sum_mul]
  rfl

omit [DecidableEq α] [DecidableEq β] in
theorem sum_log_self (P : α × β → ℝ) : ∑ v, P v * log (P v) = -∑ v, negMulLog (P v) := by
  simp [negMulLog, Finset.sum_neg_distrib]

omit [DecidableEq α] [DecidableEq β] in
/-- Mutual information is nonnegative (Gibbs' inequality). -/
theorem mi_nonneg (hP : IsDist P) : 0 ≤ mi P := by
  have hA := isDist_fstD hP
  have hB := isDist_sndD hP
  -- Each term is at least `P v - fst * snd`.
  have hterm : ∀ v : α × β, P v - fstD P v.1 * sndD P v.2 ≤
      P v * (log (P v) - log (fstD P v.1) - log (sndD P v.2)) := by
    intro v
    have hv := hP.nonneg v
    have ha := hA.nonneg v.1
    have hb := hB.nonneg v.2
    by_cases h0 : P v = 0
    · simp only [h0, zero_mul, zero_sub]
      exact neg_nonpos.mpr (mul_nonneg ha hb)
    · have hp : 0 < P v := lt_of_le_of_ne hv (Ne.symm h0)
      have hap : 0 < fstD P v.1 := lt_of_lt_of_le hp (le_fstD hP v)
      have hbp : 0 < sndD P v.2 := lt_of_lt_of_le hp (le_sndD hP v)
      have hr : 0 < fstD P v.1 * sndD P v.2 / P v := by positivity
      have hlog := Real.log_le_sub_one_of_pos hr
      rw [Real.log_div (by positivity) h0, Real.log_mul hap.ne' hbp.ne'] at hlog
      have hmul := mul_le_mul_of_nonneg_left hlog hp.le
      have he : P v * (fstD P v.1 * sndD P v.2 / P v - 1) = fstD P v.1 * sndD P v.2 - P v := by
        field_simp
      rw [he] at hmul
      nlinarith
  have hsum := Finset.sum_le_sum fun v (_ : v ∈ univ) ↦ hterm v
  have hzero : ∑ v : α × β, (P v - fstD P v.1 * sndD P v.2) = 0 := by
    rw [Finset.sum_sub_distrib, hP.sum, Fintype.sum_prod_type]
    simp only [← Finset.mul_sum, hB.sum, mul_one, hA.sum, sub_self]
  rw [hzero] at hsum
  simp only [mul_sub, Finset.sum_sub_distrib] at hsum
  rw [sum_log_self, sum_log_fst, sum_log_snd] at hsum
  unfold mi H
  have hl := log_two_pos'
  have hfst : (fun a ↦ ∑ b, P (a, b)) = fstD P := rfl
  have hsnd : (fun b ↦ ∑ a, P (a, b)) = sndD P := rfl
  rw [hfst, hsnd]
  rw [← add_div, ← sub_div]
  apply div_nonneg _ hl.le
  linarith

end CubeGod
