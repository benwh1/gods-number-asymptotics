import CubeGod.Schedule.Effective
import CubeGod.Info.Joint

/-!
# Entropy moves slowly

If two distributions on a set of size `M` differ by at most `t` in total, their entropies differ by
at most `(t·ln(M/t) + t)/ln 2` bits, and so do their mutual informations, with one such term for
each of the two parts and the pair.
-/

open Finset Real

set_option linter.unusedSectionVars false

namespace CubeGod

variable {α β : Type*} [Fintype α] [Fintype β]

/-- The bound on how far entropy moves, for a set of size `M` and a total change `t`, in bits. -/
noncomputable def contErr (M t : ℝ) : ℝ := (t * log (M / t) + t) / log 2

theorem negMulLog_sub_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hy1 : y ≤ 1) (hxy : x ≤ y) :
    negMulLog x - negMulLog y ≤ y - x := by
  set d := y - x with hd
  have hd₀ : 0 ≤ d := by linarith
  have hyd : y = x + d := by rw [hd]; ring
  rcases hx.eq_or_lt with hx0 | hxp
  · rw [← hx0, negMulLog_zero, zero_sub]
    have := negMulLog_nonneg hy hy1
    linarith
  · have hlog : log y - log x ≤ d / x := by
      rw [← log_div (by linarith) hxp.ne']
      have := log_le_sub_one_of_pos (div_pos (lt_of_lt_of_le hxp hxy) hxp)
      have e : y / x - 1 = d / x := by rw [hyd]; field_simp; ring
      linarith
    have hly : log y ≤ 0 := log_nonpos hy hy1
    have e : negMulLog x - negMulLog y = x * (log y - log x) + d * log y := by
      simp only [negMulLog, hyd]; ring
    rw [e]
    have h₁ : x * (log y - log x) ≤ d := by
      have := mul_le_mul_of_nonneg_left hlog hxp.le
      rwa [mul_div_cancel₀ _ hxp.ne'] at this
    nlinarith

/-- `|−x ln x + y ln y| ≤ −d ln d + d` for `d = |x − y|`, on `[0, 1]`. -/
theorem abs_negMulLog_sub_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hx1 : x ≤ 1) (hy1 : y ≤ 1) :
    |negMulLog x - negMulLog y| ≤ negMulLog |x - y| + |x - y| := by
  have key : ∀ {x y : ℝ}, 0 ≤ x → 0 ≤ y → x ≤ 1 → y ≤ 1 → x ≤ y →
      |negMulLog x - negMulLog y| ≤ negMulLog |x - y| + |x - y| := by
    intro x y hx hy hx1 hy1 hxy
    have hab : |x - y| = y - x := by rw [abs_sub_comm]; exact abs_of_nonneg (by linarith)
    rw [hab]
    have h₁ : negMulLog y ≤ negMulLog x + negMulLog (y - x) := by
      have := negMulLog_add_le hx (show 0 ≤ y - x by linarith)
      rwa [add_sub_cancel] at this
    have h₂ := negMulLog_sub_le hx hy hy1 hxy
    have h₃ : 0 ≤ negMulLog (y - x) := negMulLog_nonneg (by linarith) (by linarith)
    rw [abs_le]
    constructor <;> linarith
  rcases le_total x y with h | h
  · exact key hx hy hx1 hy1 h
  · rw [abs_sub_comm, abs_sub_comm x y]
    exact key hy hx hy1 hx1 h

/-- `−d ln d ≤ d·ln(1/s) + s − d` for every `s > 0`. -/
theorem negMulLog_le_lin {d s : ℝ} (hd : 0 ≤ d) (hs : 0 < s) :
    negMulLog d ≤ d * log (1 / s) + s - d := by
  rcases hd.eq_or_lt with rfl | hdp
  · simp; linarith
  · have hl := log_le_sub_one_of_pos (show 0 < s / d by positivity)
    have e : negMulLog d = d * log (1 / s) + d * log (s / d) := by
      rw [negMulLog, log_div hs.ne' hdp.ne', one_div, log_inv]; ring
    rw [e]
    have := mul_le_mul_of_nonneg_left hl hdp.le
    have e₂ : d * (s / d - 1) = s - d := by field_simp
    linarith

/-- **Entropy moves slowly.** If `∑|P − Q| ≤ t` and `0 < t ≤ |α|`, then
`|H P − H Q| ≤ (t·ln(|α|/t) + t)/ln 2`. -/
theorem abs_H_sub_le {P Q : α → ℝ} (hP : IsDist P) (hQ : IsDist Q) {t : ℝ} (ht : 0 < t)
    (htM : t ≤ Fintype.card α) (hPQ : ∑ a, |P a - Q a| ≤ t) :
    |H P - H Q| ≤ contErr (Fintype.card α) t := by
  set M : ℝ := (Fintype.card α : ℝ) with hM
  have hM₀ : 0 < M := lt_of_lt_of_le ht htM
  have hs : 0 < t / M := by positivity
  have hterm : ∀ a, |negMulLog (P a) - negMulLog (Q a)| ≤
      |P a - Q a| * log (M / t) + t / M := by
    intro a
    have h₁ := abs_negMulLog_sub_le (hP.nonneg a) (hQ.nonneg a) (hP.le_one a) (hQ.le_one a)
    have h₂ := negMulLog_le_lin (abs_nonneg (P a - Q a)) hs
    rw [one_div, inv_div] at h₂
    linarith
  have hsum : |∑ a, negMulLog (P a) - ∑ a, negMulLog (Q a)| ≤ t * log (M / t) + t := by
    rw [← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_sum fun a _ ↦ hterm a).trans ?_
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, ← hM, mul_div_cancel₀ _ hM₀.ne']
    have hlog : 0 ≤ log (M / t) := log_nonneg (by rw [le_div_iff₀ ht]; linarith)
    nlinarith
  unfold H contErr
  rw [← sub_div, abs_div, abs_of_pos log_two_pos']
  exact div_le_div_of_nonneg_right hsum log_two_pos'.le

/-- The marginals of two joint distributions are no further apart than the joints. -/
theorem sum_abs_fst_le (P Q : α × β → ℝ) :
    ∑ a, |(∑ b, P (a, b)) - ∑ b, Q (a, b)| ≤ ∑ v, |P v - Q v| := by
  rw [Fintype.sum_prod_type]
  refine Finset.sum_le_sum fun a _ ↦ ?_
  rw [← Finset.sum_sub_distrib]
  exact Finset.abs_sum_le_sum_abs _ _

theorem sum_abs_snd_le (P Q : α × β → ℝ) :
    ∑ b, |(∑ a, P (a, b)) - ∑ a, Q (a, b)| ≤ ∑ v, |P v - Q v| := by
  rw [Fintype.sum_prod_type_right]
  refine Finset.sum_le_sum fun b _ ↦ ?_
  rw [← Finset.sum_sub_distrib]
  exact Finset.abs_sum_le_sum_abs _ _

/-- The bound for mutual information: one `contErr` for each part and one for the pair. -/
noncomputable def miErr (A B t : ℝ) : ℝ := contErr A t + contErr B t + contErr (A * B) t

/-- **Mutual information moves slowly.** -/
theorem abs_mi_sub_le {P Q : α × β → ℝ} (hP : IsDist P) (hQ : IsDist Q) {t : ℝ} (ht : 0 < t)
    (htA : t ≤ Fintype.card α) (htB : t ≤ Fintype.card β) (hPQ : ∑ v, |P v - Q v| ≤ t) :
    |mi P - mi Q| ≤ miErr (Fintype.card α) (Fintype.card β) t := by
  have hA : (1 : ℝ) ≤ Fintype.card α := by
    have : 0 < Fintype.card α := by exact_mod_cast lt_of_lt_of_le ht htA
    exact_mod_cast this
  have hAB : t ≤ Fintype.card (α × β) := by
    rw [Fintype.card_prod]; push_cast; nlinarith
  have h₁ : |H (fun a ↦ ∑ b, P (a, b)) - H (fun a ↦ ∑ b, Q (a, b))| ≤ _ :=
    abs_H_sub_le (isDist_fstD hP) (isDist_fstD hQ) ht htA ((sum_abs_fst_le P Q).trans hPQ)
  have h₂ : |H (fun b ↦ ∑ a, P (a, b)) - H (fun b ↦ ∑ a, Q (a, b))| ≤ _ :=
    abs_H_sub_le (isDist_sndD hP) (isDist_sndD hQ) ht htB ((sum_abs_snd_le P Q).trans hPQ)
  have h₃ := abs_H_sub_le hP hQ ht hAB hPQ
  rw [Fintype.card_prod, Nat.cast_mul] at h₃
  unfold mi miErr
  have e : (H (fun a ↦ ∑ b, P (a, b)) + H (fun b ↦ ∑ a, P (a, b)) - H P) -
      (H (fun a ↦ ∑ b, Q (a, b)) + H (fun b ↦ ∑ a, Q (a, b)) - H Q) =
      (H (fun a ↦ ∑ b, P (a, b)) - H (fun a ↦ ∑ b, Q (a, b))) +
        (H (fun b ↦ ∑ a, P (a, b)) - H (fun b ↦ ∑ a, Q (a, b))) - (H P - H Q) := by ring
  rw [e]
  refine (abs_sub _ _).trans ?_
  refine add_le_add ((abs_add_le _ _).trans (add_le_add h₁ h₂)) ?_
  exact h₃

end CubeGod
