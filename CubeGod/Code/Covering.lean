import CubeGod.Info.Joint

/-!
# The covering lemma

`exists_cover`: if, for each target, random lists drawn independently from a fixed distribution hit
it with chance at least `p`, then about `ln(number of targets)/p` lists, drawn in advance, hit every
target. It is proved by counting: the chance that all of them miss a given target is tiny, even
after adding up over all targets. `Exact/Cover.lean` uses it for exact covering ([E3]).
-/

open Finset Real Filter Topology

set_option linter.unusedSectionVars false

namespace CubeGod

/-- Random lists cover everything. If each `t` is hit by a draw from `W` with chance at
least `q₀`, then `M` draws hit all of them, for some choice of draws, once `|T| exp(-q₀ M) < 1`. -/
theorem exists_cover {Y T : Type*} [Fintype Y] [DecidableEq Y] [Fintype T] {W : Y → ℝ}
    (hW : IsDist W) (Fit : T → Finset Y) {q₀ : ℝ} (hq : ∀ t, q₀ ≤ ∑ y ∈ Fit t, W y) (M : ℕ)
    (hM : (Fintype.card T : ℝ) * exp (-(q₀ * M)) < 1) :
    ∃ ys : Fin M → Y, ∀ t, ∃ i, ys i ∈ Fit t := by
  classical
  by_contra hall
  push Not at hall
  set q : Fin M → Y → ℝ := fun _ ↦ W with hqdef
  have hqd : ∀ i, IsDist (q i) := fun _ ↦ hW
  -- The chance that all draws miss `t`.
  have hmiss : ∀ t, ∑ ys : Fin M → Y, (if ∀ i, ys i ∉ Fit t then prodW q ys else 0) ≤
      exp (-(q₀ * M)) := by
    intro t
    have hprod : ∀ ys : Fin M → Y, (if ∀ i, ys i ∉ Fit t then prodW q ys else 0) =
        ∏ i, (if ys i ∉ Fit t then W (ys i) else 0) := by
      intro ys
      by_cases h : ∀ i, ys i ∉ Fit t
      · rw [ite_eq_left h]
        exact Finset.prod_congr rfl fun i _ ↦ by simp [h i, hqdef]
      · rw [ite_eq_right h]
        push Not at h
        obtain ⟨i, hi⟩ := h
        exact (Finset.prod_eq_zero (mem_univ i) (by simp [hi])).symm
    simp only [hprod]
    rw [sum_prod_list (fun _ y ↦ if y ∉ Fit t then W y else 0)]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    set w := ∑ y ∈ Fit t, W y with hw
    have hsplit : ∑ y, (if y ∉ Fit t then W y else 0) = 1 - w := by
      have h₁ : ∑ y, (if y ∉ Fit t then W y else 0) + ∑ y, (if y ∈ Fit t then W y else 0) = 1 := by
        rw [← Finset.sum_add_distrib, ← hW.sum]
        refine Finset.sum_congr rfl fun y _ ↦ ?_
        by_cases hy : y ∈ Fit t <;> simp [hy]
      have h₂ : ∑ y, (if y ∈ Fit t then W y else 0) = w := by
        rw [Finset.sum_ite_mem, Finset.univ_inter]
      linarith
    rw [hsplit]
    have hw₁ : 0 ≤ 1 - w := by
      rw [← hsplit]
      refine Finset.sum_nonneg fun y _ ↦ ?_
      split_ifs
      · exact le_rfl
      · exact hW.nonneg y
    calc (1 - w) ^ M ≤ exp (-w) ^ M :=
          pow_le_pow_left₀ hw₁ (Real.one_sub_le_exp_neg w) M
      _ = exp (-(w * M)) := by
          rw [← Real.exp_nat_mul]
          congr 1
          ring
      _ ≤ exp (-(q₀ * M)) := by
          apply Real.exp_le_exp.mpr
          have : q₀ * M ≤ w * M := mul_le_mul_of_nonneg_right (hq t) (by positivity)
          linarith
  -- If every choice of draws missed something, the total would be at least 1.
  have hone : (1 : ℝ) ≤ ∑ t, ∑ ys : Fin M → Y, (if ∀ i, ys i ∉ Fit t then prodW q ys else 0) := by
    rw [Finset.sum_comm, ← sum_prodW hqd]
    refine Finset.sum_le_sum fun ys _ ↦ ?_
    obtain ⟨t, ht⟩ := hall ys
    have hnn : ∀ t', 0 ≤ if ∀ i, ys i ∉ Fit t' then prodW q ys else 0 := fun t' ↦ by
      split_ifs
      · exact prodW_nonneg hqd ys
      · exact le_rfl
    calc prodW q ys = if ∀ i, ys i ∉ Fit t then prodW q ys else 0 := by rw [ite_eq_left ht]
      _ ≤ _ := Finset.single_le_sum (f := fun t' ↦
          if ∀ i, ys i ∉ Fit t' then prodW q ys else 0) (fun t' _ ↦ hnn t') (mem_univ t)
  have hsum := Finset.sum_le_sum fun t (_ : t ∈ univ) ↦ hmiss t
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum
  linarith

end CubeGod
