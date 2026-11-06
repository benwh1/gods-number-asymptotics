import CubeGod.Exact.Types

/-!
# Blind mixing, and firings that carry little

* `mi_le_of_near`: a joint distribution `P(x, b) = ½q(x)(1 + μ(x, b))` with every `|μ| ≤ μ̄ ≤ ½`
  has mutual information at most `71·μ̄²`, since information is at most `χ²/ln 2`.
* `mixAll`: a round of firings that each send half of every pattern's entries through a
  permutation, ignoring the list, acting on functions on the patterns. It keeps sums, does not
  increase the largest value, and, if only constants are fixed by all its permutations, shrinks
  the squared length of every function adding up to `0` by a fixed factor `lam < 1`
  (`exists_mix_contraction`).
-/

open Finset Real Filter Topology

set_option linter.unusedSectionVars false

namespace CubeGod

variable {X : Type*} [Fintype X] [DecidableEq X]

/-! ### Almost blind firings -/

omit [DecidableEq X] in
/-- **A firing close to `½q(x)` everywhere carries little.** -/
theorem mi_le_of_near {P : X × Fin 2 → ℝ} (hP : IsDist P) {q : X → ℝ} (hq : IsDist q)
    (hqpos : ∀ x, 0 < q x) {μ : ℝ} (hμ₀ : 0 ≤ μ) (hμ : μ ≤ 1 / 2)
    (hnear : ∀ v, |P v - q v.1 / 2| ≤ μ * (q v.1 / 2)) : mi P ≤ 71 * μ ^ 2 := by
  set Px : X → ℝ := fun x ↦ ∑ b, P (x, b) with hPx
  set Pb : Fin 2 → ℝ := fun b ↦ ∑ x, P (x, b) with hPb
  -- The parts are close to `q` and to `½`.
  have hx : ∀ x, |Px x - q x| ≤ μ * q x := by
    intro x
    have e : Px x - q x = (P (x, 0) - q x / 2) + (P (x, 1) - q x / 2) := by
      simp [hPx, Fin.sum_univ_two]; ring
    rw [e]
    have h₀ := hnear (x, 0)
    have h₁ := hnear (x, 1)
    calc |(P (x, 0) - q x / 2) + (P (x, 1) - q x / 2)| ≤ |P (x, 0) - q x / 2| + |P (x, 1) - q x / 2| :=
          abs_add_le _ _
      _ ≤ μ * (q x / 2) + μ * (q x / 2) := add_le_add h₀ h₁
      _ = μ * q x := by ring
  have hb : ∀ b, |Pb b - 1 / 2| ≤ μ * (1 / 2) := by
    intro b
    have e : Pb b - 1 / 2 = ∑ x, (P (x, b) - q x / 2) := by
      simp only [hPb, Finset.sum_sub_distrib, ← Finset.sum_div, hq.sum]
    rw [e]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ x, |P (x, b) - q x / 2| ≤ ∑ x, μ * (q x / 2) := Finset.sum_le_sum fun x _ ↦ hnear (x, b)
      _ = μ * (1 / 2) := by rw [← Finset.mul_sum, ← Finset.sum_div, hq.sum]
  -- Lower bounds.
  have hPpos : ∀ v, q v.1 / 4 ≤ P v := by
    intro v
    have := (abs_le.mp (hnear v)).1
    have := hqpos v.1
    nlinarith
  have hRlow : ∀ v : X × Fin 2, q v.1 / 8 ≤ Px v.1 * Pb v.2 := by
    intro v
    have h₁ := (abs_le.mp (hx v.1)).1
    have h₂ := (abs_le.mp (hb v.2)).1
    have hq₀ := hqpos v.1
    have : q v.1 / 2 ≤ Px v.1 := by nlinarith
    have : 1 / 4 ≤ Pb v.2 := by nlinarith
    nlinarith
  have hdiff : ∀ v : X × Fin 2, |P v - Px v.1 * Pb v.2| ≤ 7 / 2 * μ * (q v.1 / 2) := by
    intro v
    set a := P v - q v.1 / 2
    set c := Px v.1 - q v.1
    set d := Pb v.2 - 1 / 2
    have e : P v - Px v.1 * Pb v.2 = a - c / 2 - q v.1 * d - c * d := by
      simp only [a, c, d]; ring
    rw [e]
    have ha := hnear v
    have hc := hx v.1
    have hd := hb v.2
    have hq₀ := (hqpos v.1).le
    have hcd : |c * d| ≤ μ * q v.1 * (μ * (1 / 2)) := by
      rw [abs_mul]; exact mul_le_mul hc hd (abs_nonneg _) (by positivity)
    calc |a - c / 2 - q v.1 * d - c * d| ≤ |a| + |c| / 2 + q v.1 * |d| + |c * d| := by
          have h₁ := abs_sub (a - c / 2 - q v.1 * d) (c * d)
          have h₂ := abs_sub (a - c / 2) (q v.1 * d)
          have h₃ := abs_sub a (c / 2)
          rw [abs_mul, abs_of_nonneg hq₀] at h₂
          rw [abs_div, abs_two] at h₃
          linarith
      _ ≤ μ * (q v.1 / 2) + μ * q v.1 / 2 + q v.1 * (μ * (1 / 2)) + μ * q v.1 * (μ * (1 / 2)) := by
          gcongr
      _ ≤ 7 / 2 * μ * (q v.1 / 2) := by
          have := mul_le_mul_of_nonneg_left hμ (mul_nonneg hμ₀ hq₀)
          nlinarith
  -- Information is at most `χ²/ln 2`.
  have hterm : ∀ v : X × Fin 2, P v * (log (P v) - log (Px v.1) - log (Pb v.2)) ≤
      (P v - Px v.1 * Pb v.2) ^ 2 / (Px v.1 * Pb v.2) + (P v - Px v.1 * Pb v.2) := by
    intro v
    have hp : 0 < P v := lt_of_lt_of_le (by linarith [hqpos v.1]) (hPpos v)
    have hR : 0 < Px v.1 * Pb v.2 := lt_of_lt_of_le (by linarith [hqpos v.1]) (hRlow v)
    have hlog := Real.log_le_sub_one_of_pos (div_pos hp hR)
    have hpx : 0 < Px v.1 := by
      have := (abs_le.mp (hx v.1)).1; have := hqpos v.1; nlinarith
    have hpb : 0 < Pb v.2 := by have := (abs_le.mp (hb v.2)).1; nlinarith
    rw [Real.log_div hp.ne' hR.ne', Real.log_mul hpx.ne' hpb.ne'] at hlog
    have := mul_le_mul_of_nonneg_left hlog hp.le
    have e : P v * (P v / (Px v.1 * Pb v.2) - 1) =
        (P v - Px v.1 * Pb v.2) ^ 2 / (Px v.1 * Pb v.2) + (P v - Px v.1 * Pb v.2) := by
      field_simp; ring
    linarith
  have hchi : ∀ v : X × Fin 2, (P v - Px v.1 * Pb v.2) ^ 2 / (Px v.1 * Pb v.2) ≤
      49 / 2 * μ ^ 2 * q v.1 := by
    intro v
    have hR := hRlow v
    have hq₀ := hqpos v.1
    rw [div_le_iff₀ (by linarith)]
    have h₁ : (P v - Px v.1 * Pb v.2) ^ 2 ≤ (7 / 2 * μ * (q v.1 / 2)) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hdiff v) 2
    have h₂ : 49 / 2 * μ ^ 2 * q v.1 * (q v.1 / 8) ≤ 49 / 2 * μ ^ 2 * q v.1 * (Px v.1 * Pb v.2) :=
      mul_le_mul_of_nonneg_left hR (by positivity)
    nlinarith
  -- Add up.
  have hsumR : ∑ v : X × Fin 2, Px v.1 * Pb v.2 = 1 := by
    rw [Fintype.sum_prod_type]
    simp only [← Finset.mul_sum]
    have : ∑ b, Pb b = 1 := by
      rw [← hP.sum, Fintype.sum_prod_type_right]
    simp only [this, mul_one]
    rw [← hP.sum, Fintype.sum_prod_type]
  have hsum := Finset.sum_le_sum fun v (_ : v ∈ (univ : Finset (X × Fin 2))) ↦ hterm v
  have hsum₂ : ∑ v : X × Fin 2, (P v - Px v.1 * Pb v.2) = 0 := by
    rw [Finset.sum_sub_distrib, hP.sum, hsumR, sub_self]
  rw [Finset.sum_add_distrib, hsum₂, add_zero] at hsum
  have hsum₃ : ∑ v : X × Fin 2, (P v - Px v.1 * Pb v.2) ^ 2 / (Px v.1 * Pb v.2) ≤ 49 * μ ^ 2 := by
    refine (Finset.sum_le_sum fun v _ ↦ hchi v).trans ?_
    rw [Fintype.sum_prod_type]
    simp only [Fin.sum_univ_two]
    have : ∑ x, (49 / 2 * μ ^ 2 * q x + 49 / 2 * μ ^ 2 * q x) = 49 * μ ^ 2 * ∑ x, q x := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun x _ ↦ by ring
    rw [this, hq.sum, mul_one]
  -- The left side is `mi P · ln 2`.
  have hmi : mi P * log 2 = ∑ v : X × Fin 2, P v * (log (P v) - log (Px v.1) - log (Pb v.2)) := by
    show mi P * log 2 = ∑ v : X × Fin 2, P v * (log (P v) - log (fstD P v.1) - log (sndD P v.2))
    simp only [mul_sub, Finset.sum_sub_distrib]
    rw [sum_log_self, sum_log_fst, sum_log_snd]
    unfold mi H
    have := log_two_pos'
    field_simp
    simp only [fstD, sndD]
    ring
  have hl := log_two_pos'
  have hl' : (49 : ℝ) / 71 ≤ log 2 := by have := Real.log_two_gt_d9; linarith
  have : mi P * log 2 ≤ 49 * μ ^ 2 := by linarith
  by_contra hc
  push Not at hc
  have h₁ : 71 * μ ^ 2 * log 2 < mi P * log 2 := mul_lt_mul_of_pos_right hc hl
  nlinarith [sq_nonneg μ]

/-! ### Blind mixing -/

/-- Send half of each value through `σ`: the new value at `y` is the average of `v y` and
`v (σ⁻¹ y)`. -/
noncomputable def avgP (σ : Equiv.Perm X) (v : X → ℝ) : X → ℝ := fun y ↦ (v y + v (σ⁻¹ y)) / 2

/-- A round of averages, in order. -/
noncomputable def mixAll : List (Equiv.Perm X) → (X → ℝ) → (X → ℝ)
  | [], v => v
  | σ :: L, v => mixAll L (avgP σ v)

omit [DecidableEq X] in
theorem sum_avgP (σ : Equiv.Perm X) (v : X → ℝ) : ∑ y, avgP σ v y = ∑ y, v y := by
  unfold avgP
  rw [← Finset.sum_div, Finset.sum_add_distrib, Equiv.sum_comp σ⁻¹ v]
  ring

omit [DecidableEq X] in
theorem sum_mixAll (L : List (Equiv.Perm X)) (v : X → ℝ) : ∑ y, mixAll L v y = ∑ y, v y := by
  induction L generalizing v with
  | nil => rfl
  | cons σ L ih => rw [mixAll, ih, sum_avgP]

omit [Fintype X] [DecidableEq X] in
theorem mixAll_smul (L : List (Equiv.Perm X)) (c : ℝ) (v : X → ℝ) :
    mixAll L (c • v) = c • mixAll L v := by
  induction L generalizing v with
  | nil => rfl
  | cons σ L ih =>
    simp only [mixAll]
    rw [← ih]
    congr 1
    funext y
    simp [avgP]; ring

omit [Fintype X] [DecidableEq X] in
theorem mixAll_const (L : List (Equiv.Perm X)) (c : ℝ) : mixAll L (fun _ ↦ c) = fun _ ↦ c := by
  induction L with
  | nil => rfl
  | cons σ L ih =>
    simp only [mixAll]
    have : avgP σ (fun _ ↦ c) = fun _ ↦ c := by funext y; simp [avgP]
    rw [this, ih]

omit [Fintype X] [DecidableEq X] in
theorem continuous_mixAll (L : List (Equiv.Perm X)) : Continuous (mixAll L) := by
  induction L with
  | nil => exact continuous_id
  | cons σ L ih =>
    have : Continuous (avgP σ) := by unfold avgP; fun_prop
    exact ih.comp this

omit [DecidableEq X] in
/-- An average loses `¼‖v − v∘σ⁻¹‖²` of the squared length. -/
theorem sq_avgP (σ : Equiv.Perm X) (v : X → ℝ) :
    ∑ y, avgP σ v y ^ 2 = ∑ y, v y ^ 2 - (∑ y, (v y - v (σ⁻¹ y)) ^ 2) / 4 := by
  have hperm : ∑ y, v (σ⁻¹ y) ^ 2 = ∑ y, v y ^ 2 := Equiv.sum_comp σ⁻¹ (fun y ↦ v y ^ 2)
  have e : ∀ y, avgP σ v y ^ 2 = (v y ^ 2 + v (σ⁻¹ y) ^ 2) / 2 - (v y - v (σ⁻¹ y)) ^ 2 / 4 := by
    intro y; unfold avgP; ring
  simp only [e, Finset.sum_sub_distrib, ← Finset.sum_div, Finset.sum_add_distrib, hperm]
  ring

omit [DecidableEq X] in
theorem sq_mixAll_le (L : List (Equiv.Perm X)) (v : X → ℝ) :
    ∑ y, mixAll L v y ^ 2 ≤ ∑ y, v y ^ 2 := by
  induction L generalizing v with
  | nil => exact le_rfl
  | cons σ L ih =>
    refine (ih _).trans ?_
    rw [sq_avgP]
    have : 0 ≤ ∑ y, (v y - v (σ⁻¹ y)) ^ 2 := Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
    linarith

omit [DecidableEq X] in
/-- If a round keeps the squared length, every one of its permutations fixes `v`. -/
theorem fix_of_sq_mixAll (L : List (Equiv.Perm X)) (v : X → ℝ)
    (h : ∑ y, mixAll L v y ^ 2 = ∑ y, v y ^ 2) : ∀ σ ∈ L, ∀ y, v (σ⁻¹ y) = v y := by
  induction L generalizing v with
  | nil => simp
  | cons σ L ih =>
    have h₁ := sq_mixAll_le L (avgP σ v)
    have h₂ := sq_avgP σ v
    have h₀ : 0 ≤ ∑ y, (v y - v (σ⁻¹ y)) ^ 2 := Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
    simp only [mixAll] at h
    have hz : ∑ y, (v y - v (σ⁻¹ y)) ^ 2 = 0 := by linarith
    have hfix : ∀ y, v (σ⁻¹ y) = v y := by
      intro y
      have := (Finset.sum_eq_zero_iff_of_nonneg fun _ _ ↦ sq_nonneg _).mp hz y (Finset.mem_univ y)
      have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
      linarith
    have hv : avgP σ v = v := by funext y; unfold avgP; rw [hfix y]; ring
    rw [hv] at h
    intro τ hτ
    rcases List.mem_cons.mp hτ with rfl | hτ
    · exact hfix
    · exact ih v h τ hτ

omit [DecidableEq X] in
/-- **Blind mixing.** If only constants are fixed by all the permutations of a round, the round
shrinks the squared length of every function adding up to `0` by a fixed factor `lam < 1`. -/
theorem exists_mix_contraction (L : List (Equiv.Perm X))
    (hconst : ∀ v : X → ℝ, (∀ σ ∈ L, ∀ y, v (σ⁻¹ y) = v y) → ∀ x y, v x = v y) :
    ∃ lam : ℝ, 0 ≤ lam ∧ lam < 1 ∧ ∀ v : X → ℝ, ∑ y, v y = 0 →
      ∑ y, mixAll L v y ^ 2 ≤ lam * ∑ y, v y ^ 2 := by
  set K : Set (X → ℝ) := {v | ∑ x, v x = 0} ∩ {v | ∑ x, v x ^ 2 = 1} with hKdef
  have hK : IsCompact K := by
    have hbox : IsCompact (Set.pi Set.univ fun _ : X ↦ Set.Icc (-1 : ℝ) 1) :=
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
  set f : (X → ℝ) → ℝ := fun v ↦ ∑ y, mixAll L v y ^ 2 with hf
  have hfc : Continuous f := by
    have := continuous_mixAll L
    simp only [hf]
    fun_prop
  -- Below `1` on `K`.
  have hlt : ∀ v ∈ K, f v < 1 := by
    intro v hv
    have hle := sq_mixAll_le L v
    rw [hv.2] at hle
    refine lt_of_le_of_ne hle fun heq ↦ ?_
    have hfix := fix_of_sq_mixAll L v (by rw [hv.2]; exact heq)
    have hc := hconst v hfix
    obtain ⟨x₀⟩ : Nonempty X := by
      by_contra hne
      rw [not_nonempty_iff] at hne
      have := hv.2
      simp at this
    have hall : ∀ x, v x = 0 := by
      have hs := hv.1
      simp only [Set.mem_ofPred_eq] at hs
      have : ∑ x, v x = Fintype.card X * v x₀ := by
        rw [Finset.sum_congr rfl fun x _ ↦ hc x x₀]; simp
      have hcard : (0 : ℝ) < Fintype.card X := by exact_mod_cast Fintype.card_pos_iff.mpr ⟨x₀⟩
      intro x
      rw [hc x x₀]
      rw [hs] at this
      nlinarith
    have := hv.2
    simp only [Set.mem_ofPred_eq, hall] at this
    norm_num at this
  by_cases hKe : K.Nonempty
  · obtain ⟨v₀, hv₀, hmax⟩ := hK.exists_isMaxOn hKe hfc.continuousOn
    refine ⟨max (f v₀) 0, le_max_right _ _, max_lt (hlt v₀ hv₀) one_pos, fun v hv ↦ ?_⟩
    set s := ∑ y, v y ^ 2 with hs
    rcases (Finset.sum_nonneg fun y (_ : y ∈ univ) ↦ sq_nonneg (v y)).eq_or_lt with h0 | hpos
    · -- `v = 0`.
      have hv0 : ∀ y, v y = 0 := by
        intro y
        have := (Finset.sum_eq_zero_iff_of_nonneg fun _ _ ↦ sq_nonneg _).mp h0.symm y
          (Finset.mem_univ y)
        exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
      have h₁ : ∑ y, mixAll L v y ^ 2 = 0 := by
        rw [show v = fun _ ↦ 0 from funext hv0, mixAll_const]; simp
      rw [h₁]
      exact mul_nonneg (le_max_right _ _) (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)
    · set r := Real.sqrt s with hr
      have hr₀ : 0 < r := Real.sqrt_pos.mpr hpos
      have hrr : r ^ 2 = s := Real.sq_sqrt hpos.le
      set u : X → ℝ := r⁻¹ • v with hu
      have huK : u ∈ K := by
        refine ⟨?_, ?_⟩
        · simp only [Set.mem_ofPred_eq, hu, Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum, hv,
            mul_zero]
        · simp only [Set.mem_ofPred_eq, hu, Pi.smul_apply, smul_eq_mul, mul_pow, ← Finset.mul_sum,
            ← hs, inv_pow, hrr]
          exact inv_mul_cancel₀ hpos.ne'
      have hfu := hmax huK
      simp only [Set.mem_ofPred_eq] at hfu
      have hvu : v = r • u := by
        rw [hu, smul_smul, mul_inv_cancel₀ hr₀.ne', one_smul]
      have : f v = r ^ 2 * f u := by
        simp only [hf, hvu, mixAll_smul, Pi.smul_apply, smul_eq_mul, mul_pow, ← Finset.mul_sum]
      calc ∑ y, mixAll L v y ^ 2 = f v := rfl
        _ = r ^ 2 * f u := this
        _ ≤ r ^ 2 * max (f v₀) 0 := mul_le_mul_of_nonneg_left (hfu.trans (le_max_left _ _))
            (sq_nonneg r)
        _ = max (f v₀) 0 * s := by rw [hrr]; ring
  · refine ⟨0, le_rfl, one_pos, fun v hv ↦ ?_⟩
    -- Every function adding up to `0` is `0`.
    rcases (Finset.sum_nonneg fun y (_ : y ∈ univ) ↦ sq_nonneg (v y)).eq_or_lt with h0 | hpos
    · have hv0 : ∀ y, v y = 0 := by
        intro y
        have := (Finset.sum_eq_zero_iff_of_nonneg fun _ _ ↦ sq_nonneg _).mp h0.symm y
          (Finset.mem_univ y)
        exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
      have : v = fun _ ↦ 0 := funext hv0
      rw [this, mixAll_const]
      simp
    · exfalso
      apply hKe
      refine ⟨(Real.sqrt (∑ y, v y ^ 2))⁻¹ • v, ?_, ?_⟩
      · simp only [Set.mem_ofPred_eq, Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum, hv, mul_zero]
      · simp only [Set.mem_ofPred_eq, Pi.smul_apply, smul_eq_mul, mul_pow, ← Finset.mul_sum,
          inv_pow, Real.sq_sqrt hpos.le]
        exact inv_mul_cancel₀ hpos.ne'

omit [DecidableEq X] in
/-- `r` rounds shrink the squared length by `lam^r`. -/
theorem sq_mixAll_iter {L : List (Equiv.Perm X)} {lam : ℝ} (hlam : 0 ≤ lam)
    (h : ∀ v : X → ℝ, ∑ y, v y = 0 → ∑ y, mixAll L v y ^ 2 ≤ lam * ∑ y, v y ^ 2) (r : ℕ)
    (v : X → ℝ) (hv : ∑ y, v y = 0) :
    ∑ y, (mixAll L)^[r] v y ^ 2 ≤ lam ^ r * ∑ y, v y ^ 2 := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Function.iterate_succ_apply']
    have hs : ∑ y, (mixAll L)^[r] v y = 0 := by
      clear ih
      induction r with
      | zero => exact hv
      | succ r ihr => rw [Function.iterate_succ_apply', sum_mixAll, ihr]
    refine (h _ hs).trans ?_
    rw [pow_succ]
    nlinarith [mul_le_mul_of_nonneg_left ih hlam]

end CubeGod
