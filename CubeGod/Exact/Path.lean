import CubeGod.Exact.Cover

/-!
# The path

Fix a cycle system with setups `0` and `1`, and a number `m` of entries. A **path** is a list of
exact types `z₀, z₁, …, z_T` of `m` patterns, and for each step `t` a 3-cycle `g t` and joint types
for its two firings, each one's input type the previous one's output type, ending with every entry
solved. Its first firing moves an entry by `σ = e (g t) 1` if its bit is `1`, and its second by
`σ⁻¹`.

It is built backward from "all solved". At each stage the next step is a balanced step designed at
the current type `w/m`, of rate `ρ = min(ρ_full, κ·gap)`, and its splits are rounded down to whole
numbers. Rounding moves each joint type by at most `4C/m` in total, so the rates move by at most
`e′ = miErr C 2 (4C/m)` (`path_step`). Full steps lower the gap by `2ρ_full − e′`; once the gap is
below `ρ_full/κ`, bridge steps shrink it by a factor `1 − 1.5κ`. So the path reaches gap `2e′/κ`
in at most `⌈log C/(2ρ_full − e′)⌉ + ⌈ln(log C·κ/(2e′))/(1.5κ)⌉` steps (`exists_path`).
-/

open Finset Real

set_option linter.unusedSectionVars false

namespace CubeGod

open CycleSystem

variable {X : Type*} [Fintype X] [DecidableEq X]

/-! ### Two-point joint distributions -/

/-- The joint distribution of a firing that moves by `τ` with chance `t`: `(x, 0)` has
`(1 − t)V(x)` and `(x, 1)` has `t·V(τ x)`. -/
noncomputable def twoJoint (τ : Equiv.Perm X) (t : ℝ) (V : X → ℝ) (v : X × Fin 2) : ℝ :=
  if v.2 = 0 then (1 - t) * V v.1 else t * V (τ v.1)

/-- The bijection `(x, b) ↦ (b, x or τ x)`. -/
def twoEquiv (τ : Equiv.Perm X) : X × Fin 2 ≃ Fin 2 × X where
  toFun v := (v.2, if v.2 = 0 then v.1 else τ v.1)
  invFun w := (if w.1 = 0 then w.2 else τ⁻¹ w.2, w.1)
  left_inv v := by
    obtain ⟨x, b⟩ := v
    rcases fin2_cases b with rfl | rfl <;> simp
  right_inv w := by
    obtain ⟨b, y⟩ := w
    rcases fin2_cases b with rfl | rfl <;> simp

/-- The chances `1 − t` and `t`. -/
noncomputable def bitD (t : ℝ) (b : Fin 2) : ℝ := if b = 0 then 1 - t else t

theorem isDist_bitD {t : ℝ} (h₀ : 0 ≤ t) (h₁ : t ≤ 1) : IsDist (bitD t) := by
  refine ⟨fun b ↦ ?_, ?_⟩
  · unfold bitD; split_ifs <;> linarith
  · simp [bitD, Fin.sum_univ_two]

omit [Fintype X] [DecidableEq X] in
theorem twoJoint_eq (τ : Equiv.Perm X) (t : ℝ) (V : X → ℝ) :
    twoJoint τ t V = (fun w : Fin 2 × X ↦ bitD t w.1 * V w.2) ∘ twoEquiv τ := by
  funext v
  obtain ⟨x, b⟩ := v
  rcases fin2_cases b with rfl | rfl <;> simp [twoJoint, twoEquiv, bitD]

omit [DecidableEq X] in
theorem isDist_twoJoint (τ : Equiv.Perm X) {t : ℝ} (h₀ : 0 ≤ t) (h₁ : t ≤ 1) {V : X → ℝ}
    (hV : IsDist V) : IsDist (twoJoint τ t V) := by
  rw [twoJoint_eq]
  exact ((isDist_bitD h₀ h₁).prod hV).comp_equiv _

omit [DecidableEq X] in
/-- The information of a two-point firing is the entropy it adds. -/
theorem mi_twoJoint (τ : Equiv.Perm X) {t : ℝ} (h₀ : 0 ≤ t) (h₁ : t ≤ 1) {V : X → ℝ}
    (hV : IsDist V) :
    mi (twoJoint τ t V) = H (fun x ↦ (1 - t) * V x + t * V (τ x)) - H V := by
  have hfst : (fun x ↦ ∑ b, twoJoint τ t V (x, b)) = fun x ↦ (1 - t) * V x + t * V (τ x) := by
    funext x; simp [twoJoint, Fin.sum_univ_two]
  have hsnd : (fun b ↦ ∑ x, twoJoint τ t V (x, b)) = bitD t := by
    funext b
    rcases fin2_cases b with rfl | rfl
    · simp [twoJoint, bitD, ← Finset.mul_sum, hV.sum]
    · simp only [twoJoint, bitD, Fin.one_eq_zero_iff, OfNat.ofNat_ne_one, ite_false,
        ← Finset.mul_sum]
      rw [Equiv.sum_comp τ V, hV.sum, mul_one]
  unfold mi
  rw [hfst, hsnd, twoJoint_eq, H_comp_equiv, H_prod (isDist_bitD h₀ h₁) hV]
  ring

omit [DecidableEq X] in
theorem sum_abs_twoJoint_le (τ : Equiv.Perm X) {t : ℝ} (h₀ : 0 ≤ t) (h₁ : t ≤ 1) (V V' : X → ℝ) :
    ∑ v, |twoJoint τ t V v - twoJoint τ t V' v| = ∑ x, |V x - V' x| := by
  rw [Fintype.sum_prod_type]
  simp only [twoJoint, Fin.sum_univ_two, Fin.one_eq_zero_iff, OfNat.ofNat_ne_one, ite_false,
    ite_true, ← mul_sub, abs_mul, abs_of_nonneg h₀, abs_of_nonneg (by linarith : 0 ≤ 1 - t),
    Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [Equiv.sum_comp τ (fun x ↦ |V x - V' x|)]
  ring

/-! ### Rounded splits -/

/-- Split the type `w` for a firing that moves by `τ`: an entry ending at `y` comes from `τ⁻¹ y` with
bit `1` for `⌊t·w y⌋` of them, and from `y` with bit `0` for the rest. -/
noncomputable def splitT (τ : Equiv.Perm X) (t : ℝ) (w : X → ℕ) (v : X × Fin 2) : ℕ :=
  if v.2 = 0 then w v.1 - ⌊t * w v.1⌋₊ else ⌊t * w (τ v.1)⌋₊

theorem floor_le_self {t : ℝ} (h₁ : t ≤ 1) (k : ℕ) : ⌊t * k⌋₊ ≤ k := by
  have : t * k ≤ k := by nlinarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  exact Nat.floor_le_of_le this

omit [Fintype X] [DecidableEq X] in
theorem outT_splitT (τ : Equiv.Perm X) {t : ℝ} (h₁ : t ≤ 1) (w : X → ℕ) :
    outT τ (splitT τ t w) = w := by
  funext y
  simp only [outT, splitT, Fin.one_eq_zero_iff, OfNat.ofNat_ne_one, ite_false, ite_true]
  have e : τ (τ⁻¹ y) = y := by simp
  rw [e]
  have := floor_le_self h₁ (w y)
  omega

omit [DecidableEq X] in
theorem sum_splitT (τ : Equiv.Perm X) {t : ℝ} (h₁ : t ≤ 1) (w : X → ℕ) :
    ∑ v, splitT τ t w v = ∑ x, w x := by
  rw [← sum_outT τ, outT_splitT τ h₁]

omit [DecidableEq X] in
/-- Rounding the split moves it by at most `2C/m` in total. -/
theorem sum_abs_splitT_le (τ : Equiv.Perm X) {t : ℝ} (h₀ : 0 ≤ t) (h₁ : t ≤ 1) {m : ℕ}
    (hm : 0 < m) (w : X → ℕ) :
    ∑ v, |distOf m (splitT τ t w) v - twoJoint τ t (distOf m w) v| ≤
      2 * Fintype.card X / m := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hfl : ∀ k : ℕ, |(⌊t * k⌋₊ : ℝ) - t * k| ≤ 1 := by
    intro k
    have h₁ := Nat.floor_le (show 0 ≤ t * k by positivity)
    have h₂ := Nat.lt_floor_add_one (t * k)
    rw [abs_le]; constructor <;> linarith
  have hterm : ∀ v, |distOf m (splitT τ t w) v - twoJoint τ t (distOf m w) v| ≤ 1 / m := by
    rintro ⟨x, b⟩
    rcases fin2_cases b with rfl | rfl
    · simp only [distOf, splitT, twoJoint, ite_true]
      rw [Nat.cast_sub (floor_le_self h₁ _)]
      have e : ((w x : ℝ) - ⌊t * w x⌋₊) / m - (1 - t) * (w x / m) = -((⌊t * w x⌋₊ - t * w x) / m) := by
        field_simp; ring
      rw [e, abs_neg, abs_div, abs_of_pos hm']
      exact div_le_div_of_nonneg_right (hfl _) hm'.le
    · simp only [distOf, splitT, twoJoint, Fin.one_eq_zero_iff, OfNat.ofNat_ne_one, ite_false]
      have e : (⌊t * w (τ x)⌋₊ : ℝ) / m - t * (w (τ x) / m) = (⌊t * w (τ x)⌋₊ - t * w (τ x)) / m := by
        field_simp
      rw [e, abs_div, abs_of_pos hm']
      exact div_le_div_of_nonneg_right (hfl _) hm'.le
  calc ∑ v, |distOf m (splitT τ t w) v - twoJoint τ t (distOf m w) v|
      ≤ ∑ _v : X × Fin 2, (1 : ℝ) / m := Finset.sum_le_sum fun v _ ↦ hterm v
    _ = 2 * Fintype.card X / m := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul]
        push_cast; ring

omit [Fintype X] [DecidableEq X] in
theorem distOf_inT (m : ℕ) (n : X × Fin 2 → ℕ) :
    distOf m (inT n) = fun x ↦ ∑ b, distOf m n (x, b) := by
  funext x
  simp [distOf, inT, Fin.sum_univ_two, add_div]

/-! ### One step back -/

variable {G : Type*}

/-- The rate error of rounding, for `m` entries. -/
noncomputable def roundErr (X : Type*) [Fintype X] (m : ℕ) : ℝ :=
  miErr (Fintype.card X) 2 (4 * Fintype.card X / m)

/-- The type with every entry solved. -/
def solvedT (x₀ : X) (m : ℕ) (x : X) : ℕ := if x = x₀ then m else 0

namespace CycleSystem

variable (Γ : CycleSystem X (Fin 2) G)

/-- One step of a path: the 3-cycle `g` and joint types `n₁`, `n₂` take the type `z` to `w`, and
each firing carries at most `r`. -/
structure PathStep (m : ℕ) (r : ℝ) (z w : X → ℕ) (g : G) (n₁ n₂ : X × Fin 2 → ℕ) : Prop where
  in₁ : inT n₁ = z
  mid : inT n₂ = outT (Γ.e g 1) n₁
  out₂ : outT (Γ.e g 1)⁻¹ n₂ = w
  info₁ : info m n₁ ≤ r
  info₂ : info m n₂ ≤ r

end CycleSystem

omit [DecidableEq X] in
theorem card_pos_X [Nonempty X] : (0 : ℝ) < Fintype.card X := by exact_mod_cast Fintype.card_pos

namespace CycleSystem

variable (Γ : CycleSystem X (Fin 2) G)

omit [DecidableEq X] in
/-- A step lemma for setups `0` and `1`: a balanced two-point step around the setup `1`, of every
rate up to `min(ρ_far, κ·gap)`. -/
theorem exists_step_rate [Nonempty X] {γ : ℝ} (hγ : 0 < γ) (hspec : Γ.SpectralGap γ) {W : X → ℝ}
    (hW : IsDist W) (hG : 0 < gap W) {ρ : ℝ} (hρ₀ : 0 ≤ ρ) (hρf : ρ ≤ farRate γ X)
    (hρκ : ρ ≤ γ / 150 * gap W) :
    ∃ g, ∃ α β : ℝ, 0 ≤ α ∧ α ≤ 1 ∧ 0 ≤ β ∧ β ≤ 1 ∧
      gainA (Γ.e g 1) W α β = ρ ∧ gainB (Γ.e g 1) W β = ρ := by
  have hrates : ∃ ρm, ρ ≤ ρm ∧ Γ.RatesUpTo W ρm := by
    by_cases hnear : gap W ≤ etaNear X
    · have hne : W ≠ uniform X := by
        intro h; rw [h, gap_uniform] at hG; exact lt_irrefl _ hG
      obtain ⟨ρm, -, -, h₁, h₂⟩ := Γ.step_near hγ hspec hW hnear hne
      exact ⟨ρm, hρκ.trans h₁, h₂⟩
    · push Not at hnear
      obtain ⟨ρm, h₁, -, h₂⟩ := Γ.step_far hγ hspec hW hnear
      exact ⟨ρm, hρf.trans h₁, h₂⟩
  obtain ⟨ρm, hle, hr⟩ := hrates
  obtain ⟨g, a, α, β, h₁, h₂, h₃, h₄, hA, hB⟩ := hr ρ hρ₀ hle
  rcases fin2_cases a with rfl | rfl
  · -- The empty setup moves nothing, so the rate is `0`.
    have hE : Γ.e g 0 = 1 := Γ.e_zero g
    have hY : mixY (Γ.e g 0) β W = W := by funext x; simp [mixY, hE]; ring
    have : ρ = 0 := by rw [← hB, gainB, hY, sub_self]
    refine ⟨g, 0, 0, le_rfl, by norm_num, le_rfl, by norm_num, ?_, ?_⟩
    · rw [gainA_zero, this]
    · rw [gainB_zero, this]
  · exact ⟨g, α, β, h₁, h₂, h₃, h₄, hA, hB⟩

omit [DecidableEq X] in
/-- **One step back.** At a type `w` of `m` entries whose gap is positive, for each rate
`ρ ≤ min(ρ_far, κ·gap)` there is a step from some type `z` to `w` whose firings carry at most
`ρ + e′`, and the gap of `z` is at most `gap(w) − 2ρ + e′`. -/
theorem path_step [Nonempty X] {γ : ℝ} (hγ : 0 < γ) (hspec : Γ.SpectralGap γ) {m : ℕ}
    (hm : 0 < m) (hm4 : 4 * Fintype.card X ≤ m) {w : X → ℕ} (hw : ∑ x, w x = m)
    (hG : 0 < gap (distOf m w)) {ρ : ℝ} (hρ₀ : 0 ≤ ρ) (hρf : ρ ≤ farRate γ X)
    (hρκ : ρ ≤ γ / 150 * gap (distOf m w)) :
    ∃ z g n₁ n₂, Γ.PathStep m (ρ + roundErr X m) z w g n₁ n₂ ∧ ∑ x, z x = m ∧
      gap (distOf m z) ≤ gap (distOf m w) - 2 * ρ + roundErr X m := by
  set C := Fintype.card X with hC
  have hC₀ : (0 : ℝ) < C := card_pos_X
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  set Wd := distOf m w with hWd
  have hWdist : IsDist Wd := isDist_distOf hm hw
  obtain ⟨g, α, β, hα₀, hα₁, hβ₀, hβ₁, hA, hB⟩ := Γ.exists_step_rate hγ hspec hWdist hG hρ₀ hρf hρκ
  set σ := Γ.e g 1 with hσ
  -- The second firing, then the first.
  set n₂ := splitT σ⁻¹ β w with hn₂
  set u := inT n₂ with hu
  set n₁ := splitT σ α u with hn₁
  set z := inT n₁ with hz
  have hsum₂ : ∑ v, n₂ v = m := by rw [hn₂, sum_splitT _ hβ₁, hw]
  have hsumu : ∑ x, u x = m := by rw [hu, sum_inT, hsum₂]
  have hsum₁ : ∑ v, n₁ v = m := by rw [hn₁, sum_splitT _ hα₁, hsumu]
  have hsumz : ∑ x, z x = m := by rw [hz, sum_inT, hsum₁]
  -- The ideal joint distributions.
  set Q₂ := twoJoint σ⁻¹ β Wd with hQ₂
  set Y := mixY σ β Wd with hY
  set Q₁ := twoJoint σ α Y with hQ₁
  have hYdist : IsDist Y := isDist_mixY hWdist hβ₀ hβ₁
  have hQ₂d : IsDist Q₂ := isDist_twoJoint _ hβ₀ hβ₁ hWdist
  have hQ₁d : IsDist Q₁ := isDist_twoJoint _ hα₀ hα₁ hYdist
  have hmiQ₂ : mi Q₂ = ρ := by
    rw [hQ₂, mi_twoJoint _ hβ₀ hβ₁ hWdist, ← hB]; rfl
  have hmiQ₁ : mi Q₁ = ρ := by
    rw [hQ₁, mi_twoJoint _ hα₀ hα₁ hYdist, ← hA]; rfl
  -- Distances.
  have hd₂ : ∑ v, |distOf m n₂ v - Q₂ v| ≤ 2 * C / m := sum_abs_splitT_le _ hβ₀ hβ₁ hm w
  have hfst₂ : (fun x ↦ ∑ b, Q₂ (x, b)) = Y := by
    funext x; simp [hQ₂, hY, twoJoint, mixY, Fin.sum_univ_two]
  have hdu : ∑ x, |distOf m u x - Y x| ≤ 2 * C / m := by
    rw [hu, distOf_inT, ← hfst₂]
    exact (sum_abs_fst_le _ _).trans hd₂
  have hd₁ : ∑ v, |distOf m n₁ v - Q₁ v| ≤ 4 * C / m := by
    have h₁ : ∑ v, |distOf m n₁ v - twoJoint σ α (distOf m u) v| ≤ 2 * C / m :=
      sum_abs_splitT_le _ hα₀ hα₁ hm u
    have h₂ := sum_abs_twoJoint_le σ hα₀ hα₁ (distOf m u) Y
    calc ∑ v, |distOf m n₁ v - Q₁ v| ≤ ∑ v, (|distOf m n₁ v - twoJoint σ α (distOf m u) v| +
          |twoJoint σ α (distOf m u) v - Q₁ v|) :=
          Finset.sum_le_sum fun v _ ↦ abs_sub_le _ _ _
      _ ≤ 4 * C / m := by
          rw [Finset.sum_add_distrib, h₂]
          have : 4 * (C : ℝ) / m = 2 * C / m + 2 * C / m := by ring
          linarith
  -- Rates.
  set t := 4 * (C : ℝ) / m with ht
  have ht₀ : 0 < t := by positivity
  have ht₁ : t ≤ 1 := by
    rw [ht, div_le_iff₀ hm']
    have : (4 * C : ℝ) ≤ m := by exact_mod_cast hm4
    linarith
  have ht₂ : t ≤ 2 := by linarith
  have htC : t ≤ C := by
    have : (1 : ℝ) ≤ C := by exact_mod_cast Fintype.card_pos
    linarith
  have hcard2 : ((Fintype.card (Fin 2) : ℕ) : ℝ) = 2 := by simp
  have hre : roundErr X m = miErr C 2 t := rfl
  have hn₂d := isDist_distOf hm hsum₂
  have hn₁d := isDist_distOf hm hsum₁
  have hi₂ : info m n₂ ≤ ρ + roundErr X m := by
    have := abs_mi_sub_le hn₂d hQ₂d ht₀ htC (by rw [hcard2]; exact ht₂)
      (hd₂.trans (by rw [ht]; apply div_le_div_of_nonneg_right _ hm'.le; linarith))
    rw [hcard2, hmiQ₂] at this
    have := (abs_le.mp this).2
    unfold info
    rw [hre]
    linarith
  have hi₁ : info m n₁ ≤ ρ + roundErr X m := by
    have := abs_mi_sub_le hn₁d hQ₁d ht₀ htC (by rw [hcard2]; exact ht₂) hd₁
    rw [hcard2, hmiQ₁] at this
    have := (abs_le.mp this).2
    unfold info
    rw [hre]
    linarith
  -- The gap.
  have hzZ : ∑ x, |distOf m z x - mixZ σ α Y x| ≤ t := by
    have hfst₁ : (fun x ↦ ∑ b, Q₁ (x, b)) = mixZ σ α Y := by
      funext x; simp [hQ₁, twoJoint, mixZ, Fin.sum_univ_two]
    rw [hz, distOf_inT, ← hfst₁]
    exact (sum_abs_fst_le _ _).trans hd₁
  have hZd : IsDist (mixZ σ α Y) := by
    have := isDist_twoJoint σ hα₀ hα₁ hYdist
    have h := isDist_fstD this
    have e : fstD (twoJoint σ α Y) = mixZ σ α Y := by
      funext x; simp [fstD, twoJoint, mixZ, Fin.sum_univ_two]
    rwa [e] at h
  have hzd := isDist_distOf hm hsumz
  have hH := abs_H_sub_le hzd hZd ht₀ htC hzZ
  have hgapZ : gap (mixZ σ α Y) = gap Wd - 2 * ρ := by
    have e₁ : H (mixZ σ α Y) = H Y + ρ := by rw [← hA]; unfold gainA; rw [hY]; ring
    have e₂ : H Y = H Wd + ρ := by rw [← hB]; unfold gainB; rw [hY]; ring
    unfold gap; rw [e₁, e₂]; ring
  have hcont : contErr C t ≤ roundErr X m := by
    unfold roundErr miErr
    have h₁ : 0 ≤ contErr 2 t := by
      unfold contErr
      have : 0 ≤ log (2 / t) := log_nonneg (by rw [le_div_iff₀ ht₀]; linarith)
      have := log_two_pos'
      positivity
    have h₂ : 0 ≤ contErr (C * 2) t := by
      unfold contErr
      have : 0 ≤ log (C * 2 / t) := log_nonneg (by rw [le_div_iff₀ ht₀]; nlinarith)
      have := log_two_pos'
      positivity
    rw [← ht]; linarith
  refine ⟨z, g, n₁, n₂, ⟨rfl, ?_, ?_, hi₁, hi₂⟩, hsumz, ?_⟩
  · rw [hn₁, outT_splitT _ hα₁]
  · rw [hn₂, outT_splitT _ hβ₁]
  · have := (abs_le.mp hH).1
    unfold gap at hgapZ ⊢
    linarith

omit [DecidableEq X] in
theorem PathStep.mono {m : ℕ} {r r' : ℝ} {z w : X → ℕ} {g : G} {n₁ n₂ : X × Fin 2 → ℕ}
    (h : Γ.PathStep m r z w g n₁ n₂) (hr : r ≤ r') : Γ.PathStep m r' z w g n₁ n₂ :=
  ⟨h.in₁, h.mid, h.out₂, h.info₁.trans hr, h.info₂.trans hr⟩

/-- A path of `T` steps through the types `z 0, …, z T`. -/
def IsPath (m : ℕ) (r : ℝ) (T : ℕ) (g : ℕ → G) (z : ℕ → X → ℕ) (n₁ n₂ : ℕ → X × Fin 2 → ℕ) :
    Prop :=
  ∀ t < T, Γ.PathStep m r (z t) (z (t + 1)) (g t) (n₁ t) (n₂ t)

end CycleSystem

/-! ### Counting the steps -/

/-- The potential: full steps take `⌈G/a⌉` down by one, bridge steps `⌈ln(G/θ)/b⌉`. -/
noncomputable def pot (a b θ G : ℝ) : ℕ := ⌈G / a⌉₊ + ⌈log (G / θ) / b⌉₊

theorem ceil_sub_one_add_one_le {x : ℝ} (hx : 0 < x) : ⌈x - 1⌉₊ + 1 ≤ ⌈x⌉₊ := by
  rcases le_total 1 x with h | h
  · have := Nat.ceil_add_one (show 0 ≤ x - 1 by linarith)
    rw [sub_add_cancel] at this
    omega
  · have h₁ : ⌈x - 1⌉₊ = 0 := Nat.ceil_eq_zero.mpr (by linarith)
    have h₂ : 0 < ⌈x⌉₊ := Nat.ceil_pos.mpr hx
    omega

theorem pot_step {a b θ G G' : ℝ} (ha : 0 < a) (hb : 0 < b) (hb1 : b < 1) (hθ : 0 < θ)
    (hG : θ < G) (hG' : 0 ≤ G') (h : G' ≤ G - a ∨ G' ≤ (1 - b) * G) :
    pot a b θ G' + 1 ≤ pot a b θ G := by
  have hG₀ : 0 < G := hθ.trans hG
  have hle : G' ≤ G := by rcases h with h | h <;> nlinarith
  have hA : ⌈G' / a⌉₊ ≤ ⌈G / a⌉₊ := Nat.ceil_mono (div_le_div_of_nonneg_right hle ha.le)
  have hL : ⌈log (G' / θ) / b⌉₊ ≤ ⌈log (G / θ) / b⌉₊ := by
    rcases hG'.eq_or_lt with h0 | hpos
    · rw [← h0, zero_div, log_zero, zero_div, Nat.ceil_zero]; exact Nat.zero_le _
    · exact Nat.ceil_mono (div_le_div_of_nonneg_right
        (log_le_log (by positivity) (div_le_div_of_nonneg_right hle hθ.le)) hb.le)
  have hlogpos : 0 < log (G / θ) / b :=
    div_pos (log_pos (by rw [lt_div_iff₀ hθ]; linarith)) hb
  unfold pot
  rcases h with h | h
  · have hGa : 1 ≤ G / a := by rw [le_div_iff₀ ha]; linarith
    have h₁ : ⌈G' / a⌉₊ ≤ ⌈G / a - 1⌉₊ := Nat.ceil_mono (by
      rw [div_le_iff₀ ha, sub_mul, div_mul_cancel₀ _ ha.ne']; linarith)
    have h₂ := ceil_sub_one_add_one_le (show 0 < G / a by linarith)
    omega
  · have h₁ : ⌈log (G' / θ) / b⌉₊ ≤ ⌈log (G / θ) / b - 1⌉₊ := by
      rcases hG'.eq_or_lt with h0 | hpos
      · rw [← h0, zero_div, log_zero, zero_div, Nat.ceil_zero]; exact Nat.zero_le _
      · refine Nat.ceil_mono ?_
        have hl : log (G' / θ) ≤ log (G / θ) - b := by
          have h₂ : log (G' / θ) ≤ log ((1 - b) * G / θ) :=
            log_le_log (by positivity) (div_le_div_of_nonneg_right h hθ.le)
          have h₃ : log ((1 - b) * G / θ) = log (1 - b) + log (G / θ) := by
            rw [mul_div_assoc, log_mul (by linarith) (by positivity)]
          have h₄ : log (1 - b) ≤ -b := by
            have := log_le_sub_one_of_pos (show 0 < 1 - b by linarith); linarith
          linarith
        rw [div_le_iff₀ hb, sub_mul, div_mul_cancel₀ _ hb.ne']
        linarith
    have h₂ := ceil_sub_one_add_one_le hlogpos
    omega

theorem roundErr_pos (X : Type*) [Fintype X] [Nonempty X] {m : ℕ} (hm : 0 < m)
    (hm4 : 4 * Fintype.card X ≤ m) : 0 < roundErr X m := by
  have hC : (1 : ℝ) ≤ Fintype.card X := by exact_mod_cast Fintype.card_pos
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  set t := 4 * (Fintype.card X : ℝ) / m with ht
  have ht₀ : 0 < t := by positivity
  have ht₁ : t ≤ 1 := by
    rw [ht, div_le_iff₀ hm']
    have : (4 * Fintype.card X : ℝ) ≤ m := by exact_mod_cast hm4
    linarith
  have hl := log_two_pos'
  have pos : ∀ M : ℝ, 1 ≤ M → 0 < contErr M t := by
    intro M hM
    unfold contErr
    have : 0 ≤ log (M / t) := log_nonneg (by rw [le_div_iff₀ ht₀]; linarith)
    have : 0 < t * log (M / t) + t := by nlinarith
    positivity
  unfold roundErr miErr
  rw [← ht]
  have := pos _ hC
  have := pos 2 (by norm_num)
  have := pos (Fintype.card X * 2) (by nlinarith)
  linarith

omit [Fintype X] in
theorem distOf_solvedT {m : ℕ} (hm : 0 < m) (x₀ : X) :
    distOf m (solvedT x₀ m) = point x₀ := by
  have : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  funext x
  simp only [distOf, solvedT, point]
  split_ifs <;> simp [this]

theorem gap_point (x₀ : X) : gap (point x₀) = logb 2 (Fintype.card X) := by
  rw [gap, H_point, sub_zero]

/-! ### The path -/

namespace CycleSystem

variable (Γ : CycleSystem X (Fin 2) G)

/-- **The path.** For a spectral gap `γ ≤ 1`, `κ = γ/150`, and a full rate `ρ_full ≤ ρ_far` with
`e′ ≤ ρ_full/4`, there is a path from a type of gap at most `2e′/κ` to "all solved", whose firings
each carry at most `ρ_full + e′`, of at most `pot(2ρ_full − e′, 1.5κ, 2e′/κ, log C)` steps. -/
theorem exists_path [Nonempty X] [Nonempty G] {γ : ℝ} (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hspec : Γ.SpectralGap γ)
    {m : ℕ} (hm : 0 < m) (hm4 : 4 * Fintype.card X ≤ m) {ρf : ℝ} (hρf₀ : 0 < ρf)
    (hρf : ρf ≤ farRate γ X) (he : roundErr X m ≤ ρf / 4) :
    ∃ T g z n₁ n₂, Γ.IsPath m (ρf + roundErr X m) T g z n₁ n₂ ∧ (∀ t ≤ T, ∑ x, z t x = m) ∧
      z T = solvedT Γ.solved m ∧ gap (distOf m (z 0)) ≤ 2 * roundErr X m / (γ / 150) ∧
      T ≤ pot (2 * ρf - roundErr X m) (3 / 2 * (γ / 150)) (2 * roundErr X m / (γ / 150))
        (logb 2 (Fintype.card X)) := by
  set e := roundErr X m with he'
  set κ := γ / 150 with hκ
  set a := 2 * ρf - e with ha
  set b := 3 / 2 * κ with hb
  set θ := 2 * e / κ with hθ
  have he₀ : 0 < e := roundErr_pos X hm hm4
  have hκ₀ : 0 < κ := by positivity
  have ha₀ : 0 < a := by linarith
  have hb₀ : 0 < b := by positivity
  have hb₁ : b < 1 := by rw [hb, hκ]; linarith
  have hθ₀ : 0 < θ := by positivity
  -- Induction on the potential.
  have key : ∀ N : ℕ, ∀ w : X → ℕ, ∑ x, w x = m → pot a b θ (gap (distOf m w)) ≤ N →
      ∃ T ≤ N, ∃ g z n₁ n₂, Γ.IsPath m (ρf + e) T g z n₁ n₂ ∧ (∀ t ≤ T, ∑ x, z t x = m) ∧
        z T = w ∧ gap (distOf m (z 0)) ≤ θ := by
    intro N
    induction N with
    | zero =>
      intro w hw hN
      by_cases hG : gap (distOf m w) ≤ θ
      · exact ⟨0, le_rfl, fun _ ↦ Classical.arbitrary G, fun _ ↦ w, fun _ ↦ 0, fun _ ↦ 0,
          fun t ht ↦ absurd ht (Nat.not_lt_zero _), fun _ _ ↦ hw, rfl, hG⟩
      · exfalso
        push Not at hG
        have : 0 < log (gap (distOf m w) / θ) / b :=
          div_pos (log_pos (by rw [lt_div_iff₀ hθ₀]; linarith)) hb₀
        have := Nat.ceil_pos.mpr this
        unfold pot at hN
        omega
    | succ N ih =>
      intro w hw hN
      by_cases hG : gap (distOf m w) ≤ θ
      · exact ⟨0, Nat.zero_le _, fun _ ↦ Classical.arbitrary G, fun _ ↦ w, fun _ ↦ 0, fun _ ↦ 0,
          fun t ht ↦ absurd ht (Nat.not_lt_zero _), fun _ _ ↦ hw, rfl, hG⟩
      push Not at hG
      set Gw := gap (distOf m w) with hGw
      have hG₀ : 0 < Gw := hθ₀.trans hG
      set ρ := min ρf (κ * Gw) with hρ
      have hρ₀ : 0 ≤ ρ := le_min hρf₀.le (by positivity)
      obtain ⟨z', g₀, m₁, m₂, hstep, hz', hgap⟩ := Γ.path_step hγ hspec hm hm4 hw hG₀ hρ₀
        ((min_le_left _ _).trans hρf) (by rw [hρ, ← hκ]; exact min_le_right _ _)
      have hG' : 0 ≤ gap (distOf m z') := gap_nonneg (isDist_distOf hm hz')
      have hdec : gap (distOf m z') ≤ Gw - a ∨ gap (distOf m z') ≤ (1 - b) * Gw := by
        rcases le_total ρf (κ * Gw) with h | h
        · left; rw [hρ, min_eq_left h] at hgap; rw [ha]; linarith
        · right
          rw [hρ, min_eq_right h] at hgap
          have : e < κ * Gw / 2 := by
            rw [hθ, div_lt_iff₀ hκ₀] at hG; linarith
          rw [hb]; nlinarith
      have hpot := pot_step ha₀ hb₀ hb₁ hθ₀ hG hG' hdec
      obtain ⟨T, hT, g, z, n₁, n₂, hpath, hsum, hzT, hz0⟩ := ih z' hz' (by omega)
      refine ⟨T + 1, by omega, fun t ↦ if t < T then g t else g₀,
        fun t ↦ if t ≤ T then z t else w, fun t ↦ if t < T then n₁ t else m₁,
        fun t ↦ if t < T then n₂ t else m₂, ?_, ?_, ?_, ?_⟩
      · intro t ht
        by_cases htT : t < T
        · simp only [htT, ite_true, show t ≤ T by omega, show t + 1 ≤ T by omega]
          exact hpath t htT
        · have : t = T := by omega
          subst this
          simp only [lt_irrefl, ite_false, le_refl, ite_true, show ¬ (t + 1 ≤ t) by omega]
          rw [hzT]
          exact hstep.mono _ (by linarith [min_le_left ρf (κ * Gw)])
      · intro t ht
        by_cases htT : t ≤ T
        · simp only [htT, ite_true]; exact hsum t htT
        · simp only [htT, ite_false]; exact hw
      · simp
      · simp only [Nat.zero_le, ite_true]; exact hz0
  have hsol : ∑ x, solvedT Γ.solved m x = m := by simp [solvedT]
  obtain ⟨T, hT, g, z, n₁, n₂, h₁, h₂, h₃, h₄⟩ := key _ (solvedT Γ.solved m) hsol le_rfl
  refine ⟨T, g, z, n₁, n₂, h₁, h₂, h₃, h₄, ?_⟩
  rw [distOf_solvedT hm, gap_point] at hT
  exact hT

end CycleSystem

end CubeGod
