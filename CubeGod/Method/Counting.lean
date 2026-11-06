import CubeGod.Method.Method

/-!
# Counting moves

The cost of one 3-cycle of the twist, the number of orbits left for Stage 3, and that a layout with
`h·a·c ≤ N` exists. `Method/Explicit.lean` puts these together.
-/

open Finset Real Filter Topology

namespace CubeGod

variable {n h a c : ℕ}

/-- The cost of one 3-cycle of the twist. -/
theorem cycleLen_twist_le {N : ℝ} (hN : (h : ℝ) * (a * c) ≤ N) (ha : 0 < a) (hc : 0 < c) :
    (cycleLen h c a 1 2 : ℝ) ≤ 34 * (N ^ 2 / a) := by
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  have hc' : (1 : ℝ) ≤ c := by exact_mod_cast hc
  have hP : (2 : ℝ) * (groupPairs h).length ≤ (h : ℝ) ^ 2 := by
    have := two_length_groupPairs h
    have h' : ((2 * (groupPairs h).length + h : ℕ) : ℝ) = ((h ^ 2 : ℕ) : ℝ) := by rw [this]
    push_cast at h'
    have : (0 : ℝ) ≤ h := by positivity
    linarith
  set P : ℝ := ((groupPairs h).length : ℝ) with hPdef
  have hP₀ : 0 ≤ P := by positivity
  have hsq : ((h : ℝ) * (a * c)) ^ 2 ≤ N ^ 2 := pow_le_pow_left₀ (by positivity) hN 2
  have hf : ((c : ℝ) + 1) * ((c : ℝ) + 16) ≤ 34 * (c : ℝ) ^ 2 := by nlinarith
  unfold cycleLen
  simp only [Nat.div_one, pow_one, one_mul]
  push_cast
  have hexpr : P * ((c : ℝ) + 1) * (2 * (2 * (8 * (a : ℝ)) + c * a)) =
      (2 * P) * (a * (((c : ℝ) + 1) * ((c : ℝ) + 16))) := by ring
  rw [hexpr]
  have h₁ : (2 * P) * (a * (((c : ℝ) + 1) * ((c : ℝ) + 16))) ≤
      (h : ℝ) ^ 2 * (a * (34 * (c : ℝ) ^ 2)) :=
    mul_le_mul hP (mul_le_mul_of_nonneg_left hf ha'.le) (by positivity) (by positivity)
  have h₂ : (h : ℝ) ^ 2 * (a * (34 * (c : ℝ) ^ 2)) = 34 * (((h : ℝ) * (a * c)) ^ 2 / a) := by
    field_simp
  have h₃ : ((h : ℝ) * (a * c)) ^ 2 / a ≤ N ^ 2 / a := div_le_div_of_nonneg_right hsq ha'.le
  linarith

/-- Stage 3 has few orbits. -/
theorem stage3_le {N g β : ℝ} (hg₀ : 0 ≤ g) (hgN : g ≤ N) (hβ₀ : 0 ≤ β)
    (hh₁ : (h : ℝ) * g ≤ N) (hh₂ : N ≤ ((h : ℝ) + 1) * g) :
    N ^ 2 - (1 - β) * (((h : ℝ) ^ 2 - h) * g ^ 2) ≤ 3 * N * g + β * N ^ 2 := by
  have h₀ : (0 : ℝ) ≤ h := by positivity
  set E := ((h : ℝ) ^ 2 - h) * g ^ 2 with hE
  have hE₁ : E = ((h : ℝ) * g) ^ 2 - (h * g) * g := by rw [hE]; ring
  have hhg : 0 ≤ (h : ℝ) * g := by positivity
  have hE₂ : E ≤ N ^ 2 := by
    have : ((h : ℝ) * g) ^ 2 ≤ N ^ 2 := pow_le_pow_left₀ hhg hh₁ 2
    have : 0 ≤ ((h : ℝ) * g) * g := by positivity
    linarith
  have hE₃ : N ^ 2 - 3 * N * g ≤ E := by
    have h₁ : N - g ≤ (h : ℝ) * g := by linarith
    have h₂ : (N - g) ^ 2 ≤ ((h : ℝ) * g) ^ 2 := pow_le_pow_left₀ (by linarith) h₁ 2
    have h₃ : ((h : ℝ) * g) * g ≤ N * g := mul_le_mul_of_nonneg_right hh₁ hg₀
    nlinarith [sq_nonneg g]
  nlinarith

/-- Any polynomial is eventually below an exponential. -/
theorem eventually_poly_le (C : ℝ) (k : ℕ) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ l : ℕ in atTop, C * (l : ℝ) ^ k ≤ (2 : ℝ) ^ (η * l) := by
  set r : ℝ := 2 ^ η with hr
  have hr₁ : 1 < r := Real.one_lt_rpow (by norm_num) hη
  have hlim := tendsto_pow_const_div_const_pow_of_one_lt k hr₁
  have hC : (0 : ℝ) < 1 / (|C| + 1) := by positivity
  filter_upwards [hlim.eventually (gt_mem_nhds hC)] with l hl
  have hrpos : 0 < r ^ l := by positivity
  have hpow : (2 : ℝ) ^ (η * l) = r ^ l := by
    rw [hr, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
  rw [hpow]
  rw [div_lt_div_iff₀ hrpos (by positivity)] at hl
  have h₁ : C * (l : ℝ) ^ k ≤ (|C| + 1) * (l : ℝ) ^ k :=
    mul_le_mul_of_nonneg_right (by linarith [le_abs_self C]) (by positivity)
  nlinarith

/-- Pick the layers of a layout. -/
theorem exists_layout (hN : h * (a * c) ≤ n / 2 - 1) : Nonempty (Layout n h a c) := by
  classical
  have hcard : Fintype.card (Fin h × Fin a × Fin c) ≤ Fintype.card {d // d ∈ layerSet n} := by
    rw [Fintype.card_coe, card_layerSet]
    simpa using hN
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hcard
  refine ⟨⟨fun G v k ↦ (e (G, v, k)).1, ?_, fun G v k ↦ mem_layerSet.mp (e (G, v, k)).2⟩⟩
  intro G v k G' v' k' he
  have := e.injective (Subtype.ext he)
  simpa [Prod.ext_iff] using this

theorem tendsto_logN : Tendsto (fun n : ℕ ↦ Nat.log 2 (n / 2 - 1)) atTop atTop := by
  refine tendsto_atTop.mpr fun b ↦ ?_
  filter_upwards [eventually_ge_atTop (2 * 2 ^ b + 4)] with n hn
  have hb : 2 ^ b ≤ n / 2 - 1 := by omega
  exact Nat.le_log_of_pow_le (by norm_num) hb

instance : ∀ q, Nonempty (SideCycle q)
  | true => ⟨⟨_, pure_R _ List.mem_cons_self⟩⟩
  | false => ⟨⟨_, pure_L _ List.mem_cons_self⟩⟩

end CubeGod
