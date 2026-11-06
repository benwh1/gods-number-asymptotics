import CubeGod.Exact.Merge

/-!
# The merge carries little

`exists_merge`: there are constants `λ < 1` and `L₀`, depending only on the cycle system, such
that `r₀` blind rounds and `L₀` correcting rounds take every type `n₀` within `ε·m/C` of uniform to
every type `z` within `ε*·m/C` of uniform, exactly, with every firing carrying at most
`71·max((2C/m)², μ̄²)` bits. Here `μ̄` is `mergeMu`, built from the deviation `mergeDev` left after the
blind rounds.
-/

open Finset Real

set_option linter.unusedSectionVars false

namespace CubeGod

variable {X : Type*} [Fintype X] [DecidableEq X]

omit [Fintype X] [DecidableEq X] in
theorem inT_toNat {J : X × Fin 2 → ℤ} (h : ∀ v, 0 ≤ J v) :
    inT (fun v ↦ (J v).toNat) = fun x ↦ (inZ J x).toNat := by
  funext x
  unfold inT inZ
  rw [Int.toNat_add (h _) (h _)]

omit [Fintype X] [DecidableEq X] in
theorem outT_toNat {J : X × Fin 2 → ℤ} (h : ∀ v, 0 ≤ J v) (σ : Equiv.Perm X) :
    outT σ (fun v ↦ (J v).toNat) = fun x ↦ (outZ σ J x).toNat := by
  funext x
  unfold outT outZ
  rw [Int.toNat_add (h _) (h _)]

/-- The deviation from uniform left after `r₀` blind rounds, plus rounding over `F` firings. -/
noncomputable def mergeDev (C : ℕ) (lam ε : ℝ) (r₀ F m : ℕ) : ℝ :=
  Real.sqrt (lam ^ r₀ * C) * (ε * m / C) + F / 2

/-- The largest relative deviation of a correcting firing from half of uniform. -/
noncomputable def mergeMu (C m : ℕ) (Dc εs : ℝ) : ℝ :=
  (C + C * Dc + 2 * C * εs * m + 2 * (C : ℝ) ^ 2 * Dc) / m

omit [DecidableEq X] in
theorem abs_le_sqrt_sum_sq (v : X → ℝ) (y : X) : |v y| ≤ Real.sqrt (∑ x, v x ^ 2) := by
  rw [← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt (Finset.single_le_sum (f := fun x ↦ v x ^ 2) (fun _ _ ↦ sq_nonneg _)
    (Finset.mem_univ y))

variable {G : Type*} [Fintype G] [DecidableEq G]

namespace CycleSystem

variable (Γ : CycleSystem X (Fin 2) G)

omit [Fintype X] [DecidableEq X] [DecidableEq G] in
theorem mergeP_round [Nonempty G] (k j : ℕ) (hj : j < roundLen G) :
    Γ.mergeP (k * roundLen G + j) = (Γ.roundList)[j]'(by simp [roundList, hj]) := by
  rw [add_comm, Γ.mergeP_periodic]
  simp [roundList]

omit [Fintype X] [DecidableEq X] [DecidableEq G] in
theorem opR_iter [Nonempty G] (k : ℕ) (v : X → ℝ) :
    opR Γ.mergeP 0 (k * roundLen G) v = (mixAll Γ.roundList)^[k] v := by
  induction k with
  | zero => simp [opR]
  | succ k ih =>
    rw [show (k + 1) * roundLen G = k * roundLen G + roundLen G by ring, opR_add, zero_add, ih,
      Function.iterate_succ_apply']
    have hlen : (Γ.roundList).length = roundLen G := by simp [roundList]
    have := opR_mixAll Γ.mergeP Γ.roundList (k * roundLen G)
      (fun j hj ↦ Γ.mergeP_round k j (hlen ▸ hj)) ((mixAll Γ.roundList)^[k] v)
    rwa [hlen] at this

omit [Fintype X] [DecidableEq X] [DecidableEq G] in
theorem mergeP_even [Nonempty G] (t : ℕ) : Γ.mergeP (2 * t) = Γ.e (mergeG t) 1 := by
  unfold mergeP; rw [ite_eq_left (by omega), show 2 * t / 2 = t by omega]

omit [Fintype X] [DecidableEq X] [DecidableEq G] in
theorem mergeP_odd [Nonempty G] (t : ℕ) : Γ.mergeP (2 * t + 1) = (Γ.e (mergeG t) 1)⁻¹ := by
  unfold mergeP; rw [ite_eq_right (by omega), show (2 * t + 1) / 2 = t by omega]

omit [DecidableEq G] in
/-- **The merge.** -/
theorem exists_merge [Nonempty G] [Nonempty X] :
    ∃ lam : ℝ, ∃ L₀ : ℕ, 0 ≤ lam ∧ lam < 1 ∧ ∀ (m r₀ : ℕ) (ε εs : ℝ), 0 < m →
      4 * Fintype.card X ≤ m → 0 ≤ ε → 0 ≤ εs →
      ε * m / Fintype.card X + ((r₀ + L₀) * roundLen G : ℕ) / 2 ≤ m / (2 * Fintype.card X) →
      mergeMu (Fintype.card X) m (mergeDev (Fintype.card X) lam ε r₀ ((r₀ + L₀) * roundLen G) m)
        εs ≤ 1 / 2 →
      ∀ n₀ z : X → ℕ, ∑ x, n₀ x = m → ∑ x, z x = m →
      (∀ x, |(n₀ x : ℝ) - m / Fintype.card X| ≤ ε * m / Fintype.card X) →
      (∀ x, |(z x : ℝ) - m / Fintype.card X| ≤ εs * m / Fintype.card X) →
      ∃ U N₁ N₂, Γ.IsPath m (71 * max ((2 * (Fintype.card X : ℝ) / m) ^ 2)
          (mergeMu (Fintype.card X) m
            (mergeDev (Fintype.card X) lam ε r₀ ((r₀ + L₀) * roundLen G) m) εs ^ 2))
          ((r₀ + L₀) * (allG G).length) mergeG U N₁ N₂ ∧
        U 0 = n₀ ∧ U ((r₀ + L₀) * (allG G).length) = z ∧
        ∀ t ≤ (r₀ + L₀) * (allG G).length, ∑ x, U t x = m := by
  classical
  -- The constants.
  have hconst : ∀ v : X → ℝ, (∀ σ ∈ Γ.roundList, ∀ y, v (σ⁻¹ y) = v y) → ∀ x y, v x = v y := by
    intro v hv
    refine Γ.const_of_invariant fun g a x ↦ ?_
    rcases fin2_cases a with rfl | rfl
    · rw [Γ.e_zero]; rfl
    · obtain ⟨i, hi, hgi⟩ := List.getElem_of_mem (mem_allG g)
      have hmem : Γ.e g 1 ∈ Γ.roundList := by
        rw [roundList, List.mem_ofFn]
        refine ⟨⟨2 * i, by unfold roundLen; omega⟩, ?_⟩
        have hg : mergeG (G := G) i = g := by simp [mergeG, Nat.mod_eq_of_lt hi, hgi]
        simp only
        rw [Γ.mergeP_even, hg]
      have := hv _ hmem (Γ.e g 1 x)
      simp at this
      exact this.symm
  obtain ⟨lam, hlam₀, hlam₁, hlam⟩ := exists_mix_contraction Γ.roundList hconst
  obtain ⟨L₀, hL₀⟩ := Γ.exists_applyL_bound
  refine ⟨lam, L₀, hlam₀, hlam₁, fun m r₀ ε εs hm hm4 hε hεs hpos hμ n₀ z hn₀ hz hn₀d hzd ↦ ?_⟩
  set C := Fintype.card X with hC
  have hC₀ : (0 : ℝ) < C := card_pos_X
  have hC₁ : (1 : ℝ) ≤ C := by exact_mod_cast Fintype.card_pos
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  set len := roundLen G with hlen
  set ng := (allG G).length with hng
  have hlen2 : len = 2 * ng := rfl
  set F := (r₀ + L₀) * len with hF
  set f₀ := r₀ * len with hf₀
  set ps := Γ.mergeP with hps
  set Dc := mergeDev C lam ε r₀ F m with hDc
  set μ := mergeMu C m Dc εs with hμdef
  set x₀ : X := Classical.arbitrary X
  -- The routes.
  have hroute : ∀ y, ∃ β : ℕ → Fin 2, walkPos ps β f₀ x₀ (L₀ * len) = y := by
    intro y
    obtain ⟨l, hl, hly⟩ := hL₀ x₀ y
    obtain ⟨β, hβ⟩ := Γ.reach_word l L₀ hl r₀ x₀
    exact ⟨β, by rw [hβ, hly]⟩
  choose β hβ using hroute
  set c : X → ℤ := fun y ↦ (z y : ℤ) - blindU ps n₀ F y with hc
  have hcsum : ∑ y, c y = 0 := by
    simp only [hc, Finset.sum_sub_distrib]
    have h₁ : ∑ y, (z y : ℤ) = m := by exact_mod_cast hz
    have h₂ : ∑ y, (blindU ps n₀ F y : ℤ) = m := by exact_mod_cast (sum_blindU ps n₀ F).trans hn₀
    rw [h₁, h₂, sub_self]
  set J := mJ ps f₀ x₀ β c n₀ with hJ
  set U := mU ps f₀ x₀ β c n₀ with hU
  -- Deviations of the blind flow.
  set d₀ : X → ℝ := fun x ↦ (n₀ x : ℝ) - m / C with hd₀
  have hd₀b : ∀ x, |d₀ x| ≤ ε * m / C := hn₀d
  have hd₀s : ∑ x, d₀ x = 0 := by
    simp only [hd₀, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have : ((∑ x, n₀ x : ℕ) : ℝ) = m := by rw [hn₀]
    push_cast at this
    rw [this, ← hC]; field_simp; ring
  have hdev : ∀ f y, |(blindU ps n₀ f y : ℝ) - m / C| ≤ |opR ps 0 f d₀ y| + f / 2 := by
    intro f y
    have := blindU_dev ps n₀ (m / C) f y
    have h := abs_sub_abs_le_abs_sub ((blindU ps n₀ f y : ℝ) - m / C) (opR ps 0 f d₀ y)
    linarith
  have hblind : ∀ f ≤ F, ∀ y, |(blindU ps n₀ f y : ℝ) - m / C| ≤ ε * m / C + F / 2 := by
    intro f hf y
    have h₁ := hdev f y
    have h₂ := abs_opR_le ps 0 hd₀b f y
    have : (f : ℝ) ≤ F := by exact_mod_cast hf
    linarith
  have hcorr : ∀ f, f₀ ≤ f → f ≤ F → ∀ y, |(blindU ps n₀ f y : ℝ) - m / C| ≤ Dc := by
    intro f hf hfF y
    have h₁ := hdev f y
    have hsplit : opR ps 0 f d₀ = opR ps f₀ (f - f₀) (opR ps 0 f₀ d₀) := by
      funext x
      have := opR_add ps 0 f₀ (f - f₀) d₀
      rw [zero_add, Nat.add_sub_cancel' hf] at this
      rw [this]
    have hit : opR ps 0 f₀ d₀ = (mixAll Γ.roundList)^[r₀] d₀ := Γ.opR_iter r₀ d₀
    have hsq := sq_mixAll_iter hlam₀ hlam r₀ d₀ hd₀s
    have hsum : ∑ x, d₀ x ^ 2 ≤ C * (ε * m / C) ^ 2 := by
      calc ∑ x, d₀ x ^ 2 ≤ ∑ _x : X, (ε * m / C) ^ 2 := Finset.sum_le_sum fun x _ ↦ by
            rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hd₀b x) 2
        _ = C * (ε * m / C) ^ 2 := by simp [hC]
    have hbound : ∀ x, |opR ps 0 f₀ d₀ x| ≤ Real.sqrt (lam ^ r₀ * C) * (ε * m / C) := by
      intro x
      rw [hit]
      refine (abs_le_sqrt_sum_sq _ x).trans ?_
      have h₂ : lam ^ r₀ * ∑ x, d₀ x ^ 2 ≤ (Real.sqrt (lam ^ r₀ * C) * (ε * m / C)) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (by positivity)]
        have := mul_le_mul_of_nonneg_left hsum (pow_nonneg hlam₀ r₀)
        linarith
      calc Real.sqrt (∑ x, (mixAll Γ.roundList)^[r₀] d₀ x ^ 2) ≤
            Real.sqrt ((Real.sqrt (lam ^ r₀ * C) * (ε * m / C)) ^ 2) :=
            Real.sqrt_le_sqrt (hsq.trans h₂)
        _ = Real.sqrt (lam ^ r₀ * C) * (ε * m / C) := Real.sqrt_sq (by positivity)
    have h₃ := abs_opR_le ps f₀ hbound (f - f₀) y
    rw [hsplit] at h₁
    have : (f : ℝ) ≤ F := by exact_mod_cast hfF
    rw [hDc, mergeDev]
    linarith
  -- The surplus.
  have hS : ∑ y, |(c y : ℝ)| ≤ εs * m + C * Dc := by
    have hcy : ∀ y, |(c y : ℝ)| ≤ εs * m / C + Dc := by
      intro y
      have e : (c y : ℝ) = ((z y : ℝ) - m / C) - ((blindU ps n₀ F y : ℝ) - m / C) := by
        simp [hc]
      rw [e]
      refine (abs_sub _ _).trans (add_le_add (hzd y) (hcorr F (by rw [hf₀, hF]; nlinarith) le_rfl y))
    calc ∑ y, |(c y : ℝ)| ≤ ∑ _y : X, (εs * m / C + Dc) := Finset.sum_le_sum fun y _ ↦ hcy y
      _ = εs * m + C * Dc := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← hC]; field_simp
  -- Every joint type is close to half its input.
  have hJcorr : ∀ f, f₀ ≤ f → f < F → ∀ v,
      |(J f v : ℝ) - m / (2 * C)| ≤ μ * (m / (2 * C)) := by
    intro f hf hfF v
    have hb := half_bounds (blindU ps n₀ f v.1)
    have hdv := hcorr f hf hfF.le v.1
    have hcj : |(corrJ ps f₀ x₀ β c (f - f₀) v : ℝ)| ≤ ∑ y, |(c y : ℝ)| := by
      exact_mod_cast abs_corrJ_le ps f₀ x₀ β c (f - f₀) v
    have hJv : (J f v : ℝ) = (blindJ (blindU ps n₀ f) v : ℝ) + corrJ ps f₀ x₀ β c (f - f₀) v := by
      simp only [hJ, mJ, ite_eq_left hf]; push_cast; ring
    have hbl : |(blindJ (blindU ps n₀ f) v : ℝ) - (blindU ps n₀ f v.1 : ℝ) / 2| ≤ 1 / 2 := by
      unfold blindJ
      rcases fin2_cases v.2 with h | h <;> simp only [h, ite_true, Fin.one_eq_zero_iff,
        OfNat.ofNat_ne_one, ite_false] <;> rw [abs_le] <;> constructor <;> linarith [hb.1, hb.2.1,
        hb.2.2.1, hb.2.2.2]
    have key : |(J f v : ℝ) - m / (2 * C)| ≤ 1 / 2 + Dc / 2 + (εs * m + C * Dc) := by
      rw [hJv]
      have e : (blindJ (blindU ps n₀ f) v : ℝ) + corrJ ps f₀ x₀ β c (f - f₀) v - m / (2 * C) =
          ((blindJ (blindU ps n₀ f) v : ℝ) - (blindU ps n₀ f v.1 : ℝ) / 2) +
            ((blindU ps n₀ f v.1 : ℝ) - m / C) / 2 + corrJ ps f₀ x₀ β c (f - f₀) v := by
        field_simp; ring
      rw [e]
      have t₁ := abs_add_le (((blindJ (blindU ps n₀ f) v : ℝ) - (blindU ps n₀ f v.1 : ℝ) / 2) +
        ((blindU ps n₀ f v.1 : ℝ) - m / C) / 2) (corrJ ps f₀ x₀ β c (f - f₀) v : ℝ)
      have t₂ := abs_add_le ((blindJ (blindU ps n₀ f) v : ℝ) - (blindU ps n₀ f v.1 : ℝ) / 2)
        (((blindU ps n₀ f v.1 : ℝ) - m / C) / 2)
      have t₃ : |((blindU ps n₀ f v.1 : ℝ) - m / C) / 2| ≤ Dc / 2 := by
        rw [abs_div, abs_two]; linarith
      linarith
    refine key.trans (le_of_eq ?_)
    rw [hμdef, mergeMu]
    field_simp
    ring
  have hJnn : ∀ f < F, ∀ v, 0 ≤ J f v := by
    intro f hfF v
    by_cases hf : f₀ ≤ f
    · have h := (abs_le.mp (hJcorr f hf hfF v)).1
      have : (0 : ℝ) ≤ J f v := by
        have : μ * (m / (2 * C)) ≤ 1 / 2 * (m / (2 * C)) :=
          mul_le_mul_of_nonneg_right hμ (by positivity)
        have : (0 : ℝ) < m / (2 * C) := by positivity
        linarith
      exact_mod_cast this
    · simp only [hJ, mJ, ite_eq_right hf, add_zero]; positivity
  -- The natural-number flow.
  set N : ℕ → X × Fin 2 → ℕ := fun f v ↦ (J f v).toNat with hN
  set V : ℕ → X → ℕ := fun f x ↦ (U f x).toNat with hV
  have hinT : ∀ f < F, inT (N f) = V f := by
    intro f hf
    rw [hN, inT_toNat (hJnn f hf), hJ, inZ_mJ]
  have houtT : ∀ f < F, outT (ps f) (N f) = V (f + 1) := by
    intro f hf
    rw [hN, outT_toNat (hJnn f hf), hJ, outZ_mJ]
  have hV0 : V 0 = n₀ := by
    funext x
    simp only [hV, hU, mU]
    split_ifs with h
    · rw [Nat.zero_sub, corrU_zero]; simp [blindU]
    · simp [blindU]
  have hUF : ∀ x, U F x = (z x : ℤ) := by
    intro x
    simp only [hU, mU]
    have hfF : f₀ ≤ F := by rw [hf₀, hF]; nlinarith
    rw [ite_eq_left hfF, show F - f₀ = L₀ * len by rw [hF, hf₀]; rw [add_mul]; omega,
      corrU_end ps f₀ x₀ β c hβ hcsum]
    simp [hc]
  have hVF : V F = z := by
    funext x
    simp only [hV, hUF x, Int.toNat_natCast]
  have hVsum : ∀ f, ∑ x, (U f x) = m := by
    intro f
    rw [hU, sum_mU]; exact_mod_cast hn₀
  have hFT : F = 2 * ((r₀ + L₀) * ng) := by rw [hF, hlen2]; ring
  -- The information of each firing.
  have hNsum : ∀ f < F, ∑ v, N f v = m := by
    intro f hf
    rw [← sum_inT, hinT f hf]
    have : ∀ x, (U f x : ℤ) = (V f x : ℤ) := by
      intro x
      have h := congrFun (hinT f hf) x
      have hnn : 0 ≤ U f x := by
        rw [hU, ← inZ_mJ]; unfold inZ; linarith [hJnn f hf (x, 0), hJnn f hf (x, 1)]
      simp [hV, Int.toNat_of_nonneg hnn]
    have h := hVsum f
    have : ((∑ x, V f x : ℕ) : ℤ) = m := by
      push_cast; rw [← h]; exact Finset.sum_congr rfl fun x _ ↦ (this x).symm
    exact_mod_cast this
  have hinfo : ∀ f < F, info m (N f) ≤ 71 * max ((2 * (C : ℝ) / m) ^ 2) (μ ^ 2) := by
    intro f hf
    have hP := isDist_distOf hm (hNsum f hf)
    by_cases hf₀f : f₀ ≤ f
    · -- A correcting firing: close to half of uniform.
      have hU' : IsDist (uniform X) := isDist_uniform
      have h := mi_le_of_near hP hU' (fun x ↦ by unfold uniform; positivity)
        (μ := μ) (by
          have : 0 ≤ μ := by
            rw [hμdef, mergeMu, hDc, mergeDev]
            have : 0 ≤ lam ^ r₀ * C := by positivity
            positivity
          exact this) hμ (fun v ↦ by
          have hJv := hJcorr f hf₀f hf v
          have hnn := hJnn f hf v
          have e : distOf m (N f) v = (J f v : ℝ) / m := by
            simp only [distOf, hN]
            rw [show (((J f v).toNat : ℕ) : ℝ) = (J f v : ℝ) by exact_mod_cast Int.toNat_of_nonneg hnn]
          rw [e, uniform, ← hC]
          have e₂ : (J f v : ℝ) / m - (C : ℝ)⁻¹ / 2 = ((J f v : ℝ) - m / (2 * C)) / m := by
            field_simp
          have e₃ : μ * ((C : ℝ)⁻¹ / 2) = μ * (m / (2 * C)) / m := by field_simp
          rw [e₂, e₃, abs_div, abs_of_pos hm']
          exact div_le_div_of_nonneg_right hJv hm'.le)
      unfold info
      exact h.trans (by nlinarith [le_max_right ((2 * (C : ℝ) / m) ^ 2) (μ ^ 2)])
    · -- A blind firing: close to half of its input.
      push Not at hf₀f
      set u := blindU ps n₀ f with hu
      have hNf : N f = blindJ u := by
        funext v; simp only [hN, hJ, mJ, ite_eq_right (not_le.mpr hf₀f), add_zero, Int.toNat_natCast]
        rfl
      have husum : ∑ x, u x = m := (sum_blindU ps n₀ f).trans hn₀
      have hulow : ∀ x, m / (2 * C) ≤ (u x : ℝ) := by
        intro x
        have := (abs_le.mp (hblind f hf.le x)).1
        have e : (m : ℝ) / C - m / (2 * C) = m / (2 * C) := by field_simp; ring
        linarith
      have hq := isDist_distOf hm husum
      have h := mi_le_of_near hP hq (fun x ↦ by
          unfold distOf; exact div_pos (lt_of_lt_of_le (by positivity) (hulow x)) hm')
        (μ := 2 * C / m) (by positivity) (by
          rw [div_le_iff₀ hm']; have : (4 * C : ℝ) ≤ m := by exact_mod_cast hm4
          linarith) (fun v ↦ by
          rw [hNf]
          have hb := half_bounds (u v.1)
          have hbl : |(blindJ u v : ℝ) - (u v.1 : ℝ) / 2| ≤ 1 / 2 := by
            unfold blindJ
            rcases fin2_cases v.2 with h | h <;> simp only [h, ite_true, Fin.one_eq_zero_iff,
              OfNat.ofNat_ne_one, ite_false] <;> rw [abs_le] <;> constructor <;>
              linarith [hb.1, hb.2.1, hb.2.2.1, hb.2.2.2]
          simp only [distOf]
          have e : (blindJ u v : ℝ) / m - (u v.1 : ℝ) / m / 2 =
              ((blindJ u v : ℝ) - (u v.1 : ℝ) / 2) / m := by field_simp
          rw [e, abs_div, abs_of_pos hm']
          have hlow := hulow v.1
          rw [div_le_iff₀ hm']
          have : 2 * (C : ℝ) / m * ((u v.1 : ℝ) / m / 2) * m = C * u v.1 / m := by field_simp
          rw [this, le_div_iff₀ hm']
          have : (m : ℝ) / (2 * C) * C = m / 2 := by field_simp
          nlinarith)
      unfold info
      exact h.trans (by nlinarith [le_max_left ((2 * (C : ℝ) / m) ^ 2) (μ ^ 2)])
  -- The steps.
  refine ⟨fun t ↦ V (2 * t), fun t ↦ N (2 * t), fun t ↦ N (2 * t + 1), fun t ht ↦ ?_, ?_, ?_, ?_⟩
  · have h₁ : 2 * t < F := by omega
    have h₂ : 2 * t + 1 < F := by omega
    refine ⟨hinT _ h₁, ?_, ?_, hinfo _ h₁, hinfo _ h₂⟩
    · rw [hinT _ h₂, ← houtT _ h₁, hps, Γ.mergeP_even]
    · show outT _ (N (2 * t + 1)) = V (2 * (t + 1))
      rw [show 2 * (t + 1) = 2 * t + 1 + 1 by ring, ← Γ.mergeP_odd, ← hps, houtT _ h₂]
  · exact hV0
  · show V (2 * ((r₀ + L₀) * ng)) = z
    rw [← hFT]; exact hVF
  · intro t _
    have h := hVsum (2 * t)
    have hnn : ∀ x, 0 ≤ U (2 * t) x := by
      intro x
      by_cases hlt : 2 * t < F
      · rw [hU, ← inZ_mJ]; unfold inZ; linarith [hJnn _ hlt (x, 0), hJnn _ hlt (x, 1)]
      · have : 2 * t = F := by omega
        rw [this, hUF x]; positivity
    have : ((∑ x, V (2 * t) x : ℕ) : ℤ) = m := by
      push_cast
      rw [← h]
      exact Finset.sum_congr rfl fun x _ ↦ by simp [hV, Int.toNat_of_nonneg (hnn x)]
    exact_mod_cast this

end CycleSystem

end CubeGod
