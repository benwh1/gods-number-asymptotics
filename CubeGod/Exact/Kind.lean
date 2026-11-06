import CubeGod.Exact.MergeBound
import CubeGod.Code.Compression

/-!
# Codebooks for a kind

Run the merge, then the path. For each firing of the path, take an exact codebook for its joint
type; for each firing of the merge, the union of the exact codebooks over all the near-uniform
types it may start from. Then every list of `m` patterns whose counts are all within `ε·m/C` of
`m/C` is solved: at every firing its type is the input type of the joint type planned for it, so
some list of the codebook gives exactly that joint type, and the list ends all solved
(`exists_books`).
-/

open Finset Real

set_option linter.unusedSectionVars false

namespace CubeGod

variable {X : Type*} [Fintype X] [DecidableEq X] {G : Type*} [Fintype G] [DecidableEq G]

/-- The distance from uniform, relative to `1/C`, at which the path starts. -/
noncomputable def epsStar (X : Type*) [Fintype X] (γ : ℝ) (m : ℕ) : ℝ :=
  Fintype.card X * (2 * Real.sqrt (2 * roundErr X m / (γ / 150)))

/-- The most a merge firing carries. -/
noncomputable def mergeRate (X : Type*) [Fintype X] (γ lam ε : ℝ) (r₀ F m : ℕ) : ℝ :=
  71 * max ((2 * (Fintype.card X : ℝ) / m) ^ 2)
    (mergeMu (Fintype.card X) m (mergeDev (Fintype.card X) lam ε r₀ F m) (epsStar X γ m) ^ 2)

/-- The number of steps of the path. -/
noncomputable def pathLen (X : Type*) [Fintype X] (γ ρf : ℝ) (m : ℕ) : ℕ :=
  pot (2 * ρf - roundErr X m) (3 / 2 * (γ / 150)) (2 * roundErr X m / (γ / 150))
    (logb 2 (Fintype.card X))

theorem coverBound_mono {m : ℝ} (hm : 0 ≤ m) (C : ℕ) {r r' : ℝ} (h : r ≤ r') (hC : 1 ≤ (C : ℝ)) :
    coverBound m C r ≤ coverBound m C r' := by
  unfold coverBound
  have h₁ : 0 ≤ (m * log C + 2) * (m + 1) ^ C := by
    have := log_nonneg hC
    positivity
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le (by norm_num)
    (mul_le_mul_of_nonneg_left h hm)) h₁

omit [Fintype X] in
theorem eq_of_typeOf {ι : Type*} [Fintype ι] {s : ι → X} {x₀ : X}
    (h : typeOf s x₀ = Fintype.card ι) (k : ι) : s k = x₀ := by
  unfold typeOf at h
  have : (univ.filter fun k ↦ s k = x₀) = univ :=
    Finset.eq_univ_of_card _ (by rw [h])
  have hk := Finset.mem_univ k
  rw [← this] at hk
  exact (Finset.mem_filter.mp hk).2

/-- The near-uniform types. -/
noncomputable def nearTypes (X : Type*) [Fintype X] [DecidableEq X] (m : ℕ) (ε : ℝ) :
    Finset (X → ℕ) :=
  (Fintype.piFinset fun _ ↦ Finset.range (m + 1)).filter fun n ↦
    ∑ x, n x = m ∧ ∀ x, |(n x : ℝ) - m / Fintype.card X| ≤ ε * m / Fintype.card X

theorem card_nearTypes (m : ℕ) (ε : ℝ) :
    (#(nearTypes X m ε) : ℝ) ≤ ((m : ℝ) + 1) ^ Fintype.card X := by
  have h : #(nearTypes X m ε) ≤ #(Fintype.piFinset fun _ : X ↦ Finset.range (m + 1)) :=
    Finset.card_filter_le _ _
  rw [Fintype.card_piFinset] at h
  simp only [Finset.card_range, Finset.prod_const, Finset.card_univ] at h
  exact_mod_cast h

omit [Fintype X] [DecidableEq X] [Fintype G] [DecidableEq G] in
/-- Firing a step with setups `a`, `b` is firing `σ` with bits `a`, then `σ⁻¹` with bits `b`. -/
theorem fire_eq_fireL (Γ : CycleSystem X (Fin 2) G) (g : G) {ι : Type*} (s : ι → X)
    (a b : ι → Fin 2) (k : ι) :
    Γ.fire ⟨g, a k, b k⟩ (s k) = fireL (Γ.e g 1)⁻¹ (fireL (Γ.e g 1) s a) b k := by
  have he : ∀ i : Fin 2, Γ.e g i = if i = 1 then Γ.e g 1 else 1 := by
    intro i; rcases fin2_cases i with rfl | rfl
    · simp [Γ.e_zero]
    · simp
  simp only [CycleSystem.fire, fireL]
  rw [he (a k), he (b k)]
  rcases fin2_cases (a k) with h₁ | h₁ <;> rcases fin2_cases (b k) with h₂ | h₂ <;> simp [h₁, h₂]

namespace CycleSystem

variable (Γ : CycleSystem X (Fin 2) G)

omit [DecidableEq G] in
/-- **Codebooks for a kind.** -/
theorem exists_books [Nonempty G] [Nonempty X] :
    ∃ γ lam : ℝ, ∃ L₀ : ℕ, 0 < γ ∧ γ ≤ 1 ∧ 0 ≤ lam ∧ lam < 1 ∧
      ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (c r₀ : ℕ) (ε ρf : ℝ),
      0 < Fintype.card ι → 4 * Fintype.card X ≤ Fintype.card ι → 0 ≤ ε → 0 < ρf →
      ρf ≤ farRate γ X → roundErr X (Fintype.card ι) ≤ ρf / 4 →
      ε * Fintype.card ι / Fintype.card X + ((r₀ + L₀) * roundLen G : ℕ) / 2 ≤
        Fintype.card ι / (2 * Fintype.card X) →
      mergeMu (Fintype.card X) (Fintype.card ι) (mergeDev (Fintype.card X) lam ε r₀
        ((r₀ + L₀) * roundLen G) (Fintype.card ι)) (epsStar X γ (Fintype.card ι)) ≤ 1 / 2 →
      ((Fintype.card ι : ℝ) + 1) ^ Fintype.card X * coverBound (Fintype.card ι) (Fintype.card X)
        (mergeRate X γ lam ε r₀ ((r₀ + L₀) * roundLen G) (Fintype.card ι)) ≤ 2 ^ c →
      coverBound (Fintype.card ι) (Fintype.card X) (ρf + roundErr X (Fintype.card ι)) ≤ 2 ^ c →
      ∃ (T : ℕ) (g : ℕ → G) (B₁ B₂ : ℕ → Finset (ι → Fin 2)),
        T ≤ (r₀ + L₀) * (allG G).length + pathLen X γ ρf (Fintype.card ι) ∧
        (∀ t, (B₁ t).Nonempty ∧ (B₂ t).Nonempty ∧ #(B₁ t) ≤ 2 ^ c ∧ #(B₂ t) ≤ 2 ^ c) ∧
        ∀ s : ι → X, (∀ x, |(typeOf s x : ℝ) - Fintype.card ι / Fintype.card X| ≤
            ε * Fintype.card ι / Fintype.card X) →
          ∃ a b : ℕ → ι → Fin 2, (∀ t < T, a t ∈ B₁ t ∧ b t ∈ B₂ t) ∧
            ∀ k, Γ.runN (fun t ↦ ⟨g t, a t k, b t k⟩) T (s k) = Γ.solved := by
  classical
  obtain ⟨γ₀, hγ₀, hspec₀⟩ := Γ.exists_spectral_gap
  set γ := min γ₀ 1 with hγ
  have hγpos : 0 < γ := lt_min hγ₀ one_pos
  have hspec : Γ.SpectralGap γ := SpectralGap.mono hspec₀ (min_le_left _ _)
  obtain ⟨lam, L₀, hlam₀, hlam₁, hmerge⟩ := Γ.exists_merge
  refine ⟨γ, lam, L₀, hγpos, min_le_right _ _, hlam₀, hlam₁, fun ι _ _ c r₀ ε ρf hι hm4 hε hρf₀
    hρf he hpos hμ hcov₁ hcov₂ ↦ ?_⟩
  set m := Fintype.card ι with hmdef
  set C := Fintype.card X with hC
  have hC₀ : (0 : ℝ) < C := card_pos_X
  have hC₁ : (1 : ℝ) ≤ C := by exact_mod_cast Fintype.card_pos
  have hm' : (0 : ℝ) < m := by exact_mod_cast hι
  -- The path.
  obtain ⟨TP, gP, zP, n₁P, n₂P, hpath, hzsum, hzT, hz0, hTP⟩ :=
    Γ.exists_path hγpos (min_le_right _ _) hspec hι hm4 hρf₀ hρf he
  -- It starts near uniform.
  have hzd : ∀ x, |(zP 0 x : ℝ) - m / C| ≤ epsStar X γ m * m / C := by
    intro x
    have hW := isDist_distOf hι (hzsum 0 (Nat.zero_le _))
    have h := sq_sub_uniform_le hW x
    have hθ : 0 ≤ 2 * roundErr X m / (γ / 150) :=
      div_nonneg (by have := roundErr_pos X hι hm4; linarith) (by positivity)
    have h₂ : |distOf m (zP 0) x - uniform X x| ≤ 2 * Real.sqrt (2 * roundErr X m / (γ / 150)) := by
      have h₃ : (distOf m (zP 0) x - uniform X x) ^ 2 ≤
          (2 * Real.sqrt (2 * roundErr X m / (γ / 150))) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt hθ]; nlinarith
      exact abs_le_of_sq_le_sq' h₃ (by positivity) |> fun h ↦ abs_le.mpr h
    have e : (zP 0 x : ℝ) - m / C = m * (distOf m (zP 0) x - uniform X x) := by
      simp only [distOf, uniform, ← hC]; field_simp
    rw [e, abs_mul, abs_of_pos hm']
    calc (m : ℝ) * |distOf m (zP 0) x - uniform X x| ≤
          m * (2 * Real.sqrt (2 * roundErr X m / (γ / 150))) :=
          mul_le_mul_of_nonneg_left h₂ hm'.le
      _ = epsStar X γ m * m / C := by unfold epsStar; rw [← hC]; field_simp
  have hεs : 0 ≤ epsStar X γ m := by unfold epsStar; positivity
  -- The merge, for each near-uniform start.
  set TM := (r₀ + L₀) * (allG G).length with hTM
  set rM := mergeRate X γ lam ε r₀ ((r₀ + L₀) * roundLen G) m with hrM
  have hM : ∀ n₀ ∈ nearTypes X m ε, ∃ U N₁ N₂, Γ.IsPath m rM TM mergeG U N₁ N₂ ∧ U 0 = n₀ ∧
      U TM = zP 0 ∧ ∀ t ≤ TM, ∑ x, U t x = m := by
    intro n₀ hn₀
    obtain ⟨-, hn₀s, hn₀d⟩ := Finset.mem_filter.mp hn₀
    exact hmerge m r₀ ε (epsStar X γ m) hι hm4 hε hεs hpos hμ n₀ (zP 0) hn₀s
      (hzsum 0 (Nat.zero_le _)) hn₀d hzd
  choose! UM N₁M N₂M hMpath hMstart hMend hMsum using hM
  -- Exact codebooks.
  have hcov : ∀ n : X × Fin 2 → ℕ, ∃ 𝓑 : Finset (ι → Fin 2), 𝓑.Nonempty ∧
      (∑ v, n v = m → (#𝓑 : ℝ) ≤ coverBound m C (info m n) ∧
        ∀ s : ι → X, typeOf s = inT n → ∃ b ∈ 𝓑, jointType s b = n) := by
    intro n
    by_cases hn : ∑ v, n v = m
    · obtain ⟨𝓑, h₁, h₂, h₃⟩ := exact_cover (ι := ι) n hn hι
      exact ⟨𝓑, h₁, fun _ ↦ ⟨h₂, h₃⟩⟩
    · exact ⟨{fun _ ↦ 0}, Finset.singleton_nonempty _, fun h ↦ absurd h hn⟩
  choose cov hcovne hcovp using hcov
  -- The program.
  set T := TM + TP with hT
  set g : ℕ → G := fun t ↦ if t < TM then mergeG t else gP (t - TM) with hg
  set NT := nearTypes X m ε with hNT
  set B₁ : ℕ → Finset (ι → Fin 2) := fun t ↦
    if t < TM then (if (NT.biUnion fun n₀ ↦ cov (N₁M n₀ t)).Nonempty then
      NT.biUnion fun n₀ ↦ cov (N₁M n₀ t) else {fun _ ↦ 0})
    else if t < T then cov (n₁P (t - TM)) else {fun _ ↦ 0} with hB₁
  set B₂ : ℕ → Finset (ι → Fin 2) := fun t ↦
    if t < TM then (if (NT.biUnion fun n₀ ↦ cov (N₂M n₀ t)).Nonempty then
      NT.biUnion fun n₀ ↦ cov (N₂M n₀ t) else {fun _ ↦ 0})
    else if t < T then cov (n₂P (t - TM)) else {fun _ ↦ 0} with hB₂
  -- Sizes.
  have hsumN : ∀ {r : ℝ} {TT : ℕ} {gg : ℕ → G} {U : ℕ → X → ℕ} {n₁ n₂ : ℕ → X × Fin 2 → ℕ},
      Γ.IsPath m r TT gg U n₁ n₂ → (∀ t ≤ TT, ∑ x, U t x = m) → ∀ t < TT,
        ∑ v, n₁ t v = m ∧ ∑ v, n₂ t v = m := by
    intro r TT gg U n₁ n₂ hp hs t ht
    have h₁ : ∑ v, n₁ t v = m := by rw [← sum_inT, (hp t ht).in₁, hs t ht.le]
    refine ⟨h₁, ?_⟩
    rw [← sum_inT, (hp t ht).mid, sum_outT, h₁]
  have h2c : (1 : ℝ) ≤ 2 ^ c := one_le_pow₀ (by norm_num)
  have hcard_union : ∀ (N : (X → ℕ) → ℕ → X × Fin 2 → ℕ) (t : ℕ),
      (∀ n₀ ∈ NT, ∑ v, N n₀ t v = m ∧ info m (N n₀ t) ≤ rM) →
      #(if (NT.biUnion fun n₀ ↦ cov (N n₀ t)).Nonempty then NT.biUnion fun n₀ ↦ cov (N n₀ t)
        else {fun _ ↦ 0}) ≤ 2 ^ c := by
    intro N t hN
    have h₁ : (#(NT.biUnion fun n₀ ↦ cov (N n₀ t)) : ℝ) ≤
        ((m : ℝ) + 1) ^ C * coverBound m C rM := by
      calc (#(NT.biUnion fun n₀ ↦ cov (N n₀ t)) : ℝ) ≤ ∑ n₀ ∈ NT, (#(cov (N n₀ t)) : ℝ) := by
            exact_mod_cast Finset.card_biUnion_le
        _ ≤ ∑ _n₀ ∈ NT, coverBound m C rM := Finset.sum_le_sum fun n₀ h ↦
            ((hcovp _ (hN n₀ h).1).1).trans (coverBound_mono hm'.le C (hN n₀ h).2 hC₁)
        _ = #NT * coverBound m C rM := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ((m : ℝ) + 1) ^ C * coverBound m C rM := by
            refine mul_le_mul_of_nonneg_right (card_nearTypes m ε) ?_
            unfold coverBound; have := log_nonneg hC₁; positivity
    split_ifs
    · exact_mod_cast h₁.trans hcov₁
    · simp only [Finset.card_singleton]; exact_mod_cast h2c
  have hMinfo : ∀ n₀ ∈ NT, ∀ t < TM, (∑ v, N₁M n₀ t v = m ∧ info m (N₁M n₀ t) ≤ rM) ∧
      (∑ v, N₂M n₀ t v = m ∧ info m (N₂M n₀ t) ≤ rM) := by
    intro n₀ h t ht
    have hs := hsumN (hMpath n₀ h) (hMsum n₀ h) t ht
    exact ⟨⟨hs.1, ((hMpath n₀ h) t ht).info₁⟩, ⟨hs.2, ((hMpath n₀ h) t ht).info₂⟩⟩
  have hPcard : ∀ (n : X × Fin 2 → ℕ), ∑ v, n v = m → info m n ≤ ρf + roundErr X m →
      #(cov n) ≤ 2 ^ c := by
    intro n hn hi
    have := ((hcovp n hn).1).trans ((coverBound_mono hm'.le C hi hC₁).trans hcov₂)
    exact_mod_cast this
  refine ⟨T, g, B₁, B₂, ?_, fun t ↦ ?_, fun s hs ↦ ?_⟩
  · rw [hT]; exact Nat.add_le_add_left hTP _
  · -- Sizes and nonemptiness.
    by_cases ht : t < TM
    · simp only [hB₁, hB₂, ite_eq_left ht]
      refine ⟨?_, ?_, ?_, ?_⟩
      · split_ifs with h; exacts [h, Finset.singleton_nonempty _]
      · split_ifs with h; exacts [h, Finset.singleton_nonempty _]
      · exact hcard_union N₁M t fun n₀ h ↦ (hMinfo n₀ h t ht).1
      · exact hcard_union N₂M t fun n₀ h ↦ (hMinfo n₀ h t ht).2
    · simp only [hB₁, hB₂, ite_eq_right ht]
      by_cases htT : t < T
      · have htP : t - TM < TP := by omega
        simp only [ite_eq_left htT]
        exact ⟨hcovne _, hcovne _, hPcard _ (hsumN hpath hzsum _ htP).1 (hpath _ htP).info₁,
          hPcard _ (hsumN hpath hzsum _ htP).2 (hpath _ htP).info₂⟩
      · simp only [ite_eq_right htT, Finset.singleton_nonempty, Finset.card_singleton, true_and]
        have : (1 : ℕ) ≤ 2 ^ c := Nat.one_le_two_pow
        exact ⟨this, this⟩
  · -- Solving a near-uniform list.
    set n₀ := typeOf s with hn₀
    have hn₀s : ∑ x, n₀ x = m := sum_typeOf s
    have hn₀NT : n₀ ∈ NT := by
      refine Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mpr fun x ↦ Finset.mem_range.mpr ?_,
        hn₀s, hs⟩
      have : n₀ x ≤ m := by
        rw [← hn₀s]
        exact Finset.single_le_sum (f := n₀) (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ x)
      omega
    -- The whole plan of types and joint types.
    set Ua : ℕ → X → ℕ := fun t ↦ if t ≤ TM then UM n₀ t else zP (t - TM) with hUa
    set Na₁ : ℕ → X × Fin 2 → ℕ := fun t ↦ if t < TM then N₁M n₀ t else n₁P (t - TM) with hNa₁
    set Na₂ : ℕ → X × Fin 2 → ℕ := fun t ↦ if t < TM then N₂M n₀ t else n₂P (t - TM) with hNa₂
    have hstep : ∀ t < T, Γ.PathStep m (max rM (ρf + roundErr X m)) (Ua t) (Ua (t + 1)) (g t)
        (Na₁ t) (Na₂ t) ∧ cov (Na₁ t) ⊆ B₁ t ∧ cov (Na₂ t) ⊆ B₂ t ∧
        ∑ v, Na₁ t v = m ∧ ∑ v, Na₂ t v = m := by
      intro t ht
      by_cases htM : t < TM
      · have hp := (hMpath n₀ hn₀NT) t htM
        have hs₂ := hsumN (hMpath n₀ hn₀NT) (hMsum n₀ hn₀NT) t htM
        have e₁ : Ua t = UM n₀ t := by simp [hUa, htM.le]
        have e₂ : Ua (t + 1) = UM n₀ (t + 1) := by simp [hUa, show t + 1 ≤ TM by omega]
        simp only [hNa₁, hNa₂, hg, hB₁, hB₂, ite_eq_left htM, e₁, e₂]
        refine ⟨hp.mono _ (le_max_left _ _), ?_, ?_, hs₂.1, hs₂.2⟩
        · have hsub : cov (N₁M n₀ t) ⊆ NT.biUnion fun n₀ ↦ cov (N₁M n₀ t) :=
            Finset.subset_biUnion_of_mem (fun n₀ ↦ cov (N₁M n₀ t)) hn₀NT
          rw [ite_eq_left ((hcovne _).mono hsub)]; exact hsub
        · have hsub : cov (N₂M n₀ t) ⊆ NT.biUnion fun n₀ ↦ cov (N₂M n₀ t) :=
            Finset.subset_biUnion_of_mem (fun n₀ ↦ cov (N₂M n₀ t)) hn₀NT
          rw [ite_eq_left ((hcovne _).mono hsub)]; exact hsub
      · have htP : t - TM < TP := by omega
        have hp := hpath (t - TM) htP
        have hs₂ := hsumN hpath hzsum _ htP
        have e₁ : Ua t = zP (t - TM) := by
          by_cases h : t ≤ TM
          · have : t = TM := by omega
            subst this; simp [hUa, hMend n₀ hn₀NT]
          · simp [hUa, h]
        have e₂ : Ua (t + 1) = zP (t - TM + 1) := by
          simp [hUa, show ¬ (t + 1 ≤ TM) by omega, show t + 1 - TM = t - TM + 1 by omega]
        simp only [hNa₁, hNa₂, hg, hB₁, hB₂, ite_eq_right htM, ite_eq_left ht, e₁, e₂]
        exact ⟨hp.mono _ (le_max_right _ _), subset_rfl, subset_rfl, hs₂.1, hs₂.2⟩
    -- Induction over the steps.
    have key : ∀ t ≤ T, ∃ a b : ℕ → ι → Fin 2, (∀ t' < t, a t' ∈ B₁ t' ∧ b t' ∈ B₂ t') ∧
        typeOf (fun k ↦ Γ.runN (fun t ↦ ⟨g t, a t k, b t k⟩) t (s k)) = Ua t := by
      intro t
      induction t with
      | zero =>
        intro _
        refine ⟨fun _ _ ↦ 0, fun _ _ ↦ 0, fun _ h ↦ absurd h (Nat.not_lt_zero _), ?_⟩
        simp only [CycleSystem.runN, hUa, Nat.zero_le, ite_true, hMstart n₀ hn₀NT]
        rfl
      | succ t ih =>
        intro htT
        obtain ⟨a, b, hab, htype⟩ := ih (by omega)
        obtain ⟨hp, hsub₁, hsub₂, hs₁, hs₂⟩ := hstep t (by omega)
        set st : ι → X := fun k ↦ Γ.runN (fun t ↦ ⟨g t, a t k, b t k⟩) t (s k) with hst
        obtain ⟨a', ha'm, ha'⟩ := (hcovp _ hs₁).2 st (by rw [htype, hp.in₁])
        set s' := fireL (Γ.e (g t) 1) st a' with hs'
        have hs'type : typeOf s' = inT (Na₂ t) := by
          rw [hs', ← outT_jointType, ha', hp.mid]
        obtain ⟨b', hb'm, hb'⟩ := (hcovp _ hs₂).2 s' hs'type
        refine ⟨fun t' ↦ if t' < t then a t' else a', fun t' ↦ if t' < t then b t' else b',
          fun t' ht' ↦ ?_, ?_⟩
        · by_cases h : t' < t
          · simp only [ite_eq_left h]; exact hab t' h
          · have : t' = t := by omega
            subst this
            simp only [lt_irrefl, ite_false]
            exact ⟨hsub₁ ha'm, hsub₂ hb'm⟩
        · have hrun : (fun k ↦ Γ.runN (fun t'' ↦ ⟨g t'', (if t'' < t then a t'' else a') k,
              (if t'' < t then b t'' else b') k⟩) (t + 1) (s k)) =
              fireL (Γ.e (g t) 1)⁻¹ s' b' := by
            funext k
            simp only [CycleSystem.runN]
            rw [CycleSystem.runN_congr (q' := fun t ↦ ⟨g t, a t k, b t k⟩) (fun u hu ↦ by
              simp [hu])]
            simp only [lt_irrefl, ite_false]
            exact fire_eq_fireL Γ (g t) st a' b' k
          rw [hrun, ← outT_jointType, hb', hp.out₂]
    obtain ⟨a, b, hab, htype⟩ := key T le_rfl
    refine ⟨a, b, hab, fun k ↦ ?_⟩
    have hUT : Ua T = solvedT Γ.solved m := by
      by_cases hTP0 : TP = 0
      · have : T = TM := by omega
        rw [this]
        simp only [hUa, le_refl, ite_true, hMend n₀ hn₀NT]
        rw [← hzT, hTP0]
      · simp only [hUa, show ¬ (T ≤ TM) by omega, ite_false, show T - TM = TP by omega, hzT]
    rw [hUT] at htype
    have h := congrFun htype Γ.solved
    simp only [solvedT, ite_true] at h
    exact eq_of_typeOf h k

end CycleSystem

end CubeGod
