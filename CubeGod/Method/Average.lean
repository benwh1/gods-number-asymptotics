import Mathlib

/-!
# Averaging over the twist

Let a finite group `Γ` act transitively on `X`, so that each `g x` is uniform over `X`. Pick an element
`r j` of `Γ` for each `j` in a finite set `J`. A tuple `τ` uses `c` different elements of `J`, and has a
list of `c` points of `X`. After the twist its list is `r (ι τ k) • s τ k`.

If at most a fraction `β` of all lists in `X^c` are bad, then some choice of `r` leaves at most a
fraction `β` of the tuples bad. One way to see this is as an
expectation; here it's a count.
-/

open Finset

set_option linter.unusedSectionVars false

namespace CubeGod

variable {X J G T : Type*} [Fintype X] [DecidableEq X] [Fintype J] [DecidableEq J] [Fintype G]
  [DecidableEq G] [Fintype T] {c : ℕ}

/-- The number of choices of `r` meeting `c` constraints on different coordinates. Each constraint
keeps a fraction `|A k|/|G|` of the choices. -/
theorem card_constrained [Nonempty G] {ι : Fin c → J} (hι : Function.Injective ι)
    (A : Fin c → Finset G) :
    (#{r : J → G | ∀ k, r (ι k) ∈ A k} : ℝ) =
      (Fintype.card G : ℝ) ^ Fintype.card J * ∏ k, ((#(A k) : ℝ) / Fintype.card G) := by
  classical
  have hG : (Fintype.card G : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  set S : J → Finset G := Function.extend ι A fun _ ↦ univ with hS
  have hset : (univ.filter fun r : J → G ↦ ∀ k, r (ι k) ∈ A k) = Fintype.piFinset S := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset]
    constructor
    · intro h j
      by_cases hj : ∃ k, ι k = j
      · obtain ⟨k, rfl⟩ := hj
        rw [hS, hι.extend_apply]
        exact h k
      · rw [hS, Function.extend_apply' _ _ _ hj]
        exact Finset.mem_univ _
    · intro h k
      have := h (ι k)
      rwa [hS, hι.extend_apply] at this
  rw [hset, Fintype.card_piFinset]
  push_cast
  -- Divide each factor by `|G|`.
  have hsplit : ∏ j, (#(S j) : ℝ) = (Fintype.card G : ℝ) ^ Fintype.card J *
      ∏ j, ((#(S j) : ℝ) / Fintype.card G) := by
    have h₁ : ∏ j, ((#(S j) : ℝ) / Fintype.card G) =
        (∏ j, (#(S j) : ℝ)) / ∏ _j : J, (Fintype.card G : ℝ) := Finset.prod_div_distrib _ _
    have h₂ : ∏ _j : J, (Fintype.card G : ℝ) = (Fintype.card G : ℝ) ^ Fintype.card J := by
      rw [Finset.prod_const, Finset.card_univ]
    have hb : (Fintype.card G : ℝ) ^ Fintype.card J ≠ 0 := pow_ne_zero _ hG
    rw [h₁, h₂, ← mul_div_assoc, mul_div_cancel_left₀ _ hb]
  rw [hsplit]
  congr 1
  -- Only the constrained coordinates count.
  have hsub : (univ.image ι) ⊆ univ := Finset.subset_univ _
  rw [← Finset.prod_subset hsub, Finset.prod_image fun a _ b _ h ↦ hι h]
  · refine Finset.prod_congr rfl fun k _ ↦ ?_
    rw [hS, hι.extend_apply]
  · intro j _ hj
    have hj' : ¬ ∃ k, ι k = j := by
      rintro ⟨k, rfl⟩
      exact hj (Finset.mem_image_of_mem _ (Finset.mem_univ k))
    rw [hS, Function.extend_apply' _ _ _ hj', Finset.card_univ]
    exact div_self hG

variable [Group G] [MulAction G X]

omit [DecidableEq G] in
/-- In a transitive action, `g • x` is uniform: each point is hit by `|G|/|X|` elements. -/
theorem card_fiber [Nonempty X] (htrans : ∀ x y : X, ∃ g : G, g • x = y) (x y : X) :
    (#{g : G | g • x = y} : ℝ) / Fintype.card G = (Fintype.card X : ℝ)⁻¹ := by
  classical
  have hG : (Fintype.card G : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hX : (Fintype.card X : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  -- All fibers have the same size.
  have hsame : ∀ y', #{g : G | g • x = y'} = #{g : G | g • x = y} := by
    intro y'
    obtain ⟨h, rfl⟩ := htrans y y'
    refine Finset.card_bij' (fun g _ ↦ h⁻¹ * g) (fun g _ ↦ h * g) ?_ ?_ ?_ ?_
    · intro g hg
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg ⊢
      rw [mul_smul, hg, inv_smul_smul]
    · intro g hg
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg ⊢
      rw [mul_smul, hg]
    · intro g _
      simp
    · intro g _
      simp
  have hsum : ∑ y', #{g : G | g • x = y'} = Fintype.card G := by
    rw [← Finset.card_univ]
    exact (Finset.card_eq_sum_card_fiberwise (f := fun g : G ↦ g • x) (t := univ)
      (fun g _ ↦ Finset.mem_univ _)).symm
  simp only [hsame, Finset.sum_const, Finset.card_univ, smul_eq_mul] at hsum
  have hsumR : (Fintype.card X : ℝ) * (#{g : G | g • x = y} : ℝ) = Fintype.card G := by
    exact_mod_cast hsum
  rw [div_eq_iff hG, ← hsumR]
  field_simp

/-- Some choice of the twist leaves at most a fraction `β` of the tuples bad. -/
theorem exists_good_twist [Nonempty X] (htrans : ∀ x y : X, ∃ g : G, g • x = y)
    (ι : T → Fin c → J) (hι : ∀ τ, Function.Injective (ι τ)) (s : T → Fin c → X)
    (Bad : Finset (Fin c → X)) {β : ℝ}
    (hβ : (#Bad : ℝ) ≤ β * (Fintype.card X : ℝ) ^ c) :
    ∃ r : J → G, (#{τ : T | (fun k ↦ r (ι τ k) • s τ k) ∈ Bad} : ℝ) ≤ β * Fintype.card T := by
  classical
  have hX : (0 : ℝ) < Fintype.card X := by exact_mod_cast Fintype.card_pos
  set Gc : ℝ := (Fintype.card G : ℝ) ^ Fintype.card J with hGc
  have hGc₀ : 0 < Gc := by
    have : (0 : ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos
    positivity
  -- For one tuple, the fraction of `r` making it bad.
  have hone : ∀ τ, (#{r : J → G | (fun k ↦ r (ι τ k) • s τ k) ∈ Bad} : ℝ) ≤ β * Gc := by
    intro τ
    have hsub : (univ.filter fun r : J → G ↦ (fun k ↦ r (ι τ k) • s τ k) ∈ Bad) ⊆
        Bad.biUnion fun x ↦ univ.filter fun r : J → G ↦ ∀ k, r (ι τ k) ∈
          (univ.filter fun g : G ↦ g • s τ k = x k) := by
      intro r hr
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr
      exact Finset.mem_biUnion.mpr ⟨_, hr, by simp⟩
    have h₁ : (#(univ.filter fun r : J → G ↦ (fun k ↦ r (ι τ k) • s τ k) ∈ Bad) : ℝ) ≤
        ∑ x ∈ Bad, (#(univ.filter fun r : J → G ↦ ∀ k, r (ι τ k) ∈
          (univ.filter fun g : G ↦ g • s τ k = x k)) : ℝ) := by
      exact_mod_cast (Finset.card_le_card hsub).trans Finset.card_biUnion_le
    have h₂ : ∀ x ∈ Bad, (#(univ.filter fun r : J → G ↦ ∀ k, r (ι τ k) ∈
        (univ.filter fun g : G ↦ g • s τ k = x k)) : ℝ) =
        Gc * ((Fintype.card X : ℝ)⁻¹) ^ c := by
      intro x _
      rw [card_constrained (hι τ)]
      simp only [card_fiber htrans, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      rfl
    rw [Finset.sum_congr rfl h₂, Finset.sum_const, nsmul_eq_mul] at h₁
    refine h₁.trans ?_
    have hle : (#Bad : ℝ) * ((Fintype.card X : ℝ)⁻¹) ^ c ≤ β := by
      have := mul_le_mul_of_nonneg_right hβ (show 0 ≤ ((Fintype.card X : ℝ)⁻¹) ^ c by positivity)
      have he : β * (Fintype.card X : ℝ) ^ c * ((Fintype.card X : ℝ)⁻¹) ^ c = β := by
        rw [mul_assoc, ← mul_pow, mul_inv_cancel₀ hX.ne', one_pow, mul_one]
      rwa [he] at this
    calc (#Bad : ℝ) * (Gc * ((Fintype.card X : ℝ)⁻¹) ^ c)
        = ((#Bad : ℝ) * ((Fintype.card X : ℝ)⁻¹) ^ c) * Gc := by ring
      _ ≤ β * Gc := mul_le_mul_of_nonneg_right hle hGc₀.le
  -- Count pairs of a tuple and a choice of `r`, two ways.
  have hdouble : ∑ r : J → G, (#{τ : T | (fun k ↦ r (ι τ k) • s τ k) ∈ Bad} : ℝ) =
      ∑ τ : T, (#{r : J → G | (fun k ↦ r (ι τ k) • s τ k) ∈ Bad} : ℝ) := by
    simp only [Finset.card_filter, Nat.cast_sum]
    exact Finset.sum_comm
  have hle : ∑ r : J → G, (#{τ : T | (fun k ↦ r (ι τ k) • s τ k) ∈ Bad} : ℝ) ≤
      ∑ _r : J → G, β * Fintype.card T := by
    rw [hdouble, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have hcard : (Fintype.card (J → G) : ℝ) = Gc := by
      rw [hGc, Fintype.card_fun]
      push_cast
      rfl
    rw [hcard]
    calc ∑ τ : T, (#{r : J → G | (fun k ↦ r (ι τ k) • s τ k) ∈ Bad} : ℝ)
        ≤ ∑ _τ : T, β * Gc := Finset.sum_le_sum fun τ _ ↦ hone τ
      _ = Gc * (β * Fintype.card T) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          ring
  obtain ⟨r, -, hr⟩ := Finset.exists_le_of_sum_le (Finset.univ_nonempty) hle
  exact ⟨r, hr⟩

end CubeGod
