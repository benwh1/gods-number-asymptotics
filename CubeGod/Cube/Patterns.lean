import CubeGod.Cube.Word

/-!
# Patterns

A pattern of an orbit says which face the sticker at each of its 24 positions belongs on, with 4 of
each face. Each orbit has `C = 24!/4!⁶` patterns.
-/

open Finset

namespace CubeGod

/-- A function on a finite type with exactly 4 points over each face. -/
def Balanced {α : Type*} [Fintype α] (f : α → Face) : Prop :=
  ∀ c, Fintype.card {a // f a = c} = 4

/-- The solved view of a pair: each position's sticker belongs on the face it's on. -/
def solvedView (u : Pos) : Face := u.dir .outer

/-- The right-handed positions. -/
abbrev PosR := {u : Pos // u.Proper}

theorem card_posR : Fintype.card PosR = 24 := by decide +kernel

/-- Two balanced functions differ by a permutation. -/
theorem Balanced.exists_perm {α : Type*} [Fintype α] {f g : α → Face}
    (hf : Balanced f) (hg : Balanced g) : ∃ σ : Equiv.Perm α, f ∘ σ = g := by
  have e : ∀ c, {a // g a = c} ≃ {a // f a = c} := fun c ↦
    Fintype.equivOfCardEq ((hg c).trans (hf c).symm)
  refine ⟨(Equiv.sigmaFiberEquiv g).symm.trans
    ((Equiv.sigmaCongrRight e).trans (Equiv.sigmaFiberEquiv f)), ?_⟩
  funext a
  change f (e (g a) ⟨a, rfl⟩).1 = g a
  exact (e (g a) ⟨a, rfl⟩).2

/-- Composing with a permutation keeps a function balanced. -/
theorem Balanced.comp_perm {α : Type*} [Fintype α] {f : α → Face} (hf : Balanced f)
    (σ : Equiv.Perm α) : Balanced (f ∘ σ) := by
  intro c
  rw [← hf c]
  exact Fintype.card_congr (σ.subtypeEquiv fun _ ↦ Iff.rfl)

/-- The number of balanced functions on 24 points is `C`. -/
theorem card_balanced {α : Type*} [Fintype α] [DecidableEq α] (hα : Fintype.card α = 24)
    {f₀ : α → Face} (hf₀ : Balanced f₀) [Fintype {f : α → Face // Balanced f}] :
    Fintype.card {f : α → Face // Balanced f} = patternCount := by
  classical
  -- Each balanced function is `f₀ ∘ σ` for the same number of permutations `σ`.
  have hstab : Fintype.card {g : Equiv.Perm α // f₀ ∘ g = f₀} = (Nat.factorial 4) ^ 6 := by
    rw [DomMulAct.stabilizer_card]
    simp only [hf₀ _]
    simp [Finset.card_univ, show Fintype.card Face = 6 from rfl]
  have hfib : ∀ p : {f : α → Face // Balanced f},
      Fintype.card {σ : Equiv.Perm α // f₀ ∘ σ = p.1} = (Nat.factorial 4) ^ 6 := by
    intro p
    obtain ⟨τ, hτ⟩ := hf₀.exists_perm p.2
    rw [← hstab]
    refine Fintype.card_congr ⟨fun σ ↦ ⟨σ.1 * τ⁻¹, ?_⟩, fun σ ↦ ⟨σ.1 * τ, ?_⟩, ?_, ?_⟩
    · have := σ.2
      funext a
      have h₁ := congrFun this (τ⁻¹ a)
      have h₂ := congrFun hτ (τ⁻¹ a)
      simp only [Function.comp, Equiv.Perm.coe_mul] at h₁ h₂ ⊢
      rw [h₁, ← h₂]
      simp
    · have := σ.2
      funext a
      have h₁ := congrFun this (τ a)
      have h₂ := congrFun hτ a
      simp only [Function.comp, Equiv.Perm.coe_mul] at h₁ h₂ ⊢
      rw [h₁, h₂]
    · intro σ
      simp
    · intro σ
      simp
  -- Count permutations by the function they give.
  have hsum : Fintype.card (Equiv.Perm α) =
      Fintype.card {f : α → Face // Balanced f} * (Nat.factorial 4) ^ 6 := by
    have e : Equiv.Perm α ≃ Σ p : {f : α → Face // Balanced f},
        {σ : Equiv.Perm α // f₀ ∘ σ = p.1} :=
      { toFun := fun σ ↦ ⟨⟨f₀ ∘ σ, hf₀.comp_perm σ⟩, ⟨σ, rfl⟩⟩
        invFun := fun x ↦ x.2.1
        left_inv := fun σ ↦ rfl
        right_inv := by
          rintro ⟨⟨f, hf⟩, ⟨σ, hσ⟩⟩
          simp only at hσ
          subst hσ
          rfl }
    rw [Fintype.card_congr e, Fintype.card_sigma]
    simp only [hfib, Finset.sum_const, Finset.card_univ, smul_eq_mul]
  rw [Fintype.card_perm, hα] at hsum
  unfold patternCount
  rw [hsum]
  exact (Nat.mul_div_cancel _ (pow_pos (Nat.factorial_pos 4) 6)).symm

theorem solvedView_R : Balanced (fun u : PosR ↦ solvedView u.1) := by
  intro c
  revert c
  decide +kernel

end CubeGod
