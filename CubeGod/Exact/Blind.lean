import CubeGod.Exact.Mix

/-!
# The blind flow

A sequence of firings with permutations `ps 0, ps 1, …`. The **blind** rule sends half of each
pattern's entries, rounded up, through the firing's permutation, whatever the list
(`blindJ`). Starting from a type `n₀`, it gives the types `blindU ps n₀ f` before firing `f`.

Without rounding, each firing would average the type with a rearranged copy of itself (`avgP`).
Rounding moves each count by at most `½` per firing, so after `f` firings the deviation from a
constant is the exact average of the starting deviation (`opR`), give or take `f/2`
(`blindU_dev`). When the firings repeat a round `L`, the exact averages are `mixAll L`, repeated.
-/

open Finset Real

set_option linter.unusedSectionVars false

namespace CubeGod

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- The blind joint type: half of each count, rounded up, gets the bit `1`. -/
def blindJ (u : X → ℕ) (v : X × Fin 2) : ℕ := if v.2 = 0 then u v.1 / 2 else (u v.1 + 1) / 2

omit [Fintype X] [DecidableEq X] in
theorem inT_blindJ (u : X → ℕ) : inT (blindJ u) = u := by
  funext x
  simp only [inT, blindJ, ite_true, Fin.one_eq_zero_iff, OfNat.ofNat_ne_one, ite_false]
  omega

/-- The blind flow: the types before each firing. -/
def blindU (ps : ℕ → Equiv.Perm X) (n₀ : X → ℕ) : ℕ → X → ℕ
  | 0 => n₀
  | f + 1 => outT (ps f) (blindJ (blindU ps n₀ f))

omit [DecidableEq X] in
theorem sum_blindU (ps : ℕ → Equiv.Perm X) (n₀ : X → ℕ) (f : ℕ) :
    ∑ x, blindU ps n₀ f x = ∑ x, n₀ x := by
  induction f with
  | zero => rfl
  | succ f ih =>
    rw [blindU, sum_outT, ← sum_inT, inT_blindJ, ih]

/-- The exact averages of firings `f₀, …, f₀ + j − 1`. -/
noncomputable def opR (ps : ℕ → Equiv.Perm X) (f₀ : ℕ) : ℕ → (X → ℝ) → (X → ℝ)
  | 0, v => v
  | j + 1, v => avgP (ps (f₀ + j)) (opR ps f₀ j v)

omit [Fintype X] [DecidableEq X] in
theorem opR_add (ps : ℕ → Equiv.Perm X) (f₀ j₁ j₂ : ℕ) (v : X → ℝ) :
    opR ps f₀ (j₁ + j₂) v = opR ps (f₀ + j₁) j₂ (opR ps f₀ j₁ v) := by
  induction j₂ with
  | zero => rfl
  | succ j ih =>
    rw [← add_assoc, opR, ih, opR, add_assoc]

omit [Fintype X] [DecidableEq X] in
theorem opR_mixAll (ps : ℕ → Equiv.Perm X) (L : List (Equiv.Perm X)) :
    ∀ f₀, (∀ j (hj : j < L.length), ps (f₀ + j) = L[j]) → ∀ v, opR ps f₀ L.length v = mixAll L v := by
  induction L with
  | nil => intro _ _ _; rfl
  | cons σ L ih =>
    intro f₀ hps v
    rw [List.length_cons, add_comm, opR_add, mixAll]
    have h₀ : ps f₀ = σ := by
      have := hps 0 (by simp)
      rwa [add_zero, List.getElem_cons_zero] at this
    have h₁ : opR ps f₀ 1 v = avgP σ v := by simp [opR, h₀]
    rw [h₁]
    refine ih (f₀ + 1) (fun j hj ↦ ?_) _
    have := hps (j + 1) (by simp; omega)
    rw [List.getElem_cons_succ] at this
    rw [add_assoc, add_comm 1 j]
    exact this

omit [Fintype X] [DecidableEq X] in
theorem abs_opR_le (ps : ℕ → Equiv.Perm X) (f₀ : ℕ) {v : X → ℝ} {B : ℝ} (hv : ∀ y, |v y| ≤ B) :
    ∀ j y, |opR ps f₀ j v y| ≤ B := by
  intro j
  induction j with
  | zero => exact hv
  | succ j ih =>
    intro y
    simp only [opR, avgP]
    rw [abs_div, abs_two]
    have := abs_add_le (opR ps f₀ j v y) (opR ps f₀ j v ((ps (f₀ + j))⁻¹ y))
    linarith [ih y, ih ((ps (f₀ + j))⁻¹ y)]

/-- Halves, rounded down and up. -/
theorem half_bounds (a : ℕ) :
    (a : ℝ) / 2 - 1 / 2 ≤ ((a / 2 : ℕ) : ℝ) ∧ ((a / 2 : ℕ) : ℝ) ≤ (a : ℝ) / 2 ∧
      (a : ℝ) / 2 ≤ (((a + 1) / 2 : ℕ) : ℝ) ∧ (((a + 1) / 2 : ℕ) : ℝ) ≤ (a : ℝ) / 2 + 1 / 2 := by
  have h₁ := Nat.div_add_mod a 2
  have h₂ := Nat.mod_lt a (show 0 < 2 by norm_num)
  have h₃ : (a + 1) / 2 = a / 2 + a % 2 := by omega
  have hr : (a % 2 = 0) ∨ (a % 2 = 1) := by omega
  have hc : (a : ℝ) = 2 * (a / 2 : ℕ) + (a % 2 : ℕ) := by exact_mod_cast h₁.symm
  rw [h₃]
  push_cast
  rcases hr with h | h <;> rw [h] at hc ⊢ <;> push_cast at hc ⊢ <;> constructor <;>
    (try constructor) <;> (try constructor) <;> linarith

omit [Fintype X] [DecidableEq X] in
/-- **The blind flow's deviation.** After `f` firings, the deviation of the blind flow from any
constant `c₀` is the exact average of the starting deviation, give or take `f/2`. -/
theorem blindU_dev (ps : ℕ → Equiv.Perm X) (n₀ : X → ℕ) (c₀ : ℝ) (f : ℕ) :
    ∀ y, |((blindU ps n₀ f y : ℝ) - c₀) - opR ps 0 f (fun x ↦ (n₀ x : ℝ) - c₀) y| ≤ f / 2 := by
  induction f with
  | zero => intro y; simp [blindU, opR]
  | succ f ih =>
    intro y
    set u := blindU ps n₀ f with hu
    set σ := ps f with hσ
    have hval : (blindU ps n₀ (f + 1) y : ℝ) =
        ((u y / 2 : ℕ) : ℝ) + (((u (σ⁻¹ y) + 1) / 2 : ℕ) : ℝ) := by
      simp only [blindU, outT, blindJ, ite_true, Fin.one_eq_zero_iff, OfNat.ofNat_ne_one,
        ite_false, ← hu, ← hσ]
      push_cast; ring
    have hb₁ := half_bounds (u y)
    have hb₂ := half_bounds (u (σ⁻¹ y))
    have hop : opR ps 0 (f + 1) (fun x ↦ (n₀ x : ℝ) - c₀) y =
        (opR ps 0 f (fun x ↦ (n₀ x : ℝ) - c₀) y +
          opR ps 0 f (fun x ↦ (n₀ x : ℝ) - c₀) (σ⁻¹ y)) / 2 := by
      simp [opR, avgP, hσ]
    rw [hval, hop]
    have i₁ := abs_le.mp (ih y)
    have i₂ := abs_le.mp (ih (σ⁻¹ y))
    rw [abs_le]
    push_cast
    constructor <;> linarith [hb₁.1, hb₁.2.1, hb₂.2.2.1, hb₂.2.2.2]

end CubeGod
