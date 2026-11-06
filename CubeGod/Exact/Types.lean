import CubeGod.Exact.Continuity

/-!
# Types and firings

A list of patterns is a function `s : ι → X` on a finite set `ι` of entries. Its **type** counts how
many entries have each pattern. A **firing** with a permutation `σ` takes `s` and a list of bits `b`
to the list in which entry `k` has moved by `σ` if its bit is `1`. The **joint type** of the firing
counts the pairs (pattern, bit). Its input type adds up over bits, and its output type counts where
the entries go.
-/

open Finset Real

set_option linter.unusedSectionVars false

namespace CubeGod

variable {X ι : Type*} [Fintype X] [DecidableEq X] [Fintype ι] [DecidableEq ι]

/-- The type of a list: how many entries have each pattern. -/
def typeOf (s : ι → X) (x : X) : ℕ := #{k | s k = x}

/-- The joint type of a list of patterns and a list of bits. -/
def jointType (s : ι → X) (b : ι → Fin 2) (v : X × Fin 2) : ℕ := #{k | s k = v.1 ∧ b k = v.2}

/-- The input type of a joint type. -/
def inT (n : X × Fin 2 → ℕ) (x : X) : ℕ := n (x, 0) + n (x, 1)

/-- The output type of a joint type, for a firing with `σ`: an entry with bit `1` moves by `σ`. -/
def outT (σ : Equiv.Perm X) (n : X × Fin 2 → ℕ) (y : X) : ℕ := n (y, 0) + n (σ⁻¹ y, 1)

/-- The firing with `σ`: entry `k` moves by `σ` if its bit is `1`. -/
def fireL (σ : Equiv.Perm X) (s : ι → X) (b : ι → Fin 2) : ι → X :=
  fun k ↦ if b k = 1 then σ (s k) else s k

theorem fin2_cases (i : Fin 2) : i = 0 ∨ i = 1 := by fin_cases i <;> simp

omit [Fintype X] in
theorem outT_jointType (σ : Equiv.Perm X) (s : ι → X) (b : ι → Fin 2) :
    outT σ (jointType s b) = typeOf (fireL σ s b) := by
  funext y
  unfold outT jointType typeOf fireL
  rw [← Finset.card_union_of_disjoint]
  · congr 1
    ext k
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    rcases fin2_cases (b k) with h | h
    · simp [h]
    · simp only [h, and_true, ite_true]
      constructor
      · rintro (⟨-, h'⟩ | h')
        · exact absurd h' (by decide)
        · rw [h']; simp
      · intro h'; right; rw [← h']; simp
  · rw [Finset.disjoint_left]
    intro k h₁ h₂
    simp only [Finset.mem_filter] at h₁ h₂
    rw [h₁.2.2] at h₂
    exact absurd h₂.2.2 (by decide)

omit [DecidableEq ι] in
theorem sum_typeOf (s : ι → X) : ∑ x, typeOf s x = Fintype.card ι := by
  unfold typeOf
  rw [← Finset.card_eq_sum_card_fiberwise (fun k _ ↦ Finset.mem_univ (s k))]
  rfl

omit [DecidableEq X] in
theorem sum_inT (n : X × Fin 2 → ℕ) : ∑ x, inT n x = ∑ v, n v := by
  rw [Fintype.sum_prod_type]
  simp [inT, Fin.sum_univ_two]

omit [DecidableEq X] in
theorem sum_outT (σ : Equiv.Perm X) (n : X × Fin 2 → ℕ) : ∑ y, outT σ n y = ∑ v, n v := by
  rw [Fintype.sum_prod_type]
  simp only [outT, Finset.sum_add_distrib, Fin.sum_univ_two]
  rw [Equiv.sum_comp σ⁻¹ (fun x ↦ n (x, 1))]

/-- A type, as a distribution: its counts divided by `m`. -/
noncomputable def distOf {Y : Type*} (m : ℕ) (n : Y → ℕ) : Y → ℝ := fun v ↦ n v / m

theorem isDist_distOf {Y : Type*} [Fintype Y] {m : ℕ} {n : Y → ℕ} (hm : 0 < m)
    (hn : ∑ v, n v = m) : IsDist (distOf m n) := by
  refine ⟨fun v ↦ by unfold distOf; positivity, ?_⟩
  unfold distOf
  rw [← Finset.sum_div]
  have : ((∑ v, n v : ℕ) : ℝ) = m := by rw [hn]
  push_cast at this
  rw [this, div_self (by exact_mod_cast hm.ne')]

/-- The information of a joint type of `m` entries: the mutual information of its distribution. -/
noncomputable def info (m : ℕ) (n : X × Fin 2 → ℕ) : ℝ := mi (distOf m n)

omit [DecidableEq X] in
theorem info_nonneg {m : ℕ} {n : X × Fin 2 → ℕ} (hm : 0 < m) (hn : ∑ v, n v = m) :
    0 ≤ info m n :=
  mi_nonneg (isDist_distOf hm hn)

end CubeGod
