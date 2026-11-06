import CubeGod.Schedule.Basic

/-!
# Two-point steps

A two-point step uses, at each firing, either the empty setup or one fixed setup `a₀`. Working back
through it, each firing mixes a distribution with a
rearranged copy of itself: `mixY` for the second firing and `mixZ` for the first. `gainB` and
`gainA` are the entropy each firing adds.
-/

open Finset Real Filter Topology

set_option linter.unusedSectionVars false

namespace CubeGod

variable {X A G : Type*} [Fintype X] [DecidableEq X] [Fintype A] [DecidableEq A] [Zero A]

namespace CycleSystem

/-- `Y` for a two-point step, with `E` the permutation of the non-empty setup. -/
def mixY (E : Equiv.Perm X) (β : ℝ) (W : X → ℝ) : X → ℝ :=
  fun m ↦ (1 - β) * W m + β * W (E⁻¹ m)

/-- `Z` for a two-point step. -/
def mixZ (E : Equiv.Perm X) (α : ℝ) (Y : X → ℝ) : X → ℝ :=
  fun s ↦ (1 - α) * Y s + α * Y (E s)

variable {Γ : CycleSystem X A G}

omit [Fintype X] [DecidableEq X] in
theorem continuous_mixY {Y : Type*} [TopologicalSpace Y] (E : Equiv.Perm X) {f : Y → X → ℝ}
    {b : Y → ℝ} (hf : Continuous f) (hb : Continuous b) :
    Continuous fun y ↦ mixY E (b y) (f y) := by
  refine continuous_pi fun m ↦ ?_
  have h₁ : Continuous fun y ↦ f y m := (continuous_apply m).comp hf
  have h₂ : Continuous fun y ↦ f y (E⁻¹ m) := (continuous_apply (E⁻¹ m)).comp hf
  exact ((continuous_const.sub hb).mul h₁).add (hb.mul h₂)

omit [Fintype X] [DecidableEq X] in
theorem continuous_mixZ {Y : Type*} [TopologicalSpace Y] (E : Equiv.Perm X) {f : Y → X → ℝ}
    {a : Y → ℝ} (hf : Continuous f) (ha : Continuous a) :
    Continuous fun y ↦ mixZ E (a y) (f y) := by
  refine continuous_pi fun m ↦ ?_
  have h₁ : Continuous fun y ↦ f y m := (continuous_apply m).comp hf
  have h₂ : Continuous fun y ↦ f y (E m) := (continuous_apply (E m)).comp hf
  exact ((continuous_const.sub ha).mul h₁).add (ha.mul h₂)

/-- The entropy added by the second firing of a two-point step. -/
noncomputable def gainB (E : Equiv.Perm X) (W : X → ℝ) (β : ℝ) : ℝ := H (mixY E β W) - H W

/-- The entropy added by the first firing of a two-point step. -/
noncomputable def gainA (E : Equiv.Perm X) (W : X → ℝ) (α β : ℝ) : ℝ :=
  H (mixZ E α (mixY E β W)) - H (mixY E β W)

omit [DecidableEq X] in
theorem continuous_gainA' (E : Equiv.Perm X) {Y : Type*} [TopologicalSpace Y] {f : Y → X → ℝ}
    {a b : Y → ℝ} (hf : Continuous f) (ha : Continuous a) (hb : Continuous b) :
    Continuous fun y ↦ gainA E (f y) (a y) (b y) := by
  have hY := continuous_mixY E hf hb
  have hZ := continuous_mixZ E hY ha
  exact ((continuous_H (α := X)).comp hZ).sub ((continuous_H (α := X)).comp hY)

omit [DecidableEq X] in
theorem continuous_gainB' (E : Equiv.Perm X) {Y : Type*} [TopologicalSpace Y] {f : Y → X → ℝ}
    {b : Y → ℝ} (hf : Continuous f) (hb : Continuous b) :
    Continuous fun y ↦ gainB E (f y) (b y) := by
  have hY := continuous_mixY E hf hb
  exact ((continuous_H (α := X)).comp hY).sub ((continuous_H (α := X)).comp hf)

omit [Fintype X] [DecidableEq X] in
theorem mixY_zero (E : Equiv.Perm X) (W : X → ℝ) : mixY E 0 W = W := by
  funext m; simp [mixY]

omit [Fintype X] [DecidableEq X] in
theorem mixZ_zero (E : Equiv.Perm X) (Y : X → ℝ) : mixZ E 0 Y = Y := by
  funext m; simp [mixZ]

omit [DecidableEq X] in
theorem gainB_zero (E : Equiv.Perm X) (W : X → ℝ) : gainB E W 0 = 0 := by
  simp [gainB, mixY_zero]

omit [DecidableEq X] in
theorem gainA_zero (E : Equiv.Perm X) (W : X → ℝ) (β : ℝ) : gainA E W 0 β = 0 := by
  simp [gainA, mixZ_zero]

/-- The distribution all on one point. -/
def point (x₀ : X) : X → ℝ := fun x ↦ if x = x₀ then 1 else 0

theorem H_point (x₀ : X) : H (point x₀) = 0 := by
  unfold H point
  have : ∀ x : X, negMulLog (if x = x₀ then (1 : ℝ) else 0) = 0 := by
    intro x
    split_ifs <;> simp
  simp [this]

end CycleSystem

end CubeGod
