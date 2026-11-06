import CubeGod.Exact.Blind
import CubeGod.Exact.Path

/-!
# The merge

The merge takes any type `n₀` near uniform to a given type `z` near uniform, exactly, by firings
that carry little. Its steps go round and round all the 3-cycles of the kind, `allG`, in a fixed
order; each step is two firings, with `σ = e g 1` and then `σ⁻¹`.

* The first `r₀` rounds are **blind**: each firing sends half of every count through, rounded up
  (`blindJ`). They mix the type towards uniform by a factor `λ` per round, in squared length.
* The last `L₀` rounds **correct**: they follow the blind rule too, plus, for each pattern `y`, the
  surplus `c y = z y − (where the blind flow ends)` carried along a **route** from a fixed `x₀` to
  `y`, and taken back along the straight route at `x₀`. A route exists because every pattern is
  `x₀` moved by at most `L₀` 3-cycles, one per round (`reach_word`).

Every firing's joint type is then within a small factor of half its input, so it carries little
information, by `mi_le_of_near`.
-/

open Finset Real

set_option linter.unusedSectionVars false

namespace CubeGod

variable {X : Type*} [Fintype X] [DecidableEq X]

/-! ### Walks through the firings -/

/-- Where an entry starting at `x` before firing `f₀` is after `j` firings, if it moves at firing
`f` exactly when `β f = 1`. -/
def walkPos (ps : ℕ → Equiv.Perm X) (β : ℕ → Fin 2) (f₀ : ℕ) (x : X) : ℕ → X
  | 0 => x
  | j + 1 => if β (f₀ + j) = 1 then ps (f₀ + j) (walkPos ps β f₀ x j) else walkPos ps β f₀ x j

omit [Fintype X] [DecidableEq X] in
theorem walkPos_add (ps : ℕ → Equiv.Perm X) (β : ℕ → Fin 2) (f₀ : ℕ) (x : X) (j₁ j₂ : ℕ) :
    walkPos ps β f₀ x (j₁ + j₂) = walkPos ps β (f₀ + j₁) (walkPos ps β f₀ x j₁) j₂ := by
  induction j₂ with
  | zero => rfl
  | succ j ih => rw [← add_assoc, walkPos, ih, walkPos, add_assoc]

omit [Fintype X] [DecidableEq X] in
theorem walkPos_congr (ps : ℕ → Equiv.Perm X) {β β' : ℕ → Fin 2} (f₀ : ℕ) (x : X) (j : ℕ)
    (h : ∀ j' < j, β (f₀ + j') = β' (f₀ + j')) : walkPos ps β f₀ x j = walkPos ps β' f₀ x j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    simp only [walkPos]
    rw [ih fun j' hj' ↦ h j' (by omega), h j (by omega)]

omit [Fintype X] [DecidableEq X] in
theorem walkPos_stay (ps : ℕ → Equiv.Perm X) {β : ℕ → Fin 2} (f₀ : ℕ) (x : X) (j : ℕ)
    (h : ∀ j' < j, β (f₀ + j') = 0) : walkPos ps β f₀ x j = x := by
  induction j with
  | zero => rfl
  | succ j ih =>
    simp only [walkPos, h j (by omega), ih fun j' hj' ↦ h j' (by omega)]
    simp

/-- `y` can be reached from `x` in the `j` firings from `f₀`. -/
def Reach (ps : ℕ → Equiv.Perm X) (f₀ j : ℕ) (x y : X) : Prop := ∃ β, walkPos ps β f₀ x j = y

omit [Fintype X] [DecidableEq X] in
theorem Reach.refl (ps : ℕ → Equiv.Perm X) (f₀ j : ℕ) (x : X) : Reach ps f₀ j x x :=
  ⟨fun _ ↦ 0, walkPos_stay ps f₀ x j fun _ _ ↦ rfl⟩

omit [Fintype X] [DecidableEq X] in
theorem Reach.trans {ps : ℕ → Equiv.Perm X} {f₀ j₁ j₂ : ℕ} {x y z : X} (h₁ : Reach ps f₀ j₁ x y)
    (h₂ : Reach ps (f₀ + j₁) j₂ y z) : Reach ps f₀ (j₁ + j₂) x z := by
  obtain ⟨β₁, hβ₁⟩ := h₁
  obtain ⟨β₂, hβ₂⟩ := h₂
  refine ⟨fun f ↦ if f < f₀ + j₁ then β₁ f else β₂ f, ?_⟩
  rw [walkPos_add, walkPos_congr ps f₀ x j₁ (β' := β₁) fun j' hj' ↦ by simp [show f₀ + j' < f₀ + j₁ by omega],
    hβ₁, walkPos_congr ps (f₀ + j₁) y j₂ (β' := β₂) fun j' _ ↦ by simp, hβ₂]

omit [Fintype X] [DecidableEq X] in
theorem Reach.move (ps : ℕ → Equiv.Perm X) (f₀ : ℕ) (x : X) : Reach ps f₀ 1 x (ps f₀ x) :=
  ⟨fun _ ↦ 1, by simp [walkPos]⟩

/-! ### The merge's firings -/

variable {G : Type*} [Fintype G] [DecidableEq G]

/-- All the 3-cycles, in a fixed order. -/
noncomputable def allG (G : Type*) [Fintype G] : List G := (Finset.univ : Finset G).toList

omit [DecidableEq G] in
theorem mem_allG (g : G) : g ∈ allG G := Finset.mem_toList.mpr (Finset.mem_univ g)

omit [DecidableEq G] in
theorem length_allG_pos [Nonempty G] : 0 < (allG G).length := by
  rw [allG, Finset.length_toList]; exact Finset.card_pos.mpr Finset.univ_nonempty

/-- The 3-cycle of step `t` of the merge. -/
noncomputable def mergeG [Nonempty G] (t : ℕ) : G :=
  (allG G)[t % (allG G).length]'(Nat.mod_lt _ length_allG_pos)

namespace CycleSystem

variable (Γ : CycleSystem X (Fin 2) G)

/-- The permutation of firing `f` of the merge. -/
noncomputable def mergeP [Nonempty G] (f : ℕ) : Equiv.Perm X :=
  if f % 2 = 0 then Γ.e (mergeG (f / 2)) 1 else (Γ.e (mergeG (f / 2)) 1)⁻¹

/-- The length of a round, in firings. -/
noncomputable def roundLen (G : Type*) [Fintype G] : ℕ := 2 * (allG G).length

omit [Fintype X] [DecidableEq X] [DecidableEq G] in
theorem mergeP_periodic [Nonempty G] (f k : ℕ) :
    Γ.mergeP (f + k * roundLen G) = Γ.mergeP f := by
  have hk : k * roundLen G = 2 * (k * (allG G).length) := by unfold roundLen; ring
  have e₁ : (f + k * roundLen G) % 2 = f % 2 := by rw [hk]; omega
  have e₂ : (f + k * roundLen G) / 2 = f / 2 + k * (allG G).length := by rw [hk]; omega
  have e₃ : mergeG (G := G) (f / 2 + k * (allG G).length) = mergeG (f / 2) := by
    unfold mergeG; congr 1; simp [Nat.add_mul_mod_self_right]
  unfold mergeP; rw [e₁, e₂, e₃]

/-- The firings of one round. -/
noncomputable def roundList [Nonempty G] : List (Equiv.Perm X) :=
  List.ofFn fun j : Fin (roundLen G) ↦ Γ.mergeP j

omit [Fintype X] [DecidableEq X] [DecidableEq G] in
/-- In each round, an entry can move by any one 3-cycle. -/
theorem reach_round [Nonempty G] (k : ℕ) (g : G) (x : X) :
    Reach Γ.mergeP (k * roundLen G) (roundLen G) x (Γ.e g 1 x) := by
  obtain ⟨i, hi, hgi⟩ := List.getElem_of_mem (mem_allG g)
  have hP : Γ.mergeP (k * roundLen G + 2 * i) = Γ.e g 1 := by
    rw [add_comm, Γ.mergeP_periodic]
    unfold mergeP mergeG
    have h₁ : 2 * i % 2 = 0 := by omega
    have h₂ : 2 * i / 2 = i := by omega
    simp only [h₁, h₂, ite_true, Nat.mod_eq_of_lt hi, hgi]
  have h₁ := Reach.refl Γ.mergeP (k * roundLen G) (2 * i) x
  have h₂ := Reach.move Γ.mergeP (k * roundLen G + 2 * i) x
  rw [hP] at h₂
  have h₃ := Reach.refl Γ.mergeP (k * roundLen G + (2 * i + 1)) (roundLen G - (2 * i + 1))
    (Γ.e g 1 x)
  have h := (h₁.trans h₂).trans h₃
  have hlen : 2 * i + 1 ≤ roundLen G := by unfold roundLen; omega
  rwa [Nat.add_sub_cancel' hlen] at h

/-- Move by a list of 3-cycles, first to last. -/
def applyL : List G → X → X
  | [], x => x
  | g :: l, x => applyL l (Γ.e g 1 x)

omit [Fintype X] [DecidableEq X] [Fintype G] [DecidableEq G] in
theorem applyL_append (l₁ l₂ : List G) (x : X) :
    Γ.applyL (l₁ ++ l₂) x = Γ.applyL l₂ (Γ.applyL l₁ x) := by
  induction l₁ generalizing x with
  | nil => rfl
  | cons g l ih => exact ih _

omit [Fintype X] [DecidableEq X] [DecidableEq G] in
/-- In `K` rounds, an entry can move by any list of at most `K` 3-cycles. -/
theorem reach_word [Nonempty G] (l : List G) :
    ∀ K, l.length ≤ K → ∀ k x, Reach Γ.mergeP (k * roundLen G) (K * roundLen G) x (Γ.applyL l x) := by
  induction l with
  | nil => intro K _ k x; exact Reach.refl _ _ _ _
  | cons g l ih =>
    intro K hK k x
    obtain ⟨K', rfl⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by simp at hK; omega⟩
    have h₁ := Γ.reach_round k g x
    have h₂ := ih K' (by simp at hK; omega) (k + 1) (Γ.e g 1 x)
    rw [show (k + 1) * roundLen G = k * roundLen G + roundLen G by ring] at h₂
    have h := h₁.trans h₂
    rwa [show roundLen G + K' * roundLen G = (K' + 1) * roundLen G by ring] at h

omit [DecidableEq X] [Fintype G] [DecidableEq G] in
/-- Fact T with a bound: every pattern is any other moved by at most `L₀` 3-cycles. -/
theorem exists_applyL_bound [Finite (Equiv.Perm X)] :
    ∃ L₀ : ℕ, ∀ x y, ∃ l : List G, l.length ≤ L₀ ∧ Γ.applyL l x = y := by
  classical
  have hw : ∀ w ∈ Subgroup.closure (Set.range (Function.uncurry Γ.e)), ∃ l : List G,
      ∀ x, Γ.applyL l x = w x := by
    intro w hw
    have hw' : w ∈ Submonoid.closure (Set.range (Function.uncurry Γ.e)) := by
      rw [← Subgroup.closure_toSubmonoid_of_finite]; exact hw
    clear hw
    induction hw' using Submonoid.closure_induction with
    | mem w hw =>
      obtain ⟨⟨g, a⟩, rfl⟩ := hw
      rcases fin2_cases a with rfl | rfl
      · exact ⟨[], fun x ↦ by simp [applyL, Γ.e_zero]⟩
      · exact ⟨[g], fun x ↦ rfl⟩
    | one => exact ⟨[], fun x ↦ rfl⟩
    | mul w₁ w₂ _ _ h₁ h₂ =>
      obtain ⟨l₁, hl₁⟩ := h₁
      obtain ⟨l₂, hl₂⟩ := h₂
      exact ⟨l₂ ++ l₁, fun x ↦ by rw [applyL_append, hl₂, hl₁]; rfl⟩
  have hxy : ∀ p : X × X, ∃ l : List G, Γ.applyL l p.1 = p.2 := by
    intro p
    obtain ⟨w, hwm, hwx⟩ := Γ.trans p.1 p.2
    obtain ⟨l, hl⟩ := hw w hwm
    exact ⟨l, by rw [hl, hwx]⟩
  choose f hf using hxy
  exact ⟨(Finset.univ : Finset (X × X)).sup fun p ↦ (f p).length, fun x y ↦
    ⟨f (x, y), Finset.le_sup (f := fun p ↦ (f p).length) (Finset.mem_univ _), hf (x, y)⟩⟩

end CycleSystem

/-! ### Corrections along routes -/

/-- One entry at `p` with bit `b`. -/
def ind (p : X) (b : Fin 2) (v : X × Fin 2) : ℤ := if v = (p, b) then 1 else 0

/-- The input type of an integer joint type. -/
def inZ (J : X × Fin 2 → ℤ) (x : X) : ℤ := J (x, 0) + J (x, 1)

/-- The output type of an integer joint type. -/
def outZ (σ : Equiv.Perm X) (J : X × Fin 2 → ℤ) (y : X) : ℤ := J (y, 0) + J (σ⁻¹ y, 1)

omit [Fintype X] in
theorem inZ_ind (p : X) (b : Fin 2) (x : X) : inZ (ind p b) x = if x = p then 1 else 0 := by
  unfold inZ ind
  rcases fin2_cases b with rfl | rfl <;> by_cases h : x = p <;> simp [h]

omit [Fintype X] in
theorem outZ_ind (σ : Equiv.Perm X) (p : X) (b : Fin 2) (y : X) :
    outZ σ (ind p b) y = if y = (if b = 1 then σ p else p) then 1 else 0 := by
  unfold outZ ind
  rcases fin2_cases b with rfl | rfl
  · by_cases h : y = p <;> simp [h]
  · by_cases h : y = σ p
    · simp [h]
    · have : σ⁻¹ y ≠ p := fun h' ↦ h (by rw [← h']; simp)
      simp [h]
      exact this

/-- The correction at the `j`-th correcting firing: `c y` entries along the route of `y`, and
`−c y` along the straight route at `x₀`. -/
def corrJ (ps : ℕ → Equiv.Perm X) (f₀ : ℕ) (x₀ : X) (β : X → ℕ → Fin 2) (c : X → ℤ) (j : ℕ)
    (v : X × Fin 2) : ℤ :=
  ∑ y, c y * (ind (walkPos ps (β y) f₀ x₀ j) (β y (f₀ + j)) v - ind x₀ 0 v)

/-- What the corrections add to the type before the `j`-th correcting firing. -/
def corrU (ps : ℕ → Equiv.Perm X) (f₀ : ℕ) (x₀ : X) (β : X → ℕ → Fin 2) (c : X → ℤ) (j : ℕ)
    (x : X) : ℤ :=
  ∑ y, c y * ((if x = walkPos ps (β y) f₀ x₀ j then 1 else 0) - (if x = x₀ then 1 else 0))

variable (ps : ℕ → Equiv.Perm X) (f₀ : ℕ) (x₀ : X) (β : X → ℕ → Fin 2) (c : X → ℤ)

theorem inZ_corrJ (j : ℕ) : inZ (corrJ ps f₀ x₀ β c j) = corrU ps f₀ x₀ β c j := by
  funext x
  have h := fun y ↦ inZ_ind (walkPos ps (β y) f₀ x₀ j) (β y (f₀ + j)) x
  have h₀ := inZ_ind x₀ 0 x
  simp only [inZ] at h h₀
  simp only [inZ, corrJ, corrU, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun y _ ↦ ?_
  rw [← h y, ← h₀]; ring

theorem outZ_corrJ (j : ℕ) :
    outZ (ps (f₀ + j)) (corrJ ps f₀ x₀ β c j) = corrU ps f₀ x₀ β c (j + 1) := by
  funext x
  have h := fun y ↦ outZ_ind (ps (f₀ + j)) (walkPos ps (β y) f₀ x₀ j) (β y (f₀ + j)) x
  have h₀ := outZ_ind (ps (f₀ + j)) x₀ 0 x
  rw [ite_eq_right (by decide : ¬ ((0 : Fin 2) = 1))] at h₀
  simp only [outZ] at h h₀
  simp only [outZ, corrJ, corrU, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun y _ ↦ ?_
  have e : walkPos ps (β y) f₀ x₀ (j + 1) = if β y (f₀ + j) = 1 then
      ps (f₀ + j) (walkPos ps (β y) f₀ x₀ j) else walkPos ps (β y) f₀ x₀ j := rfl
  rw [e, ← h y, ← h₀]
  ring

theorem corrU_zero : corrU ps f₀ x₀ β c 0 = 0 := by
  funext x
  refine Finset.sum_eq_zero fun y _ ↦ ?_
  rw [mul_eq_zero]; right; rw [sub_eq_zero]; rfl

theorem corrU_end {K : ℕ} (hβ : ∀ y, walkPos ps (β y) f₀ x₀ K = y) (hc : ∑ y, c y = 0) :
    corrU ps f₀ x₀ β c K = c := by
  funext x
  simp only [corrU, hβ, mul_sub, Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  by_cases hx : x = x₀ <;> simp [hx, hc]

theorem sum_corrU (j : ℕ) : ∑ x, corrU ps f₀ x₀ β c j x = 0 := by
  unfold corrU
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun y _ ↦ ?_
  rw [← Finset.mul_sum, Finset.sum_sub_distrib]
  simp

theorem abs_corrJ_le (j : ℕ) (v : X × Fin 2) : |corrJ ps f₀ x₀ β c j v| ≤ ∑ y, |c y| := by
  unfold corrJ
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun y _ ↦ ?_)
  rw [abs_mul]
  have : |ind (walkPos ps (β y) f₀ x₀ j) (β y (f₀ + j)) v - ind x₀ 0 v| ≤ 1 := by
    unfold ind; split_ifs <;> simp
  nlinarith [abs_nonneg (c y)]

/-- The merge's joint types, as integers: the blind flow, plus the corrections from firing
`f₀` on. -/
def mJ (n₀ : X → ℕ) (f : ℕ) (v : X × Fin 2) : ℤ :=
  (blindJ (blindU ps n₀ f) v : ℤ) + if f₀ ≤ f then corrJ ps f₀ x₀ β c (f - f₀) v else 0

/-- The merge's types, as integers. -/
def mU (n₀ : X → ℕ) (f : ℕ) (x : X) : ℤ :=
  (blindU ps n₀ f x : ℤ) + if f₀ ≤ f then corrU ps f₀ x₀ β c (f - f₀) x else 0

theorem inZ_mJ (n₀ : X → ℕ) (f : ℕ) : inZ (mJ ps f₀ x₀ β c n₀ f) = mU ps f₀ x₀ β c n₀ f := by
  funext x
  have h₁ := congrFun (inT_blindJ (blindU ps n₀ f)) x
  have h₂ := congrFun (inZ_corrJ ps f₀ x₀ β c (f - f₀)) x
  unfold inT at h₁
  unfold inZ at h₂ ⊢
  unfold mJ mU
  split_ifs
  · rw [← h₂, ← h₁]; push_cast; ring
  · rw [← h₁]; push_cast; ring

theorem outZ_mJ (n₀ : X → ℕ) (f : ℕ) :
    outZ (ps f) (mJ ps f₀ x₀ β c n₀ f) = mU ps f₀ x₀ β c n₀ (f + 1) := by
  funext x
  have h₁ : (blindU ps n₀ (f + 1) x : ℤ) =
      (blindJ (blindU ps n₀ f) (x, 0) : ℤ) + (blindJ (blindU ps n₀ f) ((ps f)⁻¹ x, 1) : ℤ) := by
    simp only [blindU, outT]; push_cast; ring
  unfold outZ mJ mU
  by_cases hf : f₀ ≤ f
  · have h₂ := congrFun (outZ_corrJ ps f₀ x₀ β c (f - f₀)) x
    rw [show f₀ + (f - f₀) = f by omega] at h₂
    unfold outZ at h₂
    rw [ite_eq_left hf, ite_eq_left hf, ite_eq_left (by omega), h₁, show f + 1 - f₀ = f - f₀ + 1 by omega, ← h₂]
    ring
  · rw [ite_eq_right hf, ite_eq_right hf, h₁]
    by_cases hf' : f₀ ≤ f + 1
    · rw [ite_eq_left hf', show f + 1 - f₀ = 0 by omega, corrU_zero]; simp
    · rw [ite_eq_right hf']; ring

theorem sum_mU (n₀ : X → ℕ) (f : ℕ) : ∑ x, mU ps f₀ x₀ β c n₀ f x = ∑ x, (n₀ x : ℤ) := by
  unfold mU
  rw [Finset.sum_add_distrib]
  have h₁ : ∑ x, (blindU ps n₀ f x : ℤ) = ∑ x, (n₀ x : ℤ) := by
    exact_mod_cast sum_blindU ps n₀ f
  split_ifs
  · rw [h₁, sum_corrU, add_zero]
  · rw [h₁, Finset.sum_const_zero, add_zero]

end CubeGod
