import CubeGod.Cube.Stage1

/-!
# The lower bound

The oblique orbits can be set to any patterns independently, so there are at least `C^(N² - N)`
solvable states. Each is solved by a word of at most `D(n)` moves, and the word determines the state.
So `C^(N² - N) ≤ (number of words of length at most D(n))`.
-/

open Finset Real Filter Topology

namespace CubeGod

variable {n : ℕ}

/-- The layers of `I`. -/
def layerSet (n : ℕ) : Finset ℕ := Finset.Icc 2 (n / 2)

theorem mem_layerSet {d : ℕ} : d ∈ layerSet n ↔ InI n d := by
  simp only [layerSet, Finset.mem_Icc, InI]
  omega

theorem card_layerSet : #(layerSet n) = n / 2 - 1 := by
  simp [layerSet]

/-- The oblique orbits. -/
abbrev Oblique (n : ℕ) := {q : ℕ × ℕ // q ∈ (layerSet n).offDiag}

/-- An oblique orbit as an orbit. -/
def Oblique.name (q : Oblique n) : OrbitName n :=
  ⟨q.1, mem_layerSet.mp (Finset.mem_offDiag.mp q.2).1, mem_layerSet.mp (Finset.mem_offDiag.mp q.2).2.1⟩

theorem Oblique.name_inj : Function.Injective (Oblique.name (n := n)) := fun _ _ h ↦
  Subtype.ext (congrArg (fun q : OrbitName n ↦ q.1) h)

/-- A choice of a pattern for each oblique orbit. -/
abbrev Assign (n : ℕ) := Oblique n → {f : PosR → Face // Balanced f}

open Classical in
/-- The state with those patterns on the oblique orbits, and solved elsewhere. -/
noncomputable def stateOf (A : Assign n) : State n := fun E i j ↦
  if h : ∃ (q : Oblique n) (u : PosR), q.name.sticker u = (E, i, j) then
    (A h.choose).1 h.choose_spec.choose
  else E

theorem stateOf_sticker (A : Assign n) (q : Oblique n) (u : PosR) :
    (stateOf A).get (q.name.sticker u) = (A q).1 u := by
  classical
  have h : ∃ (q' : Oblique n) (u' : PosR), q'.name.sticker u' = q.name.sticker u := ⟨q, u, rfl⟩
  simp only [stateOf, State.get]
  rw [dite_eq_left h]
  obtain ⟨h₁, h₂⟩ := OrbitName.sticker_inj h.choose_spec.choose_spec
  have hq : h.choose = q := Oblique.name_inj h₁
  rw [h₂]
  rw [hq]

theorem stateOf_inj : Function.Injective (stateOf (n := n)) := by
  intro A A' h
  funext q
  apply Subtype.ext
  funext u
  have := congrArg (fun s : State n ↦ s.get (q.name.sticker u)) h
  rwa [stateOf_sticker, stateOf_sticker] at this

theorem stateOf_solvable (A : Assign n) : Solvable (stateOf A) := by
  obtain ⟨K, hK⟩ := factP2_oblique
  have hmem : ∀ q : Oblique n, (q.name : OrbitName n).1.1 ≠ q.name.1.2 := fun q ↦
    (Finset.mem_offDiag.mp q.2).2.2
  set l : List (OrbitName n) := (Finset.univ : Finset (Oblique n)).toList.map Oblique.name with hl
  have hnd : l.Nodup := (Finset.nodup_toList _).map Oblique.name_inj
  have hol : ∀ q ∈ l, ∃ q' : Oblique n, q'.name = q := by
    intro q hq
    obtain ⟨q', -, rfl⟩ := List.mem_map.mp hq
    exact ⟨q', rfl⟩
  have hcan : ∀ q ∈ l, CanSolve K q := by
    intro q hq s hs
    obtain ⟨q', rfl⟩ := hol q hq
    exact hK n _ _ q'.name.2.1 q'.name.2.2 (hmem q') s hs
  have hbal : ∀ q ∈ l, Balanced (q.view (stateOf A)) := by
    intro q hq
    obtain ⟨q', rfl⟩ := hol q hq
    have : q'.name.view (stateOf A) = (A q').1 := by
      funext u
      exact stateOf_sticker A q' u
    rw [this]
    exact (A q').2
  obtain ⟨w, -, h₁, h₂⟩ := solve_orbits l hnd hcan (stateOf A) hbal
  refine ⟨w, State.ext_get fun p ↦ ?_⟩
  by_cases hp : ∃ q ∈ l, ∃ u, p = q.sticker u
  · obtain ⟨q, hq, u, rfl⟩ := hp
    rw [h₁ q hq u]
    exact (solved_embed q.2.1 q.2.2 u.1).symm
  · push Not at hp
    rw [h₂ p hp]
    classical
    simp only [stateOf, State.get, solved]
    rw [dite_eq_right]
    rintro ⟨q, u, hqu⟩
    rw [show ((p.1, p.2.1, p.2.2) : Sticker n) = p from rfl] at hqu
    subst hqu
    exact hp _ (List.mem_map.mpr ⟨q, Finset.mem_toList.mpr (Finset.mem_univ q), rfl⟩) u rfl

theorem card_assign :
    Nat.card (Assign n) = patternCount ^ ((n / 2 - 1) * (n / 2 - 1) - (n / 2 - 1)) := by
  classical
  rw [Nat.card_pi]
  have hb : Nat.card {f : PosR → Face // Balanced f} = patternCount := by
    rw [Nat.card_eq_fintype_card, card_balanced card_posR solvedView_R]
  simp only [hb, Finset.prod_const, Finset.card_univ]
  congr 1
  rw [Fintype.card_coe, Finset.offDiag_card, card_layerSet]

/-- The counting bound behind the lower bound. -/
theorem pattern_pow_le (n : ℕ) :
    patternCount ^ ((n / 2 - 1) * (n / 2 - 1) - (n / 2 - 1)) ≤
      (Fintype.card (Move n) + 1) ^ godsNumber n := by
  classical
  have : Fintype (Assign n) := Fintype.ofFinite _
  rw [← card_assign, Nat.card_eq_fintype_card]
  set k := godsNumber n with hk
  have hword : ∀ A : Assign n, ∃ w : List (Move n), act w (stateOf A) = solved n ∧ w.length ≤ k :=
    fun A ↦ exists_word_le (stateOf_solvable A)
  choose W hW₁ hW₂ using hword
  -- A word of length at most `k` is a function from `Fin k` to `Option (Move n)`.
  have hinj : Function.Injective fun A : Assign n ↦ fun i : Fin k ↦ (W A)[(i : ℕ)]? := by
    intro A A' h
    have hw : W A = W A' := by
      apply List.ext_getElem?
      intro i
      by_cases hi : i < k
      · exact congrFun h ⟨i, hi⟩
      · rw [List.getElem?_eq_none (by have := hW₂ A; omega),
          List.getElem?_eq_none (by have := hW₂ A'; omega)]
    apply stateOf_inj
    have h₁ := act_eq (W A) (stateOf A)
    have h₂ := act_eq (W A') (stateOf A')
    rw [hW₁] at h₁ h₂
    rw [hw] at h₁
    refine State.ext_get fun p ↦ ?_
    have e₁ := congrFun h₁ (permW (W A') p)
    have e₂ := congrFun h₂ (permW (W A') p)
    simp only [Function.comp, Equiv.symm_apply_apply] at e₁ e₂
    rw [← e₁, ← e₂]
  have := Fintype.card_le_of_injective _ hinj
  simpa [Fintype.card_option] using this

theorem patternCount_ge_one : 1 ≤ patternCount := by
  unfold patternCount
  norm_num [Nat.factorial]

/-- The lower bound before dividing: `(n²/4 − 3n)·log C ≤ D(n)·(log n + log 13)`. -/
theorem lower_count (hn12 : 12 ≤ n) :
    ((n : ℝ) ^ 2 / 4 - 3 * n) * log patternCount ≤ godsNumber n * (log n + log 13) := by
  set A := log patternCount with hA
  have hC : (1 : ℝ) ≤ patternCount := by exact_mod_cast patternCount_ge_one
  have hA₀ : 0 ≤ A := log_nonneg hC
  have hn₀ : (0 : ℝ) < n := by positivity
  set N := n / 2 - 1 with hN
  set k := godsNumber n with hk
  set X := N * N - N with hX
  have hNnat : n ≤ 2 * N + 3 := by omega
  have hNge : ((n : ℝ) - 3) / 2 ≤ N := by
    have : (n : ℝ) ≤ 2 * N + 3 := by exact_mod_cast hNnat
    linarith
  have hNle : N ≤ N * N := Nat.le_mul_self N
  have hXcast : (X : ℝ) = (N : ℝ) * N - N := by
    rw [hX, Nat.cast_sub hNle]
    push_cast
    ring
  -- The number of letters.
  set M := Fintype.card (Move n) + 1 with hM
  have hMreal : (M : ℝ) ≤ 13 * n := by
    have : M ≤ 13 * n := by rw [hM, card_move]; omega
    exact_mod_cast this
  have hMpos : (0 : ℝ) < M := by positivity
  have hlogM : log (M : ℝ) ≤ log n + log 13 := by
    have h₁ : log (M : ℝ) ≤ log (13 * n) := log_le_log hMpos hMreal
    rw [log_mul (by norm_num) hn₀.ne'] at h₁
    linarith
  -- Take logs of the counting bound.
  have hcount : (X : ℝ) * A ≤ k * log (M : ℝ) := by
    have h₁ : ((patternCount : ℝ)) ^ X ≤ (M : ℝ) ^ k := by
      exact_mod_cast pattern_pow_le n
    have h₂ := log_le_log (by positivity) h₁
    rwa [log_pow, log_pow] at h₂
  -- `X` is about `n²/4`.
  have hXge : (n : ℝ) ^ 2 / 4 - 3 * n ≤ X := by
    rw [hXcast]
    have h₀ : 0 ≤ ((N : ℝ) - ((n : ℝ) - 3) / 2) * ((N : ℝ) + ((n : ℝ) - 3) / 2 - 1) := by
      have : (12 : ℝ) ≤ n := by exact_mod_cast hn12
      apply mul_nonneg <;> linarith
    nlinarith
  calc ((n : ℝ) ^ 2 / 4 - 3 * n) * A ≤ X * A := mul_le_mul_of_nonneg_right hXge hA₀
    _ ≤ k * log (M : ℝ) := hcount
    _ ≤ k * (log n + log 13) := mul_le_mul_of_nonneg_left hlogM (by positivity)

/-- The constant in the error term of the lower bound. -/
noncomputable def lowerK : ℝ := log patternCount * (log 13 / 4 + 3)

/-- The lower bound, with an explicit error: `D(n) ≥ ¼·log C·n²/log n − K·n²/(log n)²`. -/
theorem lower_bound_explicit (hn12 : 12 ≤ n) :
    log patternCount / 4 * n ^ 2 / log n - lowerK * n ^ 2 / log n ^ 2 ≤ godsNumber n := by
  have hcount := lower_count hn12
  set A := log patternCount with hA
  set L := log 13 with hL
  set ℓ := log (n : ℝ) with hℓ
  set k : ℝ := (godsNumber n : ℝ) with hk
  have hC : (1 : ℝ) ≤ patternCount := by exact_mod_cast patternCount_ge_one
  have hA₀ : 0 ≤ A := log_nonneg hC
  have hL₀ : 0 < L := log_pos (by norm_num)
  have hn' : (12 : ℝ) ≤ n := by exact_mod_cast hn12
  have hℓ₀ : 0 < ℓ := log_pos (by linarith)
  have hℓn : ℓ ≤ n := log_le_self (Nat.cast_nonneg n)
  have hk₀ : 0 ≤ k := by positivity
  rw [lowerK, ← hA, ← hL, div_sub_div _ _ hℓ₀.ne' (by positivity), div_le_iff₀ (by positivity)]
  -- Multiply the counting bound through by `ℓ²` and compare.
  have h₁ : ((n : ℝ) ^ 2 / 4 - 3 * n) * A * ℓ ^ 2 ≤ k * (ℓ + L) * ℓ ^ 2 :=
    mul_le_mul_of_nonneg_right hcount (by positivity)
  have h₂ : 0 ≤ A * (n : ℝ) * (3 * n * ℓ - 3 * ℓ ^ 2) := by
    have : 0 ≤ 3 * (n : ℝ) * ℓ - 3 * ℓ ^ 2 := by nlinarith
    positivity
  have h₃ : 0 ≤ A * (n : ℝ) ^ 2 * (L ^ 2 / 4 + 3 * L) := by positivity
  nlinarith

end CubeGod
