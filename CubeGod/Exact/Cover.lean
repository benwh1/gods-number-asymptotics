import CubeGod.Exact.Types
import CubeGod.Code.Covering

/-!
# Exact covering

For a joint type `n` of `m` pairs (pattern, bit), there is a codebook of at most
`(m·ln C + 2)·(m + 1)^C·2^(m·I(n))` lists of `m` bits such that every list of patterns of the right
input type gets the joint type exactly `n` from some list in the codebook.

Draw each bit independently, `1` with the chance `t` of a `1` in `n`. For a list of patterns of the
right type, the bit lists that give exactly `n` are those that put exactly `n(x, 1)` ones on the
entries with pattern `x`, for each `x`: there are `∏ₓ (u(x) choose n(x, 1))` of them. Each binomial
coefficient is at least `2^(u·h)/(u + 1)`, which makes the chance of hitting `n` at least
`2^(−m·I(n))/(m + 1)^C`. Then enough random draws hit every list.
-/

open Finset Real

set_option linter.unusedSectionVars false

namespace CubeGod

/-! ### The binomial terms -/

/-- The term `(u choose i)·p^i·q^(u − i)` of the binomial theorem. -/
noncomputable def binT (u : ℕ) (p q : ℝ) (i : ℕ) : ℝ := (u.choose i : ℝ) * p ^ i * q ^ (u - i)

theorem binT_nonneg {u : ℕ} {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (i : ℕ) : 0 ≤ binT u p q i := by
  unfold binT; positivity

theorem binT_succ {u i : ℕ} (hi : i < u) (p q : ℝ) :
    binT u p q (i + 1) * (i + 1) * q = binT u p q i * ((u - i : ℕ) : ℝ) * p := by
  have hc := Nat.choose_succ_right_eq u i
  have hc' : ((u.choose (i + 1) : ℕ) : ℝ) * (i + 1) = (u.choose i : ℝ) * ((u - i : ℕ) : ℝ) := by
    exact_mod_cast hc
  have he : u - i = (u - (i + 1)) + 1 := by omega
  unfold binT
  have hp : p ^ (i + 1) = p ^ i * p := pow_succ p i
  have hq : q ^ (u - i) = q ^ (u - (i + 1)) * q := by rw [he, pow_succ]
  rw [hp, hq]
  linear_combination (p ^ i * p * q ^ (u - (i + 1)) * q) * hc'

/-- **The binomial mode.** With `p = b/(a + b)`, the term at `b` is at least `1/(a + b + 1)`. -/
theorem binT_mode (a b : ℕ) :
    1 / ((a + b : ℕ) + 1 : ℝ) ≤ binT (a + b) ((b : ℝ) / (a + b : ℕ)) ((a : ℝ) / (a + b : ℕ)) b := by
  rcases Nat.eq_zero_or_pos (a + b) with h0 | hpos
  · have ha : a = 0 := by omega
    have hb : b = 0 := by omega
    subst ha hb
    simp [binT]
  set u := a + b with hu
  have hu₀ : (0 : ℝ) < u := by exact_mod_cast hpos
  set p : ℝ := b / u with hp
  set q : ℝ := a / u with hq
  have hp₀ : 0 ≤ p := by positivity
  have hq₀ : 0 ≤ q := by positivity
  have hu' : (u : ℝ) = a + b := by rw [hu]; push_cast; ring
  have hpq : p + q = 1 := by
    rw [hp, hq, ← add_div, div_eq_one_iff_eq hu₀.ne', hu']; ring
  set T := binT u p q with hT
  -- The recursion, multiplied by `u`.
  have hR : ∀ i, i < u → T (i + 1) * (i + 1) * a = T i * ((u - i : ℕ) : ℝ) * b := by
    intro i hi
    have h := binT_succ hi p q
    have e₁ : T (i + 1) * (i + 1) * a = (T (i + 1) * (i + 1) * q) * u := by
      rw [hq]; field_simp
    have e₂ : T i * ((u - i : ℕ) : ℝ) * b = (T i * ((u - i : ℕ) : ℝ) * p) * u := by
      rw [hp]; field_simp
    rw [e₁, e₂, h]
  have hTn : ∀ i, 0 ≤ T i := binT_nonneg hp₀ hq₀
  -- Up to `b` the terms grow, after `b` they shrink.
  have hup : ∀ i, i < b → T i ≤ T (i + 1) := by
    intro i hi
    have hiu : i < u := by omega
    rcases Nat.eq_zero_or_pos a with ha | ha
    · -- `q = 0`, so every term below `u` is `0`.
      have hq0 : q = 0 := by rw [hq, ha]; simp
      have : T i = 0 := by
        rw [hT]; unfold binT
        rw [hq0, zero_pow (by omega), mul_zero]
      rw [this]; exact hTn _
    · have h := hR i hiu
      have hsub : ((u - i : ℕ) : ℝ) = u - i := by rw [Nat.cast_sub hiu.le]
      rw [hsub] at h
      have hineq : ((i : ℝ) + 1) * a ≤ (u - i) * b := by
        have : (i : ℝ) + 1 ≤ b := by exact_mod_cast hi
        have hu' : (u : ℝ) = a + b := by rw [hu]; push_cast; ring
        nlinarith
      have ha' : (0 : ℝ) < (i + 1) * a := by positivity
      by_contra hc
      push Not at hc
      have : T (i + 1) * (i + 1) * a < T i * ((i + 1) * a) := by
        have := mul_lt_mul_of_pos_right hc ha'
        linarith
      have h2 : T i * ((i + 1) * a) ≤ T i * ((u - i) * b) := mul_le_mul_of_nonneg_left hineq (hTn i)
      nlinarith
  have hdown : ∀ i, b ≤ i → i < u → T (i + 1) ≤ T i := by
    intro i hi hiu
    rcases Nat.eq_zero_or_pos b with hb | hb
    · have hp0 : p = 0 := by rw [hp, hb]; simp
      have : T (i + 1) = 0 := by
        rw [hT]; unfold binT
        rw [hp0, zero_pow (by omega), mul_zero, zero_mul]
      rw [this]; exact hTn _
    · have h := hR i hiu
      have hsub : ((u - i : ℕ) : ℝ) = u - i := by rw [Nat.cast_sub hiu.le]
      rw [hsub] at h
      have hineq : (u - i) * (b : ℝ) ≤ ((i : ℝ) + 1) * a := by
        have h₁ : (b : ℝ) ≤ i := by exact_mod_cast hi
        have h₂ : (i : ℝ) < u := by exact_mod_cast hiu
        have hu' : (u : ℝ) = a + b := by rw [hu]; push_cast; ring
        nlinarith
      have hb' : (0 : ℝ) < (u - i) * b := by
        have : (i : ℝ) < u := by exact_mod_cast hiu
        have : (0 : ℝ) < b := by exact_mod_cast hb
        nlinarith
      by_contra hc
      push Not at hc
      have h3 : T i * ((u - i) * b) < T (i + 1) * ((u - i) * b) := mul_lt_mul_of_pos_right hc hb'
      have h4 : T (i + 1) * ((u - i) * b) ≤ T (i + 1) * ((i + 1) * a) :=
        mul_le_mul_of_nonneg_left hineq (hTn _)
      nlinarith
  have hle₁ : ∀ d i, i + d = b → T i ≤ T b := by
    intro d
    induction d with
    | zero => intro i hi; rw [← hi]; rfl
    | succ d ih =>
      intro i hi
      exact (hup i (by omega)).trans (ih (i + 1) (by omega))
  have hle₂ : ∀ d, b + d ≤ u → T (b + d) ≤ T b := by
    intro d
    induction d with
    | zero => intro _; rfl
    | succ d ih =>
      intro hd
      exact (hdown (b + d) (by omega) (by omega)).trans (ih (by omega))
  have hle : ∀ i, i ≤ u → T i ≤ T b := by
    intro i hiu
    rcases le_total i b with hib | hbi
    · exact hle₁ (b - i) i (by omega)
    · have := hle₂ (i - b) (by omega)
      rwa [Nat.add_sub_cancel' hbi] at this
  -- The terms add up to `1`.
  have hsum : ∑ i ∈ Finset.range (u + 1), T i = 1 := by
    have := add_pow p q u
    rw [hpq, one_pow] at this
    rw [this]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [hT]; unfold binT; ring
  have hb : b ≤ u := by omega
  have : (1 : ℝ) ≤ (u + 1) * T b := by
    calc (1 : ℝ) = ∑ i ∈ Finset.range (u + 1), T i := hsum.symm
      _ ≤ ∑ _i ∈ Finset.range (u + 1), T b :=
          Finset.sum_le_sum fun i hi ↦ hle i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))
      _ = (u + 1) * T b := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring
  rw [div_le_iff₀ (by positivity)]
  linarith

/-! ### Powers as exponentials -/

/-- `k·ln(k/M)`, with `0` when `k = 0`. -/
noncomputable def kLog (k M : ℝ) : ℝ := k * log (k / M)

theorem pow_eq_exp_kLog (k : ℕ) {M : ℝ} (hM : 0 < M) :
    ((k : ℝ) / M) ^ k = exp (kLog k M) := by
  unfold kLog
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  · have : (0 : ℝ) < k / M := by positivity
    rw [Real.exp_nat_mul, Real.exp_log this]

theorem kLog_split {k u M : ℝ} (hk : 0 ≤ k) (hku : 0 < k → 0 < u) (hM : 0 < M) :
    kLog k u = kLog k M - k * log (u / M) := by
  unfold kLog
  rcases hk.eq_or_lt with rfl | hk'
  · simp
  · have hu := hku hk'
    rw [log_div hk'.ne' hu.ne', log_div hk'.ne' hM.ne', log_div hu.ne' hM.ne']
    ring

theorem kLog_eq_negMulLog {k M : ℝ} (hM : 0 < M) : kLog k M = -(M * negMulLog (k / M)) := by
  unfold kLog negMulLog
  field_simp

variable {X ι : Type*} [Fintype X] [DecidableEq X] [Fintype ι] [DecidableEq ι]

/-! ### Counting the bit lists that give a joint type -/

/-- The bit lists that give the joint type `n` to `s`. -/
def fitSet (s : ι → X) (n : X × Fin 2 → ℕ) : Finset (ι → Fin 2) :=
  univ.filter fun b ↦ jointType s b = n

theorem card_fitSet {s : ι → X} {n : X × Fin 2 → ℕ} (hs : typeOf s = inT n) :
    #(fitSet s n) = ∏ x, (inT n x).choose (n (x, 1)) := by
  classical
  set F : X → Finset ι := fun x ↦ univ.filter fun k ↦ s k = x with hF
  have hFc : ∀ x, #(F x) = inT n x := fun x ↦ by rw [← hs]; rfl
  have htarget : (∏ x, (inT n x).choose (n (x, 1))) =
      #(Fintype.piFinset fun x ↦ (F x).powersetCard (n (x, 1))) := by
    rw [Fintype.card_piFinset]
    exact Finset.prod_congr rfl fun x _ ↦ by rw [Finset.card_powersetCard, hFc]
  rw [htarget]
  refine Finset.card_nbij' (fun b x ↦ univ.filter fun k ↦ s k = x ∧ b k = 1)
    (fun S k ↦ if k ∈ S (s k) then 1 else 0) ?_ ?_ ?_ ?_
  · intro b hb
    rw [Finset.mem_coe, fitSet, Finset.mem_filter] at hb
    rw [Finset.mem_coe, Fintype.mem_piFinset]
    intro x
    rw [Finset.mem_powersetCard]
    refine ⟨fun k hk ↦ ?_, ?_⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hk).2.1⟩
    · rw [← hb.2]; rfl
  · intro S hS
    rw [Finset.mem_coe, Fintype.mem_piFinset] at hS
    simp only [Finset.mem_powersetCard] at hS
    rw [Finset.mem_coe, fitSet, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    have hsub : ∀ x, ∀ k ∈ S x, s k = x := fun x k hk ↦ by
      have := (hS x).1 hk
      simpa [hF] using this
    funext v
    obtain ⟨x, i⟩ := v
    rcases fin2_cases i with rfl | rfl
    · -- The entries with pattern `x` not in `S x`.
      have e : (univ.filter fun k ↦ s k = x ∧ (if k ∈ S (s k) then (1 : Fin 2) else 0) = 0) =
          F x \ S x := by
        ext k
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff, hF]
        constructor
        · rintro ⟨h₁, h₂⟩
          refine ⟨h₁, fun hk ↦ ?_⟩
          rw [h₁] at h₂
          simp [hk] at h₂
        · rintro ⟨h₁, h₂⟩
          refine ⟨h₁, ?_⟩
          rw [h₁]
          simp [h₂]
      change #(univ.filter fun k ↦ s k = x ∧ (if k ∈ S (s k) then (1 : Fin 2) else 0) = 0) = _
      rw [e, Finset.card_sdiff_of_subset (hS x).1, hFc, (hS x).2]
      simp [inT]
    · have e : (univ.filter fun k ↦ s k = x ∧ (if k ∈ S (s k) then (1 : Fin 2) else 0) = 1) =
          S x := by
        ext k
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨h₁, h₂⟩
          rw [h₁] at h₂
          by_contra hk
          simp [hk] at h₂
        · intro hk
          have := hsub x k hk
          refine ⟨this, ?_⟩
          rw [this]
          simp [hk]
      change #(univ.filter fun k ↦ s k = x ∧ (if k ∈ S (s k) then (1 : Fin 2) else 0) = 1) = _
      rw [e, (hS x).2]
  · intro b _
    funext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases fin2_cases (b k) with h | h <;> simp [h]
  · intro S hS
    rw [Finset.mem_coe, Fintype.mem_piFinset] at hS
    simp only [Finset.mem_powersetCard] at hS
    funext x
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨h₁, h₂⟩
      rw [h₁] at h₂
      by_contra hk
      simp [hk] at h₂
    · intro hk
      have : s k = x := by simpa [hF] using (hS x).1 hk
      refine ⟨this, ?_⟩
      rw [this]
      simp [hk]

/-! ### The chance of hitting a joint type -/

/-- The number of ones and of zeros in a joint type. -/
def onesOf (n : X × Fin 2 → ℕ) (i : Fin 2) : ℕ := ∑ x, n (x, i)

/-- Independent bits, each `1` with the chance of a `1` in `n`. -/
noncomputable def bitW (m : ℕ) (n : X × Fin 2 → ℕ) (b : ι → Fin 2) : ℝ :=
  ∏ k, ((onesOf n (b k) : ℝ) / m)

omit [DecidableEq X] in
theorem onesOf_sum (n : X × Fin 2 → ℕ) : ∑ i, onesOf n i = ∑ v, n v := by
  rw [Fintype.sum_prod_type_right]; rfl

omit [DecidableEq X] in
theorem isDist_bitW {m : ℕ} {n : X × Fin 2 → ℕ} (hm : 0 < m) (hn : ∑ v, n v = m) :
    IsDist (bitW (ι := ι) m n) := by
  refine ⟨fun b ↦ Finset.prod_nonneg fun k _ ↦ by positivity, ?_⟩
  unfold bitW
  rw [← Fintype.prod_sum (fun (_ : ι) (i : Fin 2) ↦ (onesOf n i : ℝ) / m)]
  have : ∑ i, (onesOf n i : ℝ) / m = 1 := by
    rw [← Finset.sum_div]
    have h : ((∑ i, onesOf n i : ℕ) : ℝ) = m := by rw [onesOf_sum, hn]
    push_cast at h
    rw [h, div_self (by exact_mod_cast hm.ne')]
  simp [this]

omit [DecidableEq ι] in
theorem bitW_of_fit {m : ℕ} {n : X × Fin 2 → ℕ} {s : ι → X} {b : ι → Fin 2}
    (hb : jointType s b = n) :
    bitW m n b = ∏ i, ((onesOf n i : ℝ) / m) ^ onesOf n i := by
  unfold bitW
  have hk : ∀ k, (onesOf n (b k) : ℝ) / m =
      if b k = 0 then (onesOf n 0 : ℝ) / m else (onesOf n 1 : ℝ) / m := by
    intro k; rcases fin2_cases (b k) with h | h <;> simp [h]
  have hcnt : ∀ i, #(univ.filter fun k ↦ b k = i) = onesOf n i := by
    intro i
    rw [onesOf, ← hb]
    unfold jointType
    rw [Finset.card_eq_sum_card_fiberwise (f := s) (t := univ) (fun _ _ ↦ Finset.mem_univ _)]
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    congr 1
    ext k
    simp [and_comm]
  rw [Finset.prod_congr rfl fun k _ ↦ hk k, Finset.prod_ite, Finset.prod_const, Finset.prod_const,
    Fin.prod_univ_two, hcnt 0]
  have : (univ.filter fun k ↦ ¬ b k = 0) = univ.filter fun k ↦ b k = 1 := by
    ext k; rcases fin2_cases (b k) with h | h <;> simp [h]
  rw [this, hcnt 1]

omit [Fintype X] [DecidableEq X] in
theorem sum_inT_eq (n : X × Fin 2 → ℕ) (x : X) : ∑ i, n (x, i) = inT n x := by
  simp [inT, Fin.sum_univ_two]

omit [DecidableEq X] in
theorem exponent_eq {m : ℕ} {n : X × Fin 2 → ℕ} (hι : 0 < m) :
    ∑ i, kLog (onesOf n i) m = -(m * log 2 * info m n) +
      ∑ x, (kLog (n (x, 1)) (inT n x) + kLog (n (x, 0)) (inT n x)) := by
  have hm : (0 : ℝ) < m := by exact_mod_cast hι
  set A := ∑ x, negMulLog ((inT n x : ℝ) / m) with hA
  set B := ∑ i, negMulLog ((onesOf n i : ℝ) / m) with hB
  set D := ∑ v, negMulLog ((n v : ℝ) / m) with hD
  -- (1) the information.
  have h₁ : m * log 2 * info m n = m * (A + B - D) := by
    have e₁ : (fun a ↦ ∑ b, distOf m n (a, b)) = fun x ↦ (inT n x : ℝ) / m := by
      funext x; unfold distOf; rw [← Finset.sum_div]; congr 1; exact_mod_cast sum_inT_eq n x
    have e₂ : (fun b ↦ ∑ a, distOf m n (a, b)) = fun i ↦ (onesOf n i : ℝ) / m := by
      funext i; unfold distOf onesOf; rw [← Finset.sum_div]; push_cast; rfl
    unfold info mi
    rw [e₁, e₂]
    unfold H distOf
    have := log_two_pos'
    field_simp
    rw [hA, hB, hD]
  -- (2) the bits.
  have h₂ : ∑ i, kLog (onesOf n i) m = -(m * B) := by
    rw [hB, Finset.mul_sum, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun i _ ↦ kLog_eq_negMulLog hm
  -- (3) the patterns.
  have hsplit : ∀ x i, kLog (n (x, i)) (inT n x) =
      kLog (n (x, i)) m - n (x, i) * log (inT n x / m) := by
    intro x i
    refine kLog_split (by positivity) (fun h ↦ ?_) hm
    have hle : n (x, i) ≤ inT n x := by
      unfold inT; rcases fin2_cases i with rfl | rfl <;> omega
    have hle' : (n (x, i) : ℝ) ≤ inT n x := by exact_mod_cast hle
    linarith
  have hD' : ∑ x, (kLog (n (x, 1)) m + kLog (n (x, 0)) m) = -(m * D) := by
    rw [hD, Fintype.sum_prod_type, Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    rw [Fin.sum_univ_two, kLog_eq_negMulLog hm, kLog_eq_negMulLog hm]
    ring
  have hA' : ∑ x, ((n (x, 1) : ℝ) * log (inT n x / m) + n (x, 0) * log (inT n x / m)) =
      -(m * A) := by
    rw [hA, Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    have := kLog_eq_negMulLog (k := inT n x) hm
    unfold kLog at this
    rw [← this]
    simp [inT]; ring
  have h₃ : ∑ x, (kLog (n (x, 1)) (inT n x) + kLog (n (x, 0)) (inT n x)) = -(m * D) + m * A := by
    simp only [hsplit]
    have e : ∀ x, kLog (n (x, 1)) m - n (x, 1) * log (inT n x / m) +
        (kLog (n (x, 0)) m - n (x, 0) * log (inT n x / m)) =
        (kLog (n (x, 1)) m + kLog (n (x, 0)) m) -
          ((n (x, 1) : ℝ) * log (inT n x / m) + n (x, 0) * log (inT n x / m)) := fun x ↦ by ring
    rw [Finset.sum_congr rfl fun x _ ↦ e x, Finset.sum_sub_distrib, hD', hA']
    ring
  rw [h₂, h₁, h₃]
  ring

/-- The chance that independent bits give a list of patterns of the right type exactly the joint
type `n` is at least `exp(−m·ln 2·I(n))/(m + 1)^C`. -/
theorem fit_chance_ge {n : X × Fin 2 → ℕ} (hn : ∑ v, n v = Fintype.card ι)
    (hι : 0 < Fintype.card ι) {s : ι → X} (hs : typeOf s = inT n) :
    exp (-(Fintype.card ι * log 2 * info (Fintype.card ι) n)) /
        ((Fintype.card ι : ℝ) + 1) ^ Fintype.card X ≤
      ∑ b ∈ fitSet s n, bitW (Fintype.card ι) n b := by
  set m := Fintype.card ι with hmdef
  have hm : (0 : ℝ) < m := by exact_mod_cast hι
  -- Every list that fits has the same chance.
  have hconst : ∑ b ∈ fitSet s n, bitW m n b =
      #(fitSet s n) * ∏ i, ((onesOf n i : ℝ) / m) ^ onesOf n i := by
    have h : ∑ b ∈ fitSet s n, bitW m n b =
        ∑ _b ∈ fitSet s n, ∏ i, ((onesOf n i : ℝ) / m) ^ onesOf n i :=
      Finset.sum_congr rfl fun b hb ↦ bitW_of_fit (by
        unfold fitSet at hb; exact (Finset.mem_filter.mp hb).2)
    rw [h, Finset.sum_const, nsmul_eq_mul]
  rw [hconst, card_fitSet hs]
  push_cast
  -- The binomial bound for each pattern.
  have hbin : ∀ x, 1 / ((inT n x : ℝ) + 1) ≤ ((inT n x).choose (n (x, 1)) : ℝ) *
      exp (kLog (n (x, 1)) (inT n x) + kLog (n (x, 0)) (inT n x)) := by
    intro x
    have h := binT_mode (n (x, 0)) (n (x, 1))
    have hu : (n (x, 0) + n (x, 1) : ℕ) = inT n x := rfl
    unfold binT at h
    rw [Nat.add_sub_cancel, hu] at h
    rcases Nat.eq_zero_or_pos (inT n x) with h0 | hpos
    · have h₀ : n (x, 0) = 0 := by unfold inT at h0; omega
      have h₁ : n (x, 1) = 0 := by unfold inT at h0; omega
      simp [h0, h₀, h₁, kLog]
    · have hu₀ : (0 : ℝ) < inT n x := by exact_mod_cast hpos
      rw [pow_eq_exp_kLog _ hu₀, pow_eq_exp_kLog _ hu₀, mul_assoc, ← Real.exp_add] at h
      exact h
  have hprod := Finset.prod_le_prod₀ (s := univ) (fun x _ ↦ by positivity) fun x _ ↦ hbin x
  -- The exponents add up to `−m·ln 2·I(n)`.
  have hones : ∀ i, ((onesOf n i : ℝ) / m) ^ onesOf n i = exp (kLog (onesOf n i) m) :=
    fun i ↦ pow_eq_exp_kLog _ hm
  simp only [hones]
  rw [← Real.exp_sum]
  have hexp : ∑ i, kLog (onesOf n i) m = -(m * log 2 * info m n) +
      ∑ x, (kLog (n (x, 1)) (inT n x) + kLog (n (x, 0)) (inT n x)) :=
    exponent_eq hι
  rw [hexp, Real.exp_add]
  have hden : ∏ x, (1 / ((inT n x : ℝ) + 1)) ≥ 1 / ((m : ℝ) + 1) ^ Fintype.card X := by
    rw [Finset.prod_div_distrib, Finset.prod_const_one, ge_iff_le]
    rw [show ((m : ℝ) + 1) ^ Fintype.card X = ∏ _x : X, ((m : ℝ) + 1) by simp]
    apply one_div_le_one_div_of_le (Finset.prod_pos fun x _ ↦ by positivity)
    refine Finset.prod_le_prod₀ (fun x _ ↦ by positivity) fun x _ ↦ ?_
    have : inT n x ≤ m := by
      rw [← hn, ← sum_inT]
      exact Finset.single_le_sum (f := inT n) (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ x)
    have : (inT n x : ℝ) ≤ m := by exact_mod_cast this
    linarith
  have hE : 0 < exp (-(m * log 2 * info m n)) := Real.exp_pos _
  calc exp (-(m * log 2 * info m n)) / ((m : ℝ) + 1) ^ Fintype.card X
      = exp (-(m * log 2 * info m n)) * (1 / ((m : ℝ) + 1) ^ Fintype.card X) := by ring
    _ ≤ exp (-(m * log 2 * info m n)) * ∏ x, (1 / ((inT n x : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_left hden hE.le
    _ ≤ exp (-(m * log 2 * info m n)) * ∏ x, (((inT n x).choose (n (x, 1)) : ℝ) *
          exp (kLog (n (x, 1)) (inT n x) + kLog (n (x, 0)) (inT n x))) :=
        mul_le_mul_of_nonneg_left hprod hE.le
    _ = (∏ x, ((inT n x).choose (n (x, 1)) : ℝ)) * (exp (-(m * log 2 * info m n)) *
          exp (∑ x, (kLog (n (x, 1)) (inT n x) + kLog (n (x, 0)) (inT n x)))) := by
        rw [Finset.prod_mul_distrib, Real.exp_sum]; ring

/-! ### Exact covering -/

/-- The bound on the size of an exact codebook for `m` entries, `C` patterns and information `r`. -/
noncomputable def coverBound (m : ℝ) (C : ℕ) (r : ℝ) : ℝ := (m * log C + 2) * (m + 1) ^ C * 2 ^ (m * r)

/-- **Exact covering.** For a joint type `n` of `m` pairs, some nonempty codebook of at most
`coverBound m C I(n)` lists of bits gives every list of patterns of the input type of `n` exactly
the joint type `n`. -/
theorem exact_cover [Nonempty X] (n : X × Fin 2 → ℕ) (hn : ∑ v, n v = Fintype.card ι)
    (hι : 0 < Fintype.card ι) :
    ∃ 𝓑 : Finset (ι → Fin 2), 𝓑.Nonempty ∧
      (#𝓑 : ℝ) ≤ coverBound (Fintype.card ι) (Fintype.card X) (info (Fintype.card ι) n) ∧
      ∀ s : ι → X, typeOf s = inT n → ∃ b ∈ 𝓑, jointType s b = n := by
  classical
  set m := Fintype.card ι with hmdef
  set C := Fintype.card X with hCdef
  have hm : (0 : ℝ) < m := by exact_mod_cast hι
  have hC : (1 : ℝ) ≤ C := by exact_mod_cast Fintype.card_pos
  have hlogC : 0 ≤ log C := log_nonneg hC
  set r := info m n with hr
  set p₀ : ℝ := exp (-(m * log 2 * r)) / ((m : ℝ) + 1) ^ C with hp₀
  have hp₀pos : 0 < p₀ := by positivity
  have hr₀ : 0 ≤ r := info_nonneg hι hn
  have hp₀le : p₀ ≤ 1 := by
    rw [hp₀, div_le_one (by positivity)]
    calc exp (-(m * log 2 * r)) ≤ 1 := by
          rw [Real.exp_le_one_iff]; have := log_two_pos'; nlinarith [mul_nonneg hm.le hr₀]
      _ ≤ ((m : ℝ) + 1) ^ C := one_le_pow₀ (by linarith)
  set M : ℕ := ⌈(m * log C + 1) / p₀⌉₊ with hM
  have hMge : (m * log C + 1) / p₀ ≤ M := Nat.le_ceil _
  have hMp : m * log C + 1 ≤ p₀ * M := by
    rw [div_le_iff₀ hp₀pos] at hMge; linarith
  -- The targets: lists of patterns of the right type.
  let T := {s : ι → X // typeOf s = inT n}
  have hcover := exists_cover (Y := ι → Fin 2) (T := T) (isDist_bitW (ι := ι) hι hn)
    (fun s ↦ fitSet s.1 n) (q₀ := p₀) (fun s ↦ fit_chance_ge hn hι s.2) M (by
      have hT : (Fintype.card T : ℝ) ≤ (C : ℝ) ^ m := by
        have : Fintype.card T ≤ Fintype.card (ι → X) := Fintype.card_subtype_le _
        rw [Fintype.card_fun] at this
        exact_mod_cast this
      have hpow : (C : ℝ) ^ m = exp (m * log C) := by
        rw [← Real.exp_log (show (0 : ℝ) < C by linarith), ← Real.exp_nat_mul, Real.exp_log
          (by linarith)]
      calc (Fintype.card T : ℝ) * exp (-(p₀ * M)) ≤ exp (m * log C) * exp (-(p₀ * M)) :=
            mul_le_mul_of_nonneg_right (hpow ▸ hT) (Real.exp_pos _).le
        _ = exp (m * log C - p₀ * M) := by rw [← Real.exp_add]; ring_nf
        _ ≤ exp (-1) := Real.exp_le_exp.mpr (by linarith)
        _ < 1 := by
          have := Real.exp_lt_exp.mpr (show (-1 : ℝ) < 0 by norm_num)
          rwa [Real.exp_zero] at this)
  obtain ⟨ys, hys⟩ := hcover
  have hM1 : 1 ≤ M := by
    have : (1 : ℝ) ≤ (m * log C + 1) / p₀ := by
      rw [le_div_iff₀ hp₀pos]; nlinarith [mul_nonneg hm.le hlogC]
    exact_mod_cast this.trans hMge
  refine ⟨univ.image ys, ⟨ys ⟨0, hM1⟩, Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩, ?_, ?_⟩
  · refine (Nat.cast_le.mpr Finset.card_image_le).trans ?_
    rw [Finset.card_univ, Fintype.card_fin]
    have hM' : (M : ℝ) ≤ (m * log C + 1) / p₀ + 1 := (Nat.ceil_lt_add_one (by positivity)).le
    have h2 : (2 : ℝ) ^ (m * r) = exp (m * log 2 * r) := by
      rw [Real.rpow_def_of_pos (by norm_num)]; ring_nf
    calc (M : ℝ) ≤ (m * log C + 1) / p₀ + 1 := hM'
      _ ≤ (m * log C + 2) / p₀ := by
          have : 1 ≤ 1 / p₀ := by rw [le_div_iff₀ hp₀pos]; linarith
          rw [show (m * log C + 2) / p₀ = (m * log C + 1) / p₀ + 1 / p₀ by ring]
          linarith
      _ = coverBound m C r := by
          unfold coverBound
          rw [h2, hp₀, div_div_eq_mul_div, Real.exp_neg, div_inv_eq_mul]
  · intro s hs
    obtain ⟨i, hi⟩ := hys ⟨s, hs⟩
    exact ⟨ys i, Finset.mem_image_of_mem _ (Finset.mem_univ _), (Finset.mem_filter.mp hi).2⟩

end CubeGod
