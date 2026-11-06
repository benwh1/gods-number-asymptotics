import CubeGod.Method.Square
import CubeGod.Exact.Kind
import CubeGod.Lower

/-!
# The Method

Stage 1 solves everything except the oblique centers. The twist makes each orbit's patterns look
uniform. Stage 2 does the 3-cycles of the right-handed schedule, then those of the left-handed one,
with setups chosen by the codebooks. A right-handed 3-cycle moves only the right orbits `O(e, d)`,
and a left-handed one only the left orbits `O(d, e)`, so each orbit sees only its own schedule. This
solves the orbits of good tuples. Stage 3 solves what's left, one orbit at a time.
-/

open Finset Real

namespace CubeGod

variable {n h a c : ℕ}

/-- The group that the 3-cycles of one orbit generate on its patterns. -/
abbrev CycGroup (q : Bool) := ↥(Subgroup.closure (Set.range (Function.uncurry (sideCyc q))))

noncomputable instance (q : Bool) : Fintype (CycGroup q) := Fintype.ofFinite _

/-- A tuple: a sub-block of an earlier group `G`, and a layer `d` of a later group `H`. Its
`c` pairs are `(e, d)` for `e` in the sub-block. -/
structure Tuple (h a c : ℕ) where
  /-- the earlier group -/
  G : Fin h
  /-- the later group -/
  H : Fin h
  lt : G < H
  /-- the sub-block: a row of `G` -/
  row : Fin a
  /-- the row of `d` in `H` -/
  dRow : Fin a
  /-- the column of `d` in `H` -/
  dCol : Fin c
  deriving DecidableEq, Fintype

/-- A pair of intervals: a column of an earlier group and a column of a later group. -/
structure IntervalPair (h c : ℕ) where
  /-- the earlier group -/
  G : Fin h
  /-- the later group -/
  H : Fin h
  /-- the column of `G` -/
  col : Fin c
  /-- the column of `H` -/
  col' : Fin c
  deriving DecidableEq, Fintype

theorem card_tuple : (Fintype.card (Tuple h a c) : ℝ) =
    (groupPairs h).length * (a * (a * c)) := by
  have e : Tuple h a c ≃ {q : Fin h × Fin h // q.1 < q.2} × Fin a × Fin a × Fin c :=
    { toFun := fun τ ↦ (⟨(τ.G, τ.H), τ.lt⟩, τ.row, τ.dRow, τ.dCol)
      invFun := fun x ↦ ⟨x.1.1.1, x.1.1.2, x.1.2, x.2.1, x.2.2.1, x.2.2.2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  have hq : Fintype.card {q : Fin h × Fin h // q.1 < q.2} = (groupPairs h).length := by
    rw [← List.toFinset_card_of_nodup (nodup_groupPairs h), Fintype.card_subtype]
    congr 1
    ext q
    simp [mem_groupPairs]
  simp [Fintype.card_congr e, Fintype.card_prod, hq]

theorem letterOf_mem (d₁ d₂ : ℕ) (m : Move n) : letterOf d₁ d₂ m ∈ orbitGroup := by
  unfold letterOf
  split_ifs <;> first | exact letter_mem _ _ _ | exact one_mem _

theorem pairW_mem (d₁ d₂ : ℕ) (w : List (Move n)) : pairW d₁ d₂ w ∈ orbitGroup :=
  evalW_mem (letterOf_mem d₁ d₂) w

theorem pairView_solved {d₁ d₂ : ℕ} (h₁ : InI n d₁) (h₂ : InI n d₂) :
    pairView h₁ h₂ (solved n) = solvedView :=
  funext fun u ↦ solved_embed h₁ h₂ u

/-- A solvable state's pattern on each orbit of a pair is balanced. -/
theorem side_balanced {d₁ d₂ : ℕ} (h₁ : InI n d₁) (h₂ : InI n d₂) (hne : d₁ ≠ d₂) {s : State n}
    (hs : Solvable s) (q : Bool) : Balanced (fun u : SPos q ↦ pairView h₁ h₂ s u.1) := by
  obtain ⟨w, hw⟩ := hs
  have h := pairView_act h₁ h₂ hne w s
  rw [hw, pairView_solved] at h
  have : (fun u : SPos q ↦ pairView h₁ h₂ s u.1) =
      (sSolved q).1 ∘ restr q ⟨pairW d₁ d₂ w, pairW_mem d₁ d₂ w⟩ := by
    funext u
    have := congrFun h (pairW d₁ d₂ w u.1)
    simp only [Function.comp_apply, Equiv.symm_apply_apply] at this
    rw [← this]
    rfl
  rw [this]
  exact (sSolved q).2.comp_perm _

theorem Solvable.act' {s : State n} (hs : Solvable s) (w : List (Move n)) : Solvable (act w s) := by
  obtain ⟨x, hx⟩ := hs
  exact ⟨invW w ++ x, by rw [act_append, act_invW, hx]⟩

/-! ### The 3-cycles of one orbit -/

theorem cyclesPerm_mem (l : List Cycle) : cyclesPerm l ∈ orbitGroup :=
  evalW_mem (fun g ↦ g.perm_mem 1) l

/-- A list of 3-cycles of one orbit acts on its patterns as its permutation of the positions. -/
theorem evalW_sideCyc {q : Bool} (l : List (SideCycle q)) :
    evalW (fun g ↦ sideCyc q g 1) l =
      sideAct q ⟨cyclesPerm (l.map Subtype.val), cyclesPerm_mem _⟩ := by
  induction l with
  | nil =>
    have : (⟨cyclesPerm (([] : List (SideCycle q)).map Subtype.val), cyclesPerm_mem _⟩ :
      orbitGroup) = 1 := rfl
    rw [this, map_one]
    rfl
  | cons x l ih =>
    rw [evalW_cons, ih, sideCyc, ← map_mul]
    rfl

/-- The groups are finite, so each element is a product of 3-cycles, of bounded length. -/
theorem exists_cycle_lists : ∃ L : ℕ, ∀ q, ∀ r : CycGroup q, ∃ l : List (SideCycle q),
    l.length ≤ L ∧ evalW (fun g ↦ sideCyc q g 1) l = r.1 := by
  classical
  have one : ∀ q, ∃ L : ℕ, ∀ r : CycGroup q, ∃ l : List (SideCycle q), l.length ≤ L ∧
      evalW (fun g ↦ sideCyc q g 1) l = r.1 := by
    intro q
    have hex : ∀ r : CycGroup q, ∃ l : List (SideCycle q),
        evalW (fun g ↦ sideCyc q g 1) l = r.1 := by
      rintro ⟨σ, hσ⟩
      show ∃ l : List (SideCycle q), evalW (fun g ↦ sideCyc q g 1) l = σ
      have hr : σ ∈ Submonoid.closure (Set.range (Function.uncurry (sideCyc q))) := by
        rw [← Subgroup.closure_toSubmonoid_of_finite]
        exact hσ
      clear hσ
      induction hr using Submonoid.closure_induction with
      | mem x hx =>
        obtain ⟨⟨g, S⟩, rfl⟩ := hx
        fin_cases S
        · exact ⟨[], by simp [sideCyc_zero]⟩
        · exact ⟨[g], by simp⟩
      | one => exact ⟨[], rfl⟩
      | mul x y _ _ hx hy =>
        obtain ⟨l₁, h₁⟩ := hx
        obtain ⟨l₂, h₂⟩ := hy
        exact ⟨l₂ ++ l₁, by rw [evalW_append, h₁, h₂]⟩
    choose f hf using hex
    exact ⟨(Finset.univ : Finset (CycGroup q)).sup fun r ↦ (f r).length, fun r ↦
      ⟨f r, Finset.le_sup (f := fun r ↦ (f r).length) (Finset.mem_univ r), hf r⟩⟩
  obtain ⟨L₁, h₁⟩ := one true
  obtain ⟨L₂, h₂⟩ := one false
  refine ⟨max L₁ L₂, fun q r ↦ ?_⟩
  cases q
  · obtain ⟨l, hl, he⟩ := h₂ r
    exact ⟨l, hl.trans (le_max_right _ _), he⟩
  · obtain ⟨l, hl, he⟩ := h₁ r
    exact ⟨l, hl.trans (le_max_left _ _), he⟩

/-- Forget which orbit a 3-cycle is for. -/
def Fired.val {q : Bool} (x : Fired (Fin 2) (SideCycle q)) : Fired (Fin 2) Cycle :=
  ⟨x.cyc.1, x.first, x.second⟩

theorem fire_side {q : Bool} (x : Fired (Fin 2) (SideCycle q)) (y : OState q) :
    (cubeSys q).fire x y = sideAct q ⟨x.val.perm, Fired.perm_mem _⟩ y := by
  have : (⟨x.val.perm, Fired.perm_mem _⟩ : orbitGroup) =
      (⟨x.cyc.1.perm x.second, x.cyc.1.perm_mem _⟩ : orbitGroup)⁻¹ *
        ⟨x.cyc.1.perm x.first, x.cyc.1.perm_mem _⟩ :=
    rfl
  simp only [this, map_mul, map_inv]
  rfl

/-- `t` steps of a schedule act on an orbit's patterns as their permutation of the positions. -/
theorem runN_side {q : Bool} (qs : ℕ → Fired (Fin 2) (SideCycle q)) (t : ℕ) (x : OState q) :
    (cubeSys q).runN qs t x = sideAct q ⟨evalW (fun i ↦ (qs i).val.perm) (List.range t),
      evalW_mem (fun _ ↦ Fired.perm_mem _) _⟩ x := by
  induction t with
  | zero =>
    have : (⟨evalW (fun i ↦ (qs i).val.perm) (List.range 0),
      evalW_mem (fun _ ↦ Fired.perm_mem _) _⟩ : orbitGroup) = 1 := rfl
    rw [this, map_one]
    rfl
  | succ t ih =>
    change (cubeSys q).fire (qs t) ((cubeSys q).runN qs t x) = _
    rw [fire_side, ih, ← Equiv.Perm.mul_apply, ← map_mul]
    congr 2
    apply Subtype.ext
    simp [List.range_succ, evalW_append]

/-- A pattern given by a view of the positions, moved by `σ`, is the view moved by `σ`. -/
theorem sideAct_view {q : Bool} {σ : Equiv.Perm Pos} (hσ : σ ∈ orbitGroup) {x : OState q}
    {V : Pos → Face} (hx : ∀ u, x.1 u = V u.1) (u : SPos q) :
    (sideAct q ⟨σ, hσ⟩ x).1 u = V (σ⁻¹ u.1) := by
  rw [sideAct_val, Function.comp_apply, hx, ← map_inv]
  rfl

theorem evalW_fix {L : Type*} {φ : L → Equiv.Perm Pos} {l : List L} {u : Pos}
    (h : ∀ x ∈ l, φ x u = u) : evalW φ l u = u := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    rw [evalW_cons, Equiv.Perm.mul_apply, h x (by simp)]
    exact ih fun y hy ↦ h y (by simp [hy])

theorem cyclesPerm_pure {q : Bool} (l : List (SideCycle q)) (u : Pos) (hu : ¬ OnSide q u) :
    cyclesPerm (l.map Subtype.val) u = u := by
  rw [cyclesPerm, evalW_map]
  exact evalW_fix fun g _ ↦ g.2 u hu

/-- A product of a right-handed and a left-handed permutation, seen on one orbit. -/
theorem mul_inv_side {σ τ : Equiv.Perm Pos} (hσ : ∀ u, ¬ OnSide true u → σ u = u)
    (hτ : ∀ u, ¬ OnSide false u → τ u = u) (hτm : τ ∈ orbitGroup) (q : Bool) (u : Pos)
    (hu : OnSide q u) : (τ * σ)⁻¹ u = (cond q σ τ)⁻¹ u := by
  rw [mul_inv_rev, Equiv.Perm.mul_apply]
  cases q
  · have h₁ : OnSide false (τ⁻¹ u) := (onSide_iff (inv_mem hτm) false u).mpr hu
    have h₂ : ¬ OnSide true (τ⁻¹ u) := h₁
    rw [Equiv.Perm.inv_eq_iff_eq.mpr (hσ _ h₂).symm]
    rfl
  · have h₁ : ¬ OnSide false u := not_not.mpr hu
    rw [Equiv.Perm.inv_eq_iff_eq.mpr (hτ u h₁).symm]
    rfl

/-- `u` is right-handed, so its swap is left-handed. -/
theorem Pos.swap_not_proper : ∀ u : Pos, u.Proper → ¬ u.swap.Proper := by
  decide +kernel

/-! ### Schedules -/

/-- A schedule of one orbit's 3-cycles, with codebooks of lists of `c × c` bits, each of at most
`M` lists. -/
structure Sched (q : Bool) (c : ℕ) where
  /-- the number of steps -/
  T : ℕ
  /-- the 3-cycles -/
  g : ℕ → SideCycle q
  /-- the bound on the codebook sizes -/
  M : ℕ
  /-- the codebooks of the first firings -/
  B₁ : ℕ → Finset (Fin c × Fin c → Fin 2)
  /-- the codebooks of the second firings -/
  B₂ : ℕ → Finset (Fin c × Fin c → Fin 2)
  hne : ∀ t, (B₁ t).Nonempty ∧ (B₂ t).Nonempty
  hM₁ : ∀ t, #(B₁ t) ≤ M
  hM₂ : ∀ t, #(B₂ t) ≤ M

/-- The codebooks solve every list of `c × c` patterns whose counts are all within `ε·c²/C` of
`c²/C`. -/
def Sched.Solves {q : Bool} (S : Sched q c) (ε : ℝ) : Prop :=
  ∀ s : Fin c × Fin c → OState q,
    (∀ x, |(typeOf s x : ℝ) - (c * c : ℕ) / Fintype.card (OState q)| ≤
      ε * (c * c : ℕ) / Fintype.card (OState q)) →
    ∃ a b : ℕ → Fin c × Fin c → Fin 2, (∀ t < S.T, a t ∈ S.B₁ t ∧ b t ∈ S.B₂ t) ∧
      ∀ k, (cubeSys q).runN (fun t ↦ ⟨S.g t, a t k, b t k⟩) S.T (s k) = (cubeSys q).solved

/-- A bound on the length of a schedule's Stage 2. -/
def Sched.len {q : Bool} (S : Sched q c) (h a : ℕ) : ℕ := S.T * Layout.sqLen h a c S.M

/-- The type of a square list is the sum of the counts of its rows. -/
theorem typeOf_rows {X : Type*} [DecidableEq X] (s : Fin c × Fin c → X) (x : X) :
    typeOf s x = ∑ i, count (fun k ↦ s (i, k)) x := by
  unfold typeOf count
  rw [Finset.card_eq_sum_card_fiberwise (f := fun p : Fin c × Fin c ↦ p.1) (t := univ)
    (fun _ _ ↦ Finset.mem_univ _)]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  refine Finset.card_bij (fun p _ ↦ p.2) ?_ ?_ ?_
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    rw [← hp.2]; exact hp.1
  · intro p hp p' hp' he
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp hp'
    exact Prod.ext (hp.2.trans hp'.2.symm) he
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
    exact ⟨(i, k), by simp [hk], rfl⟩

/-- If every row of a square list is `ε`-typical for uniform, its counts are within `ε·c²/C` of
`c²/C`. -/
theorem near_of_rows {X : Type*} [Fintype X] [DecidableEq X] {ε : ℝ} {s : Fin c × Fin c → X}
    (h : ∀ i, Typical ε (uniform X) (fun k ↦ s (i, k))) (x : X) :
    |(typeOf s x : ℝ) - (c * c : ℕ) / Fintype.card X| ≤ ε * (c * c : ℕ) / Fintype.card X := by
  rw [typeOf_rows]
  push_cast
  have hlo : ∀ i, (1 - ε) * c * uniform X x ≤ count (fun k ↦ s (i, k)) x := fun i ↦ (h i x).1
  have hhi : ∀ i, (count (fun k ↦ s (i, k)) x : ℝ) ≤ (1 + ε) * c * uniform X x := fun i ↦
    (h i x).2
  have hs₁ := Finset.sum_le_sum fun i (_ : i ∈ univ) ↦ hlo i
  have hs₂ := Finset.sum_le_sum fun i (_ : i ∈ univ) ↦ hhi i
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs₁ hs₂
  unfold uniform at hs₁ hs₂
  rw [abs_le]
  constructor
  · have : (c : ℝ) * ((1 - ε) * c * (Fintype.card X : ℝ)⁻¹) =
        (c * c : ℝ) / Fintype.card X - ε * (c * c) / Fintype.card X := by ring
    linarith
  · have : (c : ℝ) * ((1 + ε) * c * (Fintype.card X : ℝ)⁻¹) =
        (c * c : ℝ) / Fintype.card X + ε * (c * c) / Fintype.card X := by ring
    linarith

namespace Layout

variable (Y : Layout n h a c)

/-- The row of a layer in a group. -/
noncomputable def rowOf (ha : 0 < a) (H : Fin h) (d : ℕ) : Fin a :=
  open Classical in if e : ∃ v k, Y.L H v k = d then e.choose else ⟨0, ha⟩

/-- The column of a layer in a group. -/
noncomputable def colOf (hc : 0 < c) (H : Fin h) (d : ℕ) : Fin c :=
  open Classical in if e : ∃ k v, Y.L H v k = d then e.choose else ⟨0, hc⟩

theorem rowOf_L (ha : 0 < a) (H : Fin h) (v : Fin a) (k : Fin c) :
    Y.rowOf ha H (Y.L H v k) = v := by
  classical
  have e : ∃ v' k', Y.L H v' k' = Y.L H v k := ⟨v, k, rfl⟩
  simp only [rowOf]
  rw [dite_eq_left e]
  obtain ⟨k', hk'⟩ := e.choose_spec
  exact (Y.inj _ _ _ _ _ _ hk').2.1

theorem colOf_L (hc : 0 < c) (H : Fin h) (v : Fin a) (k : Fin c) :
    Y.colOf hc H (Y.L H v k) = k := by
  classical
  have e : ∃ k' v', Y.L H v' k' = Y.L H v k := ⟨k, v, rfl⟩
  simp only [colOf]
  rw [dite_eq_left e]
  obtain ⟨v', hv'⟩ := e.choose_spec
  exact (Y.inj _ _ _ _ _ _ hv').2.2

end Layout

/-- A word that doesn't move a sticker doesn't change it. -/
theorem act_of_fix {w : List (Move n)} {p : Sticker n} (h : permW w p = p) (s : State n) :
    (act w s).get p = s.get p := by
  rw [act_eq, Function.comp]
  congr 1
  rw [Equiv.symm_apply_eq, h]

/-- The orbit `O(e, d)` of a pair of different layers. -/
def obliqueOf {e d : ℕ} (he : InI n e) (hd : InI n d) (hne : e ≠ d) : Oblique n :=
  ⟨(e, d), Finset.mem_offDiag.mpr ⟨mem_layerSet.mpr he, mem_layerSet.mpr hd, hne⟩⟩


/-! ### Super-tuples -/

theorem blk_lt (hca : c ∣ a) (v : Fin a) (i : Fin c) : (v : ℕ) / c * c + i < a := by
  obtain ⟨q, hq⟩ := hca
  have h₁ : (v : ℕ) < c * q := hq ▸ v.2
  have h₂ : (v : ℕ) / c < q := Nat.div_lt_of_lt_mul (by rw [mul_comm]; linarith [h₁])
  have h₃ : (v : ℕ) / c * c + c ≤ q * c := by nlinarith
  have := i.2
  calc (v : ℕ) / c * c + i < q * c := by omega
    _ = a := by rw [hq, mul_comm]

/-- Row `i` of the square block of a tuple: the same pair of groups and layer `d`. -/
def Tuple.sqRow (hca : c ∣ a) (τ : Tuple h a c) (i : Fin c) : Tuple h a c :=
  ⟨τ.G, τ.H, τ.lt, ⟨(τ.row : ℕ) / c * c + i, blk_lt hca τ.row i⟩, τ.dRow, τ.dCol⟩

/-- The first row of the square block of a tuple, standing for its super-tuple. -/
def Tuple.rep (hc : 0 < c) (hca : c ∣ a) (τ : Tuple h a c) : Tuple h a c :=
  τ.sqRow hca ⟨0, hc⟩

theorem Tuple.sqRow_rep (hc : 0 < c) (hca : c ∣ a) (τ : Tuple h a c) (i : Fin c) :
    (τ.rep hc hca).sqRow hca i = τ.sqRow hca i := by
  unfold Tuple.sqRow Tuple.rep Tuple.sqRow
  congr 2
  simp only [add_zero]
  rw [Nat.mul_div_cancel _ hc]

theorem Tuple.rep_sqRow (hc : 0 < c) (hca : c ∣ a) (τ : Tuple h a c) (i : Fin c) :
    (τ.sqRow hca i).rep hc hca = τ.rep hc hca := by
  unfold Tuple.sqRow Tuple.rep Tuple.sqRow
  congr 2
  simp only [add_zero]
  have := i.2
  rw [show ((τ.row : ℕ) / c * c + i) / c = (τ.row : ℕ) / c by
    rw [add_comm, Nat.add_mul_div_right _ _ hc, Nat.div_eq_of_lt this, zero_add]]

theorem Tuple.sqRow_self (hc : 0 < c) (hca : c ∣ a) (τ : Tuple h a c) :
    τ.sqRow hca ⟨(τ.row : ℕ) % c, Nat.mod_lt _ hc⟩ = τ := by
  unfold Tuple.sqRow
  congr 1
  ext
  simp only
  exact Nat.div_add_mod' _ _

/-- **The Method** solves any solvable state, in at most the given number of moves. -/
theorem method_solves {K₁ K₂ L : ℕ} (Y : Layout n h a c) (hn : 0 < (n + 1) / 2) (ha : 0 < a)
    (hc : 0 < c) (hca : c ∣ a)
    (hK₁ : ∀ s : State n, Solvable s → ∃ w : List (Move n), w.length ≤ K₁ * n ∧
      ∀ p, Stage1 p → (act w s).get p = (solved n).get p)
    (hK₂ : ∀ q : Oblique n, CanSolve K₂ q.name)
    (hL : ∀ q, ∀ r : CycGroup q, ∃ l : List (SideCycle q), l.length ≤ L ∧
      evalW (fun g ↦ sideCyc q g 1) l = r.1)
    (S : ∀ q, Sched q c) {τ₀ : ℝ} (hsolve : ∀ q, (S q).Solves τ₀)
    (Bad : ∀ q, Finset (Fin c → OState q))
    (hBad : ∀ q x, x ∉ Bad q → Typical τ₀ (uniform (OState q)) x)
    {β : ℝ} (hβ : ∀ q, (#(Bad q) : ℝ) ≤ β * (Fintype.card (OState q) : ℝ) ^ c)
    (s : State n) (hs : Solvable s) :
    ∃ w, act w s = solved n ∧ (w.length : ℝ) ≤
      (K₁ * n : ℕ) + (2 * L * (allCycles.length * cycleLen h c a 1 2) : ℕ) +
        (((S true).len h a + (S false).len h a : ℕ) : ℝ) +
        K₂ * (((n / 2 - 1 : ℕ) : ℝ) ^ 2 -
          (1 - c * β) * (((h : ℝ) ^ 2 - h) * ((a : ℝ) * c) ^ 2)) := by
  classical
  obtain ⟨w₁, hw₁, hw₁s⟩ := hK₁ s hs
  set s₁ := act w₁ s with hs₁def
  have hs₁ : Solvable s₁ := hs.act' w₁
  -- The pairs of a tuple.
  let dd : Tuple h a c → ℕ := fun τ ↦ Y.L τ.H τ.dRow τ.dCol
  let ee : Tuple h a c → Fin c → ℕ := fun τ k ↦ Y.L τ.G τ.row k
  have hlt : ∀ τ : Tuple h a c, τ.G < τ.H := fun τ ↦ τ.lt
  have hed : ∀ τ k, ee τ k ≠ dd τ := fun τ k ↦ Layout.layer_ne (Y := Y) (ne_of_lt (hlt τ))
  have hee : ∀ τ k, InI n (ee τ k) := fun τ k ↦ Y.mem _ _ _
  have hdd : ∀ τ, InI n (dd τ) := fun τ ↦ Y.mem _ _ _
  -- The view of a state on the pair `(e, d)`, and its patterns on the two orbits.
  let V : State n → Tuple h a c → Fin c → Pos → Face := fun s τ k ↦ pairView (hee τ k) (hdd τ) s
  let Sx : ∀ q, Tuple h a c → Fin c → OState q := fun q τ k ↦
    ⟨fun u ↦ V s₁ τ k u.1, side_balanced (hee τ k) (hdd τ) (hed τ k) hs₁ q⟩
  have hVact : ∀ (w : List (Move n)) (s' : State n) τ k (u : Pos),
      V (act w s') τ k u = V s' τ k ((pairW (ee τ k) (dd τ) w)⁻¹ u) := by
    intro w s' τ k u
    have := congrFun (pairView_act (hee τ k) (hdd τ) (hed τ k) w s') u
    exact this
  -- The twist.
  let ι : Tuple h a c → Fin c → IntervalPair h c := fun τ k ↦ ⟨τ.G, τ.H, k, τ.dCol⟩
  have hι : ∀ τ, Function.Injective (ι τ) := fun τ k k' he ↦ congrArg IntervalPair.col he
  have htrans : ∀ q, ∀ x y : OState q, ∃ r : CycGroup q, r • x = y := by
    intro q x y
    obtain ⟨w, hw, rfl⟩ := factT q x y
    exact ⟨⟨w, hw⟩, rfl⟩
  have hgood := fun q ↦ exists_good_twist (G := CycGroup q) (htrans q) ι hι (Sx q) (Bad q) (hβ q)
  choose r hr using hgood
  choose lstOf hlst₁ hlst₂ using hL
  -- The permutation of the positions that the twist gives each orbit of a pair of intervals.
  let Pt : Bool → IntervalPair h c → Equiv.Perm Pos := fun q j ↦
    cyclesPerm ((lstOf q (r q j)).map Subtype.val)
  have hPt_pure : ∀ q j u, ¬ OnSide q u → Pt q j u = u := fun q j u hu ↦
    cyclesPerm_pure _ u hu
  let lst : Fin h → Fin h → Fin c → ℕ → List Cycle := fun G H k d ↦
    (lstOf true (r true ⟨G, H, k, Y.colOf hc H d⟩)).map Subtype.val ++
      (lstOf false (r false ⟨G, H, k, Y.colOf hc H d⟩)).map Subtype.val
  set w₂ := Y.twistWord hn (2 * L) lst with hw₂
  set s₂ := act w₂ s₁ with hs₂def
  have hs₂ : Solvable s₂ := hs₁.act' w₂
  let X : ∀ q, Tuple h a c → Fin c → OState q := fun q τ k ↦ r q (ι τ k) • Sx q τ k
  have hview₂ : ∀ q τ k (u : SPos q), (X q τ k).1 u = V s₂ τ k u.1 := by
    intro q τ k u
    have h₁ : pairW (ee τ k) (dd τ) w₂ = Pt false (ι τ k) * Pt true (ι τ k) := by
      have := Layout.pairW_twistWord Y hn (L := 2 * L) (lst := lst) (hlt τ) τ.row τ.dRow k τ.dCol
      have hl : lst τ.G τ.H k (dd τ) = (lstOf true (r true (ι τ k))).map Subtype.val ++
          (lstOf false (r false (ι τ k))).map Subtype.val := by
        change (lstOf true (r true ⟨τ.G, τ.H, k, Y.colOf hc τ.H (dd τ)⟩)).map Subtype.val ++
          (lstOf false (r false ⟨τ.G, τ.H, k, Y.colOf hc τ.H (dd τ)⟩)).map Subtype.val = _
        rw [show Y.colOf hc τ.H (dd τ) = τ.dCol from Y.colOf_L hc _ _ _]
      have hlen : (lst τ.G τ.H k (dd τ)).length ≤ 2 * L := by
        rw [hl, List.length_append, List.length_map, List.length_map]
        have := hlst₁ true (r true (ι τ k))
        have := hlst₁ false (r false (ι τ k))
        omega
      rw [List.take_of_length_le hlen, hl, cyclesPerm, evalW_append] at this
      exact this
    have h₂ : X q τ k = sideAct q ⟨Pt q (ι τ k), cyclesPerm_mem _⟩ (Sx q τ k) := by
      change (r q (ι τ k)).1 (Sx q τ k) = _
      rw [← hlst₂ q (r q (ι τ k)), evalW_sideCyc]
    rw [h₂, sideAct_view (V := V s₁ τ k) _ (fun _ ↦ rfl), hVact w₂ s₁ τ k u.1, h₁,
      mul_inv_side (hPt_pure true _) (hPt_pure false _) (cyclesPerm_mem _) q u.1 u.2]
    cases q <;> rfl
  -- The super-tuples: a square block of rows of an earlier group, with a layer of a later one.
  let rep : Tuple h a c → Tuple h a c := fun τ ↦ τ.rep hc hca
  let sqR : Tuple h a c → Fin c → Tuple h a c := fun τ i ↦ τ.sqRow hca i
  let Xs : ∀ q, Tuple h a c → Fin c × Fin c → OState q := fun q σ e ↦ X q (sqR σ e.1) e.2
  let GoodSq : Bool → Tuple h a c → Prop := fun q σ ↦ ∀ i, (fun k ↦ X q (sqR σ i) k) ∉ Bad q
  -- The codebook lists of each super-tuple, on each orbit.
  have hex : ∀ q σ, ∃ A A' : ℕ → Fin c × Fin c → Fin 2,
      (∀ t, A t ∈ (S q).B₁ t ∧ A' t ∈ (S q).B₂ t) ∧
      (GoodSq q σ → ∀ e,
        (cubeSys q).runN (fun t ↦ ⟨(S q).g t, A t e, A' t e⟩) (S q).T (Xs q σ e) =
          (cubeSys q).solved) := by
    intro q σ
    have hdef₁ : ∀ t, ((S q).hne t).1.choose ∈ (S q).B₁ t := fun t ↦ ((S q).hne t).1.choose_spec
    have hdef₂ : ∀ t, ((S q).hne t).2.choose ∈ (S q).B₂ t := fun t ↦ ((S q).hne t).2.choose_spec
    by_cases hg : GoodSq q σ
    · have hnear := near_of_rows (s := Xs q σ) fun i ↦ hBad q _ (hg i)
      obtain ⟨x, y, hxy, hrun⟩ := hsolve q _ hnear
      refine ⟨fun t ↦ if t < (S q).T then x t else ((S q).hne t).1.choose,
        fun t ↦ if t < (S q).T then y t else ((S q).hne t).2.choose, fun t ↦ ?_, fun _ e ↦ ?_⟩
      · by_cases ht : t < (S q).T
        · simpa [ht] using hxy t ht
        · simpa [ht] using ⟨hdef₁ t, hdef₂ t⟩
      · rw [CycleSystem.runN_congr (q' := fun t ↦ ⟨(S q).g t, x t e, y t e⟩)]
        · exact hrun e
        · intro u hu
          simp [hu]
    · exact ⟨fun t ↦ ((S q).hne t).1.choose, fun t ↦ ((S q).hne t).2.choose,
        fun t ↦ ⟨hdef₁ t, hdef₂ t⟩, fun h' ↦ absurd h' hg⟩
  choose A A' hAB hrun using hex
  -- The lists each super-tuple picks, by groups, square block and layer.
  let sp₁ : Bool → ℕ → Fin h → Fin h → ℕ → ℕ → Fin c × Fin c → Fin 2 := fun q t G H j d ↦
    if hGH : G < H then
      (if hj : j * c < a then A q ⟨G, H, hGH, ⟨j * c, hj⟩, Y.rowOf ha H d, Y.colOf hc H d⟩ t
        else ((S q).hne t).1.choose)
    else ((S q).hne t).1.choose
  let sp₂ : Bool → ℕ → Fin h → Fin h → ℕ → ℕ → Fin c × Fin c → Fin 2 := fun q t G H j d ↦
    if hGH : G < H then
      (if hj : j * c < a then A' q ⟨G, H, hGH, ⟨j * c, hj⟩, Y.rowOf ha H d, Y.colOf hc H d⟩ t
        else ((S q).hne t).2.choose)
    else ((S q).hne t).2.choose
  have hsp₁ : ∀ q t G H j d, sp₁ q t G H j d ∈ (S q).B₁ t := by
    intro q t G H j d
    simp only [sp₁]
    split_ifs
    · exact (hAB q _ t).1
    · exact ((S q).hne t).1.choose_spec
    · exact ((S q).hne t).1.choose_spec
  have hsp₂ : ∀ q t G H j d, sp₂ q t G H j d ∈ (S q).B₂ t := by
    intro q t G H j d
    simp only [sp₂]
    split_ifs
    · exact (hAB q _ t).2
    · exact ((S q).hne t).2.choose_spec
    · exact ((S q).hne t).2.choose_spec
  have hrep : ∀ τ : Tuple h a c, (τ.row : ℕ) / c * c < a := fun τ ↦
    lt_of_le_of_lt (Nat.div_mul_le_self _ _) τ.row.2
  have hrepeq : ∀ τ : Tuple h a c, (⟨τ.G, τ.H, τ.lt, ⟨(τ.row : ℕ) / c * c, hrep τ⟩,
      Y.rowOf ha τ.H (dd τ), Y.colOf hc τ.H (dd τ)⟩ : Tuple h a c) = rep τ := by
    intro τ
    rw [show Y.rowOf ha τ.H (dd τ) = τ.dRow from Y.rowOf_L ha _ _ _,
      show Y.colOf hc τ.H (dd τ) = τ.dCol from Y.colOf_L hc _ _ _]
    simp [rep, Tuple.rep, Tuple.sqRow]
  set iOf : Tuple h a c → Fin c := fun τ ↦ ⟨(τ.row : ℕ) % c, Nat.mod_lt _ hc⟩ with hiOf
  have hpA : ∀ q τ t k, sqPicks hc (sp₁ q t) τ.G τ.H τ.row (dd τ) k = A q (rep τ) t (iOf τ, k) := by
    intro q τ t k
    simp only [sqPicks, sp₁]
    rw [dite_eq_left (hlt τ), dite_eq_left (hrep τ), hrepeq]
  have hpA' : ∀ q τ t k, sqPicks hc (sp₂ q t) τ.G τ.H τ.row (dd τ) k = A' q (rep τ) t (iOf τ, k) := by
    intro q τ t k
    simp only [sqPicks, sp₂]
    rw [dite_eq_left (hlt τ), dite_eq_left (hrep τ), hrepeq]
  -- Stage 2: the right-handed schedule, then the left-handed one.
  let w₃q : Bool → List (Move n) := fun q ↦ Y.sqStage2Word hn hc (S q).T (fun t ↦ ((S q).g t).1)
    (S q).B₁ (S q).B₂ (sp₁ q) (sp₂ q)
  set w₃ := w₃q true ++ w₃q false with hw₃
  set s₃ := act w₃ s₂ with hs₃def
  have hs₃ : Solvable s₃ := hs₂.act' w₃
  -- What Stage 2 does to the pair of a tuple.
  let Ps : Bool → Tuple h a c → Fin c → Equiv.Perm Pos := fun q τ k ↦
    evalW (fun t ↦ Fired.val ⟨(S q).g t, A q (rep τ) t (iOf τ, k), A' q (rep τ) t (iOf τ, k)⟩
      |>.perm) (List.range (S q).T)
  have hPs_pure : ∀ q τ k u, ¬ OnSide q u → Ps q τ k u = u := fun q τ k u hu ↦
    evalW_fix fun t _ ↦
      Fired.perm_pure (q := Fired.val ⟨(S q).g t, A q (rep τ) t (iOf τ, k),
        A' q (rep τ) t (iOf τ, k)⟩) ((S q).g t).2 u hu
  have hw₃q : ∀ q τ k, pairW (ee τ k) (dd τ) (w₃q q) = Ps q τ k := by
    intro q τ k
    have h₂ := Layout.pairW_sqStage2Word (Y := Y) (hn := hn) (hc := hc) hca (T := (S q).T)
      (g := fun t ↦ ((S q).g t).1) (B₁ := (S q).B₁) (B₂ := (S q).B₂) (sp₁ := sp₁ q)
      (sp₂ := sp₂ q) (hsp₁ q) (hsp₂ q) (hlt τ) τ.row τ.dRow k τ.dCol
    refine h₂.trans ?_
    refine congrArg (fun φ ↦ evalW φ (List.range (S q).T)) (funext fun t ↦ ?_)
    change Fired.perm ⟨((S q).g t).1, sqPicks hc (sp₁ q t) τ.G τ.H τ.row (dd τ) k,
      sqPicks hc (sp₂ q t) τ.G τ.H τ.row (dd τ) k⟩ = _
    rw [hpA, hpA']
    rfl
  -- Tuples of good super-tuples end solved on their orbit.
  have hview₃ : ∀ q τ, GoodSq q (rep τ) → ∀ k (u : SPos q),
      V s₃ τ k u.1 = solvedView u.1 := by
    intro q τ hg k u
    have hw : pairW (ee τ k) (dd τ) w₃ = Ps false τ k * Ps true τ k := by
      rw [hw₃, pairW, evalW_append, ← pairW, ← pairW, hw₃q, hw₃q]
    have hrun' := hrun q (rep τ) hg (iOf τ, k)
    have hXs : Xs q (rep τ) (iOf τ, k) = X q τ k := by
      change X q ((τ.rep hc hca).sqRow hca (iOf τ)) k = X q τ k
      rw [Tuple.sqRow_rep, hiOf, Tuple.sqRow_self hc]
    rw [hXs, runN_side] at hrun'
    have hval := congrArg (fun x : OState q ↦ x.1 u) hrun'
    rw [sideAct_view _ (hview₂ q τ k)] at hval
    rw [hVact w₃ s₂ τ k u.1, hw, mul_inv_side (hPs_pure true τ k) (hPs_pure false τ k)
      (evalW_mem (fun _ ↦ Fired.perm_mem _) _) q u.1 u.2]
    have : (cond q (Ps true τ k) (Ps false τ k)) = Ps q τ k := by cases q <;> rfl
    rw [this]
    exact hval
  -- Stage 1 stickers stay solved.
  have hst : ∀ p, Stage1 p → s₃.get p = (solved n).get p := by
    intro p hp
    obtain ⟨ρ, hρ⟩ := hp.one_layer
    have hmem : p ∈ OneLayer n ρ := hρ
    have hfix : permW w₃ p = p := by
      rw [hw₃, permW, evalW_append, Equiv.Perm.mul_apply, ← permW, ← permW,
        Layout.permW_sqStage2Word_oneLayer (Y := Y) (hn := hn) (hc := hc) (hsp₁ true) (hsp₂ true) hmem,
        Layout.permW_sqStage2Word_oneLayer (Y := Y) (hn := hn) (hc := hc) (hsp₁ false) (hsp₂ false)
          hmem]
    rw [hs₃def, act_of_fix hfix, hs₂def, act_of_fix (Y.permW_twistWord_oneLayer hn hmem), hs₁def]
    exact hw₁s p hp
  -- Stage 3.
  let Sv : Oblique n → Prop := fun q ↦ ∀ u, s₃.get (q.name.sticker u) = u.1.dir .outer
  set U : Finset (Oblique n) := univ.filter fun q ↦ ¬ Sv q with hU
  set l : List (OrbitName n) := U.toList.map Oblique.name with hl
  have hlnd : l.Nodup := (Finset.nodup_toList _).map Oblique.name_inj
  have hlmem : ∀ q ∈ l, ∃ q' ∈ U, q'.name = q := by
    intro q hq
    obtain ⟨q', hq', rfl⟩ := List.mem_map.mp hq
    exact ⟨q', Finset.mem_toList.mp hq', rfl⟩
  have hcan : ∀ q ∈ l, CanSolve K₂ q := by
    intro q hq
    obtain ⟨q', -, rfl⟩ := hlmem q hq
    exact hK₂ q'
  obtain ⟨w₄, hw₄, hw₄a, hw₄b⟩ := solve_orbits l hlnd hcan s₃ fun q _ ↦ hs₃.balanced q
  refine ⟨w₁ ++ (w₂ ++ (w₃ ++ w₄)), ?_, ?_⟩
  · rw [act_append, act_append, act_append]
    change act w₄ s₃ = solved n
    refine State.ext_get fun p ↦ ?_
    by_cases hp : Stage1 p
    · rw [hw₄b p, hst p hp]
      intro q hq u hpq
      obtain ⟨q', -, rfl⟩ := hlmem q hq
      exact hp ⟨q'.name, u, (Finset.mem_offDiag.mp q'.2).2.2, hpq⟩
    · obtain ⟨q, u, hqne, rfl⟩ := not_not.mp hp
      have hq' : ∃ q' : Oblique n, q'.name = q :=
        ⟨⟨q.1, Finset.mem_offDiag.mpr ⟨mem_layerSet.mpr q.2.1, mem_layerSet.mpr q.2.2, hqne⟩⟩, rfl⟩
      obtain ⟨q', rfl⟩ := hq'
      have hsolvedp : (solved n).get (q'.name.sticker u) = u.1.dir .outer :=
        solved_embed q'.name.2.1 q'.name.2.2 u.1
      by_cases hsv : Sv q'
      · rw [hw₄b _ fun q₂ hq₂ u₂ he ↦ ?_, hsv u, hsolvedp]
        obtain ⟨q₃, hq₃, rfl⟩ := hlmem q₂ hq₂
        obtain ⟨h₁, -⟩ := OrbitName.sticker_inj he
        have : q' = q₃ := Oblique.name_inj h₁
        rw [this] at hsv
        exact (Finset.mem_filter.mp hq₃).2 hsv
      · have hqU : q' ∈ U := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsv⟩
        rw [hw₄a _ (List.mem_map.mpr ⟨q', Finset.mem_toList.mpr hqU, rfl⟩) u, hsolvedp]
  · -- The length.
    have hlen₁ : (w₁.length : ℝ) ≤ (K₁ * n : ℕ) := by exact_mod_cast hw₁
    have hlen₂ : (w₂.length : ℝ) ≤ (2 * L * (allCycles.length * cycleLen h c a 1 2) : ℕ) := by
      exact_mod_cast Y.length_twistWord hn ha (2 * L) lst
    have hlen₃ : (w₃.length : ℝ) ≤ (((S true).len h a + (S false).len h a : ℕ) : ℝ) := by
      have hq : ∀ q, (w₃q q).length ≤ (S q).len h a := fun q ↦
        Y.length_sqStage2Word hn hc (S q).T _ (S q).B₁ (S q).B₂ (sp₁ q) (sp₂ q) (S q).hM₁
          (S q).hM₂
      have : w₃.length ≤ (S true).len h a + (S false).len h a := by
        rw [hw₃, List.length_append]
        exact Nat.add_le_add (hq true) (hq false)
      exact_mod_cast this
    -- Count the solved orbits.
    let Good : Bool → Finset (Tuple h a c) := fun q ↦ univ.filter fun τ ↦ GoodSq q (rep τ)
    let GS : Finset ((Tuple h a c × Fin c) × Bool) :=
      ((Good true ×ˢ univ) ×ˢ {true}) ∪ ((Good false ×ˢ univ) ×ˢ {false})
    let Ψ : (Tuple h a c × Fin c) × Bool → Oblique n := fun x ↦
      if x.2 then obliqueOf (hee x.1.1 x.1.2) (hdd x.1.1) (hed x.1.1 x.1.2)
      else obliqueOf (hdd x.1.1) (hee x.1.1 x.1.2) (Ne.symm (hed x.1.1 x.1.2))
    have hΨinj : Function.Injective Ψ := by
      rintro ⟨⟨τ, k⟩, f⟩ ⟨⟨τ', k'⟩, f'⟩ he
      have hval := congrArg Subtype.val he
      have hcase : ∀ {σ σ' : Tuple h a c} {j j' : Fin c}, ee σ j = dd σ' → dd σ = ee σ' j' →
          False := by
        intro σ σ' j j' h₁ h₂
        have a₁ := (Y.inj _ _ _ _ _ _ h₁).1
        have a₂ := (Y.inj _ _ _ _ _ _ h₂).1
        have b₁ := hlt σ
        rw [a₁, a₂] at b₁
        exact absurd b₁ (not_lt_of_gt (hlt σ'))
      have hsame : ∀ {σ σ' : Tuple h a c} {j j' : Fin c}, ee σ j = ee σ' j' → dd σ = dd σ' →
          σ = σ' ∧ j = j' := by
        intro σ σ' j j' h₁ h₂
        obtain ⟨a₁, a₂, a₃⟩ := Y.inj _ _ _ _ _ _ h₁
        obtain ⟨b₁, b₂, b₃⟩ := Y.inj _ _ _ _ _ _ h₂
        refine ⟨?_, a₃⟩
        cases σ
        cases σ'
        simp only at a₁ a₂ b₁ b₂ b₃
        subst a₁ a₂ b₁ b₂ b₃
        rfl
      cases f <;> cases f' <;> simp only [Ψ, obliqueOf, ite_true, ite_false, Bool.false_eq_true,
        Prod.mk.injEq] at hval
      · obtain ⟨h₁, h₂⟩ := hsame hval.2 hval.1
        subst h₁ h₂
        rfl
      · exact (hcase hval.2 hval.1).elim
      · exact (hcase hval.1 hval.2).elim
      · obtain ⟨h₁, h₂⟩ := hsame hval.1 hval.2
        subst h₁ h₂
        rfl
    have hΨsv : ∀ x ∈ GS, Sv (Ψ x) := by
      rintro ⟨⟨τ, k⟩, f⟩ hx
      have hτ : GoodSq f (rep τ) := by
        simp only [GS, Good, Finset.mem_union, Finset.mem_product, Finset.mem_singleton,
          Finset.mem_filter, Finset.mem_univ, true_and, and_true] at hx
        rcases hx with ⟨h₁, rfl⟩ | ⟨h₁, rfl⟩ <;> exact h₁
      have hsol := hview₃ f τ hτ k
      cases f
      · -- The left orbit `O(d, e)`.
        intro u
        have heq : OrbitName.sticker (⟨(dd τ, ee τ k), hdd τ, hee τ k⟩ : OrbitName n) u =
            embed (hee τ k) (hdd τ) u.1.swap := embed_swap (hdd τ) (hee τ k) u.1
        change s₃.get (OrbitName.sticker ⟨(dd τ, ee τ k), hdd τ, hee τ k⟩ u) = _
        rw [heq]
        exact hsol ⟨u.1.swap, Pos.swap_not_proper u.1 u.2⟩
      · -- The right orbit `O(e, d)`.
        intro u
        exact hsol u
    have hcount : #GS ≤ #(univ.filter Sv) :=
      Finset.card_le_card_of_injOn Ψ (fun x hx ↦ by
        simpa using hΨsv x hx) hΨinj.injOn
    have hcard : #GS = #(Good true) * c + #(Good false) * c := by
      rw [Finset.card_union_of_disjoint]
      · simp [Finset.card_product]
      · rw [Finset.disjoint_left]
        intro x h₁ h₂
        have e₁ := Finset.mem_singleton.mp (Finset.mem_product.mp h₁).2
        have e₂ := Finset.mem_singleton.mp (Finset.mem_product.mp h₂).2
        rw [e₁] at e₂
        exact Bool.noConfusion e₂
    have hUsv : #U + #(univ.filter Sv) = Fintype.card (Oblique n) := by
      rw [hU, add_comm, Finset.card_filter_add_card_filter_not, Finset.card_univ]
    have hobl : Fintype.card (Oblique n) ≤ (n / 2 - 1) ^ 2 := by
      rw [Fintype.card_coe, Finset.offDiag_card, card_layerSet, sq]
      omega
    have hGoodge : ∀ q, (1 - c * β) * ((groupPairs h).length * (a * (a * c))) ≤
        (#(Good q) : ℝ) := by
      intro q
      set BT := univ.filter fun τ : Tuple h a c ↦ (fun k ↦ X q τ k) ∈ Bad q with hBT
      set NG := univ.filter fun τ : Tuple h a c ↦ ¬ GoodSq q (rep τ) with hNG
      have hsplit : (#(Good q) : ℝ) + #NG = Fintype.card (Tuple h a c) := by
        have := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Tuple h a c)))
          (fun τ ↦ GoodSq q (rep τ))
        rw [Finset.card_univ] at this
        exact_mod_cast this
      -- A bad super-tuple has a bad row.
      have hbadrow : ∀ τ ∈ NG, ∃ i, sqR (rep τ) i ∈ BT := by
        intro τ hτ
        simp only [hNG, Finset.mem_filter, Finset.mem_univ, true_and, GoodSq] at hτ
        push Not at hτ
        obtain ⟨i, hi⟩ := hτ
        exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
      have : Nonempty (Fin c) := ⟨⟨0, hc⟩⟩
      choose! fr hfr using hbadrow
      have hrr : ∀ τ : Tuple h a c, rep (rep τ) = rep τ := fun τ ↦ Tuple.rep_sqRow hc hca τ _
      have hNGle : #NG ≤ c * #BT := by
        refine Finset.card_le_mul_card_image_of_maps_to (f := fun τ ↦ sqR (rep τ) (fr τ)) hfr c
          fun σ _ ↦ ?_
        have hinj : Set.InjOn iOf ({τ ∈ NG | sqR (rep τ) (fr τ) = σ} : Finset _) := by
          intro τ hτ τ' hτ' he
          simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hτ hτ'
          have h₁ : rep τ = rep τ' := by
            have := congrArg rep (hτ.2.trans hτ'.2.symm)
            simpa [sqR, rep, Tuple.rep_sqRow, hrr] using this
          calc τ = sqR (rep τ) (iOf τ) := by
                simp only [sqR, rep, Tuple.sqRow_rep, hiOf, Tuple.sqRow_self hc]
            _ = sqR (rep τ') (iOf τ') := by rw [h₁, he]
            _ = τ' := by simp only [sqR, rep, Tuple.sqRow_rep, hiOf, Tuple.sqRow_self hc]
        have := Finset.card_le_card_of_injOn iOf (t := (univ : Finset (Fin c)))
          (fun _ _ ↦ Finset.mem_coe.mpr (Finset.mem_univ _)) hinj
        simpa using this
      have hb₂ := hr q
      rw [card_tuple] at hsplit hb₂
      have hBTle : (#BT : ℝ) ≤ β * ((groupPairs h).length * (a * (a * c))) := by
        convert hb₂
      have hNGle' : (#NG : ℝ) ≤ c * #BT := by exact_mod_cast hNGle
      have hc₀ : (0 : ℝ) ≤ c := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hBTle hc₀]
    have hUreal : (#U : ℝ) ≤ ((n / 2 - 1 : ℕ) : ℝ) ^ 2 -
        c * ((#(Good true) : ℝ) + #(Good false)) := by
      have h₁ : #U + (#(Good true) * c + #(Good false) * c) ≤ (n / 2 - 1) ^ 2 := by
        rw [← hcard]
        omega
      have h₂ : ((#U + (#(Good true) * c + #(Good false) * c) : ℕ) : ℝ) ≤
          (((n / 2 - 1) ^ 2 : ℕ) : ℝ) := by
        exact_mod_cast h₁
      push_cast at h₂
      linarith
    have hP : (2 : ℝ) * (groupPairs h).length = (h : ℝ) ^ 2 - h := by
      have := two_length_groupPairs h
      have h' : ((2 * (groupPairs h).length + h : ℕ) : ℝ) = ((h ^ 2 : ℕ) : ℝ) := by rw [this]
      push_cast at h'
      linarith
    have hUfinal : (#U : ℝ) ≤ ((n / 2 - 1 : ℕ) : ℝ) ^ 2 -
        (1 - c * β) * (((h : ℝ) ^ 2 - h) * ((a : ℝ) * c) ^ 2) := by
      have hc₀ : (0 : ℝ) ≤ c := by positivity
      have h₁ := mul_le_mul_of_nonneg_left (add_le_add (hGoodge true) (hGoodge false)) hc₀
      have e : (c : ℝ) * ((1 - c * β) * ((groupPairs h).length * (a * (a * c))) +
          (1 - c * β) * ((groupPairs h).length * (a * (a * c)))) =
          (1 - c * β) * ((2 * (groupPairs h).length) * ((a : ℝ) * c) ^ 2) := by ring
      rw [e, hP] at h₁
      linarith
    have hl_len : (l.length : ℝ) = #U := by
      simp [hl]
    have hlen₄ : (w₄.length : ℝ) ≤ K₂ * (((n / 2 - 1 : ℕ) : ℝ) ^ 2 -
        (1 - c * β) * (((h : ℝ) ^ 2 - h) * ((a : ℝ) * c) ^ 2)) := by
      have h₁ : (w₄.length : ℝ) ≤ K₂ * l.length := by exact_mod_cast hw₄
      rw [hl_len] at h₁
      exact h₁.trans (mul_le_mul_of_nonneg_left hUfinal (by positivity))
    simp only [List.length_append]
    push_cast at hlen₁ hlen₂ hlen₃ hlen₄ ⊢
    linarith

end CubeGod
