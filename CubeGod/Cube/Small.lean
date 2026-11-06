import CubeGod.Cube.Classify

/-!
# A small cube inside the big one

Fix a layer `d` of `I`. The stickers of the n×n×n cube that are, from each face, in layer `1`, `d`,
the middle, `n + 1 - d` or `n` behave exactly like the stickers of a small cube: a 4×4×4 if `n` is
even, and a 5×5×5 if `n` is odd. The small cube's layers `1, 2, 3, …, m` stand for those, in order:
the big cube's layer `d` acts as layer 2 of the small cube, and so on. Every other move does nothing
to them.

So `liftS` puts `Sticker m` inside `Sticker n`, and `down` says what any move of the big cube does to
the small cube. Everything here is used by `CubeGod.Cube.Stage1`.
-/

open Finset

namespace CubeGod

instance : Fintype Direction :=
  ⟨{Cw, Ccw}, by intro x; cases x <;> simp⟩

/-- The moves, as a triple. -/
def moveEquiv (n : ℕ) : Move n ≃ Face × Fin n × Direction where
  toFun m := (m.face, ⟨m.layer - 1, by have := m.layer_pos; have := m.layer_le; omega⟩, m.dir)
  invFun t := ⟨t.1, t.2.1 + 1, t.2.2, by omega, t.2.1.2⟩
  left_inv m := by
    have := m.layer_pos
    ext <;> simp
    omega
  right_inv t := by simp

instance (n : ℕ) : Fintype (Move n) := Fintype.ofEquiv _ (moveEquiv n).symm

theorem card_move (n : ℕ) : Fintype.card (Move n) = 6 * n * 2 := by
  rw [Fintype.card_congr (moveEquiv n), Fintype.card_prod, Fintype.card_prod, Fintype.card_fin]
  simp only [show Fintype.card Face = 6 from rfl, show Fintype.card Direction = 2 from rfl]
  ring

/-- Every solvable state is solved by a word of at most `D(n)` moves. -/
theorem exists_word_le {n : ℕ} {s : State n} (hs : Solvable s) :
    ∃ w, act w s = solved n ∧ w.length ≤ godsNumber n := by
  have hne : {k | ∃ w : List (Move n), w.length = k ∧ act w s = solved n}.Nonempty := by
    obtain ⟨w, hw⟩ := hs
    exact ⟨w.length, w, rfl, hw⟩
  obtain ⟨w, hw, hsol⟩ := Nat.sInf_mem hne
  refine ⟨w, hsol, ?_⟩
  rw [hw]
  have hbdd : BddAbove {k | ∃ s : State n, Solvable s ∧ dist s = k} := by
    have : ({k | ∃ s : State n, Solvable s ∧ dist s = k} : Set ℕ) ⊆ Set.range (dist (n := n)) := by
      rintro k ⟨s, -, rfl⟩
      exact ⟨s, rfl⟩
    exact ((Set.finite_range (dist (n := n))).subset this).bddAbove
  exact le_csSup hbdd ⟨s, hs, rfl⟩


/-- `m` is the small cube for `n`: 4 if `n` is even, 5 if `n` is odd. -/
def SmallFor (n m : ℕ) : Prop := (m = 4 ∧ n % 2 = 0) ∨ (m = 5 ∧ n % 2 = 1)

variable {n m d : ℕ}

/-- The layer of the big cube that a layer of the small cube stands for. -/
def liftIdx (n m d x : ℕ) : ℕ :=
  if x = 1 then 1 else if x = 2 then d else if x = m then n else if x = m - 1 then n + 1 - d
  else (n + 1) / 2

/-- The layer of the small cube that a layer of the big cube is, if any, ignoring `d`. -/
def unliftFlat (n m l : ℕ) : Option ℕ :=
  if l = 1 then some 1 else if l = n then some m else if m = 5 ∧ 2 * l = n + 1 then some 3
  else none

/-- The layer of the small cube that a layer of the big cube is, if any. -/
def unlift (n m d l : ℕ) : Option ℕ :=
  if l = d then some 2 else if l = n + 1 - d then some (m - 1) else unliftFlat n m l

section Lift

variable (hS : SmallFor n m) (hd : InI n d)
include hS hd

omit hS in
theorem liftIdx_pos (x : ℕ) : 1 ≤ liftIdx n m d x := by
  have := hd.1; have := hd.2
  unfold liftIdx
  split_ifs <;> omega

omit hS in
theorem liftIdx_le (x : ℕ) : liftIdx n m d x ≤ n := by
  have := hd.1; have := hd.2
  unfold liftIdx
  split_ifs <;> omega

theorem liftIdx_flip {x : ℕ} (hx₁ : 1 ≤ x) (hx₂ : x ≤ m) :
    liftIdx n m d (m + 1 - x) = n + 1 - liftIdx n m d x := by
  have := hd.1; have := hd.2
  unfold liftIdx
  rcases hS with ⟨rfl, hp⟩ | ⟨rfl, hp⟩ <;> split_ifs <;> omega

theorem liftIdx_inj {x y : ℕ} (hx₁ : 1 ≤ x) (hx₂ : x ≤ m) (hy₁ : 1 ≤ y) (hy₂ : y ≤ m)
    (h : liftIdx n m d x = liftIdx n m d y) : x = y := by
  have := hd.1; have := hd.2
  unfold liftIdx at h
  rcases hS with ⟨rfl, hp⟩ | ⟨rfl, hp⟩ <;> split_ifs at h <;> omega

theorem unlift_liftIdx {x : ℕ} (hx₁ : 1 ≤ x) (hx₂ : x ≤ m) :
    unlift n m d (liftIdx n m d x) = some x := by
  have := hd.1; have := hd.2
  unfold unlift unliftFlat liftIdx
  rcases hS with ⟨rfl, hp⟩ | ⟨rfl, hp⟩ <;> split_ifs <;> first | rfl | omega | simp_all <;> omega

theorem liftIdx_of_unlift {l k : ℕ} (h : unlift n m d l = some k) :
    1 ≤ k ∧ k ≤ m ∧ liftIdx n m d k = l := by
  have := hd.1; have := hd.2
  unfold unlift unliftFlat at h
  unfold liftIdx
  rcases hS with ⟨rfl, hp⟩ | ⟨rfl, hp⟩ <;> split_ifs at h <;> simp only [Option.some.injEq] at h <;>
    subst h <;> simp <;> omega

omit hS in
/-- A small sticker in the big cube. Column or row `i` is in layer `i + 1` from one side. -/
def liftS (v : Sticker m) : Sticker n :=
  (v.1, ⟨liftIdx n m d (v.2.1 + 1) - 1, by
      have := liftIdx_le (m := m) hd (v.2.1 + 1); have := hd.1; have := hd.2; omega⟩,
    ⟨liftIdx n m d (v.2.2 + 1) - 1, by
      have := liftIdx_le (m := m) hd (v.2.2 + 1); have := hd.1; have := hd.2; omega⟩)

theorem layerFrom_liftS (G : Face) (v : Sticker m) :
    layerFrom G (liftS hd v) = liftIdx n m d (layerFrom G v) := by
  have hm : 1 ≤ m := by rcases hS with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> norm_num
  have h₀ : liftIdx n m d 1 = 1 := by simp [liftIdx]
  have h₁ : liftIdx n m d m = n := by
    have := liftIdx_flip hS hd le_rfl hm
    rw [Nat.add_sub_cancel, h₀, Nat.add_sub_cancel] at this
    exact this
  have hi := liftIdx_flip hS hd (Nat.le_add_left 1 _) v.2.1.2
  have hj := liftIdx_flip hS hd (Nat.le_add_left 1 _) v.2.2.2
  have pi := liftIdx_pos (m := m) hd (v.2.1 + 1)
  have pj := liftIdx_pos (m := m) hd (v.2.2 + 1)
  have hi' : m + 1 - (v.2.1 + 1) = m - v.2.1 := by omega
  have hj' : m + 1 - (v.2.2 + 1) = m - v.2.2 := by omega
  rw [hi'] at hi
  rw [hj'] at hj
  unfold layerFrom liftS
  split_ifs <;> simp only [h₀, h₁, hi, hj] <;> omega

end Lift

/-- A sticker is determined by its face and all its layers. -/
theorem Sticker.ext_all {p q : Sticker n} (h₁ : p.1 = q.1)
    (h₂ : ∀ f, layerFrom f p = layerFrom f q) : p = q :=
  Sticker.ext_layerFrom h₁ (h₂ _) (h₂ _)

theorem ofBool_cw (x : Move n) : Direction.ofBool x.cw = x.dir := by
  obtain ⟨E, l, d⟩ := x
  cases d <;> rfl

/-- A move of the small cube, as a move of the big cube. -/
def liftMove (hd : InI n d) (x : Move m) : Move n :=
  ⟨x.face, liftIdx n m d x.layer, x.dir, liftIdx_pos hd _, liftIdx_le hd _⟩

/-- A lifted move acts on the small cube as the move. -/
theorem perm_liftMove (hS : SmallFor n m) (hd : InI n d) (x : Move m) (v : Sticker m) :
    (liftMove hd x).perm (liftS hd v) = liftS hd (x.perm v) := by
  by_cases h : layerFrom x.face v = x.layer
  · have h' : layerFrom (liftMove hd x).face (liftS hd v) = (liftMove hd x).layer := by
      simp [liftMove, layerFrom_liftS hS hd, h]
    refine Sticker.ext_all ?_ fun f ↦ ?_
    · rw [Move.perm_face h']
      exact (Move.perm_face h).symm
    · have hf : f = x.face.turnBy x.dir (x.face.turnBy x.dir.reverse f) := by
        have := x.face.turnBy_reverse x.dir.reverse f
        rw [Direction.reverse_reverse] at this
        exact this.symm
      rw [hf]
      have e₁ := Move.layerFrom_perm h' (x.face.turnBy x.dir.reverse f)
      have e₂ := Move.layerFrom_perm h (x.face.turnBy x.dir.reverse f)
      rw [show (liftMove hd x).face = x.face from rfl,
        show (liftMove hd x).dir = x.dir from rfl] at e₁
      rw [e₁, layerFrom_liftS hS hd, layerFrom_liftS hS hd, ← e₂]
  · have h' : layerFrom (liftMove hd x).face (liftS hd v) ≠ (liftMove hd x).layer := by
      simp only [liftMove, layerFrom_liftS hS hd]
      exact fun e ↦ h (liftIdx_inj hS hd (layerFrom_pos _ _) (layerFrom_le _ _) x.layer_pos
        x.layer_le e)
    rw [Move.perm_of_ne h, Move.perm_of_ne h']

/-- A move of the big cube that isn't a layer of the small cube leaves it alone. -/
theorem perm_liftS_other (hS : SmallFor n m) (hd : InI n d) (x : Move n)
    (hx : unlift n m d x.layer = none) (v : Sticker m) : x.perm (liftS hd v) = liftS hd v := by
  refine Move.perm_of_ne fun h ↦ ?_
  rw [layerFrom_liftS hS hd] at h
  rw [← h, unlift_liftIdx hS hd (layerFrom_pos _ _) (layerFrom_le _ _)] at hx
  exact Option.some_ne_none _ hx

variable (hm : 0 < (m + 1) / 2)

/-- The move of the small cube at layer `k`, with the face and direction of `x`. -/
def smallMove (k : ℕ) (x : Move n) : Move m := mv hm k x.face x.cw

/-- What a move of the big cube does to the small cube of layer `d`. -/
def down (d : ℕ) (x : Move n) : Equiv.Perm (Sticker m) :=
  match unlift n m d x.layer with
  | some k => (smallMove hm k x).perm
  | none => 1

/-- What a move of the big cube does to the small cube of a layer that it isn't. -/
def flat (x : Move n) : Equiv.Perm (Sticker m) :=
  match unliftFlat n m x.layer with
  | some k => (smallMove hm k x).perm
  | none => 1

/-- A move of the small cube, with its inner layers, `2` and `m - 1`, dropped. -/
def dropOne (x : Move m) : Equiv.Perm (Sticker m) :=
  if x.layer = 2 ∨ x.layer = m - 1 then 1 else x.perm

theorem dropOne_inv (x : Move m) : dropOne x.inv = (dropOne x)⁻¹ := by
  have hl : x.inv.layer = x.layer := rfl
  unfold dropOne
  rw [hl]
  split_ifs
  · rw [inv_one]
  · rw [Move.perm_inv]

theorem smallMove_eq {k : ℕ} (hk₁ : 1 ≤ k) (hk₂ : k ≤ m) (x : Move n) (y : Move m)
    (hf : y.face = x.face) (hdir : y.dir = x.dir) (hl : y.layer = k) : smallMove hm k x = y := by
  apply Move.ext
  · exact hf.symm
  · exact (layer_mv hm hk₁ hk₂ _ _).trans hl.symm
  · simp only [smallMove, mv]
    rw [ofBool_cw, hdir]

theorem layer_smallMove {k : ℕ} (hk₁ : 1 ≤ k) (hk₂ : k ≤ m) (x : Move n) :
    (smallMove hm k x).layer = k :=
  layer_mv hm hk₁ hk₂ _ _

/-- A move of the big cube acts on the small cube as `down`. -/
theorem perm_liftS (hS : SmallFor n m) (hd : InI n d) (x : Move n) (v : Sticker m) :
    x.perm (liftS hd v) = liftS hd (down hm d x v) := by
  unfold down
  split
  · rename_i k hk
    obtain ⟨hk₁, hkm, hl⟩ := liftIdx_of_unlift hS hd hk
    have : liftMove hd (smallMove hm k x) = x := by
      apply Move.ext
      · rfl
      · simp [liftMove, layer_smallMove hm hk₁ hkm, hl]
      · simp [liftMove, smallMove, mv, ofBool_cw]
    rw [← perm_liftMove hS hd, this]
  · rename_i hk
    exact perm_liftS_other hS hd x hk v

theorem permW_liftS (hS : SmallFor n m) (hd : InI n d) (w : List (Move n)) (v : Sticker m) :
    permW w (liftS hd v) = liftS hd (evalW (down hm d) w v) := by
  induction w generalizing v with
  | nil => rfl
  | cons x w ih =>
    simp only [permW, evalW_cons, Equiv.Perm.mul_apply] at ih ⊢
    rw [perm_liftS hm hS hd, ih]

/-- Words that agree on a small cube agree on what they do to its stickers. -/
theorem act_liftS_eq (hS : SmallFor n m) (hd : InI n d)
    {w w' : List (Move n)} (h : evalW (down hm d) w = evalW (down hm d) w') (s : State n)
    (v : Sticker m) : (act w s).get (liftS hd v) = (act w' s).get (liftS hd v) := by
  have hsym : ∀ w : List (Move n), (permW w).symm (liftS hd v) =
      liftS hd ((evalW (down hm d) w)⁻¹ v) := by
    intro w
    rw [Equiv.symm_apply_eq, permW_liftS hm hS hd]
    simp
  rw [act_eq, act_eq, Function.comp, Function.comp, hsym, hsym, h]

end CubeGod
