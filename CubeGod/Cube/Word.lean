import CubeGod.Cube.Pos

/-!
# Words of moves

A word is a list of moves, done first to last. We evaluate a word in any group, by sending each move to
a group element. There are two uses. Sending each move to its permutation of the stickers gives what
the word does to the cube, and sending each move to its letter gives what it does to a pair.
-/

namespace CubeGod

variable {n : ℕ} {H L : Type*} [Group H]

/-- Evaluate a word in a group. The first letter is on the right, so it acts first. -/
def evalW (φ : L → H) : List L → H
  | [] => 1
  | m :: w => evalW φ w * φ m

@[simp] theorem evalW_nil (φ : L → H) : evalW φ [] = 1 := rfl

@[simp] theorem evalW_cons (φ : L → H) (m : L) (w : List L) :
    evalW φ (m :: w) = evalW φ w * φ m := rfl

theorem evalW_append (φ : L → H) (w₁ w₂ : List L) :
    evalW φ (w₁ ++ w₂) = evalW φ w₂ * evalW φ w₁ := by
  induction w₁ with
  | nil => simp
  | cons m w ih => simp [ih, mul_assoc]

/-- The word that undoes `w`. -/
def invW (w : List (Move n)) : List (Move n) := (w.map Move.inv).reverse

@[simp] theorem invW_nil : invW ([] : List (Move n)) = [] := rfl

theorem invW_cons (m : Move n) (w : List (Move n)) : invW (m :: w) = invW w ++ [m.inv] := by
  simp [invW]

@[simp] theorem length_invW (w : List (Move n)) : (invW w).length = w.length := by
  simp [invW]

theorem evalW_invW {φ : Move n → H} (hφ : ∀ m, φ m.inv = (φ m)⁻¹) (w : List (Move n)) :
    evalW φ (invW w) = (evalW φ w)⁻¹ := by
  induction w with
  | nil => simp
  | cons m w ih => simp [invW_cons, evalW_append, ih, hφ]

theorem evalW_conj {φ : Move n → H} (hφ : ∀ m, φ m.inv = (φ m)⁻¹) (w y : List (Move n)) :
    evalW φ (w ++ y ++ invW w) = (evalW φ w)⁻¹ * evalW φ y * evalW φ w := by
  rw [evalW_append, evalW_append, evalW_invW hφ, mul_assoc]

theorem letterOf_inv (d₁ d₂ : ℕ) (m : Move n) : letterOf d₁ d₂ m.inv = (letterOf d₁ d₂ m)⁻¹ := by
  have hl : m.inv.layer = m.layer := rfl
  have hf : m.inv.face = m.face := rfl
  simp only [letterOf, hl, hf, Move.cw_inv, Bool.not_not]
  split_ifs <;> simp [letter_inv]

/-- What a word does to the stickers. -/
abbrev permW (w : List (Move n)) : Equiv.Perm (Sticker n) := evalW Move.perm w

/-- What a word does to the positions of the pair `d₁`, `d₂`. -/
abbrev pairW (d₁ d₂ : ℕ) (w : List (Move n)) : Equiv.Perm Pos := evalW (letterOf d₁ d₂) w

theorem act_cons (m : Move n) (w : List (Move n)) (s : State n) :
    act (m :: w) s = act w (m.apply s) := rfl

theorem act_append (w₁ w₂ : List (Move n)) (s : State n) :
    act (w₁ ++ w₂) s = act w₂ (act w₁ s) := by
  simp [act, List.foldl_append]

theorem act_eq (w : List (Move n)) (s : State n) : (act w s).get = s.get ∘ (permW w).symm := by
  induction w generalizing s with
  | nil => rfl
  | cons m w ih =>
    rw [act_cons, ih]
    funext p
    simp [Move.apply_get, permW, evalW_cons, Equiv.Perm.mul_def]

/-- A word changes a pair's view by its letters. -/
theorem pairView_act {d₁ d₂ : ℕ} (h₁ : InI n d₁) (h₂ : InI n d₂) (hne : d₁ ≠ d₂)
    (w : List (Move n)) (s : State n) :
    pairView h₁ h₂ (act w s) = pairView h₁ h₂ s ∘ (pairW d₁ d₂ w).symm := by
  induction w generalizing s with
  | nil => rfl
  | cons m w ih =>
    rw [act_cons, ih, pairView_apply h₁ h₂ hne]
    funext u
    simp [pairW, evalW_cons, Equiv.Perm.mul_def]

end CubeGod
