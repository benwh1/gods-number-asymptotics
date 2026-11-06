import CubeGod.Cube.Defs

/-!
# The 48 positions of a pair

Fix two layers `d₁ ≠ d₂` strictly between the outside layer and the middle. The stickers in layer
`d₁` from one face and `d₂` from another are exactly the stickers on a face `u₃` in layer `d₁` from
`u₁` and `d₂` from `u₂`, where `u₁, u₂, u₃` are faces on three different axes. There are 48 such
triples, 24 right-handed and 24 left-handed, and these are the two mirror-image orbits of the pair.

A move of layer `d₁` of a face `E` moves exactly the positions with `u₁ = E`, and it turns all three of
the `uᵢ` as a whole-cube rotation would. Layer `d₂` does the same with `u₂`, and the face `E` with `u₃`.
The layers `n + 1 - d₁`, `n + 1 - d₂` and `n` are the same layers counted from the opposite face. So
the action doesn't depend on `n`, `d₁` or `d₂`.
-/

namespace CubeGod

/-- The 48 triples of faces on three different axes. -/
abbrev Pos := {u : Face × Face × Face // u.1.axis ≠ u.2.1.axis ∧ u.1.axis ≠ u.2.2.axis ∧
  u.2.1.axis ≠ u.2.2.axis}

/-- The right-handed triples: turning `u₁` clockwise takes `u₂` to the opposite of `u₃`. For example
`(R, U, F)`. -/
def Pos.Proper (u : Pos) : Prop := u.1.1.turn u.1.2.1 = u.1.2.2.opp

instance : DecidablePred Pos.Proper := fun u ↦ by
  unfold Pos.Proper; infer_instance

theorem card_pos : Fintype.card Pos = 48 := by decide +kernel

/-- Turn all three directions of a position clockwise about `E`. -/
def Pos.turn (E : Face) (u : Pos) : Pos :=
  ⟨(E.turn u.1.1, E.turn u.1.2.1, E.turn u.1.2.2),
    Face.axis_turn _ _ _ u.2.1, Face.axis_turn _ _ _ u.2.2.1, Face.axis_turn _ _ _ u.2.2.2⟩

/-- Turn all three directions of a position anticlockwise about `E`. -/
def Pos.unturn (E : Face) (u : Pos) : Pos :=
  ⟨(E.unturn u.1.1, E.unturn u.1.2.1, E.unturn u.1.2.2),
    Face.axis_unturn _ _ _ u.2.1, Face.axis_unturn _ _ _ u.2.2.1, Face.axis_unturn _ _ _ u.2.2.2⟩

/-- Which of the three directions a letter acts on. -/
inductive Role
  /-- the layer `d₁` -/
  | one
  /-- the layer `d₂` -/
  | two
  /-- the outside layer -/
  | outer
  deriving DecidableEq, Repr

/-- The direction of a position that a role looks at. -/
def Pos.dir (u : Pos) : Role → Face
  | .one => u.1.1
  | .two => u.1.2.1
  | .outer => u.1.2.2

/-- What a turn acts as on the 48 positions. -/
def letterFn (ρ : Role) (E : Face) (cw : Bool) (u : Pos) : Pos :=
  if u.dir ρ = E then (if cw then u.turn E else u.unturn E) else u

theorem Pos.dir_turn (u : Pos) (ρ : Role) (E : Face) : (u.turn E).dir ρ = E.turn (u.dir ρ) := by
  cases ρ <;> rfl

theorem Pos.dir_unturn (u : Pos) (ρ : Role) (E : Face) :
    (u.unturn E).dir ρ = E.unturn (u.dir ρ) := by
  cases ρ <;> rfl

theorem Pos.unturn_turn (E : Face) (u : Pos) : (u.turn E).unturn E = u := by
  apply Subtype.ext
  simp [Pos.turn, Pos.unturn, Face.unturn_turn]

theorem Pos.turn_unturn (E : Face) (u : Pos) : (u.unturn E).turn E = u := by
  apply Subtype.ext
  simp [Pos.turn, Pos.unturn, Face.turn_unturn]

/-- A turn as a permutation of the 48 positions. -/
def letter (ρ : Role) (E : Face) (cw : Bool) : Equiv.Perm Pos where
  toFun := letterFn ρ E cw
  invFun := letterFn ρ E (!cw)
  left_inv u := by
    unfold letterFn
    by_cases h : u.dir ρ = E <;> cases cw <;>
      simp [h, Pos.dir_turn, Pos.dir_unturn, Face.turn_self, Face.unturn_self, Pos.unturn_turn,
        Pos.turn_unturn]
  right_inv u := by
    unfold letterFn
    by_cases h : u.dir ρ = E <;> cases cw <;>
      simp [h, Pos.dir_turn, Pos.dir_unturn, Face.turn_self, Face.unturn_self, Pos.unturn_turn,
        Pos.turn_unturn]

theorem letter_inv (ρ : Role) (E : Face) (cw : Bool) : (letter ρ E cw)⁻¹ = letter ρ E (!cw) :=
  Equiv.ext fun _ ↦ rfl

/-- `d` is a layer of the set `I`: not the outside layer, and strictly before the middle, so that
`d < n + 1 - d`. -/
def InI (n d : ℕ) : Prop := 2 ≤ d ∧ 2 * d ≤ n

instance (n d : ℕ) : Decidable (InI n d) := by unfold InI; infer_instance

variable {n d₁ d₂ : ℕ}

theorem InI.lt_n {d : ℕ} (h : InI n d) : d < n := by
  have := h.1
  have := h.2
  omega

theorem InI.pos {d : ℕ} (h : InI n d) : 1 ≤ d := by
  have := h.1
  omega

/-! ### The sticker at a position -/

/-- The sticker on face `E` in layer `a + 1` from `f` and layer `b + 1` from `g`, for `E`, `f`, `g`
on three different axes. -/
def locate (E f g : Face) (a b : Fin n) : Sticker n :=
  (E, if E.right = f then a.rev else if E.right = f.opp then a else if E.right = g then b.rev else b,
    if E.up = f then a.rev else if E.up = f.opp then a else if E.up = g then b.rev else b)

theorem locate_spec : ∀ (E f g : Face), E.axis ≠ f.axis → E.axis ≠ g.axis → f.axis ≠ g.axis →
    ∀ a b : Fin n,
      layerFrom f (locate E f g a b) = a + 1 ∧ layerFrom g (locate E f g a b) = b + 1 := by
  intro E f g h₁ h₂ h₃ a b
  have := a.2
  have := b.2
  cases E <;> cases f <;> cases g <;> simp only [Face.axis, ne_eq, not_true_eq_false] at h₁ h₂ h₃ <;>
    simp [locate, layerFrom, Face.opp, Face.right, Face.up, Fin.val_rev]
  all_goals omega

/-- The sticker of a pair with layers `d₁`, `d₂` at position `u`: on the face `u₃`, in layer `d₁`
from `u₁` and `d₂` from `u₂`. -/
def embed (h₁ : InI n d₁) (h₂ : InI n d₂) (u : Pos) : Sticker n :=
  locate u.1.2.2 u.1.1 u.1.2.1 ⟨d₁ - 1, by have := h₁.lt_n; omega⟩
    ⟨d₂ - 1, by have := h₂.lt_n; omega⟩

section Embed

variable (h₁ : InI n d₁) (h₂ : InI n d₂) (u : Pos)

theorem embed_face : (embed h₁ h₂ u).1 = u.dir .outer := rfl

theorem layerFrom_embed_one : layerFrom (u.dir .one) (embed h₁ h₂ u) = d₁ := by
  show layerFrom u.1.1 (locate _ _ _ _ _) = d₁
  rw [(locate_spec _ _ _ (Ne.symm u.2.2.1) (Ne.symm u.2.2.2) u.2.1 _ _).1]
  have := h₁.pos
  simp only
  omega

theorem layerFrom_embed_two : layerFrom (u.dir .two) (embed h₁ h₂ u) = d₂ := by
  show layerFrom u.1.2.1 (locate _ _ _ _ _) = d₂
  rw [(locate_spec _ _ _ (Ne.symm u.2.2.1) (Ne.symm u.2.2.2) u.2.1 _ _).2]
  have := h₂.pos
  simp only
  omega

theorem layerFrom_embed_outer : layerFrom (u.dir .outer) (embed h₁ h₂ u) = 1 :=
  layerFrom_self (embed h₁ h₂ u)

/-- A sticker on face `u₃` in layer `d₁` from `u₁` and `d₂` from `u₂` is the pair's sticker at
`u`. -/
theorem eq_embed {p : Sticker n} (e₃ : p.1 = u.dir .outer) (e₁ : layerFrom (u.dir .one) p = d₁)
    (e₂ : layerFrom (u.dir .two) p = d₂) : p = embed h₁ h₂ u :=
  Sticker.ext_layerFrom' (f := u.dir .one) (g := u.dir .two) e₃ (by rw [e₃]; exact Ne.symm u.2.2.1)
    (by rw [e₃]; exact Ne.symm u.2.2.2) u.2.1 (by rw [e₁, layerFrom_embed_one])
    (by rw [e₂, layerFrom_embed_two])

/-- The layer of a pair's sticker from any face, in six cases. -/
theorem layerFrom_embed (G : Face) :
    (G = u.dir .one ∧ layerFrom G (embed h₁ h₂ u) = d₁) ∨
    (G = (u.dir .one).opp ∧ layerFrom G (embed h₁ h₂ u) = n + 1 - d₁) ∨
    (G = u.dir .two ∧ layerFrom G (embed h₁ h₂ u) = d₂) ∨
    (G = (u.dir .two).opp ∧ layerFrom G (embed h₁ h₂ u) = n + 1 - d₂) ∨
    (G = u.dir .outer ∧ layerFrom G (embed h₁ h₂ u) = 1) ∨
    (G = (u.dir .outer).opp ∧ layerFrom G (embed h₁ h₂ u) = n) := by
  rcases Face.eq_of_axes (u.dir .outer) (u.dir .one) (u.dir .two) G (Ne.symm u.2.2.1)
    (Ne.symm u.2.2.2) u.2.1 with e | e | e | e | e | e <;> subst e
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, layerFrom_embed_outer h₁ h₂ u⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      ⟨rfl, by rw [layerFrom_opp, layerFrom_embed_outer, Nat.add_sub_cancel]⟩))))
  · exact Or.inl ⟨rfl, layerFrom_embed_one h₁ h₂ u⟩
  · exact Or.inr (Or.inl ⟨rfl, by rw [layerFrom_opp, layerFrom_embed_one]⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨rfl, layerFrom_embed_two h₁ h₂ u⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, by rw [layerFrom_opp, layerFrom_embed_two]⟩)))

/-- A move that turns a pair's sticker takes it to the sticker at the turned position. -/
theorem perm_embed {m : Move n} (h : layerFrom m.face (embed h₁ h₂ u) = m.layer) :
    m.perm (embed h₁ h₂ u) = embed h₁ h₂ (if m.cw then u.turn m.face else u.unturn m.face) := by
  have key : ∀ ρ : Role, layerFrom ((if m.cw then u.turn m.face else u.unturn m.face).dir ρ)
      (m.perm (embed h₁ h₂ u)) = layerFrom (u.dir ρ) (embed h₁ h₂ u) := by
    intro ρ
    have : (if m.cw then u.turn m.face else u.unturn m.face).dir ρ = m.face.turnBy m.dir (u.dir ρ) := by
      obtain ⟨E, l, d⟩ := m
      cases d <;> simp [Move.cw, Pos.dir_turn, Pos.dir_unturn, Face.turnBy_Cw, Face.turnBy_Ccw]
    rw [this, Move.layerFrom_perm h]
  apply eq_embed
  · rw [Move.perm_face h, embed_face]
    obtain ⟨E, l, d⟩ := m
    cases d <;> simp [Move.cw, Pos.dir_turn, Pos.dir_unturn, Face.turnBy_Cw, Face.turnBy_Ccw]
  · rw [key, layerFrom_embed_one]
  · rw [key, layerFrom_embed_two]

end Embed

/-- What a move does to the 48 positions of the pair `d₁`, `d₂`. A layer `n + 1 - d` of a face is
the layer `d` of the opposite face, turned the other way. -/
def letterOf (d₁ d₂ : ℕ) (m : Move n) : Equiv.Perm Pos :=
  if m.layer = d₁ then letter .one m.face m.cw
  else if m.layer = n + 1 - d₁ then letter .one m.face.opp (!m.cw)
  else if m.layer = d₂ then letter .two m.face m.cw
  else if m.layer = n + 1 - d₂ then letter .two m.face.opp (!m.cw)
  else if m.layer = 1 then letter .outer m.face m.cw
  else if m.layer = n then letter .outer m.face.opp (!m.cw)
  else 1

/-- Turning the opposite face the other way is the same turn of a position. -/
theorem letterFn_opp (ρ : Role) (E : Face) (cw : Bool) (u : Pos) (h : u.dir ρ = E.opp) :
    letterFn ρ E.opp (!cw) u = if cw then u.turn E else u.unturn E := by
  have hu : ∀ v : Pos, v.unturn E.opp = v.turn E := fun v ↦
    Subtype.ext (by simp [Pos.unturn, Pos.turn, Face.opp_unturn])
  have ht : ∀ v : Pos, v.turn E.opp = v.unturn E := fun v ↦
    Subtype.ext (by simp [Pos.unturn, Pos.turn, Face.opp_turn])
  cases cw <;> simp [letterFn, h, hu, ht]

section LetterOf

variable (h₁ : InI n d₁) (h₂ : InI n d₂) (hne : d₁ ≠ d₂) (m : Move n)
include h₁ h₂ hne

omit h₁ h₂ hne in
theorem letterOf_one (h : m.layer = d₁) : letterOf d₁ d₂ m = letter .one m.face m.cw := by
  simp [letterOf, h]

omit hne in
theorem letterOf_one' (h : m.layer = n + 1 - d₁) :
    letterOf d₁ d₂ m = letter .one m.face.opp (!m.cw) := by
  have := h₁.1; have := h₁.2; have := h₂.1; have := h₂.2
  rw [letterOf]
  split_ifs <;> first | rfl | omega

theorem letterOf_two (h : m.layer = d₂) : letterOf d₁ d₂ m = letter .two m.face m.cw := by
  have := h₁.1; have := h₁.2; have := h₂.1; have := h₂.2
  rw [letterOf]
  split_ifs <;> first | rfl | omega

theorem letterOf_two' (h : m.layer = n + 1 - d₂) :
    letterOf d₁ d₂ m = letter .two m.face.opp (!m.cw) := by
  have := h₁.1; have := h₁.2; have := h₂.1; have := h₂.2
  rw [letterOf]
  split_ifs <;> first | rfl | omega

omit hne in
theorem letterOf_outer (h : m.layer = 1) : letterOf d₁ d₂ m = letter .outer m.face m.cw := by
  have := h₁.1; have := h₁.2; have := h₂.1; have := h₂.2
  rw [letterOf]
  split_ifs <;> first | rfl | omega

omit hne in
theorem letterOf_outer' (h : m.layer = n) :
    letterOf d₁ d₂ m = letter .outer m.face.opp (!m.cw) := by
  have := h₁.1; have := h₁.2; have := h₂.1; have := h₂.2
  rw [letterOf]
  split_ifs <;> first | rfl | omega

omit hne in
theorem letterOf_other (a₁ : m.layer ≠ d₁) (a₂ : m.layer ≠ n + 1 - d₁)
    (a₃ : m.layer ≠ d₂) (a₄ : m.layer ≠ n + 1 - d₂) (a₅ : m.layer ≠ 1)
    (a₆ : m.layer ≠ n) : letterOf d₁ d₂ m = 1 := by
  have := h₁.1; have := h₁.2; have := h₂.1; have := h₂.2
  rw [letterOf]
  split_ifs <;> first | rfl | omega

end LetterOf

theorem letter_apply (ρ : Role) (E : Face) (cw : Bool) (u : Pos) :
    letter ρ E cw u = letterFn ρ E cw u := rfl

/-- A move acts on a pair as its letter. So the action doesn't depend on `n`, `d₁` or `d₂`.
-/
theorem perm_embed_letter (h₁ : InI n d₁) (h₂ : InI n d₂) (hne : d₁ ≠ d₂) (m : Move n) (u : Pos) :
    m.perm (embed h₁ h₂ u) = embed h₁ h₂ (letterOf d₁ d₂ m u) := by
  have hturn : ∀ (ρ : Role) (E : Face) (cw : Bool), u.dir ρ = E →
      letter ρ E cw u = if cw then u.turn E else u.unturn E := by
    intro ρ E cw h
    simp [letter, letterFn, h]
  have hfix : ∀ (ρ : Role) (E : Face) (cw : Bool), u.dir ρ ≠ E → letter ρ E cw u = u := by
    intro ρ E cw h
    simp [letter, letterFn, h]
  have hoppd : ∀ (ρ : Role), m.face = (u.dir ρ).opp → u.dir ρ = m.face.opp := by
    intro ρ h; rw [h, Face.opp_opp]
  have dopp : ∀ (ρ : Role) (x : ℕ), layerFrom (u.dir ρ) (embed h₁ h₂ u) = x →
      layerFrom (u.dir ρ).opp (embed h₁ h₂ u) = n + 1 - x := by
    intro ρ x h; rw [layerFrom_opp, h]
  by_cases hin : layerFrom m.face (embed h₁ h₂ u) = m.layer
  · rw [perm_embed h₁ h₂ u hin]
    congr 1
    rcases layerFrom_embed h₁ h₂ u m.face with
      ⟨e, d⟩ | ⟨e, d⟩ | ⟨e, d⟩ | ⟨e, d⟩ | ⟨e, d⟩ | ⟨e, d⟩ <;> rw [d] at hin
    · rw [letterOf_one m hin.symm, hturn _ _ _ e.symm]
    · rw [letterOf_one' h₁ h₂ m hin.symm, letter_apply, letterFn_opp _ _ _ _ (hoppd _ e)]
    · rw [letterOf_two h₁ h₂ hne m hin.symm, hturn _ _ _ e.symm]
    · rw [letterOf_two' h₁ h₂ hne m hin.symm, letter_apply, letterFn_opp _ _ _ _ (hoppd _ e)]
    · rw [letterOf_outer h₁ h₂ m hin.symm, hturn _ _ _ e.symm]
    · rw [letterOf_outer' h₁ h₂ m hin.symm, letter_apply, letterFn_opp _ _ _ _ (hoppd _ e)]
  · rw [Move.perm_of_ne hin]
    congr 1
    -- The move's layer isn't the sticker's layer, so its letter fixes the position.
    have n₁ : ∀ (ρ : Role) (x : ℕ), layerFrom (u.dir ρ) (embed h₁ h₂ u) = x → m.layer = x →
        u.dir ρ ≠ m.face := by
      intro ρ x h hl e
      exact hin (by rw [← e, h, hl])
    have n₂ : ∀ (ρ : Role) (x : ℕ), layerFrom (u.dir ρ) (embed h₁ h₂ u) = x →
        m.layer = n + 1 - x → u.dir ρ ≠ m.face.opp := by
      intro ρ x h hl e
      have : m.face = (u.dir ρ).opp := by rw [e, Face.opp_opp]
      exact hin (by rw [this, dopp ρ x h, hl])
    have e₁ := layerFrom_embed_one h₁ h₂ u
    have e₂ := layerFrom_embed_two h₁ h₂ u
    have e₃ := layerFrom_embed_outer h₁ h₂ u
    by_cases a₁ : m.layer = d₁
    · rw [letterOf_one m a₁, hfix _ _ _ (n₁ _ _ e₁ a₁)]
    by_cases a₂ : m.layer = n + 1 - d₁
    · rw [letterOf_one' h₁ h₂ m a₂, hfix _ _ _ (n₂ _ _ e₁ a₂)]
    by_cases a₃ : m.layer = d₂
    · rw [letterOf_two h₁ h₂ hne m a₃, hfix _ _ _ (n₁ _ _ e₂ a₃)]
    by_cases a₄ : m.layer = n + 1 - d₂
    · rw [letterOf_two' h₁ h₂ hne m a₄, hfix _ _ _ (n₂ _ _ e₂ a₄)]
    by_cases a₅ : m.layer = 1
    · rw [letterOf_outer h₁ h₂ m a₅, hfix _ _ _ (n₁ _ _ e₃ a₅)]
    by_cases a₆ : m.layer = n
    · rw [letterOf_outer' h₁ h₂ m a₆, hfix _ _ _ (n₂ _ _ e₃ (by rw [a₆, Nat.add_sub_cancel]))]
    rw [letterOf_other h₁ h₂ m a₁ a₂ a₃ a₄ a₅ a₆]
    rfl

/-- The part of a state on a pair: which face each of the 48 positions' stickers belongs on. -/
def pairView (h₁ : InI n d₁) (h₂ : InI n d₂) (s : State n) : Pos → Face :=
  fun u ↦ s.get (embed h₁ h₂ u)

/-- A move changes a pair's view by its letter. -/
theorem pairView_apply (h₁ : InI n d₁) (h₂ : InI n d₂) (hne : d₁ ≠ d₂) (m : Move n) (s : State n) :
    pairView h₁ h₂ (m.apply s) = pairView h₁ h₂ s ∘ (letterOf d₁ d₂ m).symm := by
  funext u
  simp only [pairView, Function.comp, Move.apply_get]
  congr 1
  apply (m.perm).injective
  rw [Equiv.apply_symm_apply, perm_embed_letter h₁ h₂ hne, Equiv.apply_symm_apply]

end CubeGod
