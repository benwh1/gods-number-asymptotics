import CubeGod.Spec

/-!
# Layers, and moves as permutations of the stickers

The proof works with the cube of `CubeGod.Spec` directly. Everything about where a sticker is comes
down to the layer of each face that it's in, `layerFrom G p`, counting from `1` at the outside as in
SiGN. The facts we need are

* a sticker is determined by its face and its layers from two faces on the other two axes;
* its layer from the opposite face is `n + 1` minus its layer;
* a move of layer `l` of `G` turns exactly the stickers in layer `l` from `G`, and it takes such a
  sticker to the face its face turns to, keeping its layer from each face, turned along with it.

Here we prove these, and make each move a permutation of the stickers.
-/

namespace CubeGod

variable {n : ℕ}

/-! ### Faces -/

namespace Face

/-- The axis of a face: `0` for R and L, `1` for U and D, `2` for F and B. -/
def axis : Face → Fin 3
  | R | L => 0
  | U | D => 1
  | F | B => 2

/-- Where an anticlockwise turn of `G` takes the face `f`. -/
def unturn (G f : Face) : Face := G.turn (G.turn (G.turn f))

theorem unturn_turn : ∀ G f : Face, unturn G (turn G f) = f := by decide

theorem turn_unturn : ∀ G f : Face, turn G (unturn G f) = f := by decide

theorem turn_self : ∀ G : Face, G.turn G = G := by decide

theorem unturn_self : ∀ G : Face, G.unturn G = G := by decide

theorem opp_opp : ∀ G : Face, G.opp.opp = G := by decide

theorem axis_opp : ∀ G : Face, G.opp.axis = G.axis := by decide

theorem turn_opp : ∀ G f : Face, G.turn f.opp = (G.turn f).opp := by decide

theorem unturn_opp : ∀ G f : Face, G.unturn f.opp = (G.unturn f).opp := by decide

/-- Turning the opposite face clockwise is turning this one anticlockwise. -/
theorem opp_turn : ∀ G f : Face, G.opp.turn f = G.unturn f := by decide

theorem opp_unturn : ∀ G f : Face, G.opp.unturn f = G.turn f := by decide

theorem axis_eq_iff : ∀ E G : Face, E.axis = G.axis ↔ E = G ∨ E = G.opp := by decide

theorem axis_turn : ∀ G f g : Face, f.axis ≠ g.axis → (G.turn f).axis ≠ (G.turn g).axis := by
  decide

theorem axis_unturn : ∀ G f g : Face, f.axis ≠ g.axis → (G.unturn f).axis ≠ (G.unturn g).axis := by
  decide

theorem turnBy_Cw (G : Face) : G.turnBy Cw = G.turn := rfl

theorem turnBy_Ccw (G : Face) : G.turnBy Ccw = G.unturn := rfl

theorem turnBy_reverse (G : Face) : ∀ (d : Direction) (f : Face),
    G.turnBy d.reverse (G.turnBy d f) = f := by
  intro d f; cases d
  · exact unturn_turn G f
  · exact turn_unturn G f

theorem turnBy_self (G : Face) (d : Direction) : G.turnBy d G = G := by
  cases d
  · exact turn_self G
  · exact unturn_self G

theorem turnBy_opp (G : Face) (d : Direction) (f : Face) :
    G.turnBy d f.opp = (G.turnBy d f).opp := by
  cases d
  · exact turn_opp G f
  · exact unturn_opp G f

/-- The six faces, from a face and two faces on the other axes. -/
theorem eq_of_axes : ∀ E f g G : Face, E.axis ≠ f.axis → E.axis ≠ g.axis → f.axis ≠ g.axis →
    G = E ∨ G = E.opp ∨ G = f ∨ G = f.opp ∨ G = g ∨ G = g.opp := by
  decide

theorem axis_right : ∀ E : Face, E.axis ≠ E.right.axis := by decide

theorem axis_up : ∀ E : Face, E.axis ≠ E.up.axis := by decide

theorem axis_right_up : ∀ E : Face, E.right.axis ≠ E.up.axis := by decide

end Face

namespace Direction

theorem reverse_reverse (d : Direction) : d.reverse.reverse = d := by
  cases d <;> rfl

/-- A direction as a boolean: clockwise is `true`. -/
def ofBool : Bool → Direction
  | true => Cw
  | false => Ccw

end Direction

/-! ### Layers -/

section Layer

variable (G : Face) (p : Sticker n)

theorem layerFrom_pos : 1 ≤ layerFrom G p := by
  have := p.2.1.2
  unfold layerFrom
  split_ifs <;> omega

theorem layerFrom_le : layerFrom G p ≤ n := by
  have := p.2.1.2
  unfold layerFrom
  split_ifs <;> omega

theorem layerFrom_self : layerFrom p.1 p = 1 := by
  simp [layerFrom]

theorem layerFrom_opp : layerFrom G.opp p = n + 1 - layerFrom G p := by
  obtain ⟨E, i, j⟩ := p
  have := i.2
  have := j.2
  cases G <;> cases E <;> simp [layerFrom, Face.opp, Face.right, Face.up] <;> omega

theorem layerFrom_right : layerFrom p.1.right p = n - p.2.1 := by
  obtain ⟨E, i, j⟩ := p
  cases E <;> simp [layerFrom, Face.opp, Face.right]

theorem layerFrom_up : layerFrom p.1.up p = n - p.2.2 := by
  obtain ⟨E, i, j⟩ := p
  cases E <;> simp [layerFrom, Face.opp, Face.right, Face.up]

end Layer

/-- A sticker is determined by its face and its layers from the faces at its right and top. -/
theorem Sticker.ext_layerFrom {p q : Sticker n} (h₁ : p.1 = q.1)
    (h₂ : layerFrom p.1.right p = layerFrom p.1.right q)
    (h₃ : layerFrom p.1.up p = layerFrom p.1.up q) : p = q := by
  obtain ⟨E, i, j⟩ := p
  obtain ⟨E', i', j'⟩ := q
  simp only at h₁
  subst h₁
  rw [layerFrom_right, layerFrom_right (E, i', j')] at h₂
  rw [layerFrom_up, layerFrom_up (E, i', j')] at h₃
  have := i.2
  have := i'.2
  have := j.2
  have := j'.2
  simp only at h₂ h₃
  ext <;> simp <;> omega

/-- A sticker is determined by its face and its layers from two faces on the other axes. -/
theorem Sticker.ext_layerFrom' {p q : Sticker n} {f g : Face} (h₁ : p.1 = q.1)
    (hf : p.1.axis ≠ f.axis) (hg : p.1.axis ≠ g.axis) (hfg : f.axis ≠ g.axis)
    (h₂ : layerFrom f p = layerFrom f q) (h₃ : layerFrom g p = layerFrom g q) : p = q := by
  have ho : ∀ G : Face, layerFrom G p = layerFrom G q → layerFrom G.opp p = layerFrom G.opp q := by
    intro G h
    rw [layerFrom_opp, layerFrom_opp, h]
  have hall : ∀ G : Face, G.axis ≠ p.1.axis → layerFrom G p = layerFrom G q := by
    intro G hG
    rcases Face.eq_of_axes p.1 f g G hf hg hfg with h | h | h | h | h | h
    · exact absurd (by rw [h]) hG
    · exact absurd (by rw [h, Face.axis_opp]) hG
    · rw [h]; exact h₂
    · rw [h]; exact ho f h₂
    · rw [h]; exact h₃
    · rw [h]; exact ho g h₃
  exact Sticker.ext_layerFrom h₁ (hall _ (Ne.symm (Face.axis_right _)))
    (hall _ (Ne.symm (Face.axis_up _)))

/-! ### Moves -/

theorem moveSticker_of_ne {G : Face} {k : ℕ} {d : Direction} {p : Sticker n}
    (h : layerFrom G p ≠ k) : moveSticker G k d p = p := by
  simp [moveSticker, h]

theorem moveSticker_face {G : Face} {k : ℕ} {d : Direction} {p : Sticker n}
    (h : layerFrom G p = k) : (moveSticker G k d p).1 = G.turnBy d p.1 := by
  simp [moveSticker, h]

/-- A move keeps layers, turned along with the faces. -/
theorem layerFrom_moveSticker {G : Face} {k : ℕ} {d : Direction} {p : Sticker n}
    (h : layerFrom G p = k) (f : Face) :
    layerFrom (G.turnBy d f) (moveSticker G k d p) = layerFrom f p := by
  set q := moveSticker G k d p with hq
  have hq₁ : q.1 = G.turnBy d p.1 := moveSticker_face h
  have hcol : layerFrom q.1.right q = layerFrom (G.turnBy d.reverse q.1.right) p := by
    rw [layerFrom_right, hq]
    simp only [moveSticker, h, ↓reduceIte]
    have := layerFrom_pos (G.turnBy d.reverse (G.turnBy d p.1).right) p
    have := layerFrom_le (G.turnBy d.reverse (G.turnBy d p.1).right) p
    omega
  have hrow : layerFrom q.1.up q = layerFrom (G.turnBy d.reverse q.1.up) p := by
    rw [layerFrom_up, hq]
    simp only [moveSticker, h, ↓reduceIte]
    have := layerFrom_pos (G.turnBy d.reverse (G.turnBy d p.1).up) p
    have := layerFrom_le (G.turnBy d.reverse (G.turnBy d p.1).up) p
    omega
  -- Write `G.turnBy d f` as one of the six faces around `q`, and `f` as the face it came from.
  have hf : f = G.turnBy d.reverse (G.turnBy d f) := (G.turnBy_reverse d f).symm
  have hp : p.1 = G.turnBy d.reverse q.1 := by rw [hq₁, G.turnBy_reverse]
  have hopp : ∀ g, G.turnBy d.reverse g.opp = (G.turnBy d.reverse g).opp := G.turnBy_opp _
  rcases Face.eq_of_axes q.1 q.1.right q.1.up (G.turnBy d f) (Face.axis_right _) (Face.axis_up _)
    (Face.axis_right_up _) with e | e | e | e | e | e <;> rw [e] at hf ⊢
  · rw [hf, ← hp, layerFrom_self, layerFrom_self]
  · rw [hf, hopp, ← hp, layerFrom_opp, layerFrom_opp, layerFrom_self, layerFrom_self]
  · rw [hf, hcol]
  · rw [hf, hopp, layerFrom_opp, layerFrom_opp, hcol]
  · rw [hf, hrow]
  · rw [hf, hopp, layerFrom_opp, layerFrom_opp, hrow]

/-- A move keeps the layer from its own face. -/
theorem layerFrom_moveSticker_self (G : Face) (k : ℕ) (d : Direction) (p : Sticker n) :
    layerFrom G (moveSticker G k d p) = layerFrom G p := by
  by_cases h : layerFrom G p = k
  · have := layerFrom_moveSticker (d := d) h G
    rwa [G.turnBy_self] at this
  · rw [moveSticker_of_ne h]

/-- The opposite move undoes a move. -/
theorem moveSticker_reverse (G : Face) (k : ℕ) (d : Direction) (p : Sticker n) :
    moveSticker G k d.reverse (moveSticker G k d p) = p := by
  by_cases h : layerFrom G p = k
  · have h' : layerFrom G (moveSticker G k d p) = k := by rw [layerFrom_moveSticker_self, h]
    have hface : (moveSticker G k d.reverse (moveSticker G k d p)).1 = p.1 := by
      rw [moveSticker_face h', moveSticker_face h, G.turnBy_reverse]
    have hdep : ∀ f,
        layerFrom f (moveSticker G k d.reverse (moveSticker G k d p)) = layerFrom f p := by
      intro f
      have e₁ := layerFrom_moveSticker (d := d.reverse) h' (G.turnBy d f)
      rw [G.turnBy_reverse] at e₁
      rw [e₁, layerFrom_moveSticker h]
    exact Sticker.ext_layerFrom (by rw [hface]) (by rw [hface, hdep]) (by rw [hface, hdep])
  · rw [moveSticker_of_ne h, moveSticker_of_ne h]

namespace Move

/-- The same layer turned the other way. -/
def inv (m : Move n) : Move n := { m with dir := m.dir.reverse }

theorem inv_inv (m : Move n) : m.inv.inv = m := by
  simp [inv, Direction.reverse_reverse]

/-- Clockwise, as a boolean. -/
def cw (m : Move n) : Bool := m.dir = Cw

theorem cw_inv (m : Move n) : m.inv.cw = !m.cw := by
  obtain ⟨E, l, d⟩ := m
  cases d <;> rfl

/-- A move, as a permutation of the stickers. -/
def perm (m : Move n) : Equiv.Perm (Sticker n) where
  toFun := moveSticker m.face m.layer m.dir
  invFun := moveSticker m.face m.layer m.dir.reverse
  left_inv := moveSticker_reverse _ _ _
  right_inv p := by
    have := moveSticker_reverse m.face m.layer m.dir.reverse p
    rwa [Direction.reverse_reverse] at this

theorem perm_inv (m : Move n) : m.inv.perm = m.perm⁻¹ := by
  apply Equiv.ext
  intro p
  rfl

/-- A move turns the stickers in its layer, and no others. -/
theorem perm_of_ne {m : Move n} {p : Sticker n} (h : layerFrom m.face p ≠ m.layer) : m.perm p = p :=
  moveSticker_of_ne h

theorem perm_face {m : Move n} {p : Sticker n} (h : layerFrom m.face p = m.layer) :
    (m.perm p).1 = m.face.turnBy m.dir p.1 :=
  moveSticker_face h

theorem layerFrom_perm {m : Move n} {p : Sticker n} (h : layerFrom m.face p = m.layer) (f : Face) :
    layerFrom (m.face.turnBy m.dir f) (m.perm p) = layerFrom f p :=
  layerFrom_moveSticker h f

end Move

/-! ### States -/

/-- The colour of a sticker. -/
def State.get (s : State n) (p : Sticker n) : Face := s p.1 p.2.1 p.2.2

theorem State.ext_get {s t : State n} (h : ∀ p, s.get p = t.get p) : s = t := by
  funext E i j
  exact h (E, i, j)

/-- After a move, each sticker holds what was at the sticker the move takes to it. -/
theorem Move.apply_get (m : Move n) (s : State n) (p : Sticker n) :
    (m.apply s).get p = s.get (m.perm.symm p) := rfl

end CubeGod
