import CubeGod.Cube.Orbits

/-!
# Which stickers are in orbits

A sticker's column and row give its layers from the four faces around its face. If it is in two
different layers of `I`, the sticker is an oblique center, and it's in an orbit. Otherwise it's a
**Stage 1 sticker**: a corner, wing, middle edge, + center, middle center or X center. The X centers are
included here, because `CubeGod.Cube.Stage1` solves them along with the others, and Stage 2 leaves
them alone.
-/

open Finset

namespace CubeGod

variable {n : ℕ}

/-- `p` is in an oblique orbit. -/
def InOrbit (p : Sticker n) : Prop :=
  ∃ (q : OrbitName n) (u : PosR), q.1.1 ≠ q.1.2 ∧ p = q.sticker u

/-- A Stage 1 sticker: a corner, wing, middle edge, + center, middle center or X center. -/
def Stage1 (p : Sticker n) : Prop := ¬ InOrbit p

/-- Swap the first two directions of a position. It turns left-handed positions right-handed. -/
def Pos.swap (u : Pos) : Pos :=
  ⟨(u.1.2.1, u.1.1, u.1.2.2), u.2.1.symm, u.2.2.2, u.2.2.1⟩

theorem Pos.swap_proper : ∀ u : Pos, ¬ u.Proper → u.swap.Proper := by
  decide +kernel

theorem embed_swap {d₁ d₂ : ℕ} (h₁ : InI n d₁) (h₂ : InI n d₂) (u : Pos) :
    embed h₁ h₂ u = embed h₂ h₁ u.swap :=
  eq_embed h₂ h₁ u.swap (embed_face h₁ h₂ u) (layerFrom_embed_two h₁ h₂ u)
    (layerFrom_embed_one h₁ h₂ u)

/-- A sticker in two different layers of `I` is in an orbit. -/
theorem inOrbit_of_layers {d₁ d₂ : ℕ} (h₁ : InI n d₁) (h₂ : InI n d₂) (p : Sticker n)
    (e₁ : HasLayer d₁ p) (e₂ : HasLayer d₂ p) (hne : d₁ ≠ d₂) : InOrbit p := by
  obtain ⟨u, hp⟩ := mem_pair h₁ h₂ hne p e₁ e₂
  by_cases hproper : u.Proper
  · exact ⟨⟨(d₁, d₂), h₁, h₂⟩, ⟨u, hproper⟩, hne, hp⟩
  · exact ⟨⟨(d₂, d₁), h₂, h₁⟩, ⟨u.swap, Pos.swap_proper u hproper⟩, hne.symm,
      hp.trans (embed_swap h₁ h₂ u)⟩

/-- A Stage 1 sticker is in at most one layer of `I`. -/
theorem Stage1.one_layer {p : Sticker n} (hp : Stage1 p) :
    ∃ ρ : ℕ, ∀ d, InI n d → d ≠ ρ → ¬ HasLayer d p := by
  by_cases h : ∃ d, InI n d ∧ HasLayer d p
  · obtain ⟨d₀, h₀, r₀⟩ := h
    exact ⟨d₀, fun d hd hne hr ↦ hp (inOrbit_of_layers h₀ hd p r₀ hr (Ne.symm hne))⟩
  · push Not at h
    exact ⟨0, fun d hd _ ↦ h d hd⟩

/-- The stickers that are in no layer of `I` other than `ρ`. -/
def OneLayer (n ρ : ℕ) : Set (Sticker n) :=
  {p | ∀ d, InI n d → d ≠ ρ → ¬ HasLayer d p}

theorem oneLayer_perm {ρ : ℕ} {p : Sticker n} (hp : p ∈ OneLayer n ρ) (m : Move n) :
    m.perm p ∈ OneLayer n ρ := fun d hd hne h ↦ hp d hd hne ((hasLayer_perm m p).mp h)

/-- Keep only the moves of layer `ρ` and of the outside layer. -/
def keepLayer (ρ : ℕ) (m : Move n) : Equiv.Perm (Sticker n) :=
  if m.layer = ρ ∨ m.layer = 1 then m.perm else 1

theorem keepLayer_inv (ρ : ℕ) (m : Move n) : keepLayer ρ m.inv = (keepLayer ρ m)⁻¹ := by
  have hl : m.inv.layer = m.layer := rfl
  unfold keepLayer
  rw [hl]
  split_ifs
  · rw [Move.perm_inv]
  · rw [inv_one]

/-- On a sticker in no layer of `I` other than `ρ`, a word of moves in `I` and the outside layer is
the same as its moves of layer `ρ` and the outside layer. -/
theorem permW_eq_keepLayer {ρ : ℕ} {w : List (Move n)}
    (hw : ∀ m ∈ w, InI n m.layer ∨ m.layer = 1) {p : Sticker n} (hp : p ∈ OneLayer n ρ) :
    permW w p = evalW (keepLayer ρ) w p := by
  refine permW_eq_of_fix (H := OneLayer n ρ) (fun m _ q hq ↦ oneLayer_perm hq m) ?_ p hp
  intro m hm q hq
  unfold keepLayer
  split_ifs with h
  · rfl
  · push Not at h
    have hI : InI n m.layer := (hw m hm).resolve_right h.2
    exact (perm_eq_self hI.lt_n (Or.inl rfl) (hq _ hI h.1)).symm

theorem Pos.turn_proper : ∀ (E : Face) (u : PosR), (u.1.turn E).Proper := by
  decide +kernel

theorem Pos.unturn_proper : ∀ (E : Face) (u : PosR), (u.1.unturn E).Proper := by
  decide +kernel

/-- A move sends an orbit to itself. -/
theorem exists_move_orbit (m : Move n) (q : OrbitName n) (u : PosR) :
    ∃ u' : PosR, m.perm (q.sticker u) = q.sticker u' := by
  by_cases hc : layerFrom m.face (q.sticker u) = m.layer
  · have := perm_embed q.2.1 q.2.2 u.1 hc
    split_ifs at this
    · exact ⟨⟨u.1.turn m.face, Pos.turn_proper _ u⟩, this⟩
    · exact ⟨⟨u.1.unturn m.face, Pos.unturn_proper _ u⟩, this⟩
  · exact ⟨u, Move.perm_of_ne hc⟩

/-- A move keeps an orbit balanced. -/
theorem Balanced.apply {q : OrbitName n} {s : State n} (hs : Balanced (q.view s)) (m : Move n) :
    Balanced (q.view (m.apply s)) := by
  classical
  choose f hf using exists_move_orbit m.inv q
  have hinj : Function.Injective f := by
    intro u v h
    have : m.inv.perm (q.sticker u) = m.inv.perm (q.sticker v) := by rw [hf, hf, h]
    exact (OrbitName.sticker_inj (m.inv.perm.injective this)).2
  have hbij : Function.Bijective f := Finite.injective_iff_bijective.mp hinj
  have heq : q.view (m.apply s) = q.view s ∘ Equiv.ofBijective f hbij := by
    funext u
    simp only [OrbitName.view, Function.comp, Move.apply_get, Equiv.ofBijective_apply]
    rw [← hf u, Move.perm_inv]
    rfl
  rw [heq]
  exact hs.comp_perm _

theorem Balanced.act {q : OrbitName n} {s : State n} (hs : Balanced (q.view s)) (w : List (Move n)) :
    Balanced (q.view (act w s)) := by
  induction w generalizing s with
  | nil => exact hs
  | cons m w ih => exact ih (hs.apply m)

theorem act_invW (w : List (Move n)) (s : State n) : act (invW w) (act w s) = s := by
  refine State.ext_get fun p ↦ ?_
  have h₁ := congrFun (act_eq (invW w) (act w s)) p
  have h₂ := act_eq w s
  have : permW (invW w) = (permW w)⁻¹ := evalW_invW Move.perm_inv w
  rw [h₁, Function.comp, h₂, Function.comp, this]
  change s.get ((permW w).symm (permW w p)) = s.get p
  simp

theorem balanced_solved (q : OrbitName n) : Balanced (q.view (solved n)) := by
  have : q.view (solved n) = fun u : PosR ↦ solvedView u.1 := by
    funext u
    exact solved_embed q.2.1 q.2.2 u.1
  rw [this]
  exact solvedView_R

/-- A solvable state has 4 stickers of each face on every orbit. -/
theorem Solvable.balanced {s : State n} (hs : Solvable s) (q : OrbitName n) :
    Balanced (q.view s) := by
  obtain ⟨w, hw⟩ := hs
  have := (balanced_solved q).act (invW w)
  rwa [← hw, act_invW] at this

end CubeGod
