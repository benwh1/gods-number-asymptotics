import CubeGod.Cube.Pure

/-!
# Orbits

For layers `d₁`, `d₂` of `I`, the orbit `O(d₁, d₂)` is the set of stickers at right-handed positions.
Different orbits are disjoint, and each sticker of an orbit is at exactly one position. So orbits can
be solved one at a time.
-/

open Finset

namespace CubeGod

variable {n : ℕ}

/-- A pair of layers of `I`, naming an orbit. -/
abbrev OrbitName (n : ℕ) := {q : ℕ × ℕ // InI n q.1 ∧ InI n q.2}

/-- The sticker of an orbit at a right-handed position. -/
def OrbitName.sticker (q : OrbitName n) (u : PosR) : Sticker n := embed q.2.1 q.2.2 u.1

theorem outer_unique' : ∀ u v : PosR, u.1.dir .outer = v.1.dir .outer →
    u.1.dir .one = v.1.dir .one → u.1.dir .two = v.1.dir .two := by
  decide +kernel

theorem outer_unique (u v : Pos) (hu : u.Proper) (hv : v.Proper)
    (h₁ : u.dir .outer = v.dir .outer) (h₂ : u.dir .one = v.dir .one) : u = v :=
  Subtype.ext (Prod.ext h₂ (Prod.ext (outer_unique' ⟨u, hu⟩ ⟨v, hv⟩ h₁ h₂) h₁))

theorem swapped_impossible' : ∀ u v : PosR, u.1.dir .outer = v.1.dir .outer →
    v.1.dir .two = u.1.dir .one →
    (u.1.dir .two).axis = (v.1.dir .one).axis ∧ u.1.dir .two ≠ v.1.dir .one := by
  decide +kernel

theorem swapped_impossible (u v : Pos) (hu : u.Proper) (hv : v.Proper)
    (h₁ : u.dir .outer = v.dir .outer) (h₂ : v.dir .two = u.dir .one) :
    (u.dir .two).axis = (v.dir .one).axis ∧ u.dir .two ≠ v.dir .one :=
  swapped_impossible' ⟨u, hu⟩ ⟨v, hv⟩ h₁ h₂

/-- Different positions of different orbits are different stickers. -/
theorem embed_inj {d₁ d₂ e₁ e₂ : ℕ} (h₁ : InI n d₁) (h₂ : InI n d₂) (h₃ : InI n e₁) (h₄ : InI n e₂)
    {u v : Pos} (hu : u.Proper) (hv : v.Proper) (he : embed h₁ h₂ u = embed h₃ h₄ v) :
    d₁ = e₁ ∧ d₂ = e₂ ∧ u = v := by
  have a₁ := h₁.1; have a₂ := h₁.2; have a₃ := h₂.1; have a₄ := h₂.2
  have b₁ := h₃.1; have b₂ := h₃.2; have b₃ := h₄.1; have b₄ := h₄.2
  have ho : u.dir .outer = v.dir .outer := by
    rw [← embed_face h₁ h₂ u, he, embed_face]
  -- The first direction of `v` is one of the two directions of `u` in a layer of `I`.
  have hd₁ := layerFrom_embed_one h₃ h₄ v
  rw [← he] at hd₁
  have hone : v.dir .one = u.dir .one ∨ v.dir .one = u.dir .two := by
    rcases layerFrom_embed h₁ h₂ u (v.dir .one) with
      ⟨e, d⟩ | ⟨e, d⟩ | ⟨e, d⟩ | ⟨e, d⟩ | ⟨e, d⟩ | ⟨e, d⟩ <;> rw [d] at hd₁
    · exact Or.inl e
    · omega
    · exact Or.inr e
    · omega
    · omega
    · omega
  have huv : u = v := by
    rcases hone with h | h
    · exact outer_unique u v hu hv ho h.symm
    · exfalso
      obtain ⟨hax, hne⟩ := swapped_impossible v u hv hu ho.symm h.symm
      -- The second direction of `v` is on the axis of the first of `u`, but isn't it.
      have hd₂ := layerFrom_embed_two h₃ h₄ v
      rw [← he] at hd₂
      rcases (Face.axis_eq_iff _ _).mp hax with e | e
      · exact hne e
      · rw [e, layerFrom_opp, layerFrom_embed_one] at hd₂
        omega
  subst huv
  refine ⟨?_, ?_, rfl⟩
  · have := layerFrom_embed_one h₃ h₄ u
    rwa [← he, layerFrom_embed_one] at this
  · have := layerFrom_embed_two h₃ h₄ u
    rwa [← he, layerFrom_embed_two] at this

theorem OrbitName.sticker_inj {q q' : OrbitName n} {u u' : PosR}
    (h : q.sticker u = q'.sticker u') : q = q' ∧ u = u' := by
  obtain ⟨h₁, h₂, h₃⟩ := embed_inj q.2.1 q.2.2 q'.2.1 q'.2.2 u.2 u'.2 h
  exact ⟨Subtype.ext (Prod.ext h₁ h₂), Subtype.ext h₃⟩

/-- The view of an orbit in a state. -/
def OrbitName.view (q : OrbitName n) (s : State n) : PosR → Face := fun u ↦ s.get (q.sticker u)

/-- The orbit can be solved in `K` moves, changing nothing else. -/
def CanSolve (K : ℕ) (q : OrbitName n) : Prop :=
  ∀ s : State n, Balanced (q.view s) → ∃ w : List (Move n), w.length ≤ K ∧
    (∀ u, (act w s).get (q.sticker u) = u.1.dir .outer) ∧
    ∀ p : Sticker n, (∀ u, p ≠ q.sticker u) → (act w s).get p = s.get p

/-- Stage 3: solve a list of orbits one at a time. -/
theorem solve_orbits {K : ℕ} (l : List (OrbitName n)) (hnd : l.Nodup) (hK : ∀ q ∈ l, CanSolve K q)
    (s : State n) (hbal : ∀ q ∈ l, Balanced (q.view s)) :
    ∃ w : List (Move n), w.length ≤ K * l.length ∧
      (∀ q ∈ l, ∀ u, (act w s).get (q.sticker u) = u.1.dir .outer) ∧
      ∀ p : Sticker n, (∀ q ∈ l, ∀ u, p ≠ q.sticker u) → (act w s).get p = s.get p := by
  induction l generalizing s with
  | nil => exact ⟨[], by simp, by simp, fun p _ ↦ rfl⟩
  | cons q l ih =>
    obtain ⟨hq, hl⟩ := List.nodup_cons.mp hnd
    obtain ⟨w₁, hw₁, hsolved, hsame⟩ := hK q (by simp) s (hbal q (by simp))
    set s₁ := act w₁ s with hs₁
    -- Other orbits are unchanged by the first word.
    have hother : ∀ q' ∈ l, q'.view s₁ = q'.view s := by
      intro q' hq'
      funext u
      refine hsame _ fun v hv ↦ ?_
      obtain ⟨h₁, -⟩ := OrbitName.sticker_inj hv
      exact hq (h₁ ▸ hq')
    obtain ⟨w₂, hw₂, hsolved₂, hsame₂⟩ := ih hl (fun q' hq' ↦ hK q' (by simp [hq'])) s₁
      (fun q' hq' ↦ by rw [hother q' hq']; exact hbal q' (by simp [hq']))
    refine ⟨w₁ ++ w₂, ?_, ?_, ?_⟩
    · simp only [List.length_append, List.length_cons]
      nlinarith
    · intro q' hq' u
      rw [act_append]
      rcases List.mem_cons.mp hq' with rfl | hq''
      · rw [hsame₂ _ fun q'' hq₂ v hv ↦ ?_]
        · exact hsolved u
        · obtain ⟨h₁, -⟩ := OrbitName.sticker_inj hv
          exact hq (h₁ ▸ hq₂)
      · exact hsolved₂ q' hq'' u
    · intro p hp
      rw [act_append, hsame₂ p fun q' hq' u ↦ hp q' (by simp [hq']) u]
      exact hsame p (hp q (by simp))

end CubeGod
