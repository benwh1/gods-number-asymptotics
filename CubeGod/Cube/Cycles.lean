import CubeGod.Cube.Patterns
import CubeGod.Schedule.Basic

/-!
# The 3-cycles `[[a, b], c]` on the 48 positions, and each orbit's patterns

The 3-cycle of a pair `(e, d)` is `[[a, b], c] = a b a' b' c b a b' a' c'`, where `a` turns the
layer `e`, `b` turns an outside layer, and `c` turns the layer `d`. On the 48 positions of the pair,
`a`, `b` and `c` act as the letters of the roles `one`, `outer` and `two`, so what it does doesn't
depend on `n`, `e` or `d`. A `Cycle` records just the three turns.

The firing turn `c` turns twice, as `c` and `c'`, and each turn either sees the setup `[a, b]` or
doesn't: `perm S` is what the pair sees when the first sees the setup `S ∈ {0, 1}` and the second
doesn't. With setups `(1, 0)` the pair sees the 3-cycle, with `(0, 1)` its inverse, and otherwise
nothing.

Each 3-cycle moves positions of one orbit only: the right-handed ones (`Pos.Proper`) or the
left-handed ones. So each orbit has its own cycle system, whose states are its patterns, and whose
3-cycles are those that move nothing on the other orbit.
-/

open Finset Equiv

namespace CubeGod

/-- A turn of a face, at no particular layer. -/
structure Turn where
  /-- the face -/
  face : Face
  /-- clockwise, seen from outside `face` -/
  cw : Bool
  deriving DecidableEq, Fintype

/-- The same turn the other way. -/
def Turn.inv (t : Turn) : Turn := ⟨t.face, !t.cw⟩

/-- What the turn does to the positions, as a layer of role `ρ`. -/
def Turn.on (t : Turn) (ρ : Role) : Equiv.Perm Pos := letter ρ t.face t.cw

/-- The 3-cycle `[[a, b], c]` of a pair `(e, d)`: `a` turns the layer `e`, `b` an outside layer, and
`c` the layer `d`. -/
structure Cycle where
  /-- the turn of the setup layer `e` -/
  a : Turn
  /-- the turn of the outside layer -/
  b : Turn
  /-- the turn of the firing layer `d` -/
  c : Turn
  deriving DecidableEq, Fintype

namespace Cycle

variable (g : Cycle)

/-- The setup `[a, b] = a b a' b'`, on the positions. -/
def setup : Equiv.Perm Pos := (g.b.on .outer)⁻¹ * (g.a.on .one)⁻¹ * g.b.on .outer * g.a.on .one

/-- The firing turn `c`, on the positions. -/
def fire : Equiv.Perm Pos := g.c.on .two

/-- The setup `S`: nothing for `0`, and `[a, b]` for `1`. -/
def setP (S : Fin 2) : Equiv.Perm Pos := if S = 1 then g.setup else 1

/-- What the pair sees when the first firing turn sees the setup `S` and the second sees none. -/
def perm (S : Fin 2) : Equiv.Perm Pos := g.fire⁻¹ * (g.setP S)⁻¹ * g.fire * g.setP S

theorem perm_zero : g.perm 0 = 1 := by
  simp [perm, setP]

/-- The firing turns see the setups `a` and `b`. -/
theorem perm_two (a b : Fin 2) :
    (g.perm b)⁻¹ * g.perm a =
      (g.setP b)⁻¹ * g.fire⁻¹ * g.setP b * ((g.setP a)⁻¹ * g.fire * g.setP a) := by
  simp only [perm, mul_inv_rev, inv_inv]
  group

end Cycle

/-- `σ` keeps right-handed positions right-handed. -/
def Preserves (σ : Equiv.Perm Pos) : Prop := ∀ u, (σ u).Proper ↔ u.Proper

/-- The permutations of the positions that keep each of the two orbits. -/
def orbitGroup : Subgroup (Equiv.Perm Pos) where
  carrier := {σ | Preserves σ}
  mul_mem' {a b} ha hb u := (ha (b u)).trans (hb u)
  one_mem' _ := Iff.rfl
  inv_mem' {a} ha u := by
    have := ha (a⁻¹ u)
    simpa using this.symm

instance : Fintype Role := ⟨{.one, .two, .outer}, by intro x; cases x <;> simp⟩

theorem letter_preserves : ∀ (ρ : Role) (E : Face) (cw : Bool) (u : Pos),
    (letter ρ E cw u).Proper ↔ u.Proper := by
  decide +kernel

theorem letter_mem (ρ : Role) (E : Face) (cw : Bool) : letter ρ E cw ∈ orbitGroup :=
  fun u ↦ letter_preserves ρ E cw u

theorem Turn.on_mem (t : Turn) (ρ : Role) : t.on ρ ∈ orbitGroup := letter_mem _ _ _

theorem Cycle.perm_mem (g : Cycle) (S : Fin 2) : g.perm S ∈ orbitGroup := by
  have h₁ : g.fire ∈ orbitGroup := Turn.on_mem _ _
  have h₂ : g.setP S ∈ orbitGroup := by
    unfold Cycle.setP Cycle.setup
    split_ifs
    · exact mul_mem (mul_mem (mul_mem (inv_mem (Turn.on_mem _ _)) (inv_mem (Turn.on_mem _ _)))
        (Turn.on_mem _ _)) (Turn.on_mem _ _)
    · exact one_mem _
  exact mul_mem (mul_mem (mul_mem (inv_mem h₁) (inv_mem h₂)) h₁) h₂

/-! ### The two orbits -/

/-- The positions of one orbit of a pair: the right-handed ones for `true`, and the left-handed ones
for `false`. -/
def OnSide : Bool → Pos → Prop
  | true, u => u.Proper
  | false, u => ¬ u.Proper

instance : ∀ q, DecidablePred (OnSide q)
  | true => fun u ↦ inferInstanceAs (Decidable u.Proper)
  | false => fun u ↦ inferInstanceAs (Decidable (¬ u.Proper))

/-- The 24 positions of one orbit. -/
abbrev SPos (q : Bool) := Subtype (OnSide q)

theorem card_sPos : ∀ q, Fintype.card (SPos q) = 24 := by decide +kernel

theorem onSide_iff {σ : Equiv.Perm Pos} (hσ : σ ∈ orbitGroup) (q : Bool) (u : Pos) :
    OnSide q (σ u) ↔ OnSide q u := by
  cases q
  · exact not_congr (hσ u)
  · exact hσ u

/-- What a permutation keeping both orbits does on one of them. -/
def restr (q : Bool) : orbitGroup →* Equiv.Perm (SPos q) where
  toFun σ := σ.1.subtypePerm (onSide_iff σ.2 q)
  map_one' := Equiv.ext fun _ ↦ rfl
  map_mul' _ _ := Equiv.ext fun _ ↦ rfl

@[simp] theorem restr_apply (q : Bool) (σ : orbitGroup) (u : SPos q) :
    (restr q σ u).1 = σ.1 u.1 := rfl

/-- The patterns of an orbit: a face for each position, with 4 of each face. -/
abbrev OState (q : Bool) := {f : SPos q → Face // Balanced f}

noncomputable instance (q : Bool) : Fintype (OState q) := Fintype.ofFinite _

/-- Permutations act on balanced functions, by moving the points. -/
def balAct {α : Type*} [Fintype α] : Equiv.Perm α →* Equiv.Perm {f : α → Face // Balanced f} where
  toFun σ :=
    { toFun := fun f ↦ ⟨f.1 ∘ ⇑σ⁻¹, f.2.comp_perm _⟩
      invFun := fun f ↦ ⟨f.1 ∘ σ, f.2.comp_perm _⟩
      left_inv := fun f ↦ Subtype.ext (by funext u; simp)
      right_inv := fun f ↦ Subtype.ext (by funext u; simp) }
  map_one' := Equiv.ext fun _ ↦ rfl
  map_mul' _ _ := Equiv.ext fun f ↦ Subtype.ext (by funext u; simp [Equiv.Perm.mul_def])

@[simp] theorem balAct_val {α : Type*} [Fintype α] (σ : Equiv.Perm α)
    (f : {f : α → Face // Balanced f}) : (balAct σ f).1 = f.1 ∘ ⇑σ⁻¹ := rfl

/-- The action of `orbitGroup` on one orbit's patterns. -/
def sideAct (q : Bool) : orbitGroup →* Equiv.Perm (OState q) := balAct.comp (restr q)

theorem sideAct_val (q : Bool) (σ : orbitGroup) (f : OState q) :
    (sideAct q σ f).1 = f.1 ∘ ⇑(restr q σ)⁻¹ := rfl

theorem solved_balanced : ∀ q, Balanced (fun u : SPos q ↦ solvedView u.1) := by
  intro q c
  revert q c
  decide +kernel

/-- The solved pattern of an orbit. -/
def sSolved (q : Bool) : OState q := ⟨fun u ↦ solvedView u.1, solved_balanced q⟩

instance (q : Bool) : Nonempty (OState q) := ⟨sSolved q⟩

/-- An orbit has `C = 24!/4!⁶` patterns. -/
theorem card_oState (q : Bool) : Fintype.card (OState q) = patternCount := by
  classical
  exact card_balanced (card_sPos q) (solved_balanced q)

/-! ### The 3-cycles of one orbit -/

/-- The 3-cycle moves nothing on the other orbit. -/
def Cycle.Pure (q : Bool) (g : Cycle) : Prop := ∀ u, ¬ OnSide q u → g.perm 1 u = u

instance (q : Bool) : DecidablePred (Cycle.Pure q) := fun g ↦ by
  unfold Cycle.Pure; infer_instance

/-- The 3-cycles of an orbit: right-handed for `true`, left-handed for `false`. -/
abbrev SideCycle (q : Bool) := {g : Cycle // g.Pure q}

theorem Cycle.Pure.perm {q : Bool} {g : Cycle} (hg : g.Pure q) (S : Fin 2) (u : Pos)
    (hu : ¬ OnSide q u) : g.perm S u = u := by
  fin_cases S
  · simp [perm_zero]
  · exact hg u hu

/-- A 3-cycle of an orbit, with setups `(S, 0)`, on that orbit's patterns. -/
def sideCyc (q : Bool) (g : SideCycle q) (S : Fin 2) : Equiv.Perm (OState q) :=
  sideAct q ⟨g.1.perm S, g.1.perm_mem S⟩

theorem sideCyc_zero (q : Bool) (g : SideCycle q) : sideCyc q g 0 = 1 := by
  have : (⟨g.1.perm 0, g.1.perm_mem 0⟩ : orbitGroup) = 1 := Subtype.ext g.1.perm_zero
  simp [sideCyc, this]

end CubeGod
