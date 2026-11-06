import CubeGod.Info.Entropy

/-!
# Cycle systems

The schedule, the path, the merge and the codebooks don't need the cube. They need a finite set `X`
of states (for the cube, the patterns of one orbit), a finite set `G` of 3-cycles, and for each
3-cycle `g` and setup `a` a permutation `e g a` of `X`: what `g` does when its first firing turn
sees the setup `a` and its second sees none. When the second sees `b`, it does `(e g b)⁻¹ ∘ e g a`.
For the cube the setups are `0` and `1`, and `e g 1` is the 3-cycle.
-/

open Finset Real

set_option linter.unusedSectionVars false

namespace CubeGod

/-- A cycle system. `e g a` is the 3-cycle `g` with setups `(a, 0)`. -/
structure CycleSystem (X A G : Type*) [Zero A] where
  /-- the 3-cycle with setups `(a, 0)` -/
  e : G → A → Equiv.Perm X
  e_zero : ∀ g, e g 0 = 1
  /-- the solved state -/
  solved : X
  /-- Fact T: the 3-cycles act transitively. -/
  trans : ∀ x y : X, ∃ w ∈ Subgroup.closure (Set.range (Function.uncurry e)), w x = y

/-- A 3-cycle, with the setups its two firing turns see. -/
structure Fired (A G : Type*) where
  /-- the 3-cycle -/
  cyc : G
  /-- the setup the first firing turn sees -/
  first : A
  /-- the setup the second firing turn sees -/
  second : A

end CubeGod
