import CubeGod.Code.Covering
import CubeGod.Schedule.Core

/-!
# Running a schedule

`runN` does the first `t` firings of a schedule to a state, with given setups.
-/

open Finset Real Filter Topology

set_option linter.unusedSectionVars false

namespace CubeGod

variable {X A G : Type*} [Fintype X] [DecidableEq X] [Fintype A] [DecidableEq A] [Zero A]

namespace CycleSystem

variable {Γ : CycleSystem X A G}

/-- Do the 3-cycle `q.cyc` with setups `q.first` and `q.second`. -/
def fire (Γ : CycleSystem X A G) (q : Fired A G) (x : X) : X :=
  (Γ.e q.cyc q.second)⁻¹ (Γ.e q.cyc q.first x)

/-- Do steps `0, 1, …, t - 1` of `q`. -/
def runN (Γ : CycleSystem X A G) (q : ℕ → Fired A G) : ℕ → X → X
  | 0, x => x
  | t + 1, x => Γ.fire (q t) (runN Γ q t x)

omit [Fintype X] [DecidableEq X] [Fintype A] [DecidableEq A] in
theorem runN_congr {q q' : ℕ → Fired A G} {t : ℕ} (h : ∀ u < t, q u = q' u) (x : X) :
    Γ.runN q t x = Γ.runN q' t x := by
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [runN]
    rw [ih fun u hu ↦ h u (by omega), h t (by omega)]

end CycleSystem

end CubeGod
