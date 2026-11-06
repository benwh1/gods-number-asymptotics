import CubeGod.Method.Stage2
import CubeGod.Method.Average

/-!
# The twist

A twist is Stage 2 on the transposed layout. There, a sub-block is an interval of the original
layout, so a block of one row sets up one interval. Its codebook is the two lists whose entries are
all the same: the whole interval set up, or none of it. A 3-cycle's word then does the 3-cycle to
the pairs of the pairs of intervals that want it, and leaves the others and Stage 1 stickers alone.

The twist gives each pair of intervals a list of 3-cycles. Different pairs of intervals may want
different 3-cycles at the same time, so each round goes through all the 3-cycles.
-/

open Finset

namespace CubeGod

variable {n h a c : ℕ}

/-- What a 3-cycle does to the positions, when its firing turns see the given setups. -/
def Fired.perm (q : Fired (Fin 2) Cycle) : Equiv.Perm Pos :=
  (q.cyc.perm q.second)⁻¹ * q.cyc.perm q.first

theorem Fired.perm_mem (q : Fired (Fin 2) Cycle) : q.perm ∈ orbitGroup :=
  mul_mem (inv_mem (q.cyc.perm_mem _)) (q.cyc.perm_mem _)

/-- A 3-cycle of one orbit, whatever setups it sees, moves nothing on the other orbit. -/
theorem Fired.perm_pure {s : Bool} {q : Fired (Fin 2) Cycle} (hq : q.cyc.Pure s) (u : Pos)
    (hu : ¬ OnSide s u) : q.perm u = u := by
  simp only [Fired.perm, Equiv.Perm.mul_apply, hq.perm q.first u hu]
  rw [Equiv.Perm.inv_eq_iff_eq, hq.perm q.second u hu]

/-- Whether a list of 3-cycles has `g` at position `i`: the setup `g`'s first firing turn sees. -/
def slot (l : List Cycle) (i : ℕ) (g : Cycle) : Fin 2 := if l[i]? = some g then 1 else 0

/-- What position `i` of a list does. -/
def slotPerm (l : List Cycle) (i : ℕ) : Equiv.Perm Pos :=
  match l[i]? with
  | some g => g.perm 1
  | none => 1

/-- All the 3-cycles. -/
noncomputable def allCycles : List Cycle := (Finset.univ : Finset Cycle).toList

theorem nodup_allCycles : allCycles.Nodup := Finset.nodup_toList _

theorem mem_allCycles (g : Cycle) : g ∈ allCycles := Finset.mem_toList.mpr (Finset.mem_univ g)

/-- One round through all the 3-cycles does position `i` of the list. -/
theorem evalW_round (l : List Cycle) (i : ℕ) :
    evalW (fun g ↦ (g.perm 0)⁻¹ * g.perm (slot l i g)) allCycles = slotPerm l i := by
  have hidle : ∀ g h : Cycle, l[i]? ≠ some g → (g.perm 0)⁻¹ * g.perm (slot l i g) = 1 := by
    intro g _ hg
    simp [slot, hg, Cycle.perm_zero]
  unfold slotPerm
  cases hi : l[i]? with
  | none => exact evalW_eq_one fun g _ ↦ hidle g g (by simp [hi])
  | some q =>
    rw [evalW_single nodup_allCycles (mem_allCycles q)]
    · simp [slot, hi, Cycle.perm_zero]
    · intro g _ hg
      exact hidle g g (by simp [hi, Ne.symm hg])

theorem evalW_slotPerm (l : List Cycle) (L : ℕ) :
    evalW (slotPerm l) (List.range L) = cyclesPerm (l.take L) := by
  induction L with
  | zero => simp [cyclesPerm]
  | succ L ih =>
    rw [List.range_succ, evalW_append, ih, List.take_add_one]
    simp only [cyclesPerm, evalW_append, evalW_cons, evalW_nil, one_mul]
    unfold slotPerm
    cases hi : l[L]? <;> simp

/-- A list whose entries are all the same setup. -/
def constList (a : ℕ) (S : Fin 2) : Fin a → Fin 2 := fun _ ↦ S

/-- The lists whose entries are all the same setup. -/
def constBook (a : ℕ) : Finset (Fin a → Fin 2) := univ.image (constList a)

theorem constList_mem (S : Fin 2) : constList a S ∈ constBook a :=
  Finset.mem_image_of_mem _ (Finset.mem_univ S)

theorem card_constBook : #(constBook a) ≤ 2 := by
  have : #(constBook a) ≤ #(univ : Finset (Fin 2)) := Finset.card_image_le
  simpa using this

/-- The setups of round `i` of the twist, for the 3-cycle `g`. -/
def twistPicks (lst : Fin h → Fin h → Fin c → ℕ → List Cycle) (i : ℕ) (g : Cycle) : Picks h c a :=
  fun G H k d ↦ constList a (slot (lst G H k d) i g)

namespace Layout

variable (Y : Layout n h a c) (hn : 0 < (n + 1) / 2)

/-- One 3-cycle's round of the twist. -/
noncomputable def twistCycle (lst : Fin h → Fin h → Fin c → ℕ → List Cycle) (i : ℕ) (g : Cycle) :
    List (Move n) :=
  Y.transpose.cycleWord hn g 1 (constBook a) (constBook a) (twistPicks lst i g)
    (fun _ _ _ _ ↦ constList a 0)

/-- The twist. `lst G H k d` is the list of 3-cycles for interval `k` of `G` and the layer `d` of
`H`. -/
noncomputable def twistWord (L : ℕ) (lst : Fin h → Fin h → Fin c → ℕ → List Cycle) :
    List (Move n) :=
  (List.range L).flatMap fun i ↦ allCycles.flatMap fun g ↦ Y.twistCycle hn lst i g

/-- The twist does to a mixed pair exactly the list of 3-cycles chosen for it. -/
theorem pairW_twistWord {L : ℕ} {lst : Fin h → Fin h → Fin c → ℕ → List Cycle} {G H : Fin h}
    (hGH : G < H) (v v' : Fin a) (k k' : Fin c) :
    pairW (Y.L G v k) (Y.L H v' k') (Y.twistWord hn L lst) =
      cyclesPerm ((lst G H k (Y.L H v' k')).take L) := by
  unfold twistWord pairW
  rw [evalW_flatMap, ← evalW_slotPerm]
  refine congrArg (fun φ ↦ evalW φ (List.range L)) (funext fun i ↦ ?_)
  rw [evalW_flatMap, ← evalW_round]
  refine congrArg (fun φ ↦ evalW φ allCycles) (funext fun g ↦ ?_)
  exact Layout.pairW_cycleWord (Y := Y.transpose) (hn := hn) (g := g) (b := 1)
    (𝓑₁ := constBook a) (𝓑₂ := constBook a) (p₁ := twistPicks lst i g)
    (p₂ := fun _ _ _ _ ↦ constList a 0) (G₀ := G) (H₀ := H) (v₀ := k) (v₁ := k') (k₀ := v)
    (k₁ := v') hGH (fun _ _ _ _ ↦ constList_mem _) (fun _ _ _ _ ↦ constList_mem _)

/-- The twist leaves alone every sticker in at most one layer of `I`. -/
theorem permW_twistWord_oneLayer {L : ℕ} {lst : Fin h → Fin h → Fin c → ℕ → List Cycle} {ρ : ℕ}
    {p : Sticker n} (hp : p ∈ OneLayer n ρ) : permW (Y.twistWord hn L lst) p = p :=
  permW_flatMap_fix fun _ _ ↦ permW_flatMap_fix fun _ _ ↦
    Layout.permW_cycleWord_oneLayer (fun _ _ _ _ ↦ constList_mem _)
      (fun _ _ _ _ ↦ constList_mem _) hp

end Layout

end CubeGod
