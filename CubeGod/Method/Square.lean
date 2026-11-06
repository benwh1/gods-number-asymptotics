import CubeGod.Method.Length

/-!
# Stage 2 with square blocks

A **square block** is `c` consecutive rows of a group, so `c × c` layers. With a layer `d` of a
later group it is a **super-tuple** of `c²` pairs. A step's codebook is a set of lists of `c × c`
bits, and a walk's choices are those lists, each put on the rows of the block (`embedSq`). A
super-tuple picks one list for each walk (`sqPicks`), and the row `v` of the block reads its bits
from row `v mod c` of that list.
-/

open Finset

namespace CubeGod

variable {n h a c : ℕ}

/-- A codebook list of `c × c` bits, put on the rows of square block `j`. -/
def embedSq (hc : 0 < c) (j : ℕ) (f : Fin c × Fin c → Fin 2) : Fin a → Fin c → Fin 2 :=
  fun v k ↦ if (v : ℕ) / c = j then f (⟨v % c, Nat.mod_lt _ hc⟩, k) else 0

/-- The setups each row wants, from a list for each super-tuple: `sp G H j d` is the list of
the super-tuple of square block `j` of `G` and the layer `d` of `H`. -/
def sqPicks (hc : 0 < c) (sp : Fin h → Fin h → ℕ → ℕ → Fin c × Fin c → Fin 2) : Picks h a c :=
  fun G H v d k ↦ sp G H (v / c) d (⟨v % c, Nat.mod_lt _ hc⟩, k)

theorem wantF_sqPicks (hc : 0 < c) (sp : Fin h → Fin h → ℕ → ℕ → Fin c × Fin c → Fin 2)
    (G H : Fin h) (j d : ℕ) :
    wantF (sqPicks hc sp) G H (chunk a c j) d = embedSq hc j (sp G H j d) := by
  funext v k
  by_cases hv : (v : ℕ) / c = j
  · simp [wantF, sqPicks, embedSq, mem_chunk, hv]
  · simp [wantF, embedSq, mem_chunk, hv]

namespace Layout

variable (Y : Layout n h a c)

/-- All the block runs of a 3-cycle, one for each pair of groups and each square block. -/
noncomputable def sqWord (hn : 0 < (n + 1) / 2) (hc : 0 < c) (g : Cycle)
    (𝓒₁ 𝓒₂ : Finset (Fin c × Fin c → Fin 2))
    (sp₁ sp₂ : Fin h → Fin h → ℕ → ℕ → Fin c × Fin c → Fin 2) : List (Move n) :=
  (groupPairs h).flatMap fun q ↦ (List.range (a / c)).flatMap fun j ↦
    Y.run hn g (𝓒₁.image (embedSq hc j)) (𝓒₂.image (embedSq hc j)) (sqPicks hc sp₁)
      (sqPicks hc sp₂) q.1 q.2 (chunk a c j)

variable {Y} {hn : 0 < (n + 1) / 2} {hc : 0 < c} {g : Cycle}
  {𝓒₁ 𝓒₂ : Finset (Fin c × Fin c → Fin 2)} {sp₁ sp₂ : Fin h → Fin h → ℕ → ℕ → Fin c × Fin c → Fin 2}

theorem sqPicks_mem {𝓒 : Finset (Fin c × Fin c → Fin 2)}
    {sp : Fin h → Fin h → ℕ → ℕ → Fin c × Fin c → Fin 2} (hsp : ∀ G H j d, sp G H j d ∈ 𝓒)
    (G H : Fin h) (j d : ℕ) :
    wantF (sqPicks hc sp) G H (chunk a c j) d ∈ 𝓒.image (embedSq hc j) := by
  rw [wantF_sqPicks]
  exact Finset.mem_image_of_mem _ (hsp G H j d)

/-- Stage 2 with square blocks does a 3-cycle, its inverse or nothing to a mixed pair. -/
theorem pairW_sqWord (hca : c ∣ a) {G₀ H₀ : Fin h} {v₀ v₁ : Fin a} {k₀ k₁ : Fin c}
    (h₀ : G₀ < H₀) (hsp₁ : ∀ G H j d, sp₁ G H j d ∈ 𝓒₁) (hsp₂ : ∀ G H j d, sp₂ G H j d ∈ 𝓒₂) :
    pairW (Y.L G₀ v₀ k₀) (Y.L H₀ v₁ k₁) (Y.sqWord hn hc g 𝓒₁ 𝓒₂ sp₁ sp₂) =
      (g.perm (sqPicks hc sp₂ G₀ H₀ v₀ (Y.L H₀ v₁ k₁) k₀))⁻¹ *
        g.perm (sqPicks hc sp₁ G₀ H₀ v₀ (Y.L H₀ v₁ k₁) k₀) := by
  have hch : ∀ j, (chunk a c j).Nodup := fun j ↦ (List.nodup_finRange a).filter _
  have hv : v₀ ∈ chunk a c ((v₀ : ℕ) / c) := mem_chunk.mpr rfl
  have hj : (v₀ : ℕ) / c ∈ List.range (a / c) := by
    obtain ⟨q, hq⟩ := hca
    have h₁ : (v₀ : ℕ) < c * q := hq ▸ v₀.2
    have h₂ : a / c = q := by rw [hq, Nat.mul_div_cancel_left _ hc]
    rw [List.mem_range, h₂]
    exact Nat.div_lt_of_lt_mul h₁
  have hmatch := pairW_run_match (Y := Y) (hn := hn) (g := g)
    (Λ₁ := 𝓒₁.image (embedSq hc ((v₀ : ℕ) / c))) (Λ₂ := 𝓒₂.image (embedSq hc ((v₀ : ℕ) / c)))
    (p₁ := sqPicks hc sp₁) (p₂ := sqPicks hc sp₂) (k₀ := k₀) (v₁ := v₁) (k₁ := k₁) h₀ hv (hch _)
    (sqPicks_mem hsp₁ _ _ _ _) (sqPicks_mem hsp₂ _ _ _ _)
  unfold sqWord pairW
  rw [evalW_flatMap_single (nodup_groupPairs h) (x₀ := (G₀, H₀)) (mem_groupPairs.mpr h₀)]
  · rw [evalW_flatMap_single List.nodup_range hj, Cycle.perm_two]
    · exact hmatch
    · intro j _ hne
      refine pairW_run_quiet h₀ h₀ (fun h' ↦ hne ?_) (sqPicks_mem hsp₁ _ _ _)
        (sqPicks_mem hsp₂ _ _ _)
      exact (mem_chunk.mp h'.2.2).symm
  · intro q hq hne
    refine evalW_flatMap_eq_one fun j _ ↦ ?_
    refine pairW_run_quiet (mem_groupPairs.mp hq) h₀ (fun h' ↦ hne ?_) (sqPicks_mem hsp₁ _ _ _)
      (sqPicks_mem hsp₂ _ _ _)
    exact Prod.ext h'.1 h'.2.1

/-- Stage 2 with square blocks leaves alone every sticker in at most one layer of `I`. -/
theorem permW_sqWord_oneLayer (hsp₁ : ∀ G H j d, sp₁ G H j d ∈ 𝓒₁)
    (hsp₂ : ∀ G H j d, sp₂ G H j d ∈ 𝓒₂) {ρ : ℕ} {p : Sticker n} (hpr : p ∈ OneLayer n ρ) :
    permW (Y.sqWord hn hc g 𝓒₁ 𝓒₂ sp₁ sp₂) p = p :=
  permW_flatMap_fix fun _ hq ↦ permW_flatMap_fix fun _ _ ↦
    permW_run_oneLayer (ne_of_lt (mem_groupPairs.mp hq)) (sqPicks_mem hsp₁ _ _ _)
      (sqPicks_mem hsp₂ _ _ _) hpr

variable (Y)

/-- Stage 2 for one kind: all its steps, in order, with square blocks. -/
noncomputable def sqStage2Word (hn : 0 < (n + 1) / 2) (hc : 0 < c) (T : ℕ) (g : ℕ → Cycle)
    (B₁ B₂ : ℕ → Finset (Fin c × Fin c → Fin 2))
    (sp₁ sp₂ : ℕ → Fin h → Fin h → ℕ → ℕ → Fin c × Fin c → Fin 2) : List (Move n) :=
  (List.range T).flatMap fun t ↦ Y.sqWord hn hc (g t) (B₁ t) (B₂ t) (sp₁ t) (sp₂ t)

variable {Y}

theorem pairW_sqStage2Word (hca : c ∣ a) {T : ℕ} {g : ℕ → Cycle}
    {B₁ B₂ : ℕ → Finset (Fin c × Fin c → Fin 2)}
    {sp₁ sp₂ : ℕ → Fin h → Fin h → ℕ → ℕ → Fin c × Fin c → Fin 2}
    (hsp₁ : ∀ t G H j d, sp₁ t G H j d ∈ B₁ t) (hsp₂ : ∀ t G H j d, sp₂ t G H j d ∈ B₂ t)
    {G H : Fin h} (hGH : G < H) (v v' : Fin a) (k k' : Fin c) :
    pairW (Y.L G v k) (Y.L H v' k') (Y.sqStage2Word hn hc T g B₁ B₂ sp₁ sp₂) =
      evalW (fun t ↦ Fired.perm ⟨g t, sqPicks hc (sp₁ t) G H v (Y.L H v' k') k,
        sqPicks hc (sp₂ t) G H v (Y.L H v' k') k⟩) (List.range T) := by
  unfold sqStage2Word pairW
  rw [evalW_flatMap]
  refine congrArg (fun φ ↦ evalW φ (List.range T)) (funext fun t ↦ ?_)
  exact pairW_sqWord hca hGH (hsp₁ t) (hsp₂ t)

theorem permW_sqStage2Word_oneLayer {T : ℕ} {g : ℕ → Cycle}
    {B₁ B₂ : ℕ → Finset (Fin c × Fin c → Fin 2)}
    {sp₁ sp₂ : ℕ → Fin h → Fin h → ℕ → ℕ → Fin c × Fin c → Fin 2}
    (hsp₁ : ∀ t G H j d, sp₁ t G H j d ∈ B₁ t) (hsp₂ : ∀ t G H j d, sp₂ t G H j d ∈ B₂ t)
    {ρ : ℕ} {p : Sticker n} (hp : p ∈ OneLayer n ρ) :
    permW (Y.sqStage2Word hn hc T g B₁ B₂ sp₁ sp₂) p = p :=
  permW_flatMap_fix fun t _ ↦ permW_sqWord_oneLayer (hsp₁ t) (hsp₂ t) hp

/-! ### Lengths -/

variable (Y)

theorem length_sqRun (hn : 0 < (n + 1) / 2) (hc : 0 < c) (g : Cycle)
    {𝓒₁ 𝓒₂ : Finset (Fin c × Fin c → Fin 2)} (sp₁ sp₂ : Fin h → Fin h → ℕ → ℕ → Fin c × Fin c → Fin 2)
    (G H : Fin h) {j M : ℕ} (hM₁ : #𝓒₁ ≤ M) (hM₂ : #𝓒₂ ≤ M) :
    (Y.run hn g (𝓒₁.image (embedSq hc j)) (𝓒₂.image (embedSq hc j)) (sqPicks hc sp₁)
      (sqPicks hc sp₂) G H (chunk a c j)).length ≤ 2 * (M * (8 * (c * c)) + a * c) := by
  have hlen := length_chunk (a := a) (j := j) hc
  have hcc : 1 ≤ c * c := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero hc.ne' hc.ne')
  have hP : ∀ f, (Y.pf G (chunk a c j) f).length ≤ c * c := fun f ↦
    (Y.length_pf G (chunk a c j) f).trans (Nat.mul_le_mul_right c hlen)
  have one : ∀ (g' : Cycle) (𝓒 : Finset (Fin c × Fin c → Fin 2))
      (want : ℕ → Fin a → Fin c → Fin 2), #𝓒 ≤ M →
      (walk hn g' (Y.pf G (chunk a c j)) (Y.groupLayers H) want
        (𝓒.image (embedSq (a := a) hc j)).toList).length ≤ M * (8 * (c * c)) + a * c := by
    intro g' 𝓒 want hB
    have h₁ := length_walk hn g' (Y.pf G (chunk a c j)) want
      (Finset.nodup_toList (𝓒.image (embedSq (a := a) hc j))) (fun l _ ↦ hP l) (Y.groupLayers H)
    have h₂ : (𝓒.image (embedSq (a := a) hc j)).toList.length ≤ M := by
      rw [Finset.length_toList]; exact Finset.card_image_le.trans hB
    rw [Y.length_groupLayers] at h₁
    have h₃ := Nat.mul_le_mul_right (4 * (c * c) + 4) h₂
    have h₄ := Nat.mul_le_mul_left M (show 4 * (c * c) + 4 ≤ 8 * (c * c) by omega)
    omega
  have h₁ := one g 𝓒₁ (wantF (sqPicks hc sp₁) G H (chunk a c j)) hM₁
  have h₂ := one g.reverse 𝓒₂ (wantF (sqPicks hc sp₂) G H (chunk a c j)) hM₂
  simp only [run, blockRun, List.length_append]
  omega

/-- A bound on the length of a 3-cycle's word with square blocks. -/
def sqLen (h a c M : ℕ) : ℕ := (groupPairs h).length * (a / c) * (2 * (M * (8 * (c * c)) + a * c))

theorem length_sqWord (hn : 0 < (n + 1) / 2) (hc : 0 < c) (g : Cycle)
    {𝓒₁ 𝓒₂ : Finset (Fin c × Fin c → Fin 2)} (sp₁ sp₂ : Fin h → Fin h → ℕ → ℕ → Fin c × Fin c → Fin 2)
    {M : ℕ} (hM₁ : #𝓒₁ ≤ M) (hM₂ : #𝓒₂ ≤ M) :
    (Y.sqWord hn hc g 𝓒₁ 𝓒₂ sp₁ sp₂).length ≤ sqLen h a c M := by
  have hin : ∀ q ∈ groupPairs h, ((List.range (a / c)).flatMap fun j ↦
      Y.run hn g (𝓒₁.image (embedSq hc j)) (𝓒₂.image (embedSq hc j)) (sqPicks hc sp₁)
        (sqPicks hc sp₂) q.1 q.2 (chunk a c j)).length ≤
      (a / c) * (2 * (M * (8 * (c * c)) + a * c)) := fun q _ ↦ by
    have := length_flatMap_le (l := List.range (a / c)) (f := fun j ↦
      Y.run hn g (𝓒₁.image (embedSq hc j)) (𝓒₂.image (embedSq hc j)) (sqPicks hc sp₁)
        (sqPicks hc sp₂) q.1 q.2 (chunk a c j))
      (fun j _ ↦ Y.length_sqRun hn hc g sp₁ sp₂ q.1 q.2 hM₁ hM₂)
    simpa using this
  have hout := length_flatMap_le hin
  unfold sqWord sqLen
  rw [mul_assoc]
  exact hout

theorem length_sqStage2Word (hn : 0 < (n + 1) / 2) (hc : 0 < c) (T : ℕ) (g : ℕ → Cycle)
    (B₁ B₂ : ℕ → Finset (Fin c × Fin c → Fin 2))
    (sp₁ sp₂ : ℕ → Fin h → Fin h → ℕ → ℕ → Fin c × Fin c → Fin 2) {M : ℕ}
    (hM₁ : ∀ t, #(B₁ t) ≤ M) (hM₂ : ∀ t, #(B₂ t) ≤ M) :
    (Y.sqStage2Word hn hc T g B₁ B₂ sp₁ sp₂).length ≤ T * sqLen h a c M := by
  have := length_flatMap_le (l := List.range T) (f := fun t ↦
    Y.sqWord hn hc (g t) (B₁ t) (B₂ t) (sp₁ t) (sp₂ t))
    (fun t _ ↦ Y.length_sqWord hn hc (g t) (sp₁ t) (sp₂ t) (hM₁ t) (hM₂ t))
  simpa [sqStage2Word] using this

end Layout

end CubeGod
