import CubeGod.Cube.Classify
import CubeGod.Code.Compression

/-!
# The layout, and block runs

The layers are put in `h` groups, each an `a × c` grid. A sub-block is a row of a group, and an
interval is a column. Layers not in any group are left for Stage 3.

For a 3-cycle of a schedule, Stage 2 does a block run for each pair of groups and each block. A
choice gives each row of the block a list of `c` bits, and sets up the layers whose bit is `1`.
-/

open Finset

namespace CubeGod

variable {n h a c : ℕ}

/-- `h` groups, each an `a × c` grid of layers of `I`. -/
structure Layout (n h a c : ℕ) where
  /-- the layer at row `v` and column `k` of group `G` -/
  L : Fin h → Fin a → Fin c → ℕ
  inj : ∀ G v k G' v' k', L G v k = L G' v' k' → G = G' ∧ v = v' ∧ k = k'
  mem : ∀ G v k, InI n (L G v k)

/-- The setups a pair could want: for groups `G`, `H`, row `v` of `G` and a layer of `H`, one list
of `c` bits. -/
abbrev Picks (h a c : ℕ) := Fin h → Fin h → Fin a → ℕ → Fin c → Fin 2

/-- The choice that a layer `d` wants for a whole block `ch`. -/
def wantF (p : Picks h a c) (G H : Fin h) (ch : List (Fin a)) (d : ℕ) : Fin a → Fin c → Fin 2 :=
  fun v ↦ if v ∈ ch then p G H v d else 0

/-- All choices of a codebook list for each row of a block. -/
noncomputable def choiceSet (𝓑 : Finset (Fin c → Fin 2)) (ch : List (Fin a)) :
    Finset (Fin a → Fin c → Fin 2) :=
  Fintype.piFinset fun v ↦ if v ∈ ch then 𝓑 else {0}

theorem wantF_mem {p : Picks h a c} {𝓑 : Finset (Fin c → Fin 2)} {G H : Fin h} {ch : List (Fin a)}
    {d : ℕ} (hp : ∀ v, p G H v d ∈ 𝓑) : wantF p G H ch d ∈ choiceSet 𝓑 ch := by
  rw [choiceSet, Fintype.mem_piFinset]
  intro v
  by_cases hv : v ∈ ch <;> simp [wantF, hv, hp]

/-- The blocks of rows for block size `b`: block `j` is the rows `v` with `v / b = j`. -/
def chunk (a b j : ℕ) : List (Fin a) := (List.finRange a).filter fun v ↦ (v : ℕ) / b = j

theorem mem_chunk {a b j : ℕ} {v : Fin a} : v ∈ chunk a b j ↔ (v : ℕ) / b = j := by
  simp [chunk]

/-- The pairs of groups, earlier group first. -/
def groupPairs (h : ℕ) : List (Fin h × Fin h) :=
  (List.finRange h ×ˢ List.finRange h).filter fun q ↦ q.1 < q.2

theorem nodup_groupPairs (h : ℕ) : (groupPairs h).Nodup :=
  ((List.nodup_finRange h).product (List.nodup_finRange h)).filter _

theorem mem_groupPairs {q : Fin h × Fin h} : q ∈ groupPairs h ↔ q.1 < q.2 := by
  rw [groupPairs, List.mem_filter]
  exact ⟨fun h' ↦ by simpa using h'.2, fun h' ↦
    ⟨List.mem_product.mpr ⟨List.mem_finRange _, List.mem_finRange _⟩, by simpa using h'⟩⟩

namespace Layout

variable (Y : Layout n h a c)

/-- A list of the layers of a group. -/
def groupLayers (G : Fin h) : List ℕ :=
  (List.finRange a ×ˢ List.finRange c).map fun p ↦ Y.L G p.1 p.2

theorem mem_groupLayers {G : Fin h} {x : ℕ} :
    x ∈ Y.groupLayers G ↔ ∃ v k, Y.L G v k = x := by
  simp [groupLayers]

theorem nodup_groupLayers (G : Fin h) : (Y.groupLayers G).Nodup := by
  refine List.Nodup.map (fun p p' hp ↦ ?_) ((List.nodup_finRange a).product (List.nodup_finRange c))
  have := Y.inj _ _ _ _ _ _ hp
  exact Prod.ext this.2.1 this.2.2

/-- The layers of a block that a choice sets up: those whose bit is `1`. -/
def pf (G : Fin h) (ch : List (Fin a)) (f : Fin a → Fin c → Fin 2) : List ℕ :=
  ((ch ×ˢ List.finRange c).filter fun p ↦ f p.1 p.2 = 1).map fun p ↦ Y.L G p.1 p.2

theorem layer_of_mem_pf {G : Fin h} {ch : List (Fin a)} {f : Fin a → Fin c → Fin 2} {x : ℕ}
    (hx : x ∈ Y.pf G ch f) : ∃ v ∈ ch, ∃ k, x = Y.L G v k := by
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
  exact ⟨p.1, (List.mem_product.mp (List.mem_filter.mp hp).1).1, p.2, rfl⟩

theorem mem_pf {G : Fin h} {ch : List (Fin a)} {f : Fin a → Fin c → Fin 2} {v : Fin a} {k : Fin c} :
    Y.L G v k ∈ Y.pf G ch f ↔ v ∈ ch ∧ f v k = 1 := by
  constructor
  · intro hx
    obtain ⟨p, hp, he⟩ := List.mem_map.mp hx
    obtain ⟨-, h₁, h₂⟩ := Y.inj _ _ _ _ _ _ he
    have := List.mem_filter.mp hp
    rw [← h₁, ← h₂]
    exact ⟨(List.mem_product.mp this.1).1, by simpa using this.2⟩
  · rintro ⟨hv, hf⟩
    exact List.mem_map.mpr ⟨(v, k), List.mem_filter.mpr
      ⟨List.mem_product.mpr ⟨hv, List.mem_finRange _⟩, by simpa using hf⟩, rfl⟩

theorem nodup_pf (G : Fin h) {ch : List (Fin a)} (hch : ch.Nodup) (f : Fin a → Fin c → Fin 2) :
    (Y.pf G ch f).Nodup := by
  refine List.Nodup.map_on (fun p _ p' _ hp ↦ ?_) ((hch.product (List.nodup_finRange c)).filter _)
  have := Y.inj _ _ _ _ _ _ hp
  exact Prod.ext this.2.1 this.2.2

/-- The block run for groups `G`, `H` and the block of rows `ch`, whose walks go through the
choices `Λ₁` and `Λ₂`. -/
noncomputable def run (hn : 0 < (n + 1) / 2) (g : Cycle) (Λ₁ Λ₂ : Finset (Fin a → Fin c → Fin 2))
    (p₁ p₂ : Picks h a c) (G H : Fin h) (ch : List (Fin a)) : List (Move n) :=
  blockRun hn g (Y.pf G ch) (Y.groupLayers H) (wantF p₁ G H ch) (wantF p₂ G H ch)
    Λ₁.toList Λ₂.toList

/-- All the block runs of a 3-cycle, with block size `b` and the same codebook for every row. -/
noncomputable def cycleWord (hn : 0 < (n + 1) / 2) (g : Cycle) (b : ℕ)
    (𝓑₁ 𝓑₂ : Finset (Fin c → Fin 2)) (p₁ p₂ : Picks h a c) : List (Move n) :=
  (groupPairs h).flatMap fun q ↦ (List.range (a / b + 1)).flatMap fun j ↦
    Y.run hn g (choiceSet 𝓑₁ (chunk a b j)) (choiceSet 𝓑₂ (chunk a b j)) p₁ p₂ q.1 q.2
      (chunk a b j)

section Pair

variable {Y} {hn : 0 < (n + 1) / 2} {g : Cycle} {𝓑₁ 𝓑₂ : Finset (Fin c → Fin 2)}
  {Λ₁ Λ₂ : Finset (Fin a → Fin c → Fin 2)}
  {p₁ p₂ : Picks h a c} {G H G₀ H₀ : Fin h} {v₀ v₁ : Fin a} {k₀ k₁ : Fin c} {ch : List (Fin a)}

theorem layer_ne {G G' : Fin h} {v v' : Fin a} {k k' : Fin c} (hne : G ≠ G') :
    Y.L G v k ≠ Y.L G' v' k' := fun h ↦ hne (Y.inj _ _ _ _ _ _ h).1

/-- The other layers of a fired group do nothing to the pair. -/
theorem letterOf_group_other {x e d : ℕ} (hx : x ∈ Y.groupLayers H) (he : x ≠ e) (hd : x ≠ d)
    (he' : InI n e) (hd' : InI n d) (t : Turn) :
    letterOf e d (t.at hn x) = 1 := by
  obtain ⟨v, k, rfl⟩ := Y.mem_groupLayers.mp hx
  exact letterOf_mv_other hn (Y.mem H v k) he' hd' he hd _ _

/-- The setup of a block that doesn't hold `e` does nothing to the pair `(e, d)`. -/
theorem pairW_setups_quiet {G : Fin h} {f : Fin a → Fin c → Fin 2} (h₁ : ¬ (G = G₀ ∧ v₀ ∈ ch))
    (h₂ : G ≠ H₀) : pairW (Y.L G₀ v₀ k₀) (Y.L H₀ v₁ k₁) (setupAt hn g (Y.pf G ch f)) = 1 := by
  refine evalW_setupAt_quiet (letterOf_inv _ _) fun x hx ↦ ?_
  obtain ⟨v, hv, k, rfl⟩ := Y.layer_of_mem_pf hx
  refine letterOf_mv_other hn (Y.mem G v k) (Y.mem G₀ v₀ k₀) (Y.mem H₀ v₁ k₁) ?_
    (layer_ne h₂) _ _
  intro hel
  obtain ⟨a₁, a₂, -⟩ := Y.inj _ _ _ _ _ _ hel
  exact h₁ ⟨a₁, a₂ ▸ hv⟩

/-- A block run that doesn't match the pair does nothing to it. -/
theorem pairW_run_quiet (hq : G < H) (h₀ : G₀ < H₀) (hne : ¬ (G = G₀ ∧ H = H₀ ∧ v₀ ∈ ch))
    (hw₁ : ∀ d, wantF p₁ G H ch d ∈ Λ₁) (hw₂ : ∀ d, wantF p₂ G H ch d ∈ Λ₂) :
    pairW (Y.L G₀ v₀ k₀) (Y.L H₀ v₁ k₁) (Y.run hn g Λ₁ Λ₂ p₁ p₂ G H ch) = 1 := by
  set e := Y.L G₀ v₀ k₀ with he
  set d := Y.L H₀ v₁ k₁ with hd
  have hφ : ∀ m : Move n, letterOf e d m.inv = (letterOf e d m)⁻¹ := letterOf_inv e d
  have hG₀H₀ : G₀ ≠ H₀ := ne_of_lt h₀
  by_cases hH : H = H₀
  · -- `d` fires, and `e` has no setups in this run.
    subst hH
    have hG : ¬ (G = G₀ ∧ v₀ ∈ ch) := fun h' ↦ hne ⟨h'.1, rfl, h'.2⟩
    have hd' : d ∈ Y.groupLayers H := Y.mem_groupLayers.mpr ⟨v₁, k₁, rfl⟩
    refine evalW_blockRun_cancel hφ hd' (Y.nodup_groupLayers H) ?_ (Finset.nodup_toList _)
      (Finset.mem_toList.mpr (hw₁ _)) (Finset.nodup_toList _)
      (Finset.mem_toList.mpr (hw₂ _)) (pairW_setups_quiet hG (ne_of_lt hq))
      (pairW_setups_quiet hG (ne_of_lt hq))
    intro x hx hxd
    refine letterOf_group_other (Y := Y) (H := H) hx ?_ hxd (Y.mem G₀ v₀ k₀)
      (Y.mem H v₁ k₁) _
    obtain ⟨v, k, rfl⟩ := Y.mem_groupLayers.mp hx
    exact layer_ne (Ne.symm hG₀H₀)
  · by_cases hHe : H = G₀
    · -- `e` fires, and `d` has no setups in this run.
      subst hHe
      have he' : e ∈ Y.groupLayers H := Y.mem_groupLayers.mpr ⟨v₀, k₀, rfl⟩
      have hG : ¬ (G = H ∧ v₀ ∈ ch) := fun h' ↦ (ne_of_lt hq) h'.1
      have hGH : G ≠ H₀ := ne_of_lt (hq.trans h₀)
      refine evalW_blockRun_cancel hφ he' (Y.nodup_groupLayers H) ?_ (Finset.nodup_toList _)
        (Finset.mem_toList.mpr (hw₁ _)) (Finset.nodup_toList _)
        (Finset.mem_toList.mpr (hw₂ _)) (pairW_setups_quiet hG hGH) (pairW_setups_quiet hG hGH)
      intro x hx hxe
      refine letterOf_group_other (Y := Y) (H := H) hx hxe ?_ (Y.mem H v₀ k₀)
        (Y.mem H₀ v₁ k₁) _
      obtain ⟨v, k, rfl⟩ := Y.mem_groupLayers.mp hx
      exact layer_ne hG₀H₀
    · -- Neither layer fires.
      refine evalW_blockRun_quiet hφ fun x hx ↦ ?_
      obtain ⟨v, k, rfl⟩ := Y.mem_groupLayers.mp hx
      exact letterOf_group_other (Y := Y) (H := H) hx (layer_ne hHe) (layer_ne hH)
        (Y.mem G₀ v₀ k₀) (Y.mem H₀ v₁ k₁) _

/-- The block run that matches a pair does the 3-cycle's firing turns to it, inside the
setups its row and column pick. -/
theorem pairW_run_match (h₀ : G₀ < H₀) (hv : v₀ ∈ ch) (hch : ch.Nodup)
    (hw₁ : wantF p₁ G₀ H₀ ch (Y.L H₀ v₁ k₁) ∈ Λ₁) (hw₂ : wantF p₂ G₀ H₀ ch (Y.L H₀ v₁ k₁) ∈ Λ₂) :
    pairW (Y.L G₀ v₀ k₀) (Y.L H₀ v₁ k₁) (Y.run hn g Λ₁ Λ₂ p₁ p₂ G₀ H₀ ch) =
      (g.setP (p₂ G₀ H₀ v₀ (Y.L H₀ v₁ k₁) k₀))⁻¹ * g.fire⁻¹ *
        g.setP (p₂ G₀ H₀ v₀ (Y.L H₀ v₁ k₁) k₀) *
      ((g.setP (p₁ G₀ H₀ v₀ (Y.L H₀ v₁ k₁) k₀))⁻¹ * g.fire *
        g.setP (p₁ G₀ H₀ v₀ (Y.L H₀ v₁ k₁) k₀)) := by
  set e := Y.L G₀ v₀ k₀ with he
  set d := Y.L H₀ v₁ k₁ with hd
  have hφ : ∀ m : Move n, letterOf e d m.inv = (letterOf e d m)⁻¹ := letterOf_inv e d
  have hG₀H₀ : G₀ ≠ H₀ := ne_of_lt h₀
  have hd' : d ∈ Y.groupLayers H₀ := Y.mem_groupLayers.mpr ⟨v₁, k₁, rfl⟩
  have hne : d ≠ e := layer_ne (Ne.symm hG₀H₀)
  have hsetup : ∀ (p : Picks h a c),
      pairW e d (setupAt hn g (Y.pf G₀ ch (wantF p G₀ H₀ ch d))) = g.setP (p G₀ H₀ v₀ d k₀) := by
    intro p
    rw [pairW_setupAt hn (Y.mem G₀ v₀ k₀) (Y.mem H₀ v₁ k₁) g (Y.nodup_pf G₀ hch _) ?_ ?_]
    · simp only [Y.mem_pf, wantF, hv, ite_true, true_and, Cycle.setP]
    · intro x hx
      obtain ⟨v, -, k, rfl⟩ := Y.layer_of_mem_pf hx
      exact Y.mem G₀ v k
    · intro hdx
      obtain ⟨v, -, k, hdl⟩ := Y.layer_of_mem_pf hdx
      exact layer_ne hG₀H₀ hdl.symm
  unfold run
  have := evalW_blockRun_fire (hn := hn) (g := g) (S := Y.pf G₀ ch)
    (want₁ := wantF p₁ G₀ H₀ ch) (want₂ := wantF p₂ G₀ H₀ ch)
    (Λ₁ := Λ₁.toList) (Λ₂ := Λ₂.toList) hφ hd' (Y.nodup_groupLayers H₀)
    (fun x hx hxd ↦ letterOf_group_other (Y := Y) (H := H₀) hx
      (by obtain ⟨v, k, rfl⟩ := Y.mem_groupLayers.mp hx; exact layer_ne (Ne.symm hG₀H₀)) hxd
      (Y.mem G₀ v₀ k₀) (Y.mem H₀ v₁ k₁) _)
    (Finset.nodup_toList _) (Finset.mem_toList.mpr hw₁) (Finset.nodup_toList _)
    (Finset.mem_toList.mpr hw₂)
  have hfire : letterOf e d (g.c.at hn d) = g.fire :=
    letterOf_mv_two hn (Y.mem G₀ v₀ k₀) (Y.mem H₀ v₁ k₁) hne _ _
  have s₁ := hsetup p₁
  have s₂ := hsetup p₂
  simp only [pairW] at s₁ s₂
  rw [hfire, s₁, s₂] at this
  exact this

/-- Stage 2 does a 3-cycle, its inverse or nothing to a mixed pair. -/
theorem pairW_cycleWord {b : ℕ} (h₀ : G₀ < H₀)
    (hp₁ : ∀ G H v d, p₁ G H v d ∈ 𝓑₁) (hp₂ : ∀ G H v d, p₂ G H v d ∈ 𝓑₂) :
    pairW (Y.L G₀ v₀ k₀) (Y.L H₀ v₁ k₁) (Y.cycleWord hn g b 𝓑₁ 𝓑₂ p₁ p₂) =
      (g.perm (p₂ G₀ H₀ v₀ (Y.L H₀ v₁ k₁) k₀))⁻¹ * g.perm (p₁ G₀ H₀ v₀ (Y.L H₀ v₁ k₁) k₀) := by
  have hch : ∀ j, (chunk a b j).Nodup := fun j ↦ (List.nodup_finRange a).filter _
  have hv : v₀ ∈ chunk a b ((v₀ : ℕ) / b) := mem_chunk.mpr rfl
  have hj : (v₀ : ℕ) / b ∈ List.range (a / b + 1) :=
    List.mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right v₀.2.le))
  have hmatch := pairW_run_match (Y := Y) (hn := hn) (g := g)
    (Λ₁ := choiceSet 𝓑₁ (chunk a b ((v₀ : ℕ) / b))) (Λ₂ := choiceSet 𝓑₂ (chunk a b ((v₀ : ℕ) / b)))
    (p₁ := p₁) (p₂ := p₂) (k₀ := k₀) (v₁ := v₁) (k₁ := k₁) h₀ hv (hch _)
    (wantF_mem fun v ↦ hp₁ _ _ v _) (wantF_mem fun v ↦ hp₂ _ _ v _)
  -- Only the matching block run counts.
  unfold cycleWord pairW
  rw [evalW_flatMap_single (nodup_groupPairs h) (x₀ := (G₀, H₀)) (mem_groupPairs.mpr h₀)]
  · rw [evalW_flatMap_single List.nodup_range hj, Cycle.perm_two]
    · exact hmatch
    · intro j _ hne
      refine pairW_run_quiet h₀ h₀ (fun h' ↦ hne ?_) (fun d ↦ wantF_mem fun v ↦ hp₁ _ _ v d)
        (fun d ↦ wantF_mem fun v ↦ hp₂ _ _ v d)
      exact (mem_chunk.mp h'.2.2).symm
  · intro q hq hne
    refine evalW_flatMap_eq_one fun j _ ↦ ?_
    refine pairW_run_quiet (mem_groupPairs.mp hq) h₀ (fun h' ↦ hne ?_)
      (fun d ↦ wantF_mem fun v ↦ hp₁ _ _ v d) (fun d ↦ wantF_mem fun v ↦ hp₂ _ _ v d)
    exact Prod.ext h'.1 h'.2.1

end Pair

section Outer

variable {Y} {hn : 0 < (n + 1) / 2} {g : Cycle} {𝓑₁ 𝓑₂ : Finset (Fin c → Fin 2)}
  {Λ₁ Λ₂ : Finset (Fin a → Fin c → Fin 2)} {p₁ p₂ : Picks h a c}

theorem mem_run {G H : Fin h} {ch : List (Fin a)} {m : Move n}
    (hm : m ∈ Y.run hn g Λ₁ Λ₂ p₁ p₂ G H ch) : InI n m.layer ∨ m.layer = 1 := by
  have hP : ∀ f, ∀ x ∈ Y.pf G ch f, InI n x := by
    intro f x hx
    obtain ⟨v, -, k, rfl⟩ := Y.layer_of_mem_pf hx
    exact Y.mem G v k
  have hD : ∀ (D : List ℕ), (∀ x ∈ D, x ∈ Y.groupLayers H) → ∀ x ∈ D, InI n x := by
    intro D hD x hx
    obtain ⟨v, k, rfl⟩ := Y.mem_groupLayers.mp (hD x hx)
    exact Y.mem H v k
  rcases List.mem_append.mp hm with hm | hm <;>
  · obtain ⟨l, -, hml⟩ := List.mem_flatMap.mp hm
    exact layer_of_mem_conj (hP l) (hD _ fun x hx ↦ List.mem_of_mem_filter hx) hml

/-- A block run leaves alone every sticker in at most one layer of `I`. -/
theorem permW_run_oneLayer {G H : Fin h} (hq : G ≠ H) {ch : List (Fin a)}
    (hw₁ : ∀ d, wantF p₁ G H ch d ∈ Λ₁) (hw₂ : ∀ d, wantF p₂ G H ch d ∈ Λ₂) {ρ : ℕ}
    {p : Sticker n} (hpr : p ∈ OneLayer n ρ) : permW (Y.run hn g Λ₁ Λ₂ p₁ p₂ G H ch) p = p := by
  rw [permW_eq_keepLayer (fun m hm ↦ mem_run hm) hpr]
  have hφ := keepLayer_inv (n := n) ρ
  have hval : ∀ x (hx : InI n x) (t : Turn),
      keepLayer ρ (t.at hn x) = if x = ρ then (t.at hn x).perm else 1 := by
    intro x hx t
    unfold keepLayer Turn.at
    rw [layer_mv_I hn hx]
    have : x ≠ 1 := by have := hx.1; omega
    simp [this]
  have hkeep : evalW (keepLayer ρ) (Y.run hn g Λ₁ Λ₂ p₁ p₂ G H ch) = 1 := by
    by_cases hd : ∃ d ∈ Y.groupLayers H, d = ρ
    · obtain ⟨d, hd, hdρ⟩ := hd
      -- Only `d` of the fired group counts, and the setups are in another group.
      have hdI : InI n d := by
        obtain ⟨v, k, rfl⟩ := Y.mem_groupLayers.mp hd
        exact Y.mem H v k
      have hsetups : ∀ f, evalW (keepLayer ρ) (setupAt hn g (Y.pf G ch f)) = 1 := by
        intro f
        refine evalW_setupAt_quiet hφ fun x hx ↦ ?_
        obtain ⟨v, -, k, rfl⟩ := Y.layer_of_mem_pf hx
        rw [hval _ (Y.mem G v k)]
        obtain ⟨v', k', rfl⟩ := Y.mem_groupLayers.mp hd
        have : Y.L G v k ≠ ρ := by
          rw [← hdρ]
          exact layer_ne (Y := Y) hq
        rw [ite_eq_right_iff]
        exact fun h' ↦ absurd h' this
      refine evalW_blockRun_cancel hφ hd (Y.nodup_groupLayers H) ?_ (Finset.nodup_toList _)
        (Finset.mem_toList.mpr (hw₁ _)) (Finset.nodup_toList _) (Finset.mem_toList.mpr (hw₂ _))
        (hsetups _) (hsetups _)
      intro x hx hxd
      obtain ⟨v, k, rfl⟩ := Y.mem_groupLayers.mp hx
      rw [hval _ (Y.mem H v k)]
      have : Y.L H v k ≠ ρ := by
        rw [← hdρ]
        exact hxd
      rw [ite_eq_right_iff]
      exact fun h' ↦ absurd h' this
    · push Not at hd
      refine evalW_blockRun_quiet hφ fun x hx ↦ ?_
      obtain ⟨v, k, rfl⟩ := Y.mem_groupLayers.mp hx
      rw [hval _ (Y.mem H v k), ite_eq_right_iff]
      exact fun h' ↦ absurd h' (hd _ hx)
  rw [hkeep]
  rfl

/-- A 3-cycle's word leaves alone every sticker in at most one layer of `I`. -/
theorem permW_cycleWord_oneLayer {b : ℕ} (hp₁ : ∀ G H v d, p₁ G H v d ∈ 𝓑₁)
    (hp₂ : ∀ G H v d, p₂ G H v d ∈ 𝓑₂) {ρ : ℕ} {p : Sticker n} (hpr : p ∈ OneLayer n ρ) :
    permW (Y.cycleWord hn g b 𝓑₁ 𝓑₂ p₁ p₂) p = p :=
  permW_flatMap_fix fun _ hq ↦ permW_flatMap_fix fun _ _ ↦
    permW_run_oneLayer (ne_of_lt (mem_groupPairs.mp hq)) (fun d ↦ wantF_mem fun v ↦ hp₁ _ _ v d)
      (fun d ↦ wantF_mem fun v ↦ hp₂ _ _ v d) hpr

end Outer

/-- The same layers, with rows and columns swapped. In `Y.transpose`, a sub-block is an interval of
`Y`, so a block run on it is a twist: see `CubeGod.Method.Twist`. -/
def transpose : Layout n h c a where
  L G k v := Y.L G v k
  inj G k v G' k' v' he := by
    obtain ⟨h₁, h₂, h₃⟩ := Y.inj _ _ _ _ _ _ he
    exact ⟨h₁, h₃, h₂⟩
  mem G k v := Y.mem G v k

end Layout

end CubeGod
