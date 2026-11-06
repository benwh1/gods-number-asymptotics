import CubeGod.Method.Twist

/-!
# The lengths of the words

A walk through `Λ` costs `2|S| + 2` moves for the setup `[S·a, b]` at each choice, and the same to
undo it, plus one move for each fired layer. Each layer fires once, however large `Λ` is. That is
where the saving comes from.
-/

open Finset

namespace CubeGod

variable {n h a c : ℕ}

theorem length_flatMap_le {α β : Type*} {f : α → List β} {l : List α} {B : ℕ}
    (hB : ∀ x ∈ l, (f x).length ≤ B) : (l.flatMap f).length ≤ l.length * B := by
  induction l with
  | nil => simp
  | cons x l ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    have h₁ := hB x (by simp)
    have h₂ := ih fun y hy ↦ hB y (by simp [hy])
    nlinarith

theorem Cycle.length_conj (hn : 0 < (n + 1) / 2) (g : Cycle) (S D : List ℕ) :
    (g.conj hn S D).moves.length = 4 * S.length + 4 + D.length := by
  simp [CommConj.moves, CommConj.setup, Cycle.conj]
  ring

theorem length_walk {ι : Type*} [DecidableEq ι] (hn : 0 < (n + 1) / 2) (g : Cycle)
    (S : ι → List ℕ) (want : ℕ → ι) {Λ : List ι} (hΛ : Λ.Nodup) {p : ℕ}
    (hP : ∀ l ∈ Λ, (S l).length ≤ p) (D : List ℕ) :
    (walk hn g S D want Λ).length ≤ Λ.length * (4 * p + 4) + D.length := by
  induction Λ generalizing D with
  | nil => simp [walk]
  | cons l Λ ih =>
    obtain ⟨hl, hΛ'⟩ := List.nodup_cons.mp hΛ
    -- The other choices don't see the layers that fire at `l`.
    have hsame : walk hn g S D want Λ =
        walk hn g S (D.filter fun d ↦ want d ≠ l) want Λ := by
      unfold walk
      refine List.flatMap_congr fun l' hl' ↦ ?_
      have hne : l' ≠ l := fun e ↦ hl (e ▸ hl')
      have hF : (D.filter fun d ↦ want d = l') =
          ((D.filter fun d ↦ want d ≠ l).filter fun d ↦ want d = l') := by
        rw [List.filter_filter]
        refine List.filter_congr fun d _ ↦ ?_
        by_cases hd : want d = l'
        · simp [hd, hne]
        · simp [hd]
      rw [hF]
    have hrec := ih hΛ' (fun l' hl' ↦ hP l' (by simp [hl'])) (D.filter fun d ↦ want d ≠ l)
    rw [← hsame] at hrec
    have hstep : (g.conj hn (S l) (D.filter fun d ↦ want d = l)).moves.length ≤
        4 * p + 4 + (D.filter fun d ↦ want d = l).length := by
      have h₂ := hP l (by simp)
      rw [Cycle.length_conj]
      omega
    have hsplit : (D.filter fun d ↦ want d = l).length + (D.filter fun d ↦ want d ≠ l).length =
        D.length := by
      have := List.length_eq_length_filter_add (l := D) (fun d ↦ decide (want d = l))
      simp only [decide_not] at this ⊢
      omega
    have hunfold : walk hn g S D want (l :: Λ) =
        (g.conj hn (S l) (D.filter fun d ↦ want d = l)).moves ++ walk hn g S D want Λ := by
      simp [walk]
    rw [hunfold, List.length_append, List.length_cons]
    nlinarith

theorem length_chunk {a b j : ℕ} (hb : 0 < b) : (chunk a b j).length ≤ b := by
  have hnd : (chunk a b j).Nodup := (List.nodup_finRange a).filter _
  rw [← List.toFinset_card_of_nodup hnd]
  have hinj : Set.InjOn (fun v : Fin a ↦ (v : ℕ) % b) ((chunk a b j).toFinset : Set (Fin a)) := by
    intro v hv v' hv' he
    have h₁ : (v : ℕ) / b = j := mem_chunk.mp (List.mem_toFinset.mp hv)
    have h₂ : (v' : ℕ) / b = j := mem_chunk.mp (List.mem_toFinset.mp hv')
    apply Fin.ext
    have e₁ := Nat.div_add_mod (v : ℕ) b
    have e₂ := Nat.div_add_mod (v' : ℕ) b
    simp only at he
    rw [h₁] at e₁
    rw [h₂] at e₂
    omega
  have := Finset.card_le_card_of_injOn (t := Finset.range b) (fun v : Fin a ↦ (v : ℕ) % b)
    (fun v _ ↦ Finset.mem_coe.mpr (Finset.mem_range.mpr (Nat.mod_lt _ hb))) hinj
  simpa using this

theorem length_choiceList {𝓑 : Finset (Fin c → Fin 2)} {ch : List (Fin a)} (hch : ch.Nodup)
    {M b : ℕ} (h₀ : #𝓑 ≤ M) (h₁ : 1 ≤ M) (hb : ch.length ≤ b) :
    (choiceSet 𝓑 ch).toList.length ≤ M ^ b := by
  classical
  rw [choiceSet, Finset.length_toList, Fintype.card_piFinset]
  have hv : ∀ v : Fin a, #(if v ∈ ch then 𝓑 else {0}) ≤ if v ∈ ch then M else 1 := by
    intro v
    by_cases h : v ∈ ch <;> simp [h, h₀]
  calc ∏ v, #(if v ∈ ch then 𝓑 else {0}) ≤ ∏ v : Fin a, (if v ∈ ch then M else 1) :=
        Finset.prod_le_prod₀ (fun _ _ ↦ Nat.zero_le _) fun v _ ↦ hv v
    _ = M ^ #(univ.filter fun v : Fin a ↦ v ∈ ch) := by
        rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one]
    _ ≤ M ^ b := by
        refine Nat.pow_le_pow_right h₁ ?_
        have : (univ.filter fun v : Fin a ↦ v ∈ ch) = ch.toFinset := by
          ext v
          simp
        rw [this, List.toFinset_card_of_nodup hch]
        exact hb

/-- A bound on the length of a 3-cycle's word. -/
def cycleLen (h a c b M : ℕ) : ℕ :=
  (groupPairs h).length * (a / b + 1) * (2 * (M ^ b * (8 * (b * c)) + a * c))

namespace Layout

variable (Y : Layout n h a c)

theorem length_groupLayers (G : Fin h) : (Y.groupLayers G).length = a * c := by
  simp [groupLayers, List.length_product]

theorem length_pf (G : Fin h) (ch : List (Fin a)) (f : Fin a → Fin c → Fin 2) :
    (Y.pf G ch f).length ≤ ch.length * c := by
  simp only [pf, List.length_map]
  exact (List.length_filter_le _ _).trans (by simp [List.length_product])

theorem length_run (hn : 0 < (n + 1) / 2) (g : Cycle) {𝓑₁ 𝓑₂ : Finset (Fin c → Fin 2)}
    (p₁ p₂ : Picks h a c) (G H : Fin h) {b j M : ℕ} (hb : 0 < b) (hc : 0 < c) (hM₁ : #𝓑₁ ≤ M)
    (hM₂ : #𝓑₂ ≤ M) (hM : 1 ≤ M) :
    (Y.run hn g (choiceSet 𝓑₁ (chunk a b j)) (choiceSet 𝓑₂ (chunk a b j)) p₁ p₂ G H
      (chunk a b j)).length ≤ 2 * (M ^ b * (8 * (b * c)) + a * c) := by
  have hch : (chunk a b j).Nodup := (List.nodup_finRange a).filter _
  have hlen := length_chunk (a := a) (j := j) hb
  have hbc : 1 ≤ b * c := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero hb.ne' hc.ne')
  have hP : ∀ f, (Y.pf G (chunk a b j) f).length ≤ b * c := fun f ↦
    (Y.length_pf G (chunk a b j) f).trans (Nat.mul_le_mul_right c hlen)
  have one : ∀ (g' : Cycle) (𝓑 : Finset (Fin c → Fin 2)) (want : ℕ → Fin a → Fin c → Fin 2),
      #𝓑 ≤ M → (walk hn g' (Y.pf G (chunk a b j)) (Y.groupLayers H)
        want (choiceSet 𝓑 (chunk a b j)).toList).length ≤ M ^ b * (8 * (b * c)) + a * c := by
    intro g' 𝓑 want hB
    have h₁ := length_walk hn g' (Y.pf G (chunk a b j)) want
      (Finset.nodup_toList (choiceSet 𝓑 (chunk a b j))) (fun l _ ↦ hP l) (Y.groupLayers H)
    have h₂ := length_choiceList hch hB hM hlen
    rw [Y.length_groupLayers] at h₁
    have h₃ := Nat.mul_le_mul_right (4 * (b * c) + 4) h₂
    have h₄ := Nat.mul_le_mul_left (M ^ b) (show 4 * (b * c) + 4 ≤ 8 * (b * c) by omega)
    omega
  have h₁ := one g 𝓑₁ (wantF p₁ G H (chunk a b j)) hM₁
  have h₂ := one g.reverse 𝓑₂ (wantF p₂ G H (chunk a b j)) hM₂
  simp only [run, blockRun, List.length_append]
  omega

theorem length_cycleWord (hn : 0 < (n + 1) / 2) (g : Cycle) {𝓑₁ 𝓑₂ : Finset (Fin c → Fin 2)}
    (p₁ p₂ : Picks h a c) {b M : ℕ} (hb : 0 < b) (hc : 0 < c) (hM₁ : #𝓑₁ ≤ M) (hM₂ : #𝓑₂ ≤ M)
    (hM : 1 ≤ M) : (Y.cycleWord hn g b 𝓑₁ 𝓑₂ p₁ p₂).length ≤ cycleLen h a c b M := by
  have hin : ∀ q ∈ groupPairs h, ((List.range (a / b + 1)).flatMap fun j ↦
      Y.run hn g (choiceSet 𝓑₁ (chunk a b j)) (choiceSet 𝓑₂ (chunk a b j)) p₁ p₂ q.1 q.2
        (chunk a b j)).length ≤
      (a / b + 1) * (2 * (M ^ b * (8 * (b * c)) + a * c)) := fun q _ ↦ by
    have := length_flatMap_le (l := List.range (a / b + 1)) (f := fun j ↦
      Y.run hn g (choiceSet 𝓑₁ (chunk a b j)) (choiceSet 𝓑₂ (chunk a b j)) p₁ p₂ q.1 q.2
        (chunk a b j))
      (fun j _ ↦ Y.length_run hn g p₁ p₂ q.1 q.2 hb hc hM₁ hM₂ hM)
    simpa using this
  have hout := length_flatMap_le hin
  unfold cycleWord cycleLen
  rw [mul_assoc]
  exact hout

theorem length_twistWord (hn : 0 < (n + 1) / 2) (ha : 0 < a) (L : ℕ)
    (lst : Fin h → Fin h → Fin c → ℕ → List Cycle) :
    (Y.twistWord hn L lst).length ≤ L * (allCycles.length * cycleLen h c a 1 2) := by
  have hin : ∀ i ∈ List.range L, (allCycles.flatMap fun g ↦ Y.twistCycle hn lst i g).length ≤
      allCycles.length * cycleLen h c a 1 2 :=
    fun i _ ↦ length_flatMap_le fun g _ ↦ Y.transpose.length_cycleWord hn g _ _ one_pos ha
      card_constBook card_constBook (by norm_num)
  have := length_flatMap_le hin
  rw [List.length_range] at this
  exact this

end Layout

/-- `2·|groupPairs| + h = h²`. -/
theorem two_length_groupPairs (h : ℕ) : 2 * (groupPairs h).length + h = h ^ 2 := by
  classical
  have hlen : (groupPairs h).length = #(univ.filter fun q : Fin h × Fin h ↦ q.1 < q.2) := by
    rw [← List.toFinset_card_of_nodup (nodup_groupPairs h)]
    congr 1
    ext q
    simp [mem_groupPairs]
  have hswap : #(univ.filter fun q : Fin h × Fin h ↦ q.2 < q.1) =
      #(univ.filter fun q : Fin h × Fin h ↦ q.1 < q.2) := by
    refine Finset.card_bij (fun q _ ↦ q.swap) ?_ ?_ ?_
    · intro q hq
      simpa using hq
    · intro q _ q' _ he
      exact Prod.swap_injective he
    · intro q hq
      exact ⟨q.swap, by simpa using hq, by simp⟩
  have hdiag : #(univ.filter fun q : Fin h × Fin h ↦ q.1 = q.2) = h := by
    have : (univ.filter fun q : Fin h × Fin h ↦ q.1 = q.2) = univ.image fun i : Fin h ↦ (i, i) := by
      ext q
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
      exact ⟨fun e ↦ ⟨q.1, Prod.ext rfl e⟩, fun ⟨i, e⟩ ↦ by rw [← e]⟩
    rw [this, Finset.card_image_of_injective _ fun i j e ↦ congrArg Prod.fst e]
    simp
  have htotal : #(univ.filter fun q : Fin h × Fin h ↦ q.1 < q.2) +
      #(univ.filter fun q : Fin h × Fin h ↦ q.2 < q.1) +
      #(univ.filter fun q : Fin h × Fin h ↦ q.1 = q.2) = h ^ 2 := by
    have hc : #(univ : Finset (Fin h × Fin h)) = h ^ 2 := by
      simp [sq]
    rw [← hc]
    simp only [Finset.card_filter]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, Finset.card_eq_sum_ones]
    refine Finset.sum_congr rfl fun q _ ↦ ?_
    rcases lt_trichotomy q.1 q.2 with h' | h' | h'
    · simp [h', ne_of_lt h', not_lt_of_gt h']
    · simp [h']
    · simp [h', ne_of_gt h', not_lt_of_gt h']
  omega

end CubeGod
