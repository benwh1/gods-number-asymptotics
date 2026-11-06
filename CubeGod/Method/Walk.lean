import CubeGod.Cube.Cycles

/-!
# `[[a, b] : c]`, walks and block runs

The move sequence `[[a, b] : c] = a b a' b' c b a b' a'` (a `CommConj`) does `c` inside the setup
`[a, b]`. A walk goes through a list of choices, and at each choice does `[[S·a, b] : T·c]`: it sets
up the set `S` of layers, fires the set `T` of layers that want that choice, and undoes the setup. A
block run is two walks, the second firing `c'`.

We evaluate words in any group, through a map `φ` from moves, so that the same lemmas cover pairs and
the stickers of Stage 1.
-/

open Finset

namespace CubeGod

variable {n : ℕ} {H L ι : Type*} [Group H]

theorem evalW_map {M : Type*} (φ : L → H) (g : M → L) (l : List M) :
    evalW φ (l.map g) = evalW (φ ∘ g) l := by
  induction l with
  | nil => rfl
  | cons x l ih => simp [ih]

theorem evalW_eq_one {φ : L → H} {l : List L} (h : ∀ m ∈ l, φ m = 1) : evalW φ l = 1 := by
  induction l with
  | nil => rfl
  | cons m l ih =>
    simp only [evalW_cons, h m (by simp), mul_one]
    exact ih fun m' hm' ↦ h m' (by simp [hm'])

theorem evalW_flatMap_eq_one {φ : L → H} {f : ι → List L} {l : List ι}
    (h : ∀ x ∈ l, evalW φ (f x) = 1) : evalW φ (l.flatMap f) = 1 := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    rw [List.flatMap_cons, evalW_append, h x (by simp), mul_one]
    exact ih fun y hy ↦ h y (by simp [hy])

/-- If only one element of a list matters, the value of the whole list is its value. -/
theorem evalW_flatMap_single {φ : L → H} {f : ι → List L} {l : List ι} (hl : l.Nodup) {x₀ : ι}
    (hx₀ : x₀ ∈ l) (h : ∀ x ∈ l, x ≠ x₀ → evalW φ (f x) = 1) :
    evalW φ (l.flatMap f) = evalW φ (f x₀) := by
  induction l with
  | nil => simp at hx₀
  | cons y l ih =>
    rw [List.flatMap_cons, evalW_append]
    obtain ⟨hy, hl'⟩ := List.nodup_cons.mp hl
    by_cases hyx : y = x₀
    · subst hyx
      rw [evalW_flatMap_eq_one (fun x hx ↦ h x (by simp [hx]) (fun e ↦ hy (e ▸ hx))), one_mul]
    · rw [h y (by simp) hyx, mul_one]
      exact ih hl' ((List.mem_cons.mp hx₀).resolve_left (Ne.symm hyx))
        fun x hx ↦ h x (by simp [hx])

theorem evalW_single {φ : L → H} {l : List L} (hl : l.Nodup) {x₀ : L} (hx₀ : x₀ ∈ l)
    (h : ∀ x ∈ l, x ≠ x₀ → φ x = 1) : evalW φ l = φ x₀ := by
  have := evalW_flatMap_single (φ := φ) (f := fun x ↦ [x]) hl hx₀
    (fun x hx hne ↦ by simp [h x hx hne])
  simpa using this

/-- The value of a word of a list is the product of the values of its parts. -/
theorem evalW_flatMap {H L ι : Type*} [Group H] (φ : L → H) (f : ι → List L) (l : List ι) :
    evalW φ (l.flatMap f) = evalW (fun x ↦ evalW φ (f x)) l := by
  induction l with
  | nil => rfl
  | cons x l ih => rw [List.flatMap_cons, evalW_append, ih, evalW_cons]

/-- Words that each fix a sticker fix it together. -/
theorem permW_flatMap_fix {ι : Type*} {f : ι → List (Move n)} {l : List ι} {p : Sticker n}
    (h : ∀ x ∈ l, permW (f x) p = p) : permW (l.flatMap f) p = p := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    have hx : evalW Move.perm (f x) p = p := h x (by simp)
    show evalW Move.perm (f x ++ l.flatMap f) p = p
    rw [evalW_append, Equiv.Perm.mul_apply, hx]
    exact ih fun y hy ↦ h y (by simp [hy])

/-- The move of layer `d` of face `E`, clockwise if `cw`, for `1 ≤ d ≤ n`. -/
def mv (hn : 0 < (n + 1) / 2) (d : ℕ) (E : Face) (cw : Bool) : Move n :=
  ⟨E, (d - 1) % n + 1, Direction.ofBool cw, by omega, Nat.mod_lt _ (by omega)⟩

theorem layer_mv (hn : 0 < (n + 1) / 2) {d : ℕ} (h₁ : 1 ≤ d) (h₂ : d ≤ n) (E : Face) (cw : Bool) :
    (mv hn d E cw).layer = d := by
  simp only [mv]
  rw [Nat.mod_eq_of_lt (by omega)]
  omega

theorem layer_mv_one (hn : 0 < (n + 1) / 2) (E : Face) (cw : Bool) : (mv hn 1 E cw).layer = 1 :=
  layer_mv hn le_rfl (by omega) E cw

@[simp] theorem face_mv (hn : 0 < (n + 1) / 2) (d : ℕ) (E : Face) (cw : Bool) :
    (mv hn d E cw).face = E := rfl

@[simp] theorem cw_mv (hn : 0 < (n + 1) / 2) (d : ℕ) (E : Face) (cw : Bool) :
    (mv hn d E cw).cw = cw := by
  cases cw <;> rfl

theorem mv_not (hn : 0 < (n + 1) / 2) (d : ℕ) (E : Face) (cw : Bool) :
    mv hn d E (!cw) = (mv hn d E cw).inv := by
  cases cw <;> rfl

theorem InI.pos' {d : ℕ} (h : InI n d) : 0 < (n + 1) / 2 := by
  have := h.1
  have := h.2
  omega

theorem InI.le_n {d : ℕ} (h : InI n d) : d ≤ n := h.lt_n.le

theorem layer_mv_I (hn : 0 < (n + 1) / 2) {d : ℕ} (h : InI n d) (E : Face) (cw : Bool) :
    (mv hn d E cw).layer = d :=
  layer_mv hn h.pos h.le_n E cw

/-- The value of `letterOf` on a move, by its layer. -/
theorem letterOf_mv_one (hn : 0 < (n + 1) / 2) {e d : ℕ} (he : InI n e) (E : Face)
    (cw : Bool) : letterOf e d (mv hn e E cw) = letter .one E cw := by
  simp [letterOf, layer_mv_I hn he]

theorem letterOf_mv_two (hn : 0 < (n + 1) / 2) {e d : ℕ} (he : InI n e) (hd : InI n d)
    (hne : d ≠ e) (E : Face) (cw : Bool) :
    letterOf e d (mv hn d E cw) = letter .two E cw := by
  have := he.2
  have := hd.2
  have : d ≠ n + 1 - e := by omega
  simp [letterOf, layer_mv_I hn hd, hne, this]

theorem letterOf_mv_outer (hn : 0 < (n + 1) / 2) {e d : ℕ} (he : InI n e) (hd : InI n d)
    (E : Face) (cw : Bool) : letterOf e d (mv hn 1 E cw) = letter .outer E cw := by
  have := he.1; have := he.2; have := hd.1; have := hd.2
  have h₀ : (1 : ℕ) ≠ e := by omega
  have h₀' : (1 : ℕ) ≠ d := by omega
  have h₁ : (1 : ℕ) ≠ n + 1 - e := by omega
  have h₂ : (1 : ℕ) ≠ n + 1 - d := by omega
  simp [letterOf, layer_mv_one hn, h₀, h₀', h₁, h₂]

theorem letterOf_mv_other (hn : 0 < (n + 1) / 2) {e d x : ℕ} (hx : InI n x) (he : InI n e)
    (hd : InI n d) (h₁ : x ≠ e) (h₂ : x ≠ d) (E : Face) (cw : Bool) :
    letterOf e d (mv hn x E cw) = 1 := by
  have := hx.1; have := hx.2; have := he.1; have := he.2; have := hd.1; have := hd.2
  have a₁ : x ≠ n + 1 - e := by omega
  have a₂ : x ≠ n + 1 - d := by omega
  have a₃ : x ≠ n := by omega
  have a₀ : x ≠ 1 := by omega
  simp [letterOf, layer_mv_I hn hx, h₁, h₂, a₀, a₁, a₂, a₃]

/-- The turn `t` of layer `l`. -/
def Turn.at (hn : 0 < (n + 1) / 2) (t : Turn) (l : ℕ) : Move n := mv hn l t.face t.cw

theorem Turn.inv_at (hn : 0 < (n + 1) / 2) (t : Turn) (l : ℕ) : t.inv.at hn l = (t.at hn l).inv :=
  mv_not hn l t.face t.cw

/-- The moves `[[a, b] : c] = a b a' b' c b a b' a'`: the moves `c`, conjugated by the commutator of
`a` and `b`. The moves of `a`, and those of `c`, are parallel layers, done one after another. -/
structure CommConj (n : ℕ) where
  /-- the first moves of the commutator -/
  a : List (Move n)
  /-- the second move of the commutator -/
  b : Move n
  /-- the moves done inside the commutator -/
  c : List (Move n)

namespace CommConj

variable (x : CommConj n)

/-- The commutator `[a, b] = a b a' b'`. -/
def setup : List (Move n) := x.a ++ [x.b] ++ invW x.a ++ [x.b.inv]

/-- The whole move sequence. -/
def moves : List (Move n) := x.setup ++ x.c ++ invW x.setup

variable {x} {φ : Move n → H}

theorem evalW_moves (hφ : ∀ m, φ m.inv = (φ m)⁻¹) :
    evalW φ x.moves = (evalW φ x.setup)⁻¹ * evalW φ x.c * evalW φ x.setup :=
  evalW_conj hφ _ _

/-- If the moves of `a` do nothing, the commutator is nothing. -/
theorem evalW_setup_quiet (hφ : ∀ m, φ m.inv = (φ m)⁻¹) (ha : evalW φ x.a = 1) :
    evalW φ x.setup = 1 := by
  simp only [setup, evalW_append, evalW_invW hφ, ha, evalW_cons, evalW_nil, hφ]
  group

theorem evalW_setup (hφ : ∀ m, φ m.inv = (φ m)⁻¹) :
    evalW φ x.setup = (φ x.b)⁻¹ * (evalW φ x.a)⁻¹ * φ x.b * evalW φ x.a := by
  simp only [setup, evalW_append, evalW_invW hφ, evalW_cons, evalW_nil, hφ, one_mul, mul_assoc]

end CommConj

/-- `[[a, b] : c]` for a 3-cycle, with the layers `S` set up and the layers `D` firing. -/
def Cycle.conj (hn : 0 < (n + 1) / 2) (g : Cycle) (S D : List ℕ) : CommConj n :=
  ⟨S.map (g.a.at hn), g.b.at hn 1, D.map (g.c.at hn)⟩

/-- The same 3-cycle, with the firing turn the other way. -/
def Cycle.reverse (g : Cycle) : Cycle := ⟨g.a, g.b, g.c.inv⟩

/-- A walk through the choices `Λ`: at each choice `l`, the layers `S l` are set up, and the layers
`d` of `D` with `want d = l` fire. -/
def walk [DecidableEq ι] (hn : 0 < (n + 1) / 2) (g : Cycle) (S : ι → List ℕ) (D : List ℕ)
    (want : ℕ → ι) (Λ : List ι) : List (Move n) :=
  Λ.flatMap fun l ↦ (g.conj hn (S l) (D.filter fun d ↦ want d = l)).moves

/-- A block run: the first walk fires `c`, and the second walk fires `c'`. -/
def blockRun [DecidableEq ι] (hn : 0 < (n + 1) / 2) (g : Cycle) (S : ι → List ℕ) (D : List ℕ)
    (want₁ want₂ : ℕ → ι) (Λ₁ Λ₂ : List ι) : List (Move n) :=
  walk hn g S D want₁ Λ₁ ++ walk hn g.reverse S D want₂ Λ₂

section Eval

variable [DecidableEq ι] {hn : 0 < (n + 1) / 2} {g : Cycle} {S : ι → List ℕ} {D : List ℕ}
  {want want₁ want₂ : ℕ → ι} {Λ Λ₁ Λ₂ : List ι} {φ : Move n → H}

/-- The setup of a choice. -/
abbrev setupAt (hn : 0 < (n + 1) / 2) (g : Cycle) (S : List ℕ) : List (Move n) :=
  (g.conj hn S []).setup

/-- A setup on layers that all do nothing is `b b'`, which is nothing. -/
theorem evalW_setupAt_quiet (hφ : ∀ m, φ m.inv = (φ m)⁻¹) {L : List ℕ}
    (hL : ∀ x ∈ L, φ (g.a.at hn x) = 1) : evalW φ (setupAt hn g L) = 1 := by
  refine CommConj.evalW_setup_quiet hφ ?_
  simp only [Cycle.conj]
  rw [evalW_map]
  exact evalW_eq_one hL

/-- A walk where no firing does anything is nothing at all. -/
theorem evalW_walk_quiet (hφ : ∀ m, φ m.inv = (φ m)⁻¹) (hD : ∀ d ∈ D, φ (g.c.at hn d) = 1) :
    evalW φ (walk hn g S D want Λ) = 1 := by
  refine evalW_flatMap_eq_one fun l _ ↦ ?_
  rw [CommConj.evalW_moves hφ]
  have : evalW φ (g.conj hn (S l) (D.filter fun d ↦ want d = l)).c = 1 := by
    simp only [Cycle.conj]
    rw [evalW_map]
    exact evalW_eq_one fun d hd ↦ hD d (List.mem_of_mem_filter hd)
  simp [this]

/-- A walk where exactly one layer's firing does anything: it fires inside its own setup. -/
theorem evalW_walk_fire (hφ : ∀ m, φ m.inv = (φ m)⁻¹) {d : ℕ} (hd : d ∈ D) (hDn : D.Nodup)
    (hD : ∀ d' ∈ D, d' ≠ d → φ (g.c.at hn d') = 1) (hΛ : Λ.Nodup) (hw : want d ∈ Λ) :
    evalW φ (walk hn g S D want Λ) =
      (evalW φ (setupAt hn g (S (want d))))⁻¹ * φ (g.c.at hn d) *
        evalW φ (setupAt hn g (S (want d))) := by
  unfold walk
  rw [evalW_flatMap_single hΛ hw]
  · rw [CommConj.evalW_moves hφ]
    congr 2
    -- The firing word has `d` once, and the other layers do nothing.
    simp only [Cycle.conj]
    rw [evalW_map]
    have hmem : d ∈ D.filter fun x ↦ want x = want d := by simp [hd]
    rw [evalW_single (hDn.filter _) hmem]
    · rfl
    · intro x hx hne
      exact hD x (List.mem_of_mem_filter hx) hne
  · intro l _ hne
    rw [CommConj.evalW_moves hφ]
    have : evalW φ (g.conj hn (S l) (D.filter fun x ↦ want x = l)).c = 1 := by
      simp only [Cycle.conj]
      rw [evalW_map]
      refine evalW_eq_one fun x hx ↦ ?_
      have hxl : want x = l := by simpa using (List.mem_filter.mp hx).2
      refine hD x (List.mem_of_mem_filter hx) ?_
      rintro rfl
      exact hne hxl.symm
    simp [this]

theorem reverse_c_at (g : Cycle) (d : ℕ) : g.reverse.c.at hn d = (g.c.at hn d).inv :=
  Turn.inv_at hn g.c d

/-- A block run where no firing does anything is nothing at all. -/
theorem evalW_blockRun_quiet (hφ : ∀ m, φ m.inv = (φ m)⁻¹) (hD : ∀ d ∈ D, φ (g.c.at hn d) = 1) :
    evalW φ (blockRun hn g S D want₁ want₂ Λ₁ Λ₂) = 1 := by
  have hD' : ∀ d ∈ D, φ (g.reverse.c.at hn d) = 1 := fun d hd ↦ by
    rw [reverse_c_at, hφ, hD d hd, inv_one]
  rw [blockRun, evalW_append, evalW_walk_quiet hφ hD, evalW_walk_quiet hφ hD', one_mul]

/-- In a block run, one layer's firing fires inside the setup of each walk. -/
theorem evalW_blockRun_fire (hφ : ∀ m, φ m.inv = (φ m)⁻¹) {d : ℕ} (hd : d ∈ D) (hDn : D.Nodup)
    (hD : ∀ d' ∈ D, d' ≠ d → φ (g.c.at hn d') = 1) (hΛ₁ : Λ₁.Nodup) (hw₁ : want₁ d ∈ Λ₁)
    (hΛ₂ : Λ₂.Nodup) (hw₂ : want₂ d ∈ Λ₂) :
    evalW φ (blockRun hn g S D want₁ want₂ Λ₁ Λ₂) =
      (evalW φ (setupAt hn g (S (want₂ d))))⁻¹ * (φ (g.c.at hn d))⁻¹ *
        evalW φ (setupAt hn g (S (want₂ d))) *
      ((evalW φ (setupAt hn g (S (want₁ d))))⁻¹ * φ (g.c.at hn d) *
        evalW φ (setupAt hn g (S (want₁ d)))) := by
  have hD' : ∀ d' ∈ D, d' ≠ d → φ (g.reverse.c.at hn d') = 1 := fun d' hd' hne ↦ by
    rw [reverse_c_at, hφ, hD d' hd' hne, inv_one]
  rw [blockRun, evalW_append, evalW_walk_fire hφ hd hDn hD hΛ₁ hw₁,
    evalW_walk_fire hφ hd hDn hD' hΛ₂ hw₂, reverse_c_at, hφ]
  rfl

/-- If the setups do nothing, a block run's two firings cancel. -/
theorem evalW_blockRun_cancel (hφ : ∀ m, φ m.inv = (φ m)⁻¹) {d : ℕ} (hd : d ∈ D) (hDn : D.Nodup)
    (hD : ∀ d' ∈ D, d' ≠ d → φ (g.c.at hn d') = 1) (hΛ₁ : Λ₁.Nodup) (hw₁ : want₁ d ∈ Λ₁)
    (hΛ₂ : Λ₂.Nodup) (hw₂ : want₂ d ∈ Λ₂) (h₁ : evalW φ (setupAt hn g (S (want₁ d))) = 1)
    (h₂ : evalW φ (setupAt hn g (S (want₂ d))) = 1) :
    evalW φ (blockRun hn g S D want₁ want₂ Λ₁ Λ₂) = 1 := by
  rw [evalW_blockRun_fire hφ hd hDn hD hΛ₁ hw₁ hΛ₂ hw₂, h₁, h₂]
  simp

end Eval

/-- Every move of `[[a, b] : c]` is in a layer of `S` or `D`, or the outside layer. -/
theorem layer_of_mem_conj {hn : 0 < (n + 1) / 2} {g : Cycle} {S D : List ℕ}
    (hS : ∀ x ∈ S, InI n x) (hD : ∀ x ∈ D, InI n x) {m : Move n}
    (hm : m ∈ (g.conj hn S D).moves) : InI n m.layer ∨ m.layer = 1 := by
  have hmv : ∀ (t : Turn) (x : ℕ), InI n x → InI n (t.at hn x).layer := fun t x hx ↦ by
    rw [Turn.at, layer_mv_I hn hx]; exact hx
  have h0 : ∀ t : Turn, (t.at hn 1).layer = 1 := fun t ↦ layer_mv_one hn _ _
  have hsetup : ∀ m ∈ (g.conj hn S D).setup, InI n m.layer ∨ m.layer = 1 := by
    intro m hm
    simp only [CommConj.setup, Cycle.conj, invW, List.mem_append, List.mem_map, List.mem_reverse,
      List.mem_singleton] at hm
    rcases hm with ((⟨x, hx, rfl⟩ | rfl) | ⟨_, ⟨x, hx, rfl⟩, rfl⟩) | rfl
    · exact Or.inl (hmv g.a x (hS x hx))
    · exact Or.inr (h0 g.b)
    · exact Or.inl (hmv g.a x (hS x hx))
    · exact Or.inr (h0 g.b)
  simp only [CommConj.moves, invW, List.mem_append, List.mem_map, List.mem_reverse] at hm
  rcases hm with (hm | hm) | ⟨m', hm', rfl⟩
  · exact hsetup m hm
  · simp only [Cycle.conj, List.mem_map] at hm
    obtain ⟨x, hx, rfl⟩ := hm
    exact Or.inl (hmv g.c x (hD x hx))
  · exact hsetup m' hm'

/-- The setup of a 3-cycle on a list of layers, seen by the pair `(e, d)`: it is `[a, b]` if `e` is
set up, and nothing if not. -/
theorem pairW_setupAt (hn : 0 < (n + 1) / 2) {e d : ℕ} (he : InI n e) (hd : InI n d) (g : Cycle)
    {S : List ℕ} (hS : S.Nodup) (hSI : ∀ x ∈ S, InI n x) (hSd : d ∉ S) :
    pairW e d (setupAt hn g S) = if e ∈ S then g.setup else 1 := by
  have hφ := letterOf_inv (n := n) e d
  have hother : ∀ x ∈ S, x ≠ e → letterOf e d (g.a.at hn x) = 1 := fun x hx hne ↦
    letterOf_mv_other hn (hSI x hx) he hd hne (fun h ↦ hSd (h ▸ hx)) _ _
  have ha : evalW (letterOf e d) (g.conj hn S []).a =
      if e ∈ S then letterOf e d (g.a.at hn e) else 1 := by
    simp only [Cycle.conj]
    rw [evalW_map]
    split_ifs with heS
    · exact evalW_single hS heS hother
    · exact evalW_eq_one fun x hx ↦ hother x hx fun h ↦ heS (h ▸ hx)
  unfold pairW
  split_ifs with heS
  · simp only [heS, ↓reduceIte] at ha
    rw [CommConj.evalW_setup hφ, ha]
    simp only [Cycle.conj, Cycle.setup, Turn.at, Turn.on, letterOf_mv_one hn he,
      letterOf_mv_outer hn he hd]
  · simp only [heS, ↓reduceIte] at ha
    exact CommConj.evalW_setup_quiet hφ ha

end CubeGod
