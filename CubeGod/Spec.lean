import Mathlib

/-!
# The n×n×n cube

Everything the main theorem says is defined in this file.

The cube has `6n²` stickers, `n²` on each face. A sticker is named by its face, column and row:
`(E, i, j)` is the sticker on face `E` in column `i` and row `j`. Columns and rows count from `0` at the
bottom left corner of the face, with the faces unfolded as

```
 U
LFRB
 D
```

So on `F`, `R`, `B` and `L` the bottom row is next to `D`, on `U` the bottom row is next to `F`, and on
`D` the top row is next to `F`. A state `s` says what colour each sticker is: `s E i j` is the colour of
the sticker on face `E` in column `i` and row `j`, naming each colour by the face it belongs on.

Moves use SiGN notation: `move E k Cw` is `kE` and `move E k Ccw` is `kE'`, a quarter turn of the `k`-th
layer from face `E` (counting from `1`), clockwise or anticlockwise as seen from outside `E`. For
example `move U 3 Ccw` is `3U'`. God's number counts these moves, so it's in the slice quarter-turn
metric.

To say where a move sends a sticker we use two tables. `E.right` and `E.up` are the faces next to the
right and top edges of `E` in the picture above. `G.turn f` is the face that a clockwise turn of `G` takes
the face `f` to; for example `U` takes `F` to `L`. From these, `layerFrom G p` is the layer of
face `G` that the sticker `p` is in, counting from `1` at the outside as in SiGN, so `kG` turns `p`
exactly when `layerFrom G p = k`. A turn takes a sticker to the face that the turn takes its face
to, keeping its layer from each face, turned along with it.
-/

open Filter Topology

namespace CubeGod

/-- The six faces. -/
inductive Face
  | U | L | F | R | B | D
  deriving DecidableEq, Repr

instance : Fintype Face :=
  ⟨{.U, .L, .F, .R, .B, .D}, by intro x; cases x <;> simp⟩

/-- `C = 24!/4!⁶`, the number of patterns of an oblique orbit. -/
def patternCount : ℕ := Nat.factorial 24 / (Nat.factorial 4) ^ 6

namespace Face

/-- The opposite face. -/
def opp : Face → Face
  | U => D | D => U | L => R | R => L | F => B | B => F

/-- The face next to the right edge of `E`, as `E` is drawn in the unfolded cube. -/
def right : Face → Face
  | U => R | L => F | F => R | R => B | B => L | D => R

/-- The face next to the top edge of `E`, as `E` is drawn in the unfolded cube. -/
def up : Face → Face
  | U => B | L => U | F => U | R => U | B => U | D => F

/-- Where a clockwise quarter turn of `G`, seen from outside `G`, takes the face `f`. A turn of `G`
takes `G` and its opposite to themselves, and the four faces around `G` one step round. -/
def turn : Face → Face → Face
  | U, F => L | U, L => B | U, B => R | U, R => F
  | D, F => R | D, R => B | D, B => L | D, L => F
  | F, U => R | F, R => D | F, D => L | F, L => U
  | B, U => L | B, L => D | B, D => R | B, R => U
  | R, F => U | R, U => B | R, B => D | R, D => F
  | L, F => D | L, D => B | L, B => U | L, U => F
  | _, f => f

end Face

/-- Which way a layer turns, seen from outside the face it's counted from. -/
inductive Direction
  /-- clockwise, as in `kE` -/
  | Cw
  /-- anticlockwise, as in `kE'` -/
  | Ccw
  deriving DecidableEq, Repr

export Direction (Cw Ccw)

/-- The other direction. -/
def Direction.reverse : Direction → Direction
  | Cw => Ccw
  | Ccw => Cw

/-- Where a quarter turn of `G` in direction `d` takes the face `f`. -/
def Face.turnBy (G : Face) : Direction → Face → Face
  | Cw => G.turn
  | Ccw => fun f ↦ G.turn (G.turn (G.turn f))

/-- A sticker: its face, column and row. -/
abbrev Sticker (n : ℕ) := Face × Fin n × Fin n

/-- A state: `s E i j` is the colour of the sticker on face `E` in column `i` and row `j`. -/
abbrev State (n : ℕ) := Face → Fin n → Fin n → Face

/-- The solved state: every sticker is on its own face. -/
def solved (n : ℕ) : State n := fun E _ _ ↦ E

/-- The layer of face `G` that the sticker `p` is in, counting from `1` at the outside as in SiGN:
`1` if it's on `G`, `n` if it's on the opposite face, and otherwise how far its column or row is
from the edge next to `G`, counting the column or row at that edge as `1`. -/
def layerFrom {n : ℕ} (G : Face) (p : Sticker n) : ℕ :=
  if G = p.1 then 1
  else if G = p.1.opp then n
  else if G = p.1.right then n - p.2.1
  else if G = p.1.right.opp then p.2.1 + 1
  else if G = p.1.up then n - p.2.2
  else p.2.2 + 1

/-- Where the move `kG` (`d = Cw`) or `kG'` (`d = Ccw`) takes the sticker `p`. If `p` is in the layer,
it goes to the face that the turn takes its face to, and its column and row there are what keep its
layer from each face, turned along with the face. -/
def moveSticker {n : ℕ} (G : Face) (k : ℕ) (d : Direction) (p : Sticker n) : Sticker n :=
  if layerFrom G p = k then
    let E := G.turnBy d p.1
    let back := G.turnBy d.reverse
    (E, ⟨n - layerFrom (back E.right) p, by have := p.2.1.2; unfold layerFrom; split_ifs <;> omega⟩,
      ⟨n - layerFrom (back E.up) p, by have := p.2.1.2; unfold layerFrom; split_ifs <;> omega⟩)
  else p

/-- The move `kG` (`d = Cw`) or `kG'` (`d = Ccw`). The sticker that ends up at `(E, i, j)` is the one
that the move takes there, which is where the opposite move takes `(E, i, j)`. -/
def move {n : ℕ} (G : Face) (k : ℕ) (d : Direction) (s : State n) : State n := fun E i j ↦
  let p := moveSticker G k d.reverse (E, i, j)
  s p.1 p.2.1 p.2.2

/-- A move of the n×n×n cube: a turn of layer `layer` of `face`, in direction `dir`. -/
@[ext] structure Move (n : ℕ) where
  /-- the face the layer is counted from -/
  face : Face
  /-- the layer, counting from `1` at the outside as in SiGN, so this is the move `layer face` -/
  layer : ℕ
  /-- clockwise or anticlockwise, seen from outside `face` -/
  dir : Direction
  /-- the layer is one of `1, …, n` -/
  layer_pos : 1 ≤ layer
  layer_le : layer ≤ n
  deriving DecidableEq

/-- Do a move. -/
def Move.apply {n : ℕ} (m : Move n) (s : State n) : State n :=
  move m.face m.layer m.dir s

/-- Do the moves of a word, first to last. -/
def act {n : ℕ} (w : List (Move n)) (s : State n) : State n :=
  w.foldl (fun s m ↦ m.apply s) s

/-- Some word solves `s`. -/
def Solvable {n : ℕ} (s : State n) : Prop := ∃ w, act w s = solved n

/-- The fewest moves that solve `s`. -/
noncomputable def dist {n : ℕ} (s : State n) : ℕ :=
  sInf {k | ∃ w : List (Move n), w.length = k ∧ act w s = solved n}

/-- God's number `D(n)`: the largest number of moves needed to solve a solvable state. -/
noncomputable def godsNumber (n : ℕ) : ℕ :=
  sSup {k | ∃ s : State n, Solvable s ∧ dist s = k}

end CubeGod
