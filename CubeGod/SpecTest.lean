import CubeGod.Spec

/-!
# Checks of the spec's conventions

Small cases that can be checked by hand, so we know the columns, rows, tables and directions in
`CubeGod.Spec` mean what they say. Each says where a move takes a sticker of a 3×3×3. Not part of the
proof.
-/

namespace CubeGod

open Face

/-- Where a move of the 3×3×3 takes a sticker. -/
abbrev go (G : Face) (k : ℕ) (d : Direction) (E : Face) (i j : Fin 3) : Sticker 3 :=
  moveSticker G k d (E, i, j)

-- `U` takes the top row of `F` to the top row of `L`, keeping its order.
example : ∀ i, go U 1 Cw F i 2 = (L, i, 2) := by decide
-- `U` leaves the middle row of `F` alone, and turns `U` clockwise: back left corner to back right.
example : ∀ i, go U 1 Cw F i 1 = (F, i, 1) := by decide
example : go U 1 Cw U 0 2 = (U, 2, 2) := by decide
-- `R` takes the right column of `F` up to the right column of `U`.
example : ∀ j, go R 1 Cw F 2 j = (U, 2, j) := by decide
-- and the right column of `U` to the left column of `B`, upside down.
example : ∀ j : Fin 3, go R 1 Cw U 2 j = (B, 0, 2 - j) := by decide
-- `F` takes the bottom row of `U` to the left column of `R`, front left corner to top.
example : go F 1 Cw U 0 0 = (R, 0, 2) := by decide
-- `2U'` (the middle layer, anticlockwise from above) takes the middle row of `F` to `R`.
example : ∀ i, go U 2 Ccw F i 1 = (R, i, 1) := by decide
-- `3U` is the bottom layer, turned the way `D'` turns it, and it also turns the `D` face.
example : ∀ i, go U 3 Cw F i 0 = (L, i, 0) := by decide
example : ∀ E i j, go U 3 Cw E i j = go D 1 Ccw E i j := by decide
-- `D` takes the bottom row of `F` to `R`.
example : ∀ i, go D 1 Cw F i 0 = (R, i, 0) := by decide
-- `L` takes the left column of `U` down to `F`.
example : ∀ j, go L 1 Cw U 0 j = (F, 0, j) := by decide
-- `B` takes the top row of `U` to the left column of `L`.
example : go B 1 Cw U 0 2 = (L, 0, 0) := by decide
-- Four quarter turns of any layer do nothing.
example : ∀ (G : Face) (k : Fin 3) (p : Sticker 3),
    moveSticker G (k + 1) Cw (moveSticker G (k + 1) Cw (moveSticker G (k + 1) Cw
      (moveSticker G (k + 1) Cw p))) = p := by
  decide

/-! Move orders and counts that are well known. -/

/-- All stickers of the n×n×n cube. -/
def allStickers (n : ℕ) : List (Sticker n) :=
  [U, L, F, R, B, D].flatMap fun E ↦ (List.finRange n).flatMap fun i ↦ (List.finRange n).map
    fun j ↦ (E, i, j)

/-- Where a word of SiGN moves takes a sticker. -/
def runW {n : ℕ} (w : List (Face × ℕ × Direction)) (p : Sticker n) : Sticker n :=
  w.foldl (fun p m ↦ moveSticker m.1 m.2.1 m.2.2 p) p

/-- The order of a word as a permutation of the stickers, searched up to `b`. -/
def order (n : ℕ) (w : List (Face × ℕ × Direction)) (b : ℕ) : Option ℕ :=
  (List.range (b + 1)).tail.find? fun k ↦
    (allStickers n).all fun p ↦ runW (List.replicate k w).flatten p = p

/-- How many stickers a move moves. -/
def moved (n : ℕ) (G : Face) (k : ℕ) : ℕ :=
  ((allStickers n).filter fun p ↦ moveSticker G k Cw p ≠ p).length

-- `U` has order 4, and the sexy move `R U R' U'` has order 6.
#guard order 3 [(U, 1, Cw)] 10 = some 4
#guard order 3 [(R, 1, Cw), (U, 1, Cw), (R, 1, Ccw), (U, 1, Ccw)] 10 = some 6
-- `R U` has order 105 on the 3×3×3, and `R U'` has order 63.
#guard order 3 [(R, 1, Cw), (U, 1, Cw)] 200 = some 105
#guard order 3 [(R, 1, Cw), (U, 1, Ccw)] 200 = some 63
-- `R` moves 20 stickers of the 3×3×3, and `M` moves 12.
#guard moved 3 R 1 = 20
#guard moved 3 R 2 = 12
-- On the 4×4×4, a face turn moves the 16 stickers on the face and 16 around it. A slice moves 16.
#guard moved 4 R 1 = 32
#guard moved 4 R 2 = 16

end CubeGod
