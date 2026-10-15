/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Fin.VecNotation

/-!
# The closed fibered space is a triangulated three-sphere

Take the ends `±x, ±y, ±z` of the three open axes, and on the closed axis `w` the origin as
`+w` and the point at infinity as `−w`. Join every one of these eight points to every other
except its opposite. This is the boundary of the four-dimensional cross-polytope, the 16-cell.

* It has `8` vertices, `24` edges, `32` triangles and `16` tetrahedra, and Euler characteristic
  `8 − 24 + 32 − 16 = 0`, that of the three-sphere.
* Around every point, the origin and infinity included, the neighbours form an octahedron:
  `6` vertices, `12` edges, `8` triangles, Euler characteristic `2`, a two-sphere. Every point
  has a small sphere around it, as in a closed three-manifold.
* Each axis closes through the origin and infinity into a ring of four: `−a → 0 → +a → ∞ → −a`,
  with its two diagonals missing.

## Main results

- `Cell16.card_edges`, `Cell16.card_triangles`, `Cell16.card_tetrahedra`, `Cell16.euler` : the
  counts and `χ = 0`.
- `Cell16.link_counts` : the neighbours of the origin form an octahedron, `χ = 2`.
- `Cell16.axis_ring` : each axis is a ring of four through the origin and infinity.
-/

@[expose] public section

namespace Cell16

/-- The eight points: an axis (`0, 1, 2` for `x, y, z`, `3` for `w`) and a sign. -/
abbrev Pt := Fin 4 × Bool

/-- Two points are joined unless they are opposite ends of the same axis. -/
def Adj (u v : Pt) : Prop := u.1 ≠ v.1

instance : DecidableRel Adj := fun u v => inferInstanceAs (Decidable (u.1 ≠ v.1))

/-- The origin `+w` and infinity `−w`. -/
def origin : Pt := (3, true)
def infinity : Pt := (3, false)

/-- The cliques of size `k`: the faces of dimension `k − 1`. -/
def faces (k : ℕ) : Finset (Finset Pt) :=
  (Finset.powersetCard k Finset.univ).filter fun s => ∀ u ∈ s, ∀ v ∈ s, u ≠ v → Adj u v

theorem card_edges : (faces 2).card = 24 := by decide
theorem card_triangles : (faces 3).card = 32 := by decide
theorem card_tetrahedra : (faces 4).card = 16 := by decide

/-- **The Euler characteristic of the three-sphere**: `8 − 24 + 32 − 16 = 0`. -/
theorem euler : (Fintype.card Pt : ℤ) - (faces 2).card + (faces 3).card - (faces 4).card = 0 := by
  rw [card_edges, card_triangles, card_tetrahedra]; decide

/-- The neighbours of a point. -/
def link (p : Pt) : Finset Pt := Finset.univ.filter (Adj p)

/-- The faces of the link of a point. -/
def linkFaces (p : Pt) (k : ℕ) : Finset (Finset Pt) :=
  (Finset.powersetCard k (link p)).filter fun s => ∀ u ∈ s, ∀ v ∈ s, u ≠ v → Adj u v

/-- **Around the origin there is an octahedron**: `6` vertices, `12` edges, `8` triangles,
Euler characteristic `2`. -/
theorem link_counts : (link origin).card = 6 ∧ (linkFaces origin 2).card = 12 ∧
    (linkFaces origin 3).card = 8 ∧
    ((link origin).card : ℤ) - (linkFaces origin 2).card + (linkFaces origin 3).card = 2 := by
  decide

/-- **Each axis closes through the origin and infinity into a ring of four**:
`−a → 0 → +a → ∞ → −a`, without the diagonals. -/
theorem axis_ring (a : Fin 4) (ha : a ≠ 3) :
    Adj (a, false) origin ∧ Adj origin (a, true) ∧ Adj (a, true) infinity ∧
      Adj infinity (a, false) ∧ ¬ Adj (a, false) (a, true) ∧ ¬ Adj origin infinity := by
  simp only [Adj, origin, infinity, ne_eq, not_not, and_true]
  exact ⟨ha, Ne.symm ha, ha, Ne.symm ha⟩

end Cell16
