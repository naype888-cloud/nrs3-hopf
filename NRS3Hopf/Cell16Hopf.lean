/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NRS3Hopf.Cell16

/-!
# The Hopf fibration of the closed fibered space

On the 16-cell (`Cell16`) pick an open axis `a`. Turn a quarter at once in the plane of `a` and
`w` and in the plane of the other two axes: `+w → +a → −w → −a → +w` and `+b → +c → −b → −c → +b`.
This rotation keeps the joins, has no fixed point, its square sends every point to its opposite
and its fourth power is the identity: it is a circle acting freely, as the Hopf circle does.

* **Two fibres.** Its orbits are the two rings `{±a, ±w}` and `{±b, ±c}`, four points each. The
  ring of `a` through the origin and infinity is `Cell16.axis_ring`. The base is two points, the
  two poles.
* **Each fibre is a ring**: it carries `4` of the `24` edges; the other `16 = 4 · 4` edges join
  the two fibres.
* **Every triangle** has an edge in one fibre and a point in the other: `32 = 4 · 4 + 4 · 4`.
* **Every tetrahedron** has exactly one edge in each fibre, and each pair of edges, one from each
  fibre, spans a tetrahedron: the `16` cells are `4 × 4`, the join of the two rings.
* **Three fibrations.** The three open axes give three different fibrations, one for each way of
  pairing the four axes.

## Main results

- `Cell16.rot_adj`, `Cell16.rot_rot`, `Cell16.rot_four` : the quarter turn keeps the joins, its
  square is the antipode, its fourth power is the identity.
- `Cell16.fiber_iff_orbit` : the fibres are the orbits of the quarter turn.
- `Cell16.card_fiberEdges`, `Cell16.card_crossEdges` : `4` edges in each fibre, `16` across.
- `Cell16.card_triangles_two` : `16` triangles have an edge in a given fibre.
- `Cell16.one_edge_each` : every tetrahedron has exactly one edge in each fibre.
- `Cell16.tetrahedra_eq_join` : the tetrahedra are the unions of an edge of each fibre.
- `Cell16.fiberEdge_in_four` : every edge of a fibre lies in `4` tetrahedra.
- `Cell16.fiber_injective` : the three open axes give three different fibrations.
-/

@[expose] public section

namespace Cell16

/-- The first of the two axes other than `a` and `w`. -/
def other₁ (a : Fin 4) : Fin 4 := if a = 0 then 1 else 0

/-- The second of the two axes other than `a` and `w`. -/
def other₂ (a : Fin 4) : Fin 4 := if a = 2 then 1 else 2

/-- The quarter turn in the plane of `a` and `w` and in the plane of the other two axes. -/
def rot (a : Fin 4) (p : Pt) : Pt :=
  if p.1 = 3 then (a, p.2)
  else if p.1 = a then (3, !p.2)
  else if p.1 = other₁ a then (other₂ a, p.2)
  else (other₁ a, !p.2)

/-- The fibre of a point: `true` on the ring of `a` and `w`, `false` on the other ring. -/
def fiber (a : Fin 4) (p : Pt) : Bool := decide (p.1 = a ∨ p.1 = 3)

/-- The edges inside the fibre `b`. -/
def fiberEdges (a : Fin 4) (b : Bool) : Finset (Finset Pt) :=
  (faces 2).filter fun e => ∀ p ∈ e, fiber a p = b

/-- The edges joining the two fibres. -/
def crossEdges (a : Fin 4) : Finset (Finset Pt) :=
  (faces 2).filter fun e => ∃ p ∈ e, ∃ q ∈ e, fiber a p ≠ fiber a q

/-- **The quarter turn keeps the joins.** -/
theorem rot_adj (a : Fin 4) (ha : a ≠ 3) : ∀ p q, Adj (rot a p) (rot a q) ↔ Adj p q := by
  revert a; decide

/-- **The square of the quarter turn is the antipode**: no point is fixed. -/
theorem rot_rot (a : Fin 4) (ha : a ≠ 3) : ∀ p : Pt, rot a (rot a p) = (p.1, !p.2) := by
  revert a; decide

/-- **The fourth power of the quarter turn is the identity.** -/
theorem rot_four (a : Fin 4) (ha : a ≠ 3) : ∀ p, rot a (rot a (rot a (rot a p))) = p := by
  revert a; decide

/-- **The fibres are the orbits of the quarter turn.** -/
theorem fiber_iff_orbit (a : Fin 4) (ha : a ≠ 3) : ∀ p q,
    fiber a p = fiber a q ↔
      q ∈ ({p, rot a p, rot a (rot a p), rot a (rot a (rot a p))} : Finset Pt) := by
  revert a; decide

/-- **Each fibre has four points.** -/
theorem card_fiber (a : Fin 4) (ha : a ≠ 3) (b : Bool) :
    (Finset.univ.filter fun p => fiber a p = b).card = 4 := by
  revert a b; decide

/-- **Each fibre carries `4` edges, a ring.** -/
theorem card_fiberEdges (a : Fin 4) (ha : a ≠ 3) (b : Bool) : (fiberEdges a b).card = 4 := by
  revert a b; decide

/-- **`16 = 4 · 4` edges join the two fibres.** -/
theorem card_crossEdges (a : Fin 4) (ha : a ≠ 3) : (crossEdges a).card = 16 := by
  revert a; decide

/-- **`16` triangles have an edge in the fibre `b`**, and the other `16` in the other fibre. -/
theorem card_triangles_two (a : Fin 4) (ha : a ≠ 3) (b : Bool) :
    ((faces 3).filter fun t => (t.filter fun p => fiber a p = b).card = 2).card = 16 := by
  revert a b; decide

/-- **Every tetrahedron has exactly one edge in each fibre.** -/
theorem one_edge_each (a : Fin 4) (ha : a ≠ 3) (b : Bool) :
    ∀ t ∈ faces 4, ((t.powersetCard 2).filter fun e => ∀ p ∈ e, fiber a p = b).card = 1 := by
  revert a b; decide +kernel

/-- **The tetrahedra are the unions of an edge of each fibre**: the `16` cells are `4 × 4`. -/
theorem tetrahedra_eq_join (a : Fin 4) (ha : a ≠ 3) :
    faces 4 = (fiberEdges a true ×ˢ fiberEdges a false).image fun e => e.1 ∪ e.2 := by
  revert a; decide

/-- **Every edge of a fibre lies in `4` tetrahedra.** -/
theorem fiberEdge_in_four (a : Fin 4) (ha : a ≠ 3) (b : Bool) :
    ∀ e ∈ fiberEdges a b, ((faces 4).filter fun t => e ⊆ t).card = 4 := by
  revert a b; decide +kernel

/-- **The three open axes give three different fibrations.** -/
theorem fiber_injective (a a' : Fin 4) (ha : a ≠ 3) (ha' : a' ≠ 3)
    (h : ∀ p, fiber a p = fiber a' p) : a = a' := by
  revert a a'; decide

end Cell16
