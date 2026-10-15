/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NRS3Hopf.RobertsonEqualityPlane

/-!
# Robertson 1934 is strict on the box with the closed fiber in its band

On the box with `2` or `3` positions on `x`, `y`, `z` and the closed fiber with three positions,
take a unit state with `det Ω ≠ 0` and the fiber in its band, `|⟨i[T°, P₃]⟩| > 1`. At equality:

* the fiber has a positive defect (`ClosedAxisEntangled`), so the relations cross it in both
  directions (`RobertsonEqualityPlane`);
* but on `x`, `y`, `z` with `2` or `3` positions they cross it along a line only
  (`BoxFiberLine`), since two relations through `T°` and `P₃` leave no state.

So equality never holds: `|det Ω₈| < det Σ₈`, for every such state, entangled with `x`, `y`, `z`
or not.

## Main results

- `BoxStrict.boxPairs_isSymmetric` : the eight observables of the box are symmetric.
- `BoxStrict.robertson_det_box_lt` : Robertson 1934 is strict on the box.
-/

@[expose] public noncomputable section

open Matrix TransportPosition PathGraph3DNRS RobertsonDeterminant FourAxes CubeInBox
open RobertsonDeterminant3D

namespace BoxStrict

variable {dx dy dz : ℕ}

/-- The eight observables of the box with the closed fiber are symmetric. -/
theorem boxPairs_isSymmetric (p : Fin 2 × Fin 4) :
    (boxPairs dx dy dz 3 closedPair p).IsSymmetric := by
  obtain ⟨s, i⟩ := p
  have hT (d : ℕ) : (![Td d, Pd d] s).IsHermitian := by
    fin_cases s
    exacts [Td_isHermitian d, Pd_isHermitian d]
  match i with
  | 0 => rw [BoxCommute.box_x]
         exact Matrix.isSymmetric_toEuclideanLin_iff.mpr (liftAlong_isHermitian _ (hT dx))
  | 1 => rw [BoxCommute.box_y]
         exact Matrix.isSymmetric_toEuclideanLin_iff.mpr (liftAlong_isHermitian _ (hT dy))
  | 2 => rw [BoxCommute.box_z]
         exact Matrix.isSymmetric_toEuclideanLin_iff.mpr (liftAlong_isHermitian _ (hT dz))
  | 3 => rw [BoxCommute.box_w]
         exact Matrix.isSymmetric_toEuclideanLin_iff.mpr
           (liftAlong_isHermitian _ (closedPair_isHermitian s))

/-- **Robertson 1934 is strict on the box with the closed fiber in its band.** With `2` or `3`
positions on `x`, `y`, `z`, every unit state with `det Ω ≠ 0` and `|⟨i[T°, P₃]⟩| > 1` has
`|det Ω₈| < det Σ₈`. -/
theorem robertson_det_box_lt (hx : dx = 2 ∨ dx = 3) (hy : dy = 2 ∨ dy = 3)
    (hz : dz = 2 ∨ dz = 3) {Φ : H4D dx dy dz 3} (hΦ : ‖Φ‖ = 1)
    (hb : 1 < |tensionG (boxPairs dx dy dz 3 closedPair (0, 3))
      (boxPairs dx dy dz 3 closedPair (1, 3)) Φ|)
    (hΩ : (imMatrix (boxPairs dx dy dz 3 closedPair) Φ).det ≠ 0) :
    |(imMatrix (boxPairs dx dy dz 3 closedPair) Φ).det| <
      (covMatrix (boxPairs dx dy dz 3 closedPair) Φ).det := by
  refine (robertson_det _ Φ).lt_of_ne fun heq => ?_
  have h1 := BoxFiberLine.finrank_map_fiberPart_eq_one hx hy hz hΦ hΩ heq.symm
  rw [RobertsonEqualityPlane.map_fiberPart_eq_top
    (fun s t i j h ψ => BoxCommute.boxPairs_comm closedPair s t i j h ψ) boxPairs_isSymmetric 3
    (ClosedAxisEntangled.gramDefect_box_pos hΦ hb) hΩ heq.symm, finrank_top,
    Module.finrank_fin_fun] at h1
  exact absurd h1 (by norm_num)

end BoxStrict
