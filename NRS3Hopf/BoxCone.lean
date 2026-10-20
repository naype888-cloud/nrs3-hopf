/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NRS3Hopf.ClosedAxisEntangled
public import NRS3UncertaintyCone.TimeDilation

/-!
# The uncertainty cone on the box with the closed fiber

Every axis of the box `dx × dy × dz × dw` carries a pair `(T, P)`, and the fluctuation vectors of
that pair form an uncertainty four-vector `v` (`UncertaintyCone.coneVector`). For every state of
the box and every axis, `v` lies in the closed future cone: `0 ≤ v₀` and `0 ≤ η(v, v)`. Nothing is
spacelike. The interval `η(v, v)` is the Robertson–Schrödinger defect of the axis, so the proper
time `τ = √η(v, v)` measures the distance of the state from the edge of the cone.

On the box with the fourth axis closed with three positions, a state whose speeds on `x`, `y`, `z`
lie in the band and whose tension on the closed fiber exceeds `1` is strictly timelike on all four
axes, entangled across the axes or not: the quantum that cannot be resolved is a positive proper
time on every axis.

## Main results

- `BoxCone.axisVector_mem_futureCone` : every axis of every state lies in the closed future cone.
- `BoxCone.interval_axisVector` : the interval of an axis is its Robertson–Schrödinger defect.
- `BoxCone.timelike_box_of_band` : in the band, with the closed fiber, `η(v, v) > 0` on all four
  axes.
- `BoxCone.properTime_box_pos_of_band` : the same for the proper time.
-/

@[expose] public noncomputable section

open TransportPosition PathGraph3DNRS CauchyGram FourAxes CubeInBox UncertaintyCone VelocityBand

namespace BoxCone

variable {dx dy dz dw : ℕ}

/-- The uncertainty four-vector of axis `i` of the box, for the pair `M` on the fiber `w`. -/
def axisVector (M : Fin 2 → Matrix (Fin dw) (Fin dw) ℂ) (Φ : H4D dx dy dz dw) (i : Fin 4) :
    Fin 4 → ℝ :=
  coneVector (centeredG (boxPairs dx dy dz dw M (0, i)) Φ)
    (centeredG (boxPairs dx dy dz dw M (1, i)) Φ)

/-- **Nothing is spacelike.** For every state and every axis, the four-vector lies in the closed
future cone. -/
theorem axisVector_mem_futureCone (M : Fin 2 → Matrix (Fin dw) (Fin dw) ℂ)
    (Φ : H4D dx dy dz dw) (i : Fin 4) :
    0 ≤ axisVector M Φ i 0 ∧ 0 ≤ interval (axisVector M Φ i) :=
  mem_futureCone (H := H4D dx dy dz dw) _ _

/-- The interval of an axis is its Robertson–Schrödinger defect. -/
theorem interval_axisVector (M : Fin 2 → Matrix (Fin dw) (Fin dw) ℂ) (Φ : H4D dx dy dz dw)
    (i : Fin 4) :
    interval (axisVector M Φ i) =
      gramDefectC (centeredG (boxPairs dx dy dz dw M (0, i)) Φ)
        (centeredG (boxPairs dx dy dz dw M (1, i)) Φ) :=
  interval_eq_gramDefectC _ _

/-- **Strictly timelike on all four axes, for every state in the band.** On the box with the
fourth axis closed with three positions, speeds of `x`, `y`, `z` in the band and tension above `1`
on the closed fiber put every axis strictly inside the cone, whatever the entanglement. -/
theorem timelike_box_of_band (hx : 2 ≤ dx) (hy : 2 ≤ dy) (hz : 2 ≤ dz) {Φ : H4D dx dy dz 3}
    (hΦ : ‖Φ‖ = 1)
    (hbx : |((dx : ℝ) - 1) / 2 * tensionG (boxPairs dx dy dz 3 closedPair (0, 0))
      (boxPairs dx dy dz 3 closedPair (1, 0)) Φ| ∈ Ϙ dx)
    (hby : |((dy : ℝ) - 1) / 2 * tensionG (boxPairs dx dy dz 3 closedPair (0, 1))
      (boxPairs dx dy dz 3 closedPair (1, 1)) Φ| ∈ Ϙ dy)
    (hbz : |((dz : ℝ) - 1) / 2 * tensionG (boxPairs dx dy dz 3 closedPair (0, 2))
      (boxPairs dx dy dz 3 closedPair (1, 2)) Φ| ∈ Ϙ dz)
    (hbw : 1 < |tensionG (boxPairs dx dy dz 3 closedPair (0, 3))
      (boxPairs dx dy dz 3 closedPair (1, 3)) Φ|) :
    ∀ i, 0 < interval (axisVector closedPair Φ i) := by
  intro i
  rw [interval_axisVector]
  fin_cases i
  · exact AxisDefectEntangled.gramDefect_pos_of_band hx (eX dx dy dz 3) hΦ hbx
  · exact AxisDefectEntangled.gramDefect_pos_of_band hy (eY dx dy dz 3) hΦ hby
  · exact AxisDefectEntangled.gramDefect_pos_of_band hz (eZ dx dy dz 3) hΦ hbz
  · exact ClosedAxisEntangled.gramDefect_box_pos hΦ hbw

/-- **The unresolvable quantum is a positive proper time on every axis.** -/
theorem properTime_box_pos_of_band (hx : 2 ≤ dx) (hy : 2 ≤ dy) (hz : 2 ≤ dz)
    {Φ : H4D dx dy dz 3} (hΦ : ‖Φ‖ = 1)
    (hbx : |((dx : ℝ) - 1) / 2 * tensionG (boxPairs dx dy dz 3 closedPair (0, 0))
      (boxPairs dx dy dz 3 closedPair (1, 0)) Φ| ∈ Ϙ dx)
    (hby : |((dy : ℝ) - 1) / 2 * tensionG (boxPairs dx dy dz 3 closedPair (0, 1))
      (boxPairs dx dy dz 3 closedPair (1, 1)) Φ| ∈ Ϙ dy)
    (hbz : |((dz : ℝ) - 1) / 2 * tensionG (boxPairs dx dy dz 3 closedPair (0, 2))
      (boxPairs dx dy dz 3 closedPair (1, 2)) Φ| ∈ Ϙ dz)
    (hbw : 1 < |tensionG (boxPairs dx dy dz 3 closedPair (0, 3))
      (boxPairs dx dy dz 3 closedPair (1, 3)) Φ|) (i : Fin 4) :
    0 < properTime (axisVector closedPair Φ i) :=
  Real.sqrt_pos.2 (timelike_box_of_band hx hy hz hΦ hbx hby hbz hbw i)

end BoxCone
