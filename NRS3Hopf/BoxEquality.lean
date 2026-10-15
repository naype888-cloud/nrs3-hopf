/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NRS3Hopf.BoxCommute
public import NRS3Hopf.RobertsonEquality
public import NRS3Hopf.ClosedAxisEntangled
public import NRS3Hopf.RobertsonCoupling

/-!
# Equality on the box with a hidden closed fiber

The equality case on `n` axes (`RobertsonEquality`) applied to the box of four axes with the
fourth axis closed with three positions. The axes commute (`BoxCommute`), and the hidden fiber
carries a positive defect for every state in its band (`ClosedAxisEntangled`). So for every
unit state with tension above `1` on the fiber and `det Ω ≠ 0`, equality in Robertson 1934 on
the eight observables forces a relation among the four tensions,
`Σ_i σ_i [T_i, P_i] Φ = 0` with `σ ≠ 0`, the first step of `D49t` for the box.

## Main results

- `BoxEquality.exists_sigma_of_det_eq` : equality on the box with the fiber in its band gives
  `Σ_i σ_i [T_i, P_i] Φ = 0` with `σ ≠ 0`.
- `BoxEquality.exists_coupling` : and the hidden fiber couples to `x`, `y`, `z`: a nonzero
  combination of its fluctuation vectors is a combination of theirs.
-/

@[expose] public noncomputable section

open Matrix PathGraph3DNRS RobertsonDeterminant FourAxes CubeInBox SpectralExtremal

namespace BoxEquality

/-- **Equality on the box needs a relation among the four tensions**, the hidden closed fiber
being in its band. -/
theorem exists_sigma_of_det_eq {dx dy dz : ℕ} {Φ : H4D dx dy dz 3} (hΦ : ‖Φ‖ = 1)
    (hb : 1 < |tensionG (boxPairs dx dy dz 3 closedPair (0, 3))
      (boxPairs dx dy dz 3 closedPair (1, 3)) Φ|)
    (hΩ : (imMatrix (boxPairs dx dy dz 3 closedPair) Φ).det ≠ 0)
    (heq : (covMatrix (boxPairs dx dy dz 3 closedPair) Φ).det =
      |(imMatrix (boxPairs dx dy dz 3 closedPair) Φ).det|) :
    ∃ σ : Fin 4 → ℂ, σ ≠ 0 ∧ ∑ i, σ i • opCommutator (boxPairs dx dy dz 3 closedPair (0, i))
      (boxPairs dx dy dz 3 closedPair (1, i)) Φ = 0 :=
  RobertsonEquality.exists_sigma_of_det_eq
    (fun s t i j h ψ => BoxCommute.boxPairs_comm closedPair s t i j h ψ) 3
    (ClosedAxisEntangled.gramDefect_box_pos hΦ hb) hΩ heq

/-- **At equality the hidden fiber couples to the visible axes**: some nonzero combination
`α (T° − ⟨T°⟩)Φ + β (P₃ − ⟨P₃⟩)Φ` is a combination of the fluctuation vectors of `x`, `y`, `z`. -/
theorem exists_coupling {dx dy dz : ℕ} {Φ : H4D dx dy dz 3} (hΦ : ‖Φ‖ = 1)
    (hb : 1 < |tensionG (boxPairs dx dy dz 3 closedPair (0, 3))
      (boxPairs dx dy dz 3 closedPair (1, 3)) Φ|)
    (hΩ : (imMatrix (boxPairs dx dy dz 3 closedPair) Φ).det ≠ 0)
    (heq : (covMatrix (boxPairs dx dy dz 3 closedPair) Φ).det =
      |(imMatrix (boxPairs dx dy dz 3 closedPair) Φ).det|) :
    ∃ b : Fin 2 → ℂ, RobertsonCoupling.combAxis (boxPairs dx dy dz 3 closedPair) Φ 3 b ≠ 0 ∧
      RobertsonCoupling.combAxis (boxPairs dx dy dz 3 closedPair) Φ 3 b ∈
        LinearMap.range (RobertsonCoupling.combOff (boxPairs dx dy dz 3 closedPair) Φ 3) :=
  RobertsonCoupling.exists_coupling 3 (ClosedAxisEntangled.gramDefect_box_pos hΦ hb) hΩ heq

end BoxEquality
