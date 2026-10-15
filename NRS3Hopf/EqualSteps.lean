/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NRS3Hopf.ClosedThree
public import Mathlib.Algebra.Lie.OfAssociative
public import NavaRobertsonIndependent.Mathematics.D49i_TransportPositionLieClosure

/-!
# Equal steps: an identity of every open axis that the closed axis breaks

The positions of `P_d` are equally spaced, with step `h = 2/(d − 1)`, and `T_d` moves one step.
So `[P_d, T_d]` multiplies each step by `±h`, and

  `[P_d, [P_d, T_d]] = h² T_d`

on every open axis, for every `d`, and so in the Szegő limit (`LieClosure.commutator_P_C`,
`D49i`).

On the closed axis with three positions no basis `Y₁ = αT° + βP₃`, `Y₂ = γT° + δP₃` of the plane
of `T°`, `P₃` satisfies `[Y₂, [Y₂, Y₁]] = c Y₁`, for any `c`: the entries force `γΔ = 0` and
`δΔ = 0`, with `Δ = αδ − βγ`, so `Δ² = 0`.

## Main results

- `EqualSteps.lie_Pd_Pd_Td` : `[P_d, [P_d, T_d]] = h² T_d` for every `d`.
- `EqualSteps.closed_ne` : no basis of the plane of `T°`, `P₃` satisfies it.
-/

@[expose] public noncomputable section

open Matrix TransportPosition LieClosure

attribute [local instance 100] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

namespace EqualSteps

variable {d : ℕ}

/-- **Equal steps**: `[P_d, [P_d, T_d]] = h² T_d`, `h = 2/(d − 1)`, for every `d`. -/
theorem lie_Pd_Pd_Td :
    ⁅Pd d, ⁅Pd d, Td d⁆⁆ = ((2 : ℂ) / ((d : ℂ) - 1)) ^ 2 • Td d := by
  have h := commutator_P_C (d := d)
  rw [show ⁅Pd d, ⁅Pd d, Td d⁆⁆ = -(Pd d * C d - C d * Pd d) by
    simp only [Ring.lie_def, C]; noncomm_ring, h, neg_smul, neg_neg]
  push_cast
  rfl

/-! ## The closed axis breaks it -/

/-- **No basis of the plane of `T°`, `P₃` has equal steps**: `[Y₂, [Y₂, Y₁]] = c Y₁` forces
`αδ − βγ = 0`. -/
theorem closed_ne {α β γ δ c : ℂ} (hΔ : α * δ - β * γ ≠ 0) :
    ⁅γ • ClosedThree.Tc + δ • Pd 3, ⁅γ • ClosedThree.Tc + δ • Pd 3,
      α • ClosedThree.Tc + β • Pd 3⁆⁆ ≠ c • (α • ClosedThree.Tc + β • Pd 3) := by
  intro h
  have e (i j : Fin 3) := congrFun (congrFun h i) j
  have e01 := e 0 1
  have e02 := e 0 2
  have e12 := e 1 2
  simp [Ring.lie_def, Matrix.mul_apply, Fin.sum_univ_three, ClosedThree.Tc, Pd, posCoord]
    at e01 e02 e12
  norm_num at e01 e02 e12
  apply hΔ
  have hsq : (α * δ - β * γ) ^ 2 = 0 := by
    linear_combination (-α / 3 - 2 * β / 3) * e01 + (2 * α / 3) * e02 + (-α / 3 + 2 * β / 3) * e12
  exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hsq

end EqualSteps
