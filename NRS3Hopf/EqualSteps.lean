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

on every open axis, for every `d`, and so in the Szegő limit.

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
  ext i j
  simp only [Ring.lie_def, Matrix.sub_apply, Pd_mul_apply, mul_Pd_apply, Matrix.smul_apply,
    smul_eq_mul]
  by_cases h : MinStep i j
  · have hd : (posCoord d i : ℂ) - posCoord d j = 2 / ((d : ℂ) - 1) ∨
        (posCoord d i : ℂ) - posCoord d j = -(2 / ((d : ℂ) - 1)) := by
      simp only [posCoord]
      push_cast
      rcases h with h | h
      · right
        rw [show (j.val : ℂ) = i.val + 1 by exact_mod_cast h.symm]
        ring
      · left
        rw [show (i.val : ℂ) = j.val + 1 by exact_mod_cast h.symm]
        ring
    have key : (posCoord d i : ℂ) * ((posCoord d i : ℂ) * Td d i j - Td d i j * posCoord d j) -
        ((posCoord d i : ℂ) * Td d i j - Td d i j * posCoord d j) * posCoord d j =
        ((posCoord d i : ℂ) - posCoord d j) ^ 2 * Td d i j := by ring
    rw [key]
    rcases hd with hd | hd
    · rw [hd]
    · rw [hd]; ring
  · have h0 : Td d i j = 0 := by simp [Td, Ad, h]
    simp [h0]

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
