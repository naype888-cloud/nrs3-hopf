/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NRS3Hopf.StackedFibers
public import NavaRobertsonIndependent.Mathematics.D37e_VolumetricQuantum

/-!
# The excess of the box

The closed fiber with three positions at its maximal current state has `Cov = 0`,
`Var T° = 9/16`, `Var P₃ = 5/6` and `Im ⟪T̃°ψ, P̃₃ψ⟫ = −√6/4`, so its factor is exactly
`F = 5/4`, and its excess is `δ_w = √F − 1 = (√5 − 2)/2`.

On a product state the ratio of the box factors axis by axis (`CubeInBox.det_covMatrix_box`).
With the excess `δ(d) = C_Nava(d) − 1` of each open axis (`D25`), the excess of the box
`(1 + δ_x)(1 + δ_y)(1 + δ_z)(1 + δ_w) − 1` expands into the excesses of the axes, their products
in pairs, the volumetric quantum `𝒱 = δ_x δ_y δ_z` (`D37e`), and the terms with `w`. So `𝒱` is
the term of `x`, `y`, `z` inside the excess of the box, and the fiber enters only the terms with
`w`. At `3 × 3 × 3` every open term vanishes and the excess of the box is `δ_w`.

## Main results

- `BoxExcess.closedFactor_eq` : `F = 5/4`.
- `BoxExcess.closedExcess_eq` : `δ_w = (√5 − 2)/2`.
- `BoxExcess.boxExcess_eq` : the expansion, with `𝒱` as the term of `x`, `y`, `z`.
- `BoxExcess.boxExcess_three` : at `3 × 3 × 3` the excess of the box is `δ_w`.
-/

@[expose] public noncomputable section

open Complex NRSInequality TransportPosition EigenvectorSaturation CubeInBox StackedFibers
open DimensionalQuantum VolumetricQuantum ClosedThree

namespace BoxExcess

/-! ## 1. The factor of the closed fiber -/

section MaxState

private lemma h6 : √6 ^ 2 = 6 := Real.sq_sqrt (by norm_num)

private lemma h6' : (√6 : ℝ) ≠ 0 := by positivity

theorem mean_TcOp_maxState : mean TcOp maxState = 1 / 4 := by
  obtain ⟨t0, t1, t2⟩ := TcOp_apply maxState
  rw [mean, inner_eq, t0, t1, t2]
  simp [maxState, Complex.mul_re, Complex.div_re, Complex.div_im]
  field_simp
  nlinarith [h6]

theorem mean_PdOp_maxState : mean (PdOp 3) maxState = 0 := by
  obtain ⟨p0, p1, p2⟩ := PdOp_apply maxState
  rw [mean, inner_eq, p0, p1, p2]
  simp [maxState, Complex.mul_re, Complex.div_re, Complex.div_im]
  ring

theorem variance_TcOp_maxState : variance TcOp maxState = 9 / 16 := by
  obtain ⟨t0, t1, t2⟩ := TcOp_apply maxState
  rw [variance, normSq_eq]
  simp only [centered, mean_TcOp_maxState, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul, t0, t1,
    t2]
  simp [maxState, Complex.normSq_apply, Complex.div_re, Complex.div_im]
  field_simp
  nlinarith [h6]

theorem variance_PdOp_maxState : variance (PdOp 3) maxState = 5 / 6 := by
  obtain ⟨p0, p1, p2⟩ := PdOp_apply maxState
  rw [variance, normSq_eq]
  simp only [centered, mean_PdOp_maxState, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul, p0, p1,
    p2]
  simp [maxState, Complex.normSq_apply, Complex.div_re, Complex.div_im]
  field_simp
  nlinarith [h6]

theorem covariance_maxState : covariance TcOp (PdOp 3) maxState = 0 := by
  obtain ⟨t0, t1, t2⟩ := TcOp_apply maxState
  obtain ⟨p0, p1, p2⟩ := PdOp_apply maxState
  rw [covariance, inner_eq]
  simp only [centered, mean_TcOp_maxState, mean_PdOp_maxState, PiLp.sub_apply, PiLp.smul_apply,
    smul_eq_mul, t0, t1, t2, p0, p1, p2]
  simp [maxState, Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im]
  field_simp
  ring

theorem imPart_maxState : imPart TcOp (PdOp 3) maxState = -(√6 / 4) := by
  have ht := tension_maxState
  rw [tension, ← imPart_eq_im_inner TcOp_isSymmetric (PdOp_isSymmetric 3)] at ht
  linarith

end MaxState

/-- **The factor of the closed fiber is `5/4`.** -/
theorem closedFactor_eq : closedFactor = 5 / 4 := by
  have hi : imPart TcOp (PdOp 3) maxState ^ 2 = 3 / 8 := by
    rw [imPart_maxState, neg_sq, div_pow, Real.sq_sqrt (by norm_num)]
    norm_num
  rw [closedFactor, det_covMatrix_closed, abs_det_imMatrix_closed, gramDefectAt_eq_gap,
    variance_TcOp_maxState, variance_PdOp_maxState, covariance_maxState, hi]
  norm_num

/-- The excess of the closed fiber, `δ_w = √F − 1`. -/
def closedExcess : ℝ := √closedFactor - 1

/-- **The excess of the closed fiber is `(√5 − 2)/2`.** -/
theorem closedExcess_eq : closedExcess = (√5 - 2) / 2 := by
  rw [closedExcess, closedFactor_eq, show (5 / 4 : ℝ) = 5 / 2 ^ 2 by norm_num,
    Real.sqrt_div (by norm_num), Real.sqrt_sq (by norm_num)]
  ring

/-! ## 2. The excess of the box -/

/-- The excess of the box `dx × dy × dz` with the closed fiber,
`(1 + δ_x)(1 + δ_y)(1 + δ_z)(1 + δ_w) − 1`. -/
def boxExcess (dx dy dz : ℕ) : ℝ :=
  (1 + dimQuantum dx) * (1 + dimQuantum dy) * (1 + dimQuantum dz) * (1 + closedExcess) - 1

/-- **The volumetric quantum is the term of `x`, `y`, `z` in the excess of the box**; the fiber
enters only the terms with `w`. -/
theorem boxExcess_eq (dx dy dz : ℕ) :
    boxExcess dx dy dz =
      (dimQuantum dx + dimQuantum dy + dimQuantum dz) +
        (dimQuantum dx * dimQuantum dy + dimQuantum dx * dimQuantum dz +
          dimQuantum dy * dimQuantum dz) +
        volQuantum dx dy dz +
        closedExcess * ((1 + dimQuantum dx) * (1 + dimQuantum dy) * (1 + dimQuantum dz)) := by
  rw [boxExcess, volQuantum]
  ring

/-- **At `3 × 3 × 3` the excess of the box is the excess of the fiber**: `𝒱 = 0`, and so is
every other open term. -/
theorem boxExcess_three : boxExcess 3 3 3 = (√5 - 2) / 2 := by
  rw [boxExcess, dimQuantum_three, ← closedExcess_eq]
  ring

end BoxExcess
