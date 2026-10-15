/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NRS3Hopf.BochnerCurvature
public import NavaRobertsonIndependent.Mathematics.D49_RobertsonDeterminant

/-!
# NRS on the closed fibered space: every axis keeps its defect

On the 16-cell (`Cell16`) transport moves to any of the six neighbours, `T = A/6`, and the
position along axis `a` is its coordinate, `P_a = +1` at `+a`, `−1` at `−a`, `0` elsewhere. The
four positions commute.

* **Equal steps.** `[P_x, [P_x, T]] = T_x`, the part of transport that touches the axis `x`: the
  position moves by steps of `1`.
* **The axis keeps its defect.** The state `ψ* = (−i/2, i/2, √3/6, …, √3/6)` on `(+x, −x, rest)`
  is an eigenvector of `i[T, P_x]` with eigenvalue `1/√3` (numerically the largest). There
  `⟨T⟩ = 1/3`, `⟨P_x⟩ = 0`, `Var T = 5/18`, `Var P_x = 1/2`, `Cov = 0`, so
  `Var T · Var P_x − Cov² − (t/2)² = 1/18 > 0`, and `Var T · Var P_x / (t/2)² = 5/3`: Robertson is
  strict at the top of the tension, as on the open axes from `d = 4` (`D23`). The 16-cell has the
  same shape along `y`, `z`, `w`.

## Main results

- `NRSCell16.lie_P_P_T` : equal steps, `[P_x, [P_x, T]] = T_x`.
- `NRSCell16.top_eigenvector` : `i[T, P_x] ψ* = (1/√3) ψ*`.
- `NRSCell16.tension` : the tension at `ψ*` is `1/√3`.
- `NRSCell16.stats` : the mean, variances, covariance and tension at `ψ*`.
- `NRSCell16.defect_pos` : `Var T · Var P_x − Cov² − (t/2)² = 1/18 > 0`.
-/

@[expose] public noncomputable section

open Matrix Complex Cell16 PathGraph3DNRS SpectralExtremal RobertsonDeterminant

attribute [local instance 100] LieRing.ofAssociativeRing

namespace NRSCell16

/-- The space of the 16-cell. -/
abbrev H := EuclideanSpace ℂ Pt

/-- Transport `T = A/6`. -/
def Tm : Matrix Pt Pt ℂ := of fun u v => if Adj u v then 1 / 6 else 0

/-- The position along `x`. -/
def Pm : Matrix Pt Pt ℂ := diagonal fun p => if p.1 = 0 then (if p.2 then 1 else -1) else 0

/-- The part of transport that touches the axis `x`. -/
def Tx : Matrix Pt Pt ℂ := of fun u v => if Adj u v ∧ (u.1 = 0 ∨ v.1 = 0) then 1 / 6 else 0

/-- **Equal steps**: `[P_x, [P_x, T]] = T_x`. -/
theorem lie_P_P_T : ⁅Pm, ⁅Pm, Tm⁆⁆ = Tx := by
  ext ⟨a, s⟩ ⟨b, t⟩
  fin_cases a <;> fin_cases b <;> cases s <;> cases t <;>
    simp [Ring.lie_def, Pm, Tm, Tx, Adj, Matrix.sub_apply]

/-! ## Vectors of the form `(a at +x, b at −x, c elsewhere)` -/

/-- The vector `a` at `+x`, `b` at `−x`, `c` at the six other points. -/
def pat (a b c : ℂ) : H := WithLp.toLp 2 fun p => if p.1 = 0 then (if p.2 then a else b) else c

def T : H →ₗ[ℂ] H := Matrix.toEuclideanLin Tm
def P : H →ₗ[ℂ] H := Matrix.toEuclideanLin Pm

theorem T_pat (a b c : ℂ) : T (pat a b c) = pat c c ((a + b + 4 * c) / 6) := by
  ext ⟨i, s⟩
  fin_cases i <;> cases s <;>
    simp [T, pat, Tm, Adj, Matrix.toEuclideanLin, Matrix.toLpLin_apply, mulVec, dotProduct,
      Fintype.sum_prod_type, Fin.sum_univ_four] <;> ring

theorem P_pat (a b c : ℂ) : P (pat a b c) = pat a (-b) 0 := by
  ext ⟨i, s⟩
  fin_cases i <;> cases s <;>
    simp [P, pat, Pm, Matrix.toEuclideanLin, Matrix.toLpLin_apply, mulVec, dotProduct,
      diagonal, Fintype.sum_prod_type, Fin.sum_univ_four]

theorem pat_sub_smul (a b c a' b' c' m : ℂ) :
    pat a b c - m • pat a' b' c' = pat (a - m * a') (b - m * b') (c - m * c') := by
  ext ⟨i, s⟩
  fin_cases i <;> cases s <;> simp [pat]

theorem inner_pat (a b c a' b' c' : ℂ) :
    inner ℂ (pat a b c) (pat a' b' c') =
      starRingEnd ℂ a * a' + starRingEnd ℂ b * b' + 6 * (starRingEnd ℂ c * c') := by
  simp [pat, PiLp.inner_apply, Fintype.sum_prod_type, Fin.sum_univ_four, mul_comm]
  ring

/-! ## The state of maximal tension -/

private theorem h3 : ((√3 : ℝ) : ℂ) ^ 2 = 3 := by
  rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num

/-- `ψ* = (−i/2, i/2, √3/6, …)`. -/
def ψs : H := pat (-I / 2) (I / 2) ((√3 : ℝ) / 6)

theorem norm_ψs : ‖ψs‖ = 1 := by
  have h : (inner ℂ ψs ψs).re = 1 := by
    rw [ψs, inner_pat]
    simp [Complex.mul_re, Complex.div_re, Complex.div_im, Complex.conj_re, Complex.conj_im]
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
  have h2 : ‖ψs‖ ^ 2 = 1 := by rw [← inner_self_eq_norm_sq (𝕜 := ℂ)]; exact h
  nlinarith [norm_nonneg ψs, sq_nonneg (‖ψs‖ - 1)]

theorem T_ψs : T ψs = pat ((√3 : ℝ) / 6) ((√3 : ℝ) / 6) ((√3 : ℝ) / 9) := by
  rw [ψs, T_pat]; congr 1; ring

theorem P_ψs : P ψs = pat (-I / 2) (-I / 2) 0 := by
  rw [ψs, P_pat]; congr 1; ring

theorem mean_T : meanG T ψs = 1 / 3 := by
  rw [meanG, T_ψs, ψs, inner_pat]
  simp [Complex.mul_re, Complex.div_re, Complex.div_im, Complex.conj_re, Complex.conj_im]
  nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]

theorem mean_P : meanG P ψs = 0 := by
  rw [meanG, P_ψs, ψs, inner_pat]
  simp [Complex.mul_re, Complex.div_re, Complex.div_im, Complex.conj_re, Complex.conj_im]
  norm_num

theorem centered_T : centeredG T ψs =
    pat ((√3 : ℝ) / 6 + I / 6) ((√3 : ℝ) / 6 - I / 6) ((√3 : ℝ) / 18) := by
  rw [centeredG, mean_T, T_ψs, ψs, pat_sub_smul]; congr 1 <;> push_cast <;> ring

theorem centered_P : centeredG P ψs = pat (-I / 2) (-I / 2) 0 := by
  rw [centeredG, mean_P, P_ψs, ψs, pat_sub_smul]; congr 1 <;> push_cast <;> ring

private theorem s3 : √3 * √3 = 3 := Real.mul_self_sqrt (by norm_num)

/-- **The statistics at `ψ*`**: `Var T = 5/18`, `Var P_x = 1/2`, `Cov = 0`, and
`Im ⟪T̃ψ*, P̃ψ*⟫ = −√3/6`. -/
theorem stats : varianceG T ψs = 5 / 18 ∧ varianceG P ψs = 1 / 2 ∧
    covarianceG T P ψs = 0 ∧ (inner ℂ (centeredG T ψs) (centeredG P ψs)).im = -(√3 / 6) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [varianceG, ← inner_self_eq_norm_sq (𝕜 := ℂ), centered_T, inner_pat]
    simp [Complex.mul_re, Complex.div_re, Complex.div_im, Complex.conj_re, Complex.conj_im]
    nlinarith [s3]
  · rw [varianceG, ← inner_self_eq_norm_sq (𝕜 := ℂ), centered_P, inner_pat]
    simp [Complex.mul_re, Complex.div_re, Complex.div_im, Complex.conj_re, Complex.conj_im]
    norm_num
  · rw [covarianceG, centered_T, centered_P, inner_pat]
    simp [Complex.mul_re, Complex.div_re, Complex.div_im, Complex.conj_re, Complex.conj_im]
  · rw [centered_T, centered_P, inner_pat]
    simp [Complex.mul_im, Complex.div_re, Complex.div_im, Complex.conj_re, Complex.conj_im]
    ring

theorem T_symm : T.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr (by
  ext u v
  simp only [Tm, Adj, conjTranspose_apply, of_apply, ne_eq]
  by_cases h : u.1 = v.1
  · simp [h]
  · simp [h, Ne.symm h])

theorem P_symm : P.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr (by
  ext u v
  simp only [Pm, conjTranspose_apply, diagonal_apply]
  by_cases h : u = v
  · subst h; simp only [ite_true]; split_ifs <;> simp
  · simp [h, Ne.symm h])

/-- **The tension at `ψ*` is `1/√3`.** -/
theorem tension : tensionG T P ψs = √3 / 3 := by
  rw [tensionG_eq T_symm P_symm, stats.2.2.2]; ring

/-- **The axis keeps its defect at maximal tension**:
`Var T · Var P_x − Cov² − (t/2)² = 1/18 > 0`, and `det Σ / |det Ω| = 5/3`. -/
theorem defect_pos :
    varianceG T ψs * varianceG P ψs - covarianceG T P ψs ^ 2 - (tensionG T P ψs / 2) ^ 2 =
      1 / 18 := by
  obtain ⟨hT, hP, hC, -⟩ := stats
  rw [hT, hP, hC, tension]
  nlinarith [s3]

/-- **`ψ*` is the top eigenvector of the tension**: `i[T, P_x] ψ* = (1/√3) ψ*`. -/
theorem top_eigenvector :
    observableTension T P ψs = ((√3 : ℝ) / 3 : ℂ) • ψs := by
  have h3' : ((√3 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3)).ne'
  simp only [observableTension, opCommutator, LinearMap.smul_apply, LinearMap.sub_apply,
    LinearMap.comp_apply, P_ψs, T_ψs, T_pat, P_pat]
  rw [ψs]
  ext ⟨i, s⟩
  fin_cases i <;> cases s <;> simp [pat] <;> field_simp <;> ring_nf <;> simp [h3]

end NRSCell16
