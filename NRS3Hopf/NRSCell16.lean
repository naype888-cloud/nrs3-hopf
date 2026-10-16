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
position along axis `k` is its coordinate, `P_k = +1` at `+k`, `−1` at `−k`, `0` elsewhere. Every
statement holds for each of the four axes `k = x, y, z, w`.

* **Equal steps.** `[P_k, [P_k, T]] = T_k`, the part of transport that touches the axis `k`: the
  position moves by steps of `1`.
* **The maximal tension is `1/√3`.** `C = i[T, P_k] = (i/6) B` with `B` an integer matrix,
  `B³ = −12 B`, so `C³ = C/3`; for every unit state `‖Cψ‖² ≤ 1/3`, and `t² ≤ 1/3`.
* **Every axis keeps its defect.** The state `ψ* = (−i/2, i/2, √3/6, …, √3/6)` on
  `(+k, −k, rest)` is an eigenvector of `i[T, P_k]` with eigenvalue `1/√3`, the maximal tension.
  There `⟨T⟩ = 1/3`, `⟨P_k⟩ = 0`, `Var T = 5/18`, `Var P_k = 1/2`, `Cov = 0`, so
  `Var T · Var P_k − Cov² − (t/2)² = 1/18 > 0`, and `Var T · Var P_k / (t/2)² = 5/3`: Robertson
  is strict at the top of the tension on every axis, as on the open axes from `d = 4` (`D23`).

## Main results

- `NRSCell16.lie_P_P_T` : equal steps, `[P_x, [P_x, T]] = T_x`.
- `NRSCell16.top_eigenvector` : `i[T, P_x] ψ* = (1/√3) ψ*`.
- `NRSCell16.tension` : the tension at `ψ*` is `1/√3`.
- `NRSCell16.C_cube`, `NRSCell16.tension_sq_le`, `NRSCell16.tension_max` : `C³ = C/3` for
  `C = i[T, P_k]`, so `t² ≤ 1/3` on every unit state, and `ψ*` reaches it.
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

/-- The position along axis `k`. -/
def Pm (k : Fin 4) : Matrix Pt Pt ℂ :=
  diagonal fun p => if p.1 = k then (if p.2 then 1 else -1) else 0

/-- The part of transport that touches the axis `k`. -/
def Tx (k : Fin 4) : Matrix Pt Pt ℂ :=
  of fun u v => if Adj u v ∧ (u.1 = k ∨ v.1 = k) then 1 / 6 else 0

/-- **Equal steps**: `[P_k, [P_k, T]] = T_k`. -/
theorem lie_P_P_T (k : Fin 4) : ⁅Pm k, ⁅Pm k, Tm⁆⁆ = Tx k := by
  ext ⟨a, s⟩ ⟨b, t⟩
  fin_cases k <;> fin_cases a <;> fin_cases b <;> cases s <;> cases t <;>
    simp [Ring.lie_def, Pm, Tm, Tx, Adj, Matrix.sub_apply]

/-! ## Vectors of the form `(a at +x, b at −x, c elsewhere)` -/

/-- The vector `a` at `+k`, `b` at `−k`, `c` at the six other points. -/
def patk (k : Fin 4) (a b c : ℂ) : H :=
  WithLp.toLp 2 fun p => if p.1 = k then (if p.2 then a else b) else c

def T : H →ₗ[ℂ] H := Matrix.toEuclideanLin Tm
def Pos (k : Fin 4) : H →ₗ[ℂ] H := Matrix.toEuclideanLin (Pm k)

section Axis

variable (k : Fin 4)

local notation "pat" => patk k
local notation "P" => Pos k

theorem T_pat (a b c : ℂ) : T (pat a b c) = pat c c ((a + b + 4 * c) / 6) := by
  ext ⟨i, s⟩
  fin_cases k <;> fin_cases i <;> cases s <;>
    simp [T, patk, Tm, Adj, Matrix.toEuclideanLin, Matrix.toLpLin_apply, mulVec, dotProduct,
      Fintype.sum_prod_type, Fin.sum_univ_four] <;> ring

theorem P_pat (a b c : ℂ) : P (pat a b c) = pat a (-b) 0 := by
  ext ⟨i, s⟩
  fin_cases k <;> fin_cases i <;> cases s <;>
    simp [Pos, patk, Pm, Matrix.toEuclideanLin, Matrix.toLpLin_apply, mulVec, dotProduct,
      diagonal, Fintype.sum_prod_type, Fin.sum_univ_four]

theorem pat_sub_smul (a b c a' b' c' m : ℂ) :
    pat a b c - m • pat a' b' c' = pat (a - m * a') (b - m * b') (c - m * c') := by
  ext ⟨i, s⟩
  fin_cases k <;> fin_cases i <;> cases s <;> simp [patk]

theorem inner_pat (a b c a' b' c' : ℂ) :
    inner ℂ (pat a b c) (pat a' b' c') =
      starRingEnd ℂ a * a' + starRingEnd ℂ b * b' + 6 * (starRingEnd ℂ c * c') := by
  fin_cases k <;>
    simp [patk, PiLp.inner_apply, Fintype.sum_prod_type, Fin.sum_univ_four, mul_comm] <;> ring

/-! ## The state of maximal tension -/

private theorem h3 : ((√3 : ℝ) : ℂ) ^ 2 = 3 := by
  rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num

/-- `ψ* = (−i/2, i/2, √3/6, …)` on `(+k, −k, rest)`. -/
def psiK : H := patk k (-I / 2) (I / 2) ((√3 : ℝ) / 6)

local notation "ψs" => psiK k

theorem norm_ψs : ‖ψs‖ = 1 := by
  have h : (inner ℂ ψs ψs).re = 1 := by
    rw [psiK, inner_pat]
    simp [Complex.mul_re, Complex.div_re, Complex.div_im, Complex.conj_re, Complex.conj_im]
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
  have h2 : ‖ψs‖ ^ 2 = 1 := by rw [← inner_self_eq_norm_sq (𝕜 := ℂ)]; exact h
  nlinarith [norm_nonneg ψs, sq_nonneg (‖ψs‖ - 1)]

theorem T_ψs : T ψs = pat ((√3 : ℝ) / 6) ((√3 : ℝ) / 6) ((√3 : ℝ) / 9) := by
  rw [psiK, T_pat]; congr 1; ring

theorem P_ψs : P ψs = pat (-I / 2) (-I / 2) 0 := by
  rw [psiK, P_pat]; congr 1; ring

theorem mean_T : meanG T ψs = 1 / 3 := by
  rw [meanG, T_ψs, psiK, inner_pat]
  simp [Complex.mul_re, Complex.div_re, Complex.div_im, Complex.conj_re, Complex.conj_im]
  nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]

theorem mean_P : meanG P ψs = 0 := by
  rw [meanG, P_ψs, psiK, inner_pat]
  simp [Complex.mul_re, Complex.div_re, Complex.div_im, Complex.conj_re, Complex.conj_im]
  norm_num

theorem centered_T : centeredG T ψs =
    pat ((√3 : ℝ) / 6 + I / 6) ((√3 : ℝ) / 6 - I / 6) ((√3 : ℝ) / 18) := by
  rw [centeredG, mean_T, T_ψs, psiK, pat_sub_smul]; congr 1 <;> push_cast <;> ring

theorem centered_P : centeredG P ψs = pat (-I / 2) (-I / 2) 0 := by
  rw [centeredG, mean_P, P_ψs, psiK, pat_sub_smul]; congr 1 <;> push_cast <;> ring

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

theorem P_symm : (P).IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr (by
  ext u v
  simp only [Pm, conjTranspose_apply, diagonal_apply]
  by_cases h : u = v
  · subst h; simp only [ite_true]; split_ifs <;> simp
  · simp [h, Ne.symm h])

/-- **The tension at `ψ*` is `1/√3`.** -/
theorem tension : tensionG T P ψs = √3 / 3 := by
  rw [tensionG_eq T_symm (P_symm k), (stats k).2.2.2]; ring

/-- **The axis keeps its defect at maximal tension**:
`Var T · Var P_x − Cov² − (t/2)² = 1/18 > 0`, and `det Σ / |det Ω| = 5/3`. -/
theorem defect_pos :
    varianceG T ψs * varianceG P ψs - covarianceG T P ψs ^ 2 - (tensionG T P ψs / 2) ^ 2 =
      1 / 18 := by
  obtain ⟨hT, hP, hC, -⟩ := stats k
  rw [hT, hP, hC, tension k]
  nlinarith [s3]

/-- **`ψ*` is the top eigenvector of the tension**: `i[T, P_x] ψ* = (1/√3) ψ*`. -/
theorem top_eigenvector :
    observableTension T P ψs = ((√3 : ℝ) / 3 : ℂ) • ψs := by
  have h3' : ((√3 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3)).ne'
  simp only [observableTension, opCommutator, LinearMap.smul_apply, LinearMap.sub_apply,
    LinearMap.comp_apply, P_ψs, T_ψs, T_pat, P_pat]
  rw [psiK]
  ext ⟨i, s⟩
  fin_cases k <;> fin_cases i <;> cases s <;> simp [patk] <;> field_simp <;> ring_nf <;> simp [h3]

/-! ## The maximal tension is `1/√3` -/

/-- The coordinate of axis `k`, in the integers. -/
def pz (p : Pt) : ℤ := if p.1 = k then (if p.2 then 1 else -1) else 0

/-- The integer matrix `B = 6 [T, P_k]`. -/
def Bz : Matrix Pt Pt ℤ := of fun u v => if u.1 ≠ v.1 then pz k v - pz k u else 0

/-- The swap of the axes `x` and `k`, a symmetry of the 16-cell. -/
def axisSwap : Equiv.Perm Pt := signedPerm (Equiv.swap 0 k) fun _ => false

/-- `B` on axis `k` is `B` on axis `x` read through the swap of the axes. -/
theorem Bz_axisSwap : Bz k = (Bz 0).submatrix (axisSwap k) (axisSwap k) := by
  ext u v
  simp only [Bz, pz, axisSwap, submatrix_apply, signedPerm_apply, of_apply, Bool.false_xor, ne_eq,
    (Equiv.swap 0 k).injective.eq_iff, Equiv.swap_apply_eq_iff, Equiv.swap_apply_left]

/-- **`B³ = −12 B`** on every axis: checked once on the axis `x`, and carried to the axis `k`
by the swap of the axes. -/
theorem Bz_cube : Bz k * Bz k * Bz k = (-12 : ℤ) • Bz k := by
  have h0 : Bz 0 * Bz 0 * Bz 0 = (-12 : ℤ) • Bz 0 := by decide
  rw [Bz_axisSwap, submatrix_mul_equiv, submatrix_mul_equiv, h0]
  rfl

theorem comm_eq : Tm * Pm k - Pm k * Tm = (1 / 6 : ℂ) • (Bz k).map (Int.cast : ℤ → ℂ) := by
  ext ⟨a, s⟩ ⟨b, t⟩
  simp only [Matrix.sub_apply, mul_diagonal, diagonal_mul, Pm, Matrix.smul_apply, Matrix.map_apply,
    Bz, pz, Tm, Adj, of_apply, smul_eq_mul]
  fin_cases k <;> fin_cases a <;> fin_cases b <;> cases s <;> cases t <;> norm_num

theorem C_eq : observableTension T P =
    Matrix.toEuclideanLin ((I / 6) • (Bz k).map (Int.cast : ℤ → ℂ)) := by
  rw [observableTension, opCommutator, T, Pos, ← Matrix.toLpLin_mul_same, ← Matrix.toLpLin_mul_same,
    ← map_sub, comm_eq, ← map_smul, smul_smul]
  congr 2; ring

/-- **`C³ = C/3`** for `C = i[T, P_k]`: its eigenvalues are `0` and `±1/√3`. -/
theorem C_cube (v : H) :
    observableTension T P (observableTension T P (observableTension T P v)) =
      (1 / 3 : ℂ) • observableTension T P v := by
  have hB : (Bz k).map (Int.cast : ℤ → ℂ) * (Bz k).map (Int.cast : ℤ → ℂ) *
      (Bz k).map (Int.cast : ℤ → ℂ) = (-12 : ℂ) • (Bz k).map (Int.cast : ℤ → ℂ) := by
    ext i j
    have h := congrFun (congrFun (Bz_cube k) i) j
    simp only [Matrix.mul_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul] at h ⊢
    exact_mod_cast h
  have hM : ((I / 6) • (Bz k).map (Int.cast : ℤ → ℂ)) * ((I / 6) • (Bz k).map (Int.cast : ℤ → ℂ)) *
      ((I / 6) • (Bz k).map (Int.cast : ℤ → ℂ)) =
      (1 / 3 : ℂ) • ((I / 6) • (Bz k).map (Int.cast : ℤ → ℂ)) := by
    simp only [smul_mul_assoc, mul_smul_comm, smul_smul, hB]
    congr 1
    ring_nf
    rw [show I ^ 3 = -I by rw [pow_succ, Complex.I_sq]; ring]
    ring
  rw [C_eq]
  have h1 := congrArg (fun M => Matrix.toEuclideanLin M v) hM
  simp only [Matrix.toLpLin_mul_same, LinearMap.comp_apply, map_smul, LinearMap.smul_apply] at h1
  simpa [Matrix.toEuclideanLin, Matrix.toLpLin_mul_same] using h1

/-- **The tension is at most `1/√3`** on every unit state, on every axis. -/
theorem tension_sq_le {ψ : H} (hψ : ‖ψ‖ = 1) : tensionG T P ψ ^ 2 ≤ 1 / 3 := by
  set C := observableTension T P
  have hs : C.IsSymmetric := observableTension_isSymmetric T P T_symm (P_symm k)
  set x := C ψ
  set y := C x
  have hx : ‖x‖ ^ 2 = (inner ℂ ψ y).re := by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ), show inner ℂ x x = inner ℂ ψ y from hs ψ x]; rfl
  have hy : ‖y‖ ^ 2 = (1 / 3) * ‖x‖ ^ 2 := by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ), ← inner_self_eq_norm_sq (𝕜 := ℂ),
      show inner ℂ y y = inner ℂ x (C y) from hs x y, show C y = (1 / 3 : ℂ) • x from C_cube k ψ,
      inner_smul_right]
    simp
  have hle : (inner ℂ ψ y).re ≤ ‖y‖ := by
    have h1 := Complex.re_le_norm (inner ℂ ψ y)
    have h2 := norm_inner_le_norm (𝕜 := ℂ) ψ y
    rw [hψ, one_mul] at h2
    exact h1.trans h2
  have hx2 : ‖x‖ ^ 2 ≤ 1 / 3 := by
    have h0 := norm_nonneg y
    nlinarith [sq_nonneg (‖x‖ ^ 2), norm_nonneg x]
  have ht : |tensionG T P ψ| ≤ ‖x‖ := by
    have h1 := Complex.abs_re_le_norm (inner ℂ ψ x)
    have h2 := norm_inner_le_norm (𝕜 := ℂ) ψ x
    rw [hψ, one_mul] at h2
    exact h1.trans h2
  have := sq_le_sq' (abs_le.mp ht).1 (abs_le.mp ht).2
  linarith

/-- **`ψ*` reaches the maximal tension**: `t(ψ*)² = 1/3`. -/
theorem tension_max : tensionG T P ψs ^ 2 = 1 / 3 := by
  rw [tension k, div_pow, Real.sq_sqrt (by norm_num)]; norm_num

end Axis

end NRSCell16
