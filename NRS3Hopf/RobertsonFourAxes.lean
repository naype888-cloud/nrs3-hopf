/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NRS3Hopf.FourAxes
public import NavaRobertsonIndependent.Mathematics.D9_Monotonicity
public import NavaRobertsonIndependent.Mathematics.D20_GramStepCoherenceConstant
public import NavaRobertsonIndependent.Mathematics.D41_MandelstamTammCramerRao

/-!
# Robertson 1934 on four axes

Robertson's relation `|det Ω| ≤ det Σ` holds for any finite family of observables
(`robertson_det`, `D49`); here the family is the eight observables of the box
`dx × dy × dz × dw`. On product states both matrices are block diagonal (`FourAxes`), so

  `det Σ = Π (s_i + t_i²/4)`,  `|det Ω| = Π t_i²/4`,

with `s_i` the Robertson–Schrödinger surplus and `t_i` the tension of axis `i`. At the maximal
current state of the box every block carries `C_N(d)²`, so

  `det Σ = (C_N(dx) C_N(dy) C_N(dz) C_N(dw))² · |det Ω|`.

The ratio is `1` exactly when every axis has `2` or `3` positions, is strictly above `1` when
every axis has `4` or more, stays strictly below `C_N-inf⁸ = (π²/3 − 2)⁴` and tends to it as the four
axes grow (`D8`, `D9`).

## Main results

- `RobertsonFourAxes.robertson_det_four` : Robertson 1934 for the eight observables, every state.
- `RobertsonFourAxes.det_covMatrix_prod4`, `RobertsonFourAxes.abs_det_imMatrix_prod4` : the two
  determinants on product states.
- `RobertsonFourAxes.robertson_det_prod4_strict` : positive surplus on the four axes makes it
  strict.
- `RobertsonFourAxes.det_covMatrix_maxCurrentState4` : the ratio at the maximal current state.
- `RobertsonFourAxes.det_eq_iff` : equality iff every axis has `2` or `3` positions.
- `RobertsonFourAxes.robertson_det_maxCurrentState4_strict` : strict from `4` on every axis.
- `RobertsonFourAxes.ratio_lt_inf`, `RobertsonFourAxes.tendsto_ratio` : below `C_N-inf⁸`, and the
  limit.
-/

@[expose] public noncomputable section

open Matrix Filter Topology TransportPosition SpectralExtremal NRSInequality NearMaxTension
open PathGraph3DNRS RobertsonDeterminant RobertsonDeterminantProduct Gnomon FourAxes

namespace RobertsonFourAxes

variable {dx dy dz dw : ℕ}

/-- **Robertson 1934 on the box of four axes**, for every state. -/
theorem robertson_det_four (Φ : H4D dx dy dz dw) :
    |(imMatrix (pairs4 dx dy dz dw) Φ).det| ≤ (covMatrix (pairs4 dx dy dz dw) Φ).det :=
  robertson_det _ Φ

section Product

variable {u : Hd dx} {v : Hd dy} {w : Hd dz} {s : Hd dw}
  (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) (hs : ‖s‖ = 1)
include hu hv hw hs

/-- `det Σ = Π (s_i + t_i²/4)` on product states. -/
theorem det_covMatrix_prod4 :
    (covMatrix (pairs4 dx dy dz dw) (prod4 u v w s)).det =
      (surplus dx u + tension dx u ^ 2 / 4) * (surplus dy v + tension dy v ^ 2 / 4) *
        (surplus dz w + tension dz w ^ 2 / 4) * (surplus dw s + tension dw s ^ 2 / 4) := by
  rw [covMatrix_prod4 hu hv hw hs, det_blockDiagonal, Fin.prod_univ_four]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, det_covMatrix_pair]

/-- `|det Ω| = Π t_i²/4` on product states. -/
theorem abs_det_imMatrix_prod4 :
    |(imMatrix (pairs4 dx dy dz dw) (prod4 u v w s)).det| =
      tension dx u ^ 2 / 4 * (tension dy v ^ 2 / 4) * (tension dz w ^ 2 / 4) *
        (tension dw s ^ 2 / 4) := by
  rw [imMatrix_prod4 hu hv hw hs, det_blockDiagonal, Fin.prod_univ_four]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, det_imMatrix_pair]
  exact abs_of_nonneg (by positivity)

/-- **Strict on product states.** A positive surplus on each of the four axes makes the bound
strict. -/
theorem robertson_det_prod4_strict (hsx : 0 < surplus dx u) (hsy : 0 < surplus dy v)
    (hsz : 0 < surplus dz w) (hsw : 0 < surplus dw s) :
    |(imMatrix (pairs4 dx dy dz dw) (prod4 u v w s)).det| <
      (covMatrix (pairs4 dx dy dz dw) (prod4 u v w s)).det := by
  rw [abs_det_imMatrix_prod4 hu hv hw hs, det_covMatrix_prod4 hu hv hw hs]
  have ha := sq_nonneg (tension dx u)
  have hb := sq_nonneg (tension dy v)
  have hc := sq_nonneg (tension dz w)
  have he := sq_nonneg (tension dw s)
  have h1 := mul_lt_mul'' (show tension dx u ^ 2 / 4 < surplus dx u + tension dx u ^ 2 / 4 by
    linarith) (show tension dy v ^ 2 / 4 < surplus dy v + tension dy v ^ 2 / 4 by linarith)
    (by positivity) (by positivity)
  have h2 := mul_lt_mul'' h1 (show tension dz w ^ 2 / 4 < surplus dz w + tension dz w ^ 2 / 4
    by linarith) (by positivity) (by positivity)
  exact mul_lt_mul'' h2 (show tension dw s ^ 2 / 4 < surplus dw s + tension dw s ^ 2 / 4
    by linarith) (by positivity) (by positivity)

end Product

/-! ## The maximal current state of the box -/

variable (dx dy dz dw) in
/-- The maximal current state of the box: the maximal current state on each axis. -/
def maxCurrentState4 : H4D dx dy dz dw :=
  prod4 (maxCurrentState dx) (maxCurrentState dy) (maxCurrentState dz) (maxCurrentState dw)

variable (hx : 2 ≤ dx) (hy : 2 ≤ dy) (hz : 2 ≤ dz) (hw : 2 ≤ dw)
include hx hy hz hw

theorem abs_det_imMatrix_maxCurrentState4_pos :
    0 < |(imMatrix (pairs4 dx dy dz dw) (maxCurrentState4 dx dy dz dw)).det| := by
  rw [maxCurrentState4, abs_det_imMatrix_prod4 (norm_maxCurrentState hx)
    (norm_maxCurrentState hy) (norm_maxCurrentState hz) (norm_maxCurrentState hw),
    tension_maxCurrentState hx, tension_maxCurrentState hy, tension_maxCurrentState hz,
    tension_maxCurrentState hw]
  have h (d : ℕ) (hd : 2 ≤ d) : 0 < (2 / ((d : ℝ) - 1)) ^ 2 / 4 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    have : 0 < (d : ℝ) - 1 := by linarith
    positivity
  have := h dx hx; have := h dy hy; have := h dz hz; have := h dw hw
  positivity

/-- **The ratio at the maximal current state**: `det Σ = (Π C_N(d_i))² · |det Ω|`. -/
theorem det_covMatrix_maxCurrentState4 :
    (covMatrix (pairs4 dx dy dz dw) (maxCurrentState4 dx dy dz dw)).det =
      (CoherenceConstant dx * CoherenceConstant dy * CoherenceConstant dz *
        CoherenceConstant dw) ^ 2 *
        |(imMatrix (pairs4 dx dy dz dw) (maxCurrentState4 dx dy dz dw)).det| := by
  have hu := norm_maxCurrentState hx
  have hv := norm_maxCurrentState hy
  have hw' := norm_maxCurrentState hz
  have hs := norm_maxCurrentState hw
  rw [maxCurrentState4, det_covMatrix_prod4 hu hv hw' hs, abs_det_imMatrix_prod4 hu hv hw' hs,
    block_maxCurrentState hx, block_maxCurrentState hy, block_maxCurrentState hz,
    block_maxCurrentState hw]
  ring

omit hx hy hz hw in
private theorem mul_eq_one_iff_of_one_le {a b : ℝ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    a * b = 1 ↔ a = 1 ∧ b = 1 := by
  refine ⟨fun h => ?_, fun h => by rw [h.1, h.2, one_mul]⟩
  have : a ≤ 1 := by nlinarith
  have : b ≤ 1 := by nlinarith
  exact ⟨by linarith, by linarith⟩

/-- **Saturation on four axes**: Robertson is an equality at the maximal current state exactly
when every axis has `2` or `3` positions. -/
theorem det_eq_iff :
    (covMatrix (pairs4 dx dy dz dw) (maxCurrentState4 dx dy dz dw)).det =
        |(imMatrix (pairs4 dx dy dz dw) (maxCurrentState4 dx dy dz dw)).det| ↔
      (dx = 2 ∨ dx = 3) ∧ (dy = 2 ∨ dy = 3) ∧ (dz = 2 ∨ dz = 3) ∧ (dw = 2 ∨ dw = 3) := by
  have hpos := abs_det_imMatrix_maxCurrentState4_pos hx hy hz hw
  have cx := GroupVelocity.one_le_CoherenceConstant hx
  have cy := GroupVelocity.one_le_CoherenceConstant hy
  have cz := GroupVelocity.one_le_CoherenceConstant hz
  have cw := GroupVelocity.one_le_CoherenceConstant hw
  rw [det_covMatrix_maxCurrentState4 hx hy hz hw, ← CoherenceConstant_eq_one_iff dx hx,
    ← CoherenceConstant_eq_one_iff dy hy, ← CoherenceConstant_eq_one_iff dz hz,
    ← CoherenceConstant_eq_one_iff dw hw]
  have hxy : 1 ≤ CoherenceConstant dx * CoherenceConstant dy := by nlinarith
  have hxyz : 1 ≤ CoherenceConstant dx * CoherenceConstant dy * CoherenceConstant dz := by
    nlinarith
  rw [show ∀ r : ℝ, r * |(imMatrix (pairs4 dx dy dz dw) (maxCurrentState4 dx dy dz dw)).det| =
      |(imMatrix (pairs4 dx dy dz dw) (maxCurrentState4 dx dy dz dw)).det| ↔ r = 1 from
      fun r => by rw [mul_eq_right₀ hpos.ne'], pow_eq_one_iff_of_nonneg (by positivity) two_ne_zero,
    mul_eq_one_iff_of_one_le hxyz cw, mul_eq_one_iff_of_one_le hxy cz,
    mul_eq_one_iff_of_one_le cx cy]
  tauto

omit hx hy hz hw in
/-- **Strict from `4` positions on every axis.** -/
theorem robertson_det_maxCurrentState4_strict (hx : 4 ≤ dx) (hy : 4 ≤ dy) (hz : 4 ≤ dz)
    (hw : 4 ≤ dw) :
    |(imMatrix (pairs4 dx dy dz dw) (maxCurrentState4 dx dy dz dw)).det| <
      (covMatrix (pairs4 dx dy dz dw) (maxCurrentState4 dx dy dz dw)).det := by
  refine lt_of_le_of_ne (robertson_det_four _) fun h => ?_
  have := (det_eq_iff (by omega) (by omega) (by omega) (by omega)).mp h.symm
  omega

omit hx hy hz hw in
/-- `C_N-inf⁸ = (π²/3 − 2)⁴`. -/
theorem CoherenceConstantInf_pow_eight : CoherenceConstantInf ^ 8 = (Real.pi ^ 2 / 3 - 2) ^ 4 := by
  rw [show (8 : ℕ) = 2 * 4 from rfl, pow_mul, CoherenceConstantInf,
    Real.sq_sqrt (by nlinarith [Real.pi_gt_three])]

omit hx hy hz hw in
/-- **No box reaches the limit**: from `4` positions on every axis the ratio stays below
`C_N-inf⁸`. -/
theorem ratio_lt_inf (hx : 4 ≤ dx) (hy : 4 ≤ dy) (hz : 4 ≤ dz) (hw : 4 ≤ dw) :
    (CoherenceConstant dx * CoherenceConstant dy * CoherenceConstant dz *
      CoherenceConstant dw) ^ 2 < CoherenceConstantInf ^ 8 := by
  have c0 (d : ℕ) (hd : 4 ≤ d) : 0 ≤ CoherenceConstant d :=
    zero_le_one.trans (GroupVelocity.one_le_CoherenceConstant (by omega))
  have ax := c0 dx hx
  have ay := c0 dy hy
  have az := c0 dz hz
  have aw := c0 dw hw
  have h1 := mul_lt_mul'' (CoherenceConstant_lt_CoherenceConstantInf dx hx)
    (CoherenceConstant_lt_CoherenceConstantInf dy hy) ax ay
  have h2 := mul_lt_mul'' h1 (CoherenceConstant_lt_CoherenceConstantInf dz hz)
    (by positivity) az
  have h3 := mul_lt_mul'' h2 (CoherenceConstant_lt_CoherenceConstantInf dw hw)
    (by positivity) aw
  calc _ < (CoherenceConstantInf * CoherenceConstantInf * CoherenceConstantInf *
        CoherenceConstantInf) ^ 2 := pow_lt_pow_left₀ h3 (by positivity) two_ne_zero
    _ = CoherenceConstantInf ^ 8 := by ring

omit hx hy hz hw in
/-- **The limit**: as the four axes grow, independently, the ratio tends to `C_N-inf⁸`. -/
theorem tendsto_ratio :
    Tendsto (fun p : ℕ × ℕ × ℕ × ℕ => (CoherenceConstant p.1 * CoherenceConstant p.2.1 *
        CoherenceConstant p.2.2.1 * CoherenceConstant p.2.2.2) ^ 2)
      (atTop ×ˢ (atTop ×ˢ (atTop ×ˢ atTop))) (𝓝 (CoherenceConstantInf ^ 8)) := by
  let F : Filter (ℕ × ℕ × ℕ × ℕ) := atTop ×ˢ (atTop ×ˢ (atTop ×ˢ atTop))
  have h := tendsto_CoherenceConstant
  have t1 : Tendsto (fun p : ℕ × ℕ × ℕ × ℕ => CoherenceConstant p.1) F
      (𝓝 CoherenceConstantInf) := h.comp tendsto_fst
  have t2 : Tendsto (fun p : ℕ × ℕ × ℕ × ℕ => CoherenceConstant p.2.1) F
      (𝓝 CoherenceConstantInf) := h.comp (tendsto_fst.comp tendsto_snd)
  have t3 : Tendsto (fun p : ℕ × ℕ × ℕ × ℕ => CoherenceConstant p.2.2.1) F
      (𝓝 CoherenceConstantInf) := h.comp (tendsto_fst.comp (tendsto_snd.comp tendsto_snd))
  have t4 : Tendsto (fun p : ℕ × ℕ × ℕ × ℕ => CoherenceConstant p.2.2.2) F
      (𝓝 CoherenceConstantInf) := h.comp (tendsto_snd.comp (tendsto_snd.comp tendsto_snd))
  convert (((t1.mul t2).mul t3).mul t4).pow 2 using 2
  ring

end RobertsonFourAxes
