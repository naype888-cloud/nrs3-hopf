/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NRS3Hopf.ClosedThree

/-!
# The band of the closed axis with three positions

On the closed axis of `ClosedThree` the tension of a unit state reaches at most `√6/2`, the `c`
of the closed axis: `⟨K⟩ = m · (x × y)` for `ψ = x + iy` and `m = (−1, 2, −1)`, so
`⟨K⟩² ≤ 6 |x × y|² ≤ (3/2) ‖ψ‖⁴`. A minimum-uncertainty unit state reaches tension `1`
exactly, at `ψ = (1 + i, 2, 1 − i)/(2√2)`, with `centered T° = i • centered P₃`.

In speeds `v = ⟨K⟩/(√6/2)`, the threshold of the closed axis is `v* = √(2/3)`, and the band
`(√(2/3), 1]` is not empty, while on the open axis `d = 3` has no band (`D44`).

## Main results

- `ClosedThree.abs_tension_le_max`, `ClosedThree.tension_maxState` : `|⟨K⟩| ≤ √6/2`, attained.
- `ClosedThree.saturated_satState`, `ClosedThree.tension_satState` : a minimum-uncertainty unit
  state with tension `1`.
- `ClosedThree.isGreatest_satTension` : `1` is the largest tension of a minimum-uncertainty
  unit state.
- `ClosedThree.threshold_eq`, `ClosedThree.threshold_lt_one` : the threshold speed is
  `1/(√6/2) = √(2/3) < 1`.
- `ClosedThree.surplus_pos_of_speed` : above `√(2/3)` every unit state has a positive surplus.
-/

@[expose] public noncomputable section

open Complex NRSInequality TransportPosition SpectralExtremal EigenvectorSaturation

namespace ClosedThree

/-! ## 1. The `c` of the closed axis -/

/-- **The cone of the closed axis**: `|⟨K⟩| ≤ (√6/2) ‖ψ‖²`. -/
theorem abs_tension_le_max (ψ : Hd 3) : |tension ψ| ≤ √6 / 2 * ‖ψ‖ ^ 2 := by
  rw [tension_eq, normSq_eq]
  simp only [Complex.normSq_apply]
  set x0 := (ψ 0).re
  set x1 := (ψ 1).re
  set x2 := (ψ 2).re
  set y0 := (ψ 0).im
  set y1 := (ψ 1).im
  set y2 := (ψ 2).im
  set w0 := x1 * y2 - x2 * y1
  set w1 := x2 * y0 - x0 * y2
  set w2 := x0 * y1 - x1 * y0
  have hK : -(x0 * y1) - 2 * (x0 * y2) + x1 * y0 - x1 * y2 + 2 * (x2 * y0) + x2 * y1 =
      -w0 + 2 * w1 - w2 := by ring
  set X := x0 ^ 2 + x1 ^ 2 + x2 ^ 2
  set Y := y0 ^ 2 + y1 ^ 2 + y2 ^ 2
  have hN : x0 * x0 + y0 * y0 + (x1 * x1 + y1 * y1) + (x2 * x2 + y2 * y2) = X + Y := by ring
  have hw : w0 ^ 2 + w1 ^ 2 + w2 ^ 2 ≤ X * Y := by
    nlinarith [sq_nonneg (x0 * y0 + x1 * y1 + x2 * y2)]
  have hcs : (-w0 + 2 * w1 - w2) ^ 2 ≤ 6 * (w0 ^ 2 + w1 ^ 2 + w2 ^ 2) := by
    nlinarith [sq_nonneg (2 * w0 + w1), sq_nonneg (w0 - w2), sq_nonneg (w1 + 2 * w2)]
  have hXY : 4 * (X * Y) ≤ (X + Y) ^ 2 := by nlinarith [sq_nonneg (X - Y)]
  have h6 : √6 ^ 2 = 6 := Real.sq_sqrt (by norm_num)
  rw [hK, hN]
  have hpos : 0 ≤ √6 / 2 * (X + Y) := by positivity
  rw [← abs_of_nonneg hpos]
  apply sq_le_sq.mp
  rw [mul_pow, div_pow, h6]
  nlinarith

/-- The maximal current state of the closed axis, `(x − iy)/…` with `x = (1, 0, −1)/2` and
`y = (1, 1, 1)/√6`. -/
def maxState : Hd 3 :=
  WithLp.toLp 2 ![1 / 2 - I / √6, -I / √6, -1 / 2 - I / √6]

theorem norm_maxState : ‖maxState‖ = 1 := by
  have h6 : √6 ^ 2 = 6 := Real.sq_sqrt (by norm_num)
  have h6' : (√6 : ℝ) ≠ 0 := by positivity
  have h : ‖maxState‖ ^ 2 = 1 := by
    rw [normSq_eq]
    simp [maxState, Complex.div_re, Complex.div_im, Complex.normSq_apply]
    field_simp
    nlinarith [h6]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp h

/-- **The maximal current of the closed axis is `√6/2`.** -/
theorem tension_maxState : tension maxState = √6 / 2 := by
  have h6 : √6 ^ 2 = 6 := Real.sq_sqrt (by norm_num)
  have h6' : (√6 : ℝ) ≠ 0 := by positivity
  rw [tension_eq]
  simp [maxState, Complex.div_re, Complex.div_im, Complex.normSq_apply]
  field_simp
  nlinarith [h6]

/-! ## 2. A minimum-uncertainty state at tension `1` -/

/-- The minimum-uncertainty state `(1 + i, 2, 1 − i)/(2√2)`. -/
def satState : Hd 3 :=
  WithLp.toLp 2 ![(√2 / 4 : ℝ) * (1 + I), (√2 / 4 : ℝ) * 2, (√2 / 4 : ℝ) * (1 - I)]

theorem tension_satState : tension satState = 1 := by
  have h2 : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  rw [tension_eq]
  simp [satState]
  nlinarith [h2]

theorem norm_satState : ‖satState‖ = 1 := by
  have h2 : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h : ‖satState‖ ^ 2 = 1 := by
    rw [normSq_eq]
    simp [satState, Complex.normSq_apply]
    nlinarith [h2]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp h

theorem mean_TcOp_satState : mean TcOp satState = 1 / 2 := by
  have h2 : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  obtain ⟨t0, t1, t2⟩ := TcOp_apply satState
  rw [mean, inner_eq, t0, t1, t2]
  simp [satState, Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im]
  nlinarith [h2]

theorem mean_PdOp_satState : mean (PdOp 3) satState = 0 := by
  obtain ⟨p0, p1, p2⟩ := PdOp_apply satState
  rw [mean, inner_eq, p0, p1, p2]
  simp [satState, Complex.mul_re, Complex.mul_im]
  ring

/-- `centered T° = i • centered P₃` at `satState`. -/
theorem centered_satState :
    centered TcOp satState = I • centered (PdOp 3) satState := by
  obtain ⟨t0, t1, t2⟩ := TcOp_apply satState
  obtain ⟨p0, p1, p2⟩ := PdOp_apply satState
  ext j
  simp only [centered, mean_TcOp_satState, mean_PdOp_satState, PiLp.sub_apply,
    PiLp.smul_apply, smul_eq_mul]
  fin_cases j
  · simp only [Fin.zero_eta, t0, p0]
    simp [satState]
    ring_nf
    rw [I_sq]
    ring
  · simp only [Fin.mk_one, t1, p1]
    simp [satState]
    ring
  · simp only [Fin.reduceFinMk, t2, p2]
    simp [satState]
    ring_nf
    rw [I_sq]
    ring

/-- **`satState` is a minimum-uncertainty state.** -/
theorem saturated_satState : gramDefectAt TcOp (PdOp 3) satState = 0 :=
  gramDefectAt_eq_zero_of_parallel _ _ _ I centered_satState

/-! ## 3. The threshold and the band -/

/-- The tensions `|⟨K⟩|` of the minimum-uncertainty unit states of the closed axis. -/
def satTensions : Set ℝ :=
  {s | ∃ ψ : Hd 3, ‖ψ‖ = 1 ∧ gramDefectAt TcOp (PdOp 3) ψ = 0 ∧ |tension ψ| = s}

/-- **`1` is the largest tension of a minimum-uncertainty unit state.** -/
theorem isGreatest_satTension : IsGreatest satTensions 1 := by
  refine ⟨⟨satState, norm_satState, saturated_satState, by rw [tension_satState, abs_one]⟩, ?_⟩
  rintro s ⟨ψ, hψ, hs, rfl⟩
  have := abs_tension_le_of_saturated hs
  rwa [hψ, one_pow] at this

/-- **The threshold speed of the closed axis**: `1/(√6/2) = √(2/3)`. -/
theorem threshold_eq : 1 / (√6 / 2) = √(2 / 3) := by
  rw [Real.sqrt_div' _ (by norm_num : (0 : ℝ) ≤ 3), one_div_div]
  rw [show (6 : ℝ) = 2 * 3 by norm_num, Real.sqrt_mul (by norm_num)]
  have h2 : (0 : ℝ) < √2 := by positivity
  have h3 : (0 : ℝ) < √3 := by positivity
  field_simp
  rw [Real.sq_sqrt (by norm_num)]

/-- **The band of the closed axis is not empty**: `√(2/3) < 1`, so the speeds in `(√(2/3), 1]`
force a Robertson–Schrödinger surplus (`surplus_pos_of_one_lt`). -/
theorem threshold_lt_one : √(2 / 3) < 1 := by
  rw [Real.sqrt_lt' one_pos]
  norm_num

/-- **The band in speeds**: a unit state of the closed axis moving faster than `√(2/3)` of its
`c` has a positive Robertson–Schrödinger surplus. -/
theorem surplus_pos_of_speed {ψ : Hd 3} (hψ : ‖ψ‖ = 1)
    (hv : √(2 / 3) < |tension ψ| / (√6 / 2)) : 0 < gramDefectAt TcOp (PdOp 3) ψ := by
  refine surplus_pos_of_one_lt hψ ?_
  rw [← threshold_eq, div_lt_div_iff_of_pos_right (by positivity)] at hv
  exact hv

end ClosedThree
