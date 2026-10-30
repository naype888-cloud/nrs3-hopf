/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NRS3Hopf.RobertsonFourAxes

/-!
# The excess of Robertson is a time with a floor and a ceiling

At the maximal current state (the `c` of the system) the box saturates the algebra's bound only
when every axis has `2` or `3` positions. From `4` positions on every axis the ratio
`det Σ / |det Ω| = (C_{d_x} C_{d_y} C_{d_z} C_{d_w})²` exceeds `1`. That excess is the defect
`δ = ratio − 1`: it has no physical measure, it is algebraic (with `c = 1` in the lab it is a
number). Crossing it at speed `c` takes the proper time `τ = δ · a / c`, one step being `a / c`.

The defect is monotone in the sizes (`D9`) and bounded by the Szegő limit (`D8`), so it lies in
a band that does not depend on the box:

  `C_4⁸ − 1 ≤ δ < C_∞⁸ − 1`,   with `0 < C_4⁸ − 1`.

## Main results

- `ProperTimeBand.defect_pos` : the defect is positive from `4` positions on every axis.
- `ProperTimeBand.defect_ge` : `C_4⁸ − 1 ≤ δ`, for every box of sides `≥ 4`.
- `ProperTimeBand.defect_lt` : `δ < C_∞⁸ − 1`, no box reaches the limit.
- `ProperTimeBand.properTime_band` : the proper time `δ a / c` lies in
  `[(C_4⁸ − 1) a / c, (C_∞⁸ − 1) a / c)`.
-/

@[expose] public noncomputable section

namespace ProperTimeBand

open Gnomon RobertsonFourAxes

variable {dx dy dz dw : ℕ}

/-- The defect of the box at the maximal current state: the excess of Robertson's ratio. -/
def defect (dx dy dz dw : ℕ) : ℝ :=
  (CoherenceConstant dx * CoherenceConstant dy * CoherenceConstant dz *
    CoherenceConstant dw) ^ 2 - 1

/-- **The defect is bounded below by that of the smallest box with a positive defect**. -/
theorem defect_ge (hx : 4 ≤ dx) (hy : 4 ≤ dy) (hz : 4 ≤ dz) (hw : 4 ≤ dw) :
    CoherenceConstant 4 ^ 8 - 1 ≤ defect dx dy dz dw := by
  have c4 : 1 ≤ CoherenceConstant 4 := (one_lt_CoherenceConstant_of_four_le 4 le_rfl).le
  have h : CoherenceConstant 4 ^ 4 ≤ CoherenceConstant dx * CoherenceConstant dy *
      CoherenceConstant dz * CoherenceConstant dw := by
    have a := CoherenceConstant_four_le dx hx
    have b := CoherenceConstant_four_le dy hy
    have c := CoherenceConstant_four_le dz hz
    have d := CoherenceConstant_four_le dw hw
    have p0 : 0 ≤ CoherenceConstant 4 := by linarith
    have px : 0 ≤ CoherenceConstant dx := by linarith
    have py : 0 ≤ CoherenceConstant dy := by linarith
    have pz : 0 ≤ CoherenceConstant dz := by linarith
    have pw : 0 ≤ CoherenceConstant dw := by linarith
    have pxy : 0 ≤ CoherenceConstant dx * CoherenceConstant dy := mul_nonneg px py
    have pxyz : 0 ≤ CoherenceConstant dx * CoherenceConstant dy * CoherenceConstant dz :=
      mul_nonneg pxy pz
    calc CoherenceConstant 4 ^ 4 = CoherenceConstant 4 * CoherenceConstant 4 *
          CoherenceConstant 4 * CoherenceConstant 4 := by ring
      _ ≤ _ := mul_le_mul (mul_le_mul (mul_le_mul a b p0 px) c p0 pxy) d p0 pxyz
  unfold defect
  have := pow_le_pow_left₀ (by positivity) h 2
  nlinarith [this, show CoherenceConstant 4 ^ 8 = (CoherenceConstant 4 ^ 4) ^ 2 by ring]

/-- **The defect is positive** from `4` positions on every axis. -/
theorem defect_pos (hx : 4 ≤ dx) (hy : 4 ≤ dy) (hz : 4 ≤ dz) (hw : 4 ≤ dw) :
    0 < defect dx dy dz dw := by
  have c4 := one_lt_CoherenceConstant_of_four_le 4 le_rfl
  have : 1 < CoherenceConstant 4 ^ 8 := one_lt_pow₀ c4 (by norm_num)
  linarith [defect_ge hx hy hz hw]

/-- **No box reaches the Szegő limit**: the defect stays below `C_∞⁸ − 1`. -/
theorem defect_lt (hx : 4 ≤ dx) (hy : 4 ≤ dy) (hz : 4 ≤ dz) (hw : 4 ≤ dw) :
    defect dx dy dz dw < CoherenceConstantInf ^ 8 - 1 := by
  unfold defect
  linarith [ratio_lt_inf hx hy hz hw]

/-- **The proper time lies in a band that does not depend on the box**: with one step taking
`a / c`, crossing the defect takes `δ a / c ∈ [(C_4⁸ − 1) a / c, (C_∞⁸ − 1) a / c)`, and in
particular it is positive. -/
theorem properTime_band {a c : ℝ} (ha : 0 < a) (hc : 0 < c) (hx : 4 ≤ dx) (hy : 4 ≤ dy)
    (hz : 4 ≤ dz) (hw : 4 ≤ dw) :
    (CoherenceConstant 4 ^ 8 - 1) * (a / c) ≤ defect dx dy dz dw * (a / c) ∧
      defect dx dy dz dw * (a / c) < (CoherenceConstantInf ^ 8 - 1) * (a / c) ∧
      0 < defect dx dy dz dw * (a / c) := by
  have hac : 0 < a / c := div_pos ha hc
  exact ⟨mul_le_mul_of_nonneg_right (defect_ge hx hy hz hw) hac.le,
    mul_lt_mul_of_pos_right (defect_lt hx hy hz hw) hac, mul_pos (defect_pos hx hy hz hw) hac⟩

end ProperTimeBand
