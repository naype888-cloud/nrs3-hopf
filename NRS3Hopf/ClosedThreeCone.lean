/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NRS3Hopf.ClosedThreeBand
public import NRS3UncertaintyCone.TimeDilation

/-!
# Proper time on the closed axis with three positions

The fluctuation vectors of `(T°, P₃)` form an uncertainty four-vector (`UncertaintyCone`): it
lies in the closed future cone, so its proper time `τ = √η(v, v)` is never negative, and
`η(v, v)` is the Robertson–Schrödinger surplus. On the open axis with three positions the
maximal current state is null, `τ = 0` (`null_maxCurrentState_iff`). On the closed axis every
unit state in the band `(√(2/3), 1]` is strictly timelike, the maximal current state included:
closing the axis gives proper time from three positions on.

## Main results

- `ClosedThree.interval_eq_gramDefectAt` : the interval is the Robertson–Schrödinger surplus.
- `ClosedThree.properTime_pos_of_speed` : in the band, `τ > 0` for every unit state.
- `ClosedThree.properTime_maxState_pos` : `τ > 0` at the maximal current state of the closed
  axis.
- `ClosedThree.properTime_open_three` : on the open axis with three positions, `τ = 0` at the
  maximal current state.
-/

@[expose] public noncomputable section

open NRSInequality TransportPosition SpectralExtremal EigenvectorSaturation UncertaintyCone

namespace ClosedThree

/-- The interval of the uncertainty four-vector is the Robertson–Schrödinger surplus. -/
theorem interval_eq_gramDefectAt (ψ : Hd 3) :
    interval (coneVector (centered TcOp ψ) (centered (PdOp 3) ψ)) =
      gramDefectAt TcOp (PdOp 3) ψ := by
  rw [interval_eq_gramDefectC]
  rfl

/-- **Proper time in the band**: a unit state moving faster than `√(2/3)` of the `c` of the
closed axis has positive proper time. -/
theorem properTime_pos_of_speed {ψ : Hd 3} (hψ : ‖ψ‖ = 1)
    (hv : √(2 / 3) < |tension ψ| / (√6 / 2)) :
    0 < properTime (coneVector (centered TcOp ψ) (centered (PdOp 3) ψ)) := by
  rw [properTime, Real.sqrt_pos, interval_eq_gramDefectAt]
  exact surplus_pos_of_speed hψ hv

/-- **The maximal current state of the closed axis has positive proper time.** -/
theorem properTime_maxState_pos :
    0 < properTime (coneVector (centered TcOp maxState) (centered (PdOp 3) maxState)) := by
  refine properTime_pos_of_speed norm_maxState ?_
  rw [tension_maxState, abs_of_pos (by positivity), div_self (by positivity)]
  exact threshold_lt_one

/-- **On the open axis with three positions the maximal current state is null**: `τ = 0`. -/
theorem properTime_open_three :
    properTime (coneVector (centered (TdOp 3) (maxCurrentState 3))
      (centered (PdOp 3) (maxCurrentState 3))) = 0 := by
  rw [properTime, (null_maxCurrentState_iff (by norm_num)).mpr (Or.inr rfl), Real.sqrt_zero]

end ClosedThree
