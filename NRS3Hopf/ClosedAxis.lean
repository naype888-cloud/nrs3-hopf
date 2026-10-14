/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NavaRobertsonIndependent.Mathematics.D38_GroupVelocity
public import NavaRobertsonIndependent.Mathematics.D47_PlatformBlindness

/-!
# The closed axis: its `c` tends to `1`

Close the axis of `d = n + 3` positions with the link `{0, d − 1}` (`D16e`). The transport is
`(A_d + S)/2`, with `A_d = ρ_d T_d` the open adjacency and `S` the seam, the link from the last
position back to the first. The position stays `P_d`, from `−1` to `1`, so the seam jumps the
whole range while every open link moves `2/(d − 1)`.

The tension splits as `(ρ_d/2) ⟨K_d⟩ − 2 Im(ψ̄₀ ψ_{d−1})`: the open part is at most
`2/(d − 1)` (`D38`), the seam part at most `1`. A state on the two seam positions reaches `1`
exactly. So the `c` of the closed axis, its maximal tension, lies in `[1, 1 + 2/(d − 1)]` and
tends to `1`: as the axis grows the current concentrates on the seam. Every system fixes its
own `c`; this is the `c` of the closed axis.

## Main results

- `ClosedAxis.tension_eq` : the tension is the open tension times `ρ_d/2` plus the seam.
- `ClosedAxis.abs_tension_le` : `|⟨K⟩| ≤ 1 + 2/(d − 1)` for unit states.
- `ClosedAxis.tension_seamState` : the seam state has `⟨K⟩ = 1`.
- `ClosedAxis.one_le_cMax`, `ClosedAxis.cMax_le` : `1 ≤ c ≤ 1 + 2/(d − 1)`.
- `ClosedAxis.tendsto_cMax` : `c → 1`.
-/

@[expose] public noncomputable section

open Complex Filter Topology NRSInequality TransportPosition SpectralExtremal
open EigenvectorSaturation PlatformBlindness

namespace ClosedAxis

variable (n : ℕ)

/-- The last position `d − 1` of the closed axis with `d = n + 3`. -/
abbrev last : Fin (n + 3) := Fin.last (n + 2)

/-- The seam: the link between the last position and the first. -/
def seamOp : Hd (n + 3) →ₗ[ℂ] Hd (n + 3) :=
  (EuclideanSpace.proj (last n) : Hd (n + 3) →L[ℂ] ℂ).toLinearMap.smulRight
      (EuclideanSpace.single 0 1) +
    (EuclideanSpace.proj 0 : Hd (n + 3) →L[ℂ] ℂ).toLinearMap.smulRight
      (EuclideanSpace.single (last n) 1)

/-- The closed transport `(A_d + S)/2`, with `A_d = ρ_d T_d`. -/
def transport : Hd (n + 3) →ₗ[ℂ] Hd (n + 3) :=
  ((rho (n + 3) / 2 : ℝ) : ℂ) • TdOp (n + 3) + (1 / 2 : ℂ) • seamOp n

/-- The tension `⟨i[T°, P_d]⟩ = −2 Im ⟪T°ψ, P_dψ⟫` of the closed axis. -/
def tension (ψ : Hd (n + 3)) : ℝ := -2 * (inner ℂ (transport n ψ) (PdOp (n + 3) ψ)).im

theorem posCoord_zero : posCoord (n + 3) 0 = -1 := by
  have : ((n : ℝ) + 3) - 1 ≠ 0 := by have : (0 : ℝ) ≤ n := n.cast_nonneg; linarith
  simp [posCoord]
  field_simp
  ring

theorem posCoord_last : posCoord (n + 3) (last n) = 1 := by
  have : ((n : ℝ) + 3) - 1 ≠ 0 := by have : (0 : ℝ) ≤ n := n.cast_nonneg; linarith
  simp [posCoord]
  field_simp
  ring

variable {n}

/-- **The tension splits**: `(ρ_d/2) ⟨K_d⟩ − 2 Im(ψ̄₀ ψ_{d−1})`. -/
theorem tension_eq (ψ : Hd (n + 3)) :
    tension n ψ = rho (n + 3) / 2 * NearMaxTension.tension (n + 3) ψ -
      2 * ((starRingEnd ℂ) (ψ 0) * ψ (last n)).im := by
  rw [NearMaxTension.tension, re_inner_KdOp, tension, transport]
  simp only [LinearMap.add_apply, LinearMap.smul_apply, inner_add_left, inner_smul_left,
    seamOp, LinearMap.smulRight_apply, ContinuousLinearMap.coe_coe, PiLp.proj_apply,
    EuclideanSpace.inner_single_left, PdOp_apply_coord, posCoord_zero, posCoord_last]
  simp only [Complex.conj_ofReal, map_div₀, map_one, Complex.conj_ofNat, one_mul,
    Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.div_re,
    Complex.div_im, Complex.one_re, Complex.one_im, Complex.conj_re, Complex.conj_im,
    Complex.neg_re, Complex.neg_im, Complex.ofReal_neg, Complex.ofReal_one, Complex.mul_re]
  norm_num
  ring

theorem two_coords_le (ψ : Hd (n + 3)) : ‖ψ 0‖ ^ 2 + ‖ψ (last n)‖ ^ 2 ≤ ‖ψ‖ ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
  have h0 : (0 : Fin (n + 3)) ≠ last n := by
    simp [Fin.ext_iff]
  rw [← Finset.sum_pair (f := fun i => ‖ψ i‖ ^ 2) h0]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    fun _ _ _ => by positivity

/-- **The seam carries at most `1`**: `|2 Im(ψ̄₀ ψ_{d−1})| ≤ ‖ψ‖²`. -/
theorem abs_seam_le (ψ : Hd (n + 3)) :
    |2 * ((starRingEnd ℂ) (ψ 0) * ψ (last n)).im| ≤ ‖ψ‖ ^ 2 := by
  have h1 := Complex.abs_im_le_norm ((starRingEnd ℂ) (ψ 0) * ψ (last n))
  rw [norm_mul, Complex.norm_conj] at h1
  have h2 := two_coords_le ψ
  rw [abs_mul, abs_two]
  nlinarith [sq_nonneg (‖ψ 0‖ - ‖ψ (last n)‖)]

theorem rho_le_two : rho (n + 3) ≤ 2 := by
  have := Real.cos_le_one (Real.pi / ((((n + 3 : ℕ) : ℝ)) + 1))
  rw [rho]
  linarith

/-- **Bound on the tension**: `|⟨K⟩| ≤ 1 + 2/(d − 1)` for unit states. -/
theorem abs_tension_le (ψ : Hd (n + 3)) (hψ : ‖ψ‖ = 1) :
    |tension n ψ| ≤ 1 + 2 / ((n : ℝ) + 2) := by
  have hρ0 := (rho_pos (n + 3) (by omega)).le
  have hρ2 := rho_le_two (n := n)
  have ho := GroupVelocity.abs_tension_le (d := n + 3) (by omega) ψ hψ
  have hs := abs_seam_le ψ
  rw [hψ, one_pow] at hs
  have hd : ((n + 3 : ℕ) : ℝ) - 1 = (n : ℝ) + 2 := by push_cast; ring
  rw [hd] at ho
  have hq : 0 ≤ 2 / ((n : ℝ) + 2) := by positivity
  rw [tension_eq]
  calc |rho (n + 3) / 2 * NearMaxTension.tension (n + 3) ψ -
        2 * ((starRingEnd ℂ) (ψ 0) * ψ (last n)).im|
      ≤ |rho (n + 3) / 2 * NearMaxTension.tension (n + 3) ψ| +
          |2 * ((starRingEnd ℂ) (ψ 0) * ψ (last n)).im| := abs_sub _ _
    _ ≤ 1 * (2 / ((n : ℝ) + 2)) + 1 := by
        rw [abs_mul, abs_of_nonneg (by positivity)]
        gcongr
        linarith
    _ = 1 + 2 / ((n : ℝ) + 2) := by ring

/-! ## The seam state -/

variable (n) in
/-- The seam state `(e₀ − i e_{d−1})/√2`. -/
def seamState : Hd (n + 3) :=
  ((1 / √2 : ℝ) : ℂ) • (EuclideanSpace.single 0 1 - I • EuclideanSpace.single (last n) 1)

theorem seamState_apply (j : Fin (n + 3)) :
    seamState n j = ((1 / √2 : ℝ) : ℂ) *
      ((if j = 0 then 1 else 0) - I * (if j = last n then 1 else 0)) := by
  simp [seamState]

theorem norm_seamState : ‖seamState n‖ = 1 := by
  have h0 : (0 : Fin (n + 3)) ≠ last n := by simp [Fin.ext_iff]
  have h2 : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h : ‖seamState n‖ ^ 2 = 1 := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity), ← Finset.add_sum_erase _ _
      (Finset.mem_univ 0), ← Finset.add_sum_erase _ _ (Finset.mem_erase.mpr
        ⟨h0.symm, Finset.mem_univ (last n)⟩)]
    rw [Finset.sum_eq_zero fun j hj => ?_]
    · simp [seamState_apply, h0, h0.symm]
      field_simp
      norm_num
    · obtain ⟨hjl, hj0⟩ := Finset.mem_erase.mp hj
      obtain ⟨hj0, -⟩ := Finset.mem_erase.mp hj0
      simp [seamState_apply, hj0, hjl]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp h

/-- The open transport does not link the two seam positions. -/
theorem Td_seam (i j : Fin (n + 3)) (hi : i = 0 ∨ i = last n) (hj : j = 0 ∨ j = last n) :
    Td (n + 3) i j = 0 := by
  have : ¬ MinStep i j := by
    rcases hi with rfl | rfl <;> rcases hj with rfl | rfl <;>
      simp [MinStep]
  simp [Td, Ad, this]

/-- The open part of the tension vanishes on the seam state. -/
theorem openTension_seamState : NearMaxTension.tension (n + 3) (seamState n) = 0 := by
  rw [NearMaxTension.tension, re_inner_KdOp]
  suffices h : inner ℂ (TdOp (n + 3) (seamState n)) (PdOp (n + 3) (seamState n)) = 0 by
    rw [h]; simp
  rw [PiLp.inner_apply]
  refine Finset.sum_eq_zero fun j _ => ?_
  by_cases hj : j = 0 ∨ j = last n
  · suffices h : TdOp (n + 3) (seamState n) j = 0 by simp [h]
    rw [TdOp_apply_coord]
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hk : k = 0 ∨ k = last n
    · rw [Td_seam j k hj hk, zero_mul]
    · simp only [not_or] at hk
      simp [seamState_apply, hk.1, hk.2]
  · simp only [not_or] at hj
    simp [PdOp_apply_coord, seamState_apply, hj.1, hj.2]

/-- **The seam state reaches tension `1`.** -/
theorem tension_seamState : tension n (seamState n) = 1 := by
  have h0 : (0 : Fin (n + 3)) ≠ last n := by simp [Fin.ext_iff]
  have h2 : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  rw [tension_eq, openTension_seamState, mul_zero, zero_sub, seamState_apply, seamState_apply]
  simp [h0, h0.symm, Complex.mul_im, Complex.mul_re]
  field_simp
  linarith

/-! ## The `c` of the closed axis -/

variable (n) in
/-- The `c` of the closed axis: the largest tension of a unit state. -/
def cMax : ℝ := sSup ((fun ψ => |tension n ψ|) '' {ψ : Hd (n + 3) | ‖ψ‖ = 1})

theorem bddAbove_tensions :
    BddAbove ((fun ψ => |tension n ψ|) '' {ψ : Hd (n + 3) | ‖ψ‖ = 1}) :=
  ⟨1 + 2 / ((n : ℝ) + 2), by rintro _ ⟨ψ, hψ, rfl⟩; exact abs_tension_le ψ hψ⟩

/-- **`c ≥ 1`**, reached on the seam. -/
theorem one_le_cMax : 1 ≤ cMax n :=
  le_csSup_of_le bddAbove_tensions ⟨seamState n, norm_seamState, rfl⟩
    (by show 1 ≤ |tension n (seamState n)|; rw [tension_seamState, abs_one])

/-- **`c ≤ 1 + 2/(d − 1)`.** -/
theorem cMax_le : cMax n ≤ 1 + 2 / ((n : ℝ) + 2) :=
  csSup_le ⟨_, seamState n, norm_seamState, rfl⟩ fun _ ⟨ψ, hψ, h⟩ => h ▸ abs_tension_le ψ hψ

/-- **The `c` of the closed axis tends to `1`**: the current concentrates on the seam. -/
theorem tendsto_cMax : Tendsto cMax atTop (𝓝 1) := by
  have hup : Tendsto (fun n : ℕ => 1 + 2 / ((n : ℝ) + 2)) atTop (𝓝 1) := by
    have : Tendsto (fun n : ℕ => 2 / ((n : ℝ) + 2)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop
        (tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop)
    simpa using this.const_add 1
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup
    (fun _ => one_le_cMax) (fun _ => cMax_le)

end ClosedAxis
