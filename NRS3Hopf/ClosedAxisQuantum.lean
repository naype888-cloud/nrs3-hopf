/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NRS3Hopf.ClosedAxis

/-!
# The quantum of the closed axis survives at its `c`: the ratio is `√2`

On the closed axis with `d = n + 3` positions, the seam state `(e₀ − i e_{d−1})/√2` has, for
every `d`,

  `Var T° = 1/2`, `Var P_d = 1`, `cov = 0`, `⟨K⟩ = 1`,

so its Robertson–Schrödinger surplus is `1/4` and the ratio
`Var T° · Var P_d / (⟨K⟩/2)² = 2`: the uncertainty ratio is `√2`, never `1`. Its speed is
`1/c`, and `c → 1` (`ClosedAxis.tendsto_cMax`), so as the axis grows the seam state moves at the
`c` of the closed axis and keeps the ratio `√2`: the quantum `√2 − 1` survives at the limit.

The variance comes from the columns of the closed transport: the first and the last position
have two neighbours each, `1` and `d − 1` for the first, `d − 2` and `0` for the last.

## Main results

- `ClosedAxis.transport_seamState_apply` : `T°` on the seam state, coordinate by coordinate.
- `ClosedAxis.variance_transport_seamState`, `ClosedAxis.variance_PdOp_seamState` : `1/2`, `1`.
- `ClosedAxis.gramDefectAt_seamState` : the surplus is `1/4` for every `d`.
- `ClosedAxis.ratio_seamState` : the ratio `Var T° · Var P_d / (⟨K⟩/2)²` is `2`.
- `ClosedAxis.tendsto_speed_seamState` : the speed `⟨K⟩/c` of the seam state tends to `1`.
-/

@[expose] public noncomputable section

open Complex Filter Topology NRSInequality TransportPosition SpectralExtremal
open EigenvectorSaturation PlatformBlindness

namespace ClosedAxis

variable {n : ℕ}

/-- The neighbour `d − 2` of the last position. -/
abbrev prev (n : ℕ) : Fin (n + 3) := ⟨n + 1, by omega⟩

theorem Ad_zero (j : Fin (n + 3)) : Ad (n + 3) j 0 = if j = 1 then 1 else 0 := by
  have : MinStep j 0 ↔ j = 1 := by
    simp only [MinStep, Fin.ext_iff, Fin.val_zero, Fin.val_one]
    omega
  simp only [Ad, this]

theorem Ad_last (j : Fin (n + 3)) : Ad (n + 3) j (last n) = if j = prev n then 1 else 0 := by
  have : MinStep j (last n) ↔ j = prev n := by
    simp only [MinStep, Fin.ext_iff, Fin.val_last]
    omega
  simp only [Ad, this]

/-- `Σ_k f k ψ_k` on the seam state picks the two seam coordinates. -/
theorem sum_mul_seamState (f : Fin (n + 3) → ℂ) :
    ∑ k, f k * seamState n k = ((1 / √2 : ℝ) : ℂ) * (f 0 - I * f (last n)) := by
  simp only [seamState_apply, mul_sub, mul_ite, mul_one, mul_zero,
    Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  ring

variable (n) in
/-- The column of the first position in `A_d + S`: its neighbours `1` and `d − 1`. -/
def alpha (j : Fin (n + 3)) : ℝ := (if j = 1 then 1 else 0) + (if j = last n then 1 else 0)

variable (n) in
/-- The column of the last position in `A_d + S`: its neighbours `d − 2` and `0`. -/
def beta (j : Fin (n + 3)) : ℝ := (if j = prev n then 1 else 0) + (if j = 0 then 1 else 0)

theorem one_ne_last : (1 : Fin (n + 3)) ≠ last n := by simp [Fin.ext_iff]

theorem prev_ne_zero : prev n ≠ 0 := by simp [Fin.ext_iff]

theorem zero_ne_last : (0 : Fin (n + 3)) ≠ last n := by simp [Fin.ext_iff]

/-- `T°` on the seam state: `(α_j − i β_j)/(2√2)`. -/
theorem transport_seamState_apply (j : Fin (n + 3)) :
    transport n (seamState n) j =
      ((1 / (2 * √2) : ℝ) : ℂ) * ((alpha n j : ℂ) - I * (beta n j : ℂ)) := by
  have hρ : (rho (n + 3) : ℂ) ≠ 0 := by exact_mod_cast (rho_pos (n + 3) (by omega)).ne'
  have h2 : (√2 : ℂ) ≠ 0 := by exact_mod_cast (by positivity : (0 : ℝ) < √2).ne'
  have hT : TdOp (n + 3) (seamState n) j = ((1 / √2 : ℝ) : ℂ) *
      ((Ad (n + 3) j 0 - I * Ad (n + 3) j (last n)) / (rho (n + 3) : ℂ)) := by
    rw [TdOp_apply_coord, sum_mul_seamState]
    simp only [Td]
    ring
  have hS : seamOp n (seamState n) j = ((1 / √2 : ℝ) : ℂ) *
      ((if j = last n then 1 else 0) - I * (if j = 0 then 1 else 0)) := by
    simp only [seamOp, LinearMap.add_apply, LinearMap.smulRight_apply,
      ContinuousLinearMap.coe_coe, PiLp.proj_apply, PiLp.add_apply, PiLp.smul_apply,
      smul_eq_mul, seamState_apply, PiLp.single_apply, zero_ne_last,
      zero_ne_last.symm, ite_true, ite_false]
    split_ifs <;> ring
  simp only [transport, LinearMap.add_apply, LinearMap.smul_apply, PiLp.add_apply,
    PiLp.smul_apply, smul_eq_mul, hT, hS, Ad_zero, Ad_last, alpha, beta]
  push_cast
  field_simp
  split_ifs <;> simp only [Complex.ofReal_one, Complex.ofReal_zero] <;> ring

theorem norm_transport_seamState : ‖transport n (seamState n)‖ ^ 2 = 1 / 2 := by
  have h2 : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
  simp only [transport_seamState_apply, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    mul_pow, sq_abs, ← Finset.mul_sum]
  have hn (a b : ℝ) : ‖((a : ℂ)) - I * (b : ℂ)‖ ^ 2 = a ^ 2 + b ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp
    ring
  have hsum : ∑ j : Fin (n + 3), ‖(alpha n j : ℂ) - I * (beta n j : ℂ)‖ ^ 2 = 4 := by
    simp only [hn, alpha, beta, add_sq, Finset.sum_add_distrib]
    simp [one_ne_last.symm, prev_ne_zero.symm]
    norm_num
  rw [hsum]
  field_simp
  rw [h2]
  norm_num

/-- `Σ_k ψ̄_k g_k` on the seam state picks the two seam coordinates. -/
theorem sum_conj_seamState_mul (g : Fin (n + 3) → ℂ) :
    ∑ k, (starRingEnd ℂ) (seamState n k) * g k =
      ((1 / √2 : ℝ) : ℂ) * (g 0 + I * g (last n)) := by
  simp only [seamState_apply, map_mul, Complex.conj_ofReal, map_sub, apply_ite (starRingEnd ℂ),
    map_one, map_zero, Complex.conj_I, mul_assoc, ← Finset.mul_sum]
  simp only [sub_mul, neg_mul, mul_ite, mul_one, mul_zero, ite_mul, one_mul, zero_mul,
    Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  ring

theorem alpha_zero : alpha n 0 = 0 := by
  simp [alpha, Fin.ext_iff]

theorem beta_zero : beta n 0 = 1 := by simp [beta, prev_ne_zero.symm]

theorem alpha_last : alpha n (last n) = 1 := by simp [alpha, one_ne_last.symm]

theorem beta_last : beta n (last n) = 0 := by
  simp [beta, zero_ne_last.symm, Fin.ext_iff]

theorem inner_seamState_transport :
    inner ℂ (seamState n) (transport n (seamState n)) = 0 := by
  rw [PiLp.inner_apply]
  simp only [RCLike.inner_apply, mul_comm (transport n (seamState n) _)]
  rw [sum_conj_seamState_mul, transport_seamState_apply, transport_seamState_apply, alpha_zero,
    beta_zero, alpha_last, beta_last]
  push_cast
  ring

theorem mean_transport_seamState : mean (transport n) (seamState n) = 0 := by
  rw [mean, inner_seamState_transport, Complex.zero_re]

theorem mean_PdOp_seamState : mean (PdOp (n + 3)) (seamState n) = 0 := by
  have h2 : (√2 : ℂ) ≠ 0 := by exact_mod_cast (by positivity : (0 : ℝ) < √2).ne'
  rw [mean, PiLp.inner_apply]
  simp only [RCLike.inner_apply, PdOp_apply_coord, mul_comm (((posCoord _ _ : ℝ) : ℂ) * _)]
  rw [sum_conj_seamState_mul, posCoord_zero, posCoord_last, seamState_apply, seamState_apply]
  simp [zero_ne_last.symm]

/-- **`Var T° = 1/2`** at the seam state. -/
theorem variance_transport_seamState : variance (transport n) (seamState n) = 1 / 2 := by
  rw [variance, centered, mean_transport_seamState, Complex.ofReal_zero, zero_smul, sub_zero,
    norm_transport_seamState]

theorem norm_PdOp_seamState : ‖PdOp (n + 3) (seamState n)‖ ^ 2 = 1 := by
  have h2 : (√2 : ℂ) ^ 2 = 2 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num
  have h20 : (√2 : ℂ) ≠ 0 := by exact_mod_cast (by positivity : (0 : ℝ) < √2).ne'
  have h := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (PdOp (n + 3) (seamState n))
  rw [PiLp.inner_apply] at h
  simp only [RCLike.inner_apply, PdOp_apply_coord, map_mul, Complex.conj_ofReal] at h
  have hs : ∑ x : Fin (n + 3), ((posCoord (n + 3) x : ℝ) : ℂ) * seamState n x *
      (((posCoord (n + 3) x : ℝ) : ℂ) * (starRingEnd ℂ) (seamState n x)) =
      ∑ x, (starRingEnd ℂ) (seamState n x) *
        (((posCoord (n + 3) x : ℝ) : ℂ) ^ 2 * seamState n x) :=
    Finset.sum_congr rfl fun x _ => by ring
  rw [hs, sum_conj_seamState_mul, posCoord_zero, posCoord_last, seamState_apply,
    seamState_apply] at h
  simp only [zero_ne_last, zero_ne_last.symm, ite_true, ite_false] at h
  have hv : ((1 / √2 : ℝ) : ℂ) * (((-1 : ℝ) : ℂ) ^ 2 * (((1 / √2 : ℝ) : ℂ) * (1 - I * 0)) +
      I * (((1 : ℝ) : ℂ) ^ 2 * (((1 / √2 : ℝ) : ℂ) * (0 - I * 1)))) = 1 := by
    push_cast
    field_simp
    ring_nf
    rw [I_sq, h2]
    ring
  have key := h.symm.trans hv
  have key3 : ((‖PdOp (n + 3) (seamState n)‖ : ℂ)) ^ 2 = 1 := key
  have key4 : ((‖PdOp (n + 3) (seamState n)‖ ^ 2 : ℝ) : ℂ) = 1 := by push_cast; exact key3
  exact_mod_cast key4

theorem centered_transport_seamState :
    centered (transport n) (seamState n) = transport n (seamState n) := by
  rw [centered, mean_transport_seamState, Complex.ofReal_zero, zero_smul, sub_zero]

theorem centered_PdOp_seamState :
    centered (PdOp (n + 3)) (seamState n) = PdOp (n + 3) (seamState n) := by
  rw [centered, mean_PdOp_seamState, Complex.ofReal_zero, zero_smul, sub_zero]

/-- **`Var P_d = 1`** at the seam state. -/
theorem variance_PdOp_seamState : variance (PdOp (n + 3)) (seamState n) = 1 := by
  rw [variance, centered_PdOp_seamState, norm_PdOp_seamState]

theorem inner_transport_PdOp_seamState :
    inner ℂ (transport n (seamState n)) (PdOp (n + 3) (seamState n)) = -I / 2 := by
  have h2 : (√2 : ℂ) ^ 2 = 2 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num
  have h20 : (√2 : ℂ) ≠ 0 := by exact_mod_cast (by positivity : (0 : ℝ) < √2).ne'
  rw [PiLp.inner_apply]
  simp only [RCLike.inner_apply, PdOp_apply_coord]
  have hs : ∑ x : Fin (n + 3), ((posCoord (n + 3) x : ℝ) : ℂ) * seamState n x *
      (starRingEnd ℂ) (transport n (seamState n) x) =
      ∑ x, (((posCoord (n + 3) x : ℝ) : ℂ) * (starRingEnd ℂ) (transport n (seamState n) x)) *
        seamState n x := Finset.sum_congr rfl fun x _ => by ring
  rw [hs, sum_mul_seamState, transport_seamState_apply, transport_seamState_apply, alpha_zero,
    beta_zero, alpha_last, beta_last, posCoord_zero, posCoord_last]
  simp only [map_mul, Complex.conj_ofReal, map_sub, Complex.conj_I]
  push_cast
  field_simp
  ring_nf
  rw [h2]

/-- **The surplus of the seam state is `1/4`, for every `d`.** -/
theorem gramDefectAt_seamState :
    gramDefectAt (transport n) (PdOp (n + 3)) (seamState n) = 1 / 4 := by
  rw [gramDefectAt, variance_transport_seamState, variance_PdOp_seamState,
    centered_transport_seamState, centered_PdOp_seamState, inner_transport_PdOp_seamState]
  rw [norm_div, norm_neg, Complex.norm_I, Complex.norm_ofNat]
  norm_num

/-- **The ratio is `2`**: `Var T° · Var P_d / (⟨K⟩/2)² = 2`, so the uncertainty ratio of the seam
state is `√2` for every `d`. -/
theorem ratio_seamState :
    variance (transport n) (seamState n) * variance (PdOp (n + 3)) (seamState n) /
      (tension n (seamState n) / 2) ^ 2 = 2 := by
  rw [variance_transport_seamState, variance_PdOp_seamState, tension_seamState]
  norm_num

/-- **The seam state moves at the `c` of the closed axis in the limit**: its speed `⟨K⟩/c` tends
to `1`. -/
theorem tendsto_speed_seamState :
    Tendsto (fun n => tension n (seamState n) / cMax n) atTop (𝓝 1) := by
  simp_rw [tension_seamState, one_div]
  simpa using tendsto_cMax.inv₀ one_ne_zero

end ClosedAxis
