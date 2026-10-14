/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NavaRobertsonIndependent.Mathematics.D23_EigenvectorSaturation

/-!
# The closed axis with three positions

Close the axis of `T₃ : P₃` with the link `{0, 2}` (`D16e`): the transport becomes
`T° = (J − I)/2`, every position linked to the other two, normalized by its spectral radius `2`,
and the position stays `P₃ = diag(−1, 0, 1)`. Its tension is `⟨K⟩ = −2 Im ⟪T°ψ, P₃ψ⟫`,
`K = i[T°, P₃]`.

On the open axis, `d = 3` saturates Robertson–Schrödinger at the cone (`D21`). On the closed
axis it does not. Every minimum-uncertainty state carries tension at most `‖ψ‖²`, and the bound
is attained. Proof:

* saturation gives `centered T° = c • centered P₃` (`D23`); row by row, with
  `B = 1/2 + ⟨T°⟩ − c⟨P₃⟩`, `B (2 ψ₀ ψ₂ − ψ₁ (ψ₀ + ψ₂)) = 0`. If `B = 0` either `c = 0`, and the
  tension vanishes, or `ψ₀ = ψ₂ = 0`. So a minimum-uncertainty state that moves satisfies
  `2 ψ₀ ψ₂ = ψ₁ (ψ₀ + ψ₂)`;
* on that quadric, scaled to `ψ₁ = 2`, `(ψ₀ − 1)(ψ₂ − 1) = 1`. With `ζ = ψ₀ − 1 = a + ib`,
  `|ζ|² (‖ψ‖² ∓ ⟨K⟩) = (a² + a + b² + 1 ∓ 2b)² + 3a² ≥ 0`.

## Main results

- `ClosedThree.relation_of_saturated` : a minimum-uncertainty state that moves lies on the
  quadric `2 ψ₀ ψ₂ = ψ₁ (ψ₀ + ψ₂)`.
- `ClosedThree.abs_tension_le_of_relation` : on the quadric, `|⟨K⟩| ≤ ‖ψ‖²`.
- `ClosedThree.abs_tension_le_of_saturated` : every minimum-uncertainty state has
  `|⟨K⟩| ≤ ‖ψ‖²`.
- `ClosedThree.surplus_pos_of_one_lt` : above tension `1` every unit state has a positive
  Robertson–Schrödinger surplus.
-/

@[expose] public noncomputable section

open Complex NRSInequality TransportPosition SpectralExtremal EigenvectorSaturation

namespace ClosedThree

/-- The closed transport on three positions: every position linked to the other two, normalized
by the spectral radius `2`. -/
def Tc : Matrix (Fin 3) (Fin 3) ℂ := fun i j => if i = j then 0 else 1 / 2

/-- `T°` as a linear map. -/
def TcOp : Hd 3 →ₗ[ℂ] Hd 3 := Matrix.toEuclideanLin Tc

theorem Tc_isHermitian : Tc.IsHermitian := by
  ext i j
  simp only [Matrix.conjTranspose_apply, Tc]
  split_ifs with h₁ h₂ h₂ <;> simp_all [eq_comm]

theorem TcOp_isSymmetric : TcOp.IsSymmetric :=
  Matrix.isSymmetric_toEuclideanLin_iff.mpr Tc_isHermitian

/-- The tension `⟨i[T°, P₃]⟩ = −2 Im ⟪T°ψ, P₃ψ⟫`. -/
def tension (ψ : Hd 3) : ℝ := -2 * (inner ℂ (TcOp ψ) (PdOp 3 ψ)).im

/-! ## 1. Coordinates -/

section Coordinates

variable (ψ : Hd 3)

theorem TcOp_apply : TcOp ψ 0 = (ψ 1 + ψ 2) / 2 ∧ TcOp ψ 1 = (ψ 0 + ψ 2) / 2 ∧
    TcOp ψ 2 = (ψ 0 + ψ 1) / 2 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [TcOp, Tc, Matrix.toEuclideanLin, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct,
      Fin.sum_univ_three] <;>
    ring

theorem PdOp_apply : PdOp 3 ψ 0 = -ψ 0 ∧ PdOp 3 ψ 1 = 0 ∧ PdOp 3 ψ 2 = ψ 2 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [PdOp, Pd, posCoord, Matrix.toEuclideanLin, Matrix.toLpLin_apply, Matrix.mulVec,
      dotProduct] <;> norm_num

theorem inner_eq (φ χ : Hd 3) :
    inner ℂ φ χ = (starRingEnd ℂ) (φ 0) * χ 0 + (starRingEnd ℂ) (φ 1) * χ 1 +
      (starRingEnd ℂ) (φ 2) * χ 2 := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, Fin.sum_univ_three]
  ring

/-- The tension in coordinates. -/
theorem tension_eq : tension ψ =
    -((ψ 0).re * (ψ 1).im) - 2 * ((ψ 0).re * (ψ 2).im) + (ψ 1).re * (ψ 0).im -
      (ψ 1).re * (ψ 2).im + 2 * ((ψ 2).re * (ψ 0).im) + (ψ 2).re * (ψ 1).im := by
  obtain ⟨t0, t1, t2⟩ := TcOp_apply ψ
  obtain ⟨p0, p1, p2⟩ := PdOp_apply ψ
  rw [tension, inner_eq, t0, t1, t2, p0, p1, p2]
  simp only [map_div₀, map_add, mul_zero, add_zero, Complex.add_im, Complex.mul_im,
    Complex.div_re, Complex.div_im, Complex.conj_re, Complex.conj_im, Complex.add_re,
    Complex.neg_re, Complex.neg_im]
  norm_num
  ring

theorem normSq_eq : ‖ψ‖ ^ 2 = Complex.normSq (ψ 0) + Complex.normSq (ψ 1) +
    Complex.normSq (ψ 2) := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity), Fin.sum_univ_three]
  simp only [Complex.sq_norm]

theorem tension_smul (c : ℂ) : tension (c • ψ) = Complex.normSq c * tension ψ := by
  rw [tension, tension, map_smul, map_smul, inner_smul_left, inner_smul_right, ← mul_assoc,
    Complex.conj_mul', ← Complex.ofReal_pow, Complex.sq_norm, Complex.im_ofReal_mul]
  ring

end Coordinates

/-! ## 2. Minimum uncertainty puts a moving state on a quadric -/

/-- **A minimum-uncertainty state that moves lies on `2 ψ₀ ψ₂ = ψ₁ (ψ₀ + ψ₂)`.** -/
theorem relation_of_saturated {ψ : Hd 3} (hs : gramDefectAt TcOp (PdOp 3) ψ = 0)
    (ht : tension ψ ≠ 0) : 2 * ψ 0 * ψ 2 = ψ 1 * (ψ 0 + ψ 2) := by
  have himp : tension ψ = -2 * imPart TcOp (PdOp 3) ψ := by
    rw [tension, imPart_eq_im_inner TcOp_isSymmetric (PdOp_isSymmetric 3)]
  rcases (gramDefectAt_eq_zero_iff TcOp (PdOp 3) ψ).mp hs with hv | ⟨c, hc⟩
  · exfalso
    apply ht
    have h0 : centered (PdOp 3) ψ = 0 := by
      unfold variance at hv
      exact norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp hv)
    rw [himp, imPart, h0, inner_zero_right, Complex.zero_im, mul_zero]
  · obtain ⟨t0, t1, t2⟩ := TcOp_apply ψ
    obtain ⟨p0, p1, p2⟩ := PdOp_apply ψ
    have row (j : Fin 3) := congrFun (congrArg (fun v : Hd 3 => (v : Fin 3 → ℂ)) hc) j
    simp only [centered, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul] at row
    have r0 := row 0
    have r1 := row 1
    have r2 := row 2
    rw [t0, p0] at r0
    rw [t1, p1] at r1
    rw [t2, p2] at r2
    set t : ℂ := (mean TcOp ψ : ℂ)
    set m : ℂ := (mean (PdOp 3) ψ : ℂ)
    have hB : (1 / 2 + t - c * m) * (2 * ψ 0 * ψ 2 - ψ 1 * (ψ 0 + ψ 2)) = 0 := by
      linear_combination (-(ψ 2)) * r0 + (ψ 0 + ψ 2) * r1 - (ψ 0) * r2
    rcases mul_eq_zero.mp hB with hB0 | hR
    · have hS : ψ 0 + ψ 1 + ψ 2 = 0 := by linear_combination 2 * r1 + 2 * ψ 1 * hB0
      by_cases hc0 : c = 0
      · exfalso
        apply ht
        rw [hc0, zero_smul] at hc
        rw [himp, imPart, hc, inner_zero_left, Complex.zero_im, mul_zero]
      · have h0 : ψ 0 = 0 := by
          have : c * ψ 0 = 0 := by linear_combination r0 + ψ 0 * hB0 - hS / 2
          exact (mul_eq_zero.mp this).resolve_left hc0
        have h2 : ψ 2 = 0 := by
          have : c * ψ 2 = 0 := by linear_combination -r2 - ψ 2 * hB0 + hS / 2
          exact (mul_eq_zero.mp this).resolve_left hc0
        rw [h0, h2]
        ring
    · exact sub_eq_zero.mp hR

/-! ## 3. The bound on the quadric -/

/-- The bound with `ψ₁ = 2`: `(ψ₀ − 1)(ψ₂ − 1) = 1` gives `|⟨K⟩| ≤ ‖ψ‖²`. -/
theorem abs_tension_le_two {ψ : Hd 3} (h1 : ψ 1 = 2) (hq : (ψ 0 - 1) * (ψ 2 - 1) = 1) :
    |tension ψ| ≤ ‖ψ‖ ^ 2 := by
  rw [tension_eq, normSq_eq, h1]
  set a := (ψ 0).re - 1 with ha
  set b := (ψ 0).im
  set c := (ψ 2).re - 1 with hc
  set d := (ψ 2).im
  have e1 : a * c - b * d = 1 := by
    have := congrArg Complex.re hq
    simp only [Complex.mul_re, Complex.sub_re, Complex.sub_im, Complex.one_re,
      Complex.one_im, sub_zero] at this
    linarith
  have e2 : a * d + b * c = 0 := by
    have := congrArg Complex.im hq
    simp only [Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.one_re,
      Complex.one_im, sub_zero, Complex.one_im] at this
    linarith
  have hr : 0 < a ^ 2 + b ^ 2 := by
    rcases eq_or_ne a 0 with h | h
    · have hb : b ≠ 0 := by intro hb0; rw [h, hb0] at e1; linarith
      positivity
    · positivity
  have hcr : c * (a ^ 2 + b ^ 2) = a := by linear_combination a * e1 + b * e2
  have hdr : d * (a ^ 2 + b ^ 2) = -b := by linear_combination a * e2 - b * e1
  have hcd : (c ^ 2 + d ^ 2) * (a ^ 2 + b ^ 2) = 1 := by
    linear_combination (a * c - b * d + 1) * e1 + (a * d + b * c) * e2
  simp only [Complex.normSq_apply, Complex.re_ofNat, Complex.im_ofNat, mul_zero, add_zero]
  have hx0 : (ψ 0).re = a + 1 := by rw [ha]; ring
  have hx2 : (ψ 2).re = c + 1 := by rw [hc]; ring
  rw [hx0, hx2]
  have key (s : ℝ) (hs : s = 1 ∨ s = -1) :
      (a ^ 2 + b ^ 2) * ((a + 1) * (a + 1) + b * b + 2 * 2 + ((c + 1) * (c + 1) + d * d) -
        s * (-((a + 1) * 0) - 2 * ((a + 1) * d) + 2 * b - 2 * d + 2 * ((c + 1) * b) +
          (c + 1) * 0)) =
        (a ^ 2 + a + b ^ 2 + 1 - 2 * s * b) ^ 2 + 3 * a ^ 2 := by
    rcases hs with rfl | rfl
    · linear_combination (2 - 2 * b) * hcr + (4 + 2 * a) * hdr + hcd
    · linear_combination (2 + 2 * b) * hcr - (4 + 2 * a) * hdr + hcd
  rw [abs_le]
  constructor
  · have := key (-1) (Or.inr rfl)
    nlinarith [sq_nonneg (a ^ 2 + a + b ^ 2 + 1 - 2 * (-1) * b), sq_nonneg a]
  · have := key 1 (Or.inl rfl)
    nlinarith [sq_nonneg (a ^ 2 + a + b ^ 2 + 1 - 2 * 1 * b), sq_nonneg a]

/-- **On the quadric `2 ψ₀ ψ₂ = ψ₁ (ψ₀ + ψ₂)`, `|⟨K⟩| ≤ ‖ψ‖²`.** -/
theorem abs_tension_le_of_relation {ψ : Hd 3} (hR : 2 * ψ 0 * ψ 2 = ψ 1 * (ψ 0 + ψ 2)) :
    |tension ψ| ≤ ‖ψ‖ ^ 2 := by
  by_cases h1 : ψ 1 = 0
  · rw [h1, zero_mul, mul_assoc, mul_eq_zero, mul_eq_zero] at hR
    rw [tension_eq, h1]
    rcases hR with h | h | h
    · norm_num at h
    · rw [h]; simp
    · rw [h]; simp
  · set k : ℂ := 2 / ψ 1
    have hk : k ≠ 0 := div_ne_zero two_ne_zero h1
    have hφ1 : (k • ψ) 1 = 2 := by
      simp only [PiLp.smul_apply, smul_eq_mul, k]; field_simp
    have hφq : ((k • ψ) 0 - 1) * ((k • ψ) 2 - 1) = 1 := by
      simp only [PiLp.smul_apply, smul_eq_mul, k]
      field_simp
      linear_combination 2 * hR
    have h := abs_tension_le_two hφ1 hφq
    rw [tension_smul, norm_smul, mul_pow, abs_mul, abs_of_nonneg (Complex.normSq_nonneg k),
      ← Complex.sq_norm] at h
    exact le_of_mul_le_mul_left h (by positivity)

/-- **Minimum uncertainty on the closed axis: `|⟨K⟩| ≤ ‖ψ‖²`.** -/
theorem abs_tension_le_of_saturated {ψ : Hd 3} (hs : gramDefectAt TcOp (PdOp 3) ψ = 0) :
    |tension ψ| ≤ ‖ψ‖ ^ 2 := by
  by_cases ht : tension ψ = 0
  · rw [ht, abs_zero]; positivity
  · exact abs_tension_le_of_relation (relation_of_saturated hs ht)

/-- **The band of the closed axis**: a unit state with tension above `1` has a positive
Robertson–Schrödinger surplus. -/
theorem surplus_pos_of_one_lt {ψ : Hd 3} (hψ : ‖ψ‖ = 1) (ht : 1 < |tension ψ|) :
    0 < gramDefectAt TcOp (PdOp 3) ψ := by
  refine lt_of_le_of_ne (gramDefectAt_nonneg _ _ _) fun h => ?_
  have := abs_tension_le_of_saturated h.symm
  rw [hψ] at this
  linarith

end ClosedThree
