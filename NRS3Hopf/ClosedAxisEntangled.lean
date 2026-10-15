/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NRS3Hopf.CubeInBox
public import NavaRobertsonCertificados.D49e_AxisDefectEntangled

/-!
# The defect of the closed axis in the band, for every state

The analogue of `D49e` for the closed axis with three positions. A state `Φ` lives on a product
`ℂ³ ⊗ ℂ^β`, the closed axis and the rest, and may be entangled across the factors. If the tension
of the closed axis exceeds `1`, the band of `ClosedThree`, the Robertson–Schrödinger defect of
`(T°, P₃)` on that axis is positive.

The argument is that of `D49e`. A vanishing defect makes the fluctuation vectors parallel,
`(T° − αP₃ − μ)Φ = 0`, column by column. The tension forces `α ≠ 0`. With `α ≠ 0` a solution of
`T° v = αP₃ v + μv` with `v₀ = 0` vanishes: the rows give `v₂ = −v₁` and `α v₁ = 0`. So every
column is a multiple of one vector and `Φ` is a product, whose defect is the defect of its axis
factor, positive in the band (`ClosedThree.surplus_pos_of_one_lt`). Entanglement with the rest
cannot hide the defect of the closed axis.

On the box of four axes with the fourth axis closed, this holds for every state: the hidden fiber
keeps its defect whatever its entanglement with `x`, `y`, `z`.

## Main results

- `ClosedAxisEntangled.eq_zero_of_eigen` : with `α ≠ 0`, a solution with `v₀ = 0` vanishes.
- `ClosedAxisEntangled.exists_prodAlong_of_eigen` : a state whose columns solve it is a product.
- `ClosedAxisEntangled.gramDefect_pos_of_band` : tension above `1` forces the defect of the closed
  axis, for every unit state of the product.
- `ClosedAxisEntangled.gramDefect_box_pos` : on the box of four axes with the fourth axis closed,
  every unit state with tension above `1` on that axis has a positive defect there.
-/

@[expose] public noncomputable section

open TransportPosition PathGraph3DNRS CauchyGram RobertsonDeterminant RobertsonDeterminant3D
open AxisDefectEntangled NRSInequality EigenvectorSaturation FourAxes CubeInBox

namespace ClosedAxisEntangled

variable {ι β : Type*} [Fintype ι] [Fintype β] [DecidableEq ι] [DecidableEq β]

/-! ## 1. The rows of `T° − αP₃` -/

/-- **With `α ≠ 0`, a solution of `T° v = αP₃ v + μv` with `v₀ = 0` vanishes.** -/
theorem eq_zero_of_eigen {α μ : ℂ} (hα : α ≠ 0) {v : Fin 3 → ℂ}
    (h : ∀ i, ClosedThree.Tc.mulVec v i = α * (Pd 3).mulVec v i + μ * v i) (h0 : v 0 = 0) :
    v = 0 := by
  have r0 := h 0
  have r1 := h 1
  have r2 := h 2
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, ClosedThree.Tc, Pd, posCoord, h0]
    at r0 r1 r2
  norm_num at r0 r1 r2
  have hv1 : α * v 1 = 0 := by linear_combination r1 + r2 + (2 * α + 2 * μ - 1) * r0
  have h1 : v 1 = 0 := (mul_eq_zero.mp hv1).resolve_left hα
  have h2 : v 2 = 0 := by linear_combination 2 * r0 - h1
  funext i
  fin_cases i
  exacts [h0, h1, h2]

omit [Fintype β] [DecidableEq ι] [DecidableEq β] in
/-- A state whose columns all solve `T° v = αP₃ v + μv`, `α ≠ 0`, is a product `φ ⊗ χ`. -/
theorem exists_prodAlong_of_eigen (e : ι ≃ Fin 3 × β) {Φ : EuclideanSpace ℂ ι} (hΦ : Φ ≠ 0)
    {α μ : ℂ} (hα : α ≠ 0)
    (h : ∀ r i, ClosedThree.Tc.mulVec (col e Φ r) i =
      α * (Pd 3).mulVec (col e Φ r) i + μ * col e Φ r i) :
    ∃ (φ : EuclideanSpace ℂ (Fin 3)) (χ : EuclideanSpace ℂ β), Φ = prodAlong e φ χ := by
  obtain ⟨p, hp⟩ : ∃ p, Φ p ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hΦ (by ext p; simp [hc])
  set v := col e Φ (e p).2
  have hv0 : v 0 ≠ 0 := by
    intro h0
    have hz := congrFun (eq_zero_of_eigen hα (h (e p).2) h0) (e p).1
    simp [col] at hz
    exact hp hz
  have hprop (r : β) (i : Fin 3) : col e Φ r i = col e Φ r 0 / v 0 * v i := by
    have hu := eq_zero_of_eigen hα (μ := μ)
      (v := v 0 • col e Φ r - col e Φ r 0 • v) (fun i => by
        simp only [Matrix.mulVec_sub, Matrix.mulVec_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
          h r i, h (e p).2 i, v]
        ring) (by simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring)
    have hi := congrFun hu i
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hi
    field_simp
    linear_combination hi
  refine ⟨WithLp.toLp 2 v, WithLp.toLp 2 fun r => col e Φ r 0 / v 0, ?_⟩
  ext q
  have hq := hprop (e q).2 (e q).1
  simp only [col, Prod.mk.eta, Equiv.symm_apply_apply] at hq
  rw [prodAlong_apply, hq]
  simp [mul_comm, col]

/-! ## 2. The defect of the closed axis in the band -/

/-- The tension of the closed axis is `tensionG` of its pair. -/
theorem tensionG_eq_tension (ψ : Hd 3) :
    tensionG ClosedThree.TcOp (PdOp 3) ψ = ClosedThree.tension ψ := by
  rw [tensionG_eq ClosedThree.TcOp_isSymmetric (PdOp_isSymmetric 3), ClosedThree.tension]
  exact congrArg (fun x => -2 * x)
    (imPart_eq_im_inner ClosedThree.TcOp_isSymmetric (PdOp_isSymmetric 3) ψ)

/-- **The defect of the closed axis in the band, for every state.** If the tension of the closed
axis exceeds `1`, the Gram defect of `(T°, P₃)` on that axis is positive, whether or not `Φ` is
entangled with the rest. -/
theorem gramDefect_pos_of_band (e : ι ≃ Fin 3 × β) {Φ : EuclideanSpace ℂ ι} (hΦ : ‖Φ‖ = 1)
    (hb : 1 < |tensionG (Matrix.toEuclideanLin (liftAlong e ClosedThree.Tc))
      (Matrix.toEuclideanLin (liftAlong e (Pd 3))) Φ|) :
    0 < gramDefectC (centeredG (Matrix.toEuclideanLin (liftAlong e ClosedThree.Tc)) Φ)
      (centeredG (Matrix.toEuclideanLin (liftAlong e (Pd 3))) Φ) := by
  set T := Matrix.toEuclideanLin (liftAlong e ClosedThree.Tc)
  set P := Matrix.toEuclideanLin (liftAlong e (Pd 3))
  have hTs : T.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr
    (liftAlong_isHermitian e ClosedThree.Tc_isHermitian)
  have hPs : P.IsSymmetric :=
    Matrix.isSymmetric_toEuclideanLin_iff.mpr (liftAlong_isHermitian e (Pd_isHermitian 3))
  rcases (gramDefectC_nonneg (centeredG T Φ) (centeredG P Φ)).lt_or_eq with h | h
  · exact h
  exfalso
  have ht := tensionG_eq (Φ := Φ) hTs hPs
  by_cases hcP : centeredG P Φ = 0
  · rw [hcP, inner_zero_right, Complex.zero_im, mul_zero] at ht
    rw [ht, abs_zero] at hb
    linarith
  have hcs : ‖inner ℂ (centeredG P Φ) (centeredG T Φ)‖ = ‖centeredG P Φ‖ * ‖centeredG T Φ‖ := by
    rw [norm_inner_symm, ((gramDefectC_eq_zero_iff _ _).mp h.symm), mul_comm]
  obtain ⟨α, hα⟩ := Or.resolve_left
    (((norm_inner_eq_norm_tfae ℂ (centeredG P Φ) (centeredG T Φ)).out 1 3).mp hcs) hcP
  have hα0 : α ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hα
    rw [hα, inner_zero_left, Complex.zero_im, mul_zero] at ht
    rw [ht, abs_zero] at hb
    linarith
  have hcol (r : β) (i : Fin 3) : ClosedThree.Tc.mulVec (col e Φ r) i =
      α * (Pd 3).mulVec (col e Φ r) i + ((meanG T Φ : ℂ) - α * meanG P Φ) * col e Φ r i := by
    have hx := congrArg (fun x : EuclideanSpace ℂ ι => x (e.symm (i, r))) hα
    simp only [centeredG, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul] at hx
    rw [liftAlong_apply_col, liftAlong_apply_col] at hx
    simp only [col] at hx ⊢
    linear_combination hx
  have hΦ0 : Φ ≠ 0 := by
    rintro rfl
    simp at hΦ
  obtain ⟨φ, χ, hprod⟩ := exists_prodAlong_of_eigen e hΦ0 hα0 hcol
  have hφ0 : φ ≠ 0 := by
    rintro rfl
    apply hΦ0
    rw [hprod]
    ext p
    simp [prodAlong_apply]
  have hn : (‖φ‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_ne_zero_iff.mpr hφ0)
  set φ' := (‖φ‖ : ℂ)⁻¹ • φ
  set χ' := (‖φ‖ : ℂ) • χ
  have hprod' : Φ = prodAlong e φ' χ' := by
    rw [hprod]
    ext p
    simp only [prodAlong_apply, φ', χ', PiLp.smul_apply, smul_eq_mul]
    field_simp
  have hφ' : ‖φ'‖ = 1 := by
    simp only [φ', norm_smul, norm_inv, Complex.norm_real, norm_norm]
    exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hφ0)
  have hχ' : ‖χ'‖ = 1 := by
    have hi := inner_prodAlong e φ' φ' χ' χ'
    rw [← hprod', inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K,
      inner_self_eq_norm_sq_to_K, hΦ, hφ'] at hi
    push_cast at hi
    have hsq : ‖χ'‖ ^ 2 = 1 := by
      have h2 : ((‖χ'‖ ^ 2 : ℝ) : ℂ) = 1 := by push_cast; linear_combination -hi
      exact_mod_cast h2
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp hsq
  have hdef : gramDefectC (centeredG T Φ) (centeredG P Φ) =
      gramDefectAt ClosedThree.TcOp (PdOp 3) φ' := by
    simp only [T, P]
    rw [hprod', centeredG_lift e hχ', centeredG_lift e hχ']
    unfold gramDefectC varianceC
    rw [norm_sq_prodAlong e _ _ hχ', norm_sq_prodAlong e _ _ hχ', inner_prodAlong,
      inner_self_of_norm_one hχ', mul_one]
    rfl
  have hten : tensionG T P Φ = ClosedThree.tension φ' := by
    simp only [T, P]
    rw [hprod', tensionG_lift e hχ', ← tensionG_eq_tension]
    rfl
  have hs := ClosedThree.surplus_pos_of_one_lt hφ' (by rwa [← hten])
  linarith

/-! ## 3. The hidden closed fiber of the box -/

/-- **The hidden closed fiber keeps its defect, for every state of the box.** On the box of four
axes with the fourth axis closed with three positions, every unit state whose tension on that
axis exceeds `1` has a positive defect there, entangled with `x`, `y`, `z` or not. -/
theorem gramDefect_box_pos {dx dy dz : ℕ} {Φ : H4D dx dy dz 3} (hΦ : ‖Φ‖ = 1)
    (hb : 1 < |tensionG (boxPairs dx dy dz 3 closedPair (0, 3))
      (boxPairs dx dy dz 3 closedPair (1, 3)) Φ|) :
    0 < gramDefectC (centeredG (boxPairs dx dy dz 3 closedPair (0, 3)) Φ)
      (centeredG (boxPairs dx dy dz 3 closedPair (1, 3)) Φ) :=
  gramDefect_pos_of_band (eW dx dy dz 3) hΦ hb

end ClosedAxisEntangled
