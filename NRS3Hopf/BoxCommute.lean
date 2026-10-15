/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NRS3Hopf.FourAxes

/-!
# Different axes of the box commute

On the box `dx × dy × dz × dw` an operator lifted along one axis acts on that coordinate only, so
operators of different axes commute, whatever the pair on the fourth axis. This is the
hypothesis of the equality case on `n` axes (`RobertsonEquality`), for the box of four axes; on
the cube it is `D37` (`liftAlong_xy_comm`).

## Main results

- `BoxCommute.liftAlong_xy_comm` and the five other pairs : lifted matrices of different axes
  commute.
- `BoxCommute.boxPairs_comm` : the eight observables of the box commute across axes.
-/

@[expose] public noncomputable section

open Matrix PathGraph3DNRS FourAxes TransportPosition

namespace BoxCommute

variable {dx dy dz dw : ℕ}

section Pairs

variable (A : Matrix (Fin dx) (Fin dx) ℂ) (B : Matrix (Fin dy) (Fin dy) ℂ)
  (C : Matrix (Fin dz) (Fin dz) ℂ) (D : Matrix (Fin dw) (Fin dw) ℂ)

theorem liftAlong_xy_comm :
    liftAlong (eX dx dy dz dw) A * liftAlong (eY dx dy dz dw) B =
      liftAlong (eY dx dy dz dw) B * liftAlong (eX dx dy dz dw) A := by
  ext ⟨i, j, k, l⟩ ⟨i', j', k', l'⟩
  simp only [Matrix.mul_apply, liftAlong, Matrix.of_apply, FourAxes.eX, FourAxes.eY,
    Equiv.refl_apply, Equiv.coe_fn_mk, Fintype.sum_prod_type, Prod.mk.injEq]
  simp [ite_and, mul_ite, Finset.sum_ite_eq, Finset.sum_ite_eq', mul_comm]

theorem liftAlong_xz_comm :
    liftAlong (eX dx dy dz dw) A * liftAlong (eZ dx dy dz dw) C =
      liftAlong (eZ dx dy dz dw) C * liftAlong (eX dx dy dz dw) A := by
  ext ⟨i, j, k, l⟩ ⟨i', j', k', l'⟩
  simp only [Matrix.mul_apply, liftAlong, Matrix.of_apply, FourAxes.eX, FourAxes.eZ,
    Equiv.refl_apply, Equiv.coe_fn_mk, Fintype.sum_prod_type, Prod.mk.injEq]
  simp [ite_and, mul_ite, Finset.sum_ite_eq, Finset.sum_ite_eq', mul_comm]

theorem liftAlong_xw_comm :
    liftAlong (eX dx dy dz dw) A * liftAlong (eW dx dy dz dw) D =
      liftAlong (eW dx dy dz dw) D * liftAlong (eX dx dy dz dw) A := by
  ext ⟨i, j, k, l⟩ ⟨i', j', k', l'⟩
  simp only [Matrix.mul_apply, liftAlong, Matrix.of_apply, FourAxes.eX, FourAxes.eW,
    Equiv.refl_apply, Equiv.coe_fn_mk, Fintype.sum_prod_type, Prod.mk.injEq]
  simp [ite_and, mul_ite, Finset.sum_ite_eq, Finset.sum_ite_eq', mul_comm]

theorem liftAlong_yz_comm :
    liftAlong (eY dx dy dz dw) B * liftAlong (eZ dx dy dz dw) C =
      liftAlong (eZ dx dy dz dw) C * liftAlong (eY dx dy dz dw) B := by
  ext ⟨i, j, k, l⟩ ⟨i', j', k', l'⟩
  simp only [Matrix.mul_apply, liftAlong, Matrix.of_apply, FourAxes.eY, FourAxes.eZ,
    Equiv.coe_fn_mk, Fintype.sum_prod_type, Prod.mk.injEq]
  simp [ite_and, mul_ite, Finset.sum_ite_eq, Finset.sum_ite_eq', mul_comm]

theorem liftAlong_yw_comm :
    liftAlong (eY dx dy dz dw) B * liftAlong (eW dx dy dz dw) D =
      liftAlong (eW dx dy dz dw) D * liftAlong (eY dx dy dz dw) B := by
  ext ⟨i, j, k, l⟩ ⟨i', j', k', l'⟩
  simp only [Matrix.mul_apply, liftAlong, Matrix.of_apply, FourAxes.eY, FourAxes.eW,
    Equiv.coe_fn_mk, Fintype.sum_prod_type, Prod.mk.injEq]
  simp [ite_and, mul_ite, Finset.sum_ite_eq, Finset.sum_ite_eq', mul_comm]

theorem liftAlong_zw_comm :
    liftAlong (eZ dx dy dz dw) C * liftAlong (eW dx dy dz dw) D =
      liftAlong (eW dx dy dz dw) D * liftAlong (eZ dx dy dz dw) C := by
  ext ⟨i, j, k, l⟩ ⟨i', j', k', l'⟩
  simp only [Matrix.mul_apply, liftAlong, Matrix.of_apply, FourAxes.eZ, FourAxes.eW,
    Equiv.coe_fn_mk, Fintype.sum_prod_type, Prod.mk.injEq]
  simp [ite_and, mul_ite, Finset.sum_ite_eq, Finset.sum_ite_eq', mul_comm]

end Pairs

theorem apply_comm {ι : Type*} [Fintype ι] [DecidableEq ι] {X Y : Matrix ι ι ℂ} (h : X * Y = Y * X)
    (ψ : EuclideanSpace ℂ ι) :
    Matrix.toEuclideanLin X (Matrix.toEuclideanLin Y ψ) =
      Matrix.toEuclideanLin Y (Matrix.toEuclideanLin X ψ) := by
  rw [← LinearMap.comp_apply, ← LinearMap.comp_apply, Matrix.toEuclideanLin,
    ← Matrix.toLpLin_mul_same, ← Matrix.toLpLin_mul_same, h]

section Box

variable (M : Fin 2 → Matrix (Fin dw) (Fin dw) ℂ) (s : Fin 2)

theorem box_x : boxPairs dx dy dz dw M (s, 0) =
    Matrix.toEuclideanLin (liftAlong (FourAxes.eX dx dy dz dw) (![Td dx, Pd dx] s)) := rfl
theorem box_y : boxPairs dx dy dz dw M (s, 1) =
    Matrix.toEuclideanLin (liftAlong (FourAxes.eY dx dy dz dw) (![Td dy, Pd dy] s)) := rfl
theorem box_z : boxPairs dx dy dz dw M (s, 2) =
    Matrix.toEuclideanLin (liftAlong (FourAxes.eZ dx dy dz dw) (![Td dz, Pd dz] s)) := rfl
theorem box_w : boxPairs dx dy dz dw M (s, 3) =
    Matrix.toEuclideanLin (liftAlong (FourAxes.eW dx dy dz dw) (M s)) := rfl

end Box

/-- **The eight observables of the box commute across axes**, whatever the pair on the fourth
axis. -/
theorem boxPairs_comm (M : Fin 2 → Matrix (Fin dw) (Fin dw) ℂ) (s t : Fin 2) (i j : Fin 4)
    (hij : i ≠ j) (ψ : H4D dx dy dz dw) :
    boxPairs dx dy dz dw M (t, j) (boxPairs dx dy dz dw M (s, i) ψ) =
      boxPairs dx dy dz dw M (s, i) (boxPairs dx dy dz dw M (t, j) ψ) := by
  fin_cases i <;> fin_cases j
  all_goals simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] at hij ⊢
  · exact absurd rfl hij
  · rw [box_x, box_y]; exact (apply_comm (liftAlong_xy_comm _ _) ψ).symm
  · rw [box_x, box_z]; exact (apply_comm (liftAlong_xz_comm _ _) ψ).symm
  · rw [box_x, box_w]; exact (apply_comm (liftAlong_xw_comm _ _) ψ).symm
  · rw [box_x, box_y]; exact apply_comm (liftAlong_xy_comm _ _) ψ
  · exact absurd rfl hij
  · rw [box_y, box_z]; exact (apply_comm (liftAlong_yz_comm _ _) ψ).symm
  · rw [box_y, box_w]; exact (apply_comm (liftAlong_yw_comm _ _) ψ).symm
  · rw [box_x, box_z]; exact apply_comm (liftAlong_xz_comm _ _) ψ
  · rw [box_y, box_z]; exact apply_comm (liftAlong_yz_comm _ _) ψ
  · exact absurd rfl hij
  · rw [box_z, box_w]; exact (apply_comm (liftAlong_zw_comm _ _) ψ).symm
  · rw [box_x, box_w]; exact apply_comm (liftAlong_xw_comm _ _) ψ
  · rw [box_y, box_w]; exact apply_comm (liftAlong_yw_comm _ _) ψ
  · rw [box_z, box_w]; exact apply_comm (liftAlong_zw_comm _ _) ψ
  · exact absurd rfl hij

end BoxCommute
