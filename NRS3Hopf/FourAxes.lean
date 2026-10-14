/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NavaRobertsonIndependent.Mathematics.D49c_RobertsonDeterminantProduct

/-!
# Four axes: the box `dx × dy × dz × dw`

The cube of `D37` with a fourth axis `w`. Each of `x`, `y`, `z`, `w` carries its pair
`(T_d, P_d)`, lifted to the box with the identity on the other three axes, so the box carries
eight observables. On a product state `u ⊗ v ⊗ w ⊗ s` the fluctuation vectors of different axes
are orthogonal, so `Σ` and `Ω` are block diagonal, one `2 × 2` block per axis, as on the cube
(`D49c`).

## Main results

- `FourAxes.inner_prod4` : inner products factor over the four axes.
- `FourAxes.covMatrix_prod4` : `Σ` is block diagonal on product states.
- `FourAxes.imMatrix_prod4` : `Ω` is block diagonal on product states.
- `FourAxes.det_imMatrix_pair` : the `2 × 2` block of `Ω` has determinant `t²/4`.
-/

@[expose] public noncomputable section

open Matrix TransportPosition SpectralExtremal NearMaxTension PathGraph3DNRS
open RobertsonDeterminant RobertsonDeterminant3D RobertsonDeterminantProduct CubeSpectrum
open CubePythagoras

namespace FourAxes

variable (dx dy dz dw : ℕ)

/-- The positions of the box: one coordinate per axis. -/
abbrev Site4D := Fin dx × Fin dy × Fin dz × Fin dw

/-- States on the box. -/
abbrev H4D := EuclideanSpace ℂ (Site4D dx dy dz dw)

/-- The `x` axis and the rest `(y, z, w)`. -/
def eX : Site4D dx dy dz dw ≃ Fin dx × (Fin dy × Fin dz × Fin dw) := Equiv.refl _

/-- The `y` axis and the rest `(x, z, w)`. -/
def eY : Site4D dx dy dz dw ≃ Fin dy × (Fin dx × Fin dz × Fin dw) where
  toFun p := (p.2.1, p.1, p.2.2.1, p.2.2.2)
  invFun q := (q.2.1, q.1, q.2.2.1, q.2.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

/-- The `z` axis and the rest `(x, y, w)`. -/
def eZ : Site4D dx dy dz dw ≃ Fin dz × (Fin dx × Fin dy × Fin dw) where
  toFun p := (p.2.2.1, p.1, p.2.1, p.2.2.2)
  invFun q := (q.2.1, q.2.2.1, q.1, q.2.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

/-- The `w` axis and the rest `(x, y, z)`. -/
def eW : Site4D dx dy dz dw ≃ Fin dw × (Fin dx × Fin dy × Fin dz) where
  toFun p := (p.2.2.2, p.1, p.2.1, p.2.2.1)
  invFun q := (q.2.1, q.2.2.1, q.2.2.2, q.1)
  left_inv _ := rfl
  right_inv _ := rfl

/-- The eight observables: `(0, i)` is the transport of axis `i`, `(1, i)` its position. -/
def pairs4 (p : Fin 2 × Fin 4) : H4D dx dy dz dw →ₗ[ℂ] H4D dx dy dz dw :=
  ![Matrix.toEuclideanLin (liftAlong (eX dx dy dz dw) (![Td dx, Pd dx] p.1)),
    Matrix.toEuclideanLin (liftAlong (eY dx dy dz dw) (![Td dy, Pd dy] p.1)),
    Matrix.toEuclideanLin (liftAlong (eZ dx dy dz dw) (![Td dz, Pd dz] p.1)),
    Matrix.toEuclideanLin (liftAlong (eW dx dy dz dw) (![Td dw, Pd dw] p.1))] p.2

variable {dx dy dz dw}

/-- Product of one state per axis. -/
def prod4 (u : Hd dx) (v : Hd dy) (w : Hd dz) (s : Hd dw) : H4D dx dy dz dw :=
  WithLp.toLp 2 fun p => u p.1 * v p.2.1 * w p.2.2.1 * s p.2.2.2

section Product

variable (u : Hd dx) (v : Hd dy) (w : Hd dz) (s : Hd dw)

theorem prod4_eq_eX : prod4 u v w s = prodAlong (eX dx dy dz dw) u (prod3 v w s) := by
  ext p; simp [prod4, prod3, prodAlong_apply, eX, mul_assoc]

theorem prod4_eq_eY : prod4 u v w s = prodAlong (eY dx dy dz dw) v (prod3 u w s) := by
  ext p; simp [prod4, prod3, prodAlong_apply, eY]; ring

theorem prod4_eq_eZ : prod4 u v w s = prodAlong (eZ dx dy dz dw) w (prod3 u v s) := by
  ext p; simp [prod4, prod3, prodAlong_apply, eZ]; ring

theorem prod4_eq_eW : prod4 u v w s = prodAlong (eW dx dy dz dw) s (prod3 u v w) := by
  ext p; simp [prod4, prod3, prodAlong_apply, eW]; ring

/-- Inner products factor over the four axes. -/
theorem inner_prod4 (u' : Hd dx) (v' : Hd dy) (w' : Hd dz) (s' : Hd dw) :
    inner ℂ (prod4 u v w s) (prod4 u' v' w' s') =
      inner ℂ u u' * inner ℂ v v' * inner ℂ w w' * inner ℂ s s' := by
  rw [prod4_eq_eX, prod4_eq_eX, inner_prodAlong, inner_prod3]; ring

end Product

theorem norm_prod3_eq_one {a b c : ℕ} {u : Hd a} {v : Hd b} {w : Hd c} (hu : ‖u‖ = 1)
    (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) : ‖prod3 u v w‖ = 1 := by
  rw [prod3_eq_eX]
  exact norm_prodAlong_eq_one _ hu (norm_prodAlong_eq_one _ hv hw)

variable {u : Hd dx} {v : Hd dy} {w : Hd dz} {s : Hd dw}
  (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) (hs : ‖s‖ = 1)

section Centered

include hv hw hs in
theorem centered_x (a : Fin 2) :
    centeredG (pairs4 dx dy dz dw (a, 0)) (prod4 u v w s) =
      prod4 (centeredG (pair dx a) u) v w s := by
  rw [show pairs4 dx dy dz dw (a, 0) = Matrix.toEuclideanLin (liftAlong (eX dx dy dz dw)
    (![Td dx, Pd dx] a)) from rfl, pair_eq, prod4_eq_eX,
    centeredG_lift _ (norm_prod3_eq_one hv hw hs), ← prod4_eq_eX]

include hu hw hs in
theorem centered_y (a : Fin 2) :
    centeredG (pairs4 dx dy dz dw (a, 1)) (prod4 u v w s) =
      prod4 u (centeredG (pair dy a) v) w s := by
  rw [show pairs4 dx dy dz dw (a, 1) = Matrix.toEuclideanLin (liftAlong (eY dx dy dz dw)
    (![Td dy, Pd dy] a)) from rfl, pair_eq, prod4_eq_eY,
    centeredG_lift _ (norm_prod3_eq_one hu hw hs), ← prod4_eq_eY]

include hu hv hs in
theorem centered_z (a : Fin 2) :
    centeredG (pairs4 dx dy dz dw (a, 2)) (prod4 u v w s) =
      prod4 u v (centeredG (pair dz a) w) s := by
  rw [show pairs4 dx dy dz dw (a, 2) = Matrix.toEuclideanLin (liftAlong (eZ dx dy dz dw)
    (![Td dz, Pd dz] a)) from rfl, pair_eq, prod4_eq_eZ,
    centeredG_lift _ (norm_prod3_eq_one hu hv hs), ← prod4_eq_eZ]

include hu hv hw in
theorem centered_w (a : Fin 2) :
    centeredG (pairs4 dx dy dz dw (a, 3)) (prod4 u v w s) =
      prod4 u v w (centeredG (pair dw a) s) := by
  rw [show pairs4 dx dy dz dw (a, 3) = Matrix.toEuclideanLin (liftAlong (eW dx dy dz dw)
    (![Td dw, Pd dw] a)) from rfl, pair_eq, prod4_eq_eW,
    centeredG_lift _ (norm_prod3_eq_one hu hv hw), ← prod4_eq_eW]

end Centered

include hu hv hw hs

/-- The centered vectors of the box at a product state, axis by axis. -/
theorem inner_centered_pairs4 (a b : Fin 2) (i j : Fin 4) :
    inner ℂ (centeredG (pairs4 dx dy dz dw (a, i)) (prod4 u v w s))
        (centeredG (pairs4 dx dy dz dw (b, j)) (prod4 u v w s)) =
      if i = j then
        ![inner ℂ (centeredG (pair dx a) u) (centeredG (pair dx b) u),
          inner ℂ (centeredG (pair dy a) v) (centeredG (pair dy b) v),
          inner ℂ (centeredG (pair dz a) w) (centeredG (pair dz b) w),
          inner ℂ (centeredG (pair dw a) s) (centeredG (pair dw b) s)] i
      else 0 := by
  have ul a := inner_self_centeredG (pair_isSymmetric dx a) hu
  have ur a := inner_centeredG_self (pair_isSymmetric dx a) hu
  have vl a := inner_self_centeredG (pair_isSymmetric dy a) hv
  have vr a := inner_centeredG_self (pair_isSymmetric dy a) hv
  have wl a := inner_self_centeredG (pair_isSymmetric dz a) hw
  have wr a := inner_centeredG_self (pair_isSymmetric dz a) hw
  have sl a := inner_self_centeredG (pair_isSymmetric dw a) hs
  have sr a := inner_centeredG_self (pair_isSymmetric dw a) hs
  fin_cases i <;> fin_cases j <;>
    simp [centered_x hv hw hs, centered_y hu hw hs, centered_z hu hv hs, centered_w hu hv hw,
      inner_prod4, ul, ur, vl, vr, wl, wr, sl, sr, hu, hv, hw, hs]

/-- On a product state `Σ` is block diagonal, one `2 × 2` block per axis. -/
theorem covMatrix_prod4 :
    covMatrix (pairs4 dx dy dz dw) (prod4 u v w s) =
      blockDiagonal ![covMatrix (pair dx) u, covMatrix (pair dy) v, covMatrix (pair dz) w,
        covMatrix (pair dw) s] := by
  ext ⟨a, i⟩ ⟨b, j⟩
  simp only [covMatrix, of_apply, blockDiagonal_apply, covarianceG,
    inner_centered_pairs4 hu hv hw hs]
  split_ifs with h
  · subst h; fin_cases i <;> rfl
  · rfl

/-- On a product state `Ω` is block diagonal, one `2 × 2` block per axis. -/
theorem imMatrix_prod4 :
    imMatrix (pairs4 dx dy dz dw) (prod4 u v w s) =
      blockDiagonal ![imMatrix (pair dx) u, imMatrix (pair dy) v, imMatrix (pair dz) w,
        imMatrix (pair dw) s] := by
  ext ⟨a, i⟩ ⟨b, j⟩
  simp only [imMatrix, of_apply, blockDiagonal_apply, inner_centered_pairs4 hu hv hw hs]
  split_ifs with h
  · subst h; fin_cases i <;> rfl
  · rfl

omit hu hv hw hs

/-- The `2 × 2` block of `Ω` on one axis has determinant `t²/4`, `t` the tension. -/
theorem det_imMatrix_pair (d : ℕ) (ψ : Hd d) :
    (imMatrix (pair d) ψ).det = tension d ψ ^ 2 / 4 := by
  have ht : tension d ψ = -2 * (inner ℂ (centeredG (pair d 0) ψ) (centeredG (pair d 1) ψ)).im :=
    tensionG_eq (pair_isSymmetric d 0) (pair_isSymmetric d 1)
  have h0 (x : Hd d) : (inner ℂ x x).im = 0 := by simpa using inner_self_im (𝕜 := ℂ) x
  rw [det_fin_two, ht]
  simp only [imMatrix, of_apply, h0]
  rw [inner_im_swap]
  ring

end FourAxes
