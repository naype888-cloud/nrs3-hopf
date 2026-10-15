/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NRS3Hopf.ClosedAxisEntangled

/-!
# The algebra of the closed axis with three positions

The commutators of the closed transport `T° = (J − I)/2` with `P₃ = diag(−1, 0, 1)`, the
analogues of `D49i` and `D49r` for the closed axis:

* `[T°, P₃] = ½ [[0, 1, 2], [−1, 0, 1], [−2, −1, 0]]`: the seam weighs twice an open link;
* `[P₃, [T°, P₃]] = −T° − (3/2) S`, with `S` the seam. On the open axis it is `−h² T`. Here it is
  invertible: it annihilates no nonzero state;
* `[T°, [T°, P₃]] = (3/2)(P₃ + P₃T° + T°P₃)`. On the open axis it lives on the two ends (`D49r`);
  here it is not diagonal, and its kernel is the line of `(1, −2, 1)`, also the kernel of
  `[T°, P₃]`;
* `T°` is invertible, with eigenvalues `1, −1/2, −1/2`: no state is annihilated by transport.

Every statement has its column version on a product `ℂ³ ⊗ ℂ^β`, for the closed fiber of the box.

## Main results

- `ClosedAxisAlgebra.comm_eq`, `ClosedAxisAlgebra.PC_eq`, `ClosedAxisAlgebra.TC_eq` : the three
  commutators.
- `ClosedAxisAlgebra.eq_zero_of_Tc`, `ClosedAxisAlgebra.eq_zero_of_PC` : `T°` and
  `[P₃, [T°, P₃]]` annihilate no nonzero vector.
- `ClosedAxisAlgebra.comm_mulVec_eq_zero_iff`, `ClosedAxisAlgebra.TC_mulVec_eq_zero_iff` : the
  kernels of `[T°, P₃]` and `[T°, [T°, P₃]]` are the line of `(1, −2, 1)`.
- `ClosedAxisAlgebra.eq_zero_of_lift` : an invertible matrix lifted to a product annihilates no
  nonzero state.
- `ClosedAxisAlgebra.eq_zero_of_lift_Tc`, `ClosedAxisAlgebra.eq_zero_of_lift_PC` : on a product,
  `T°` and `[P₃, [T°, P₃]]` annihilate no nonzero state, entangled or not.
- `ClosedAxisAlgebra.liftAlong_mul`, `ClosedAxisAlgebra.lift_PC` : lifting respects products, so
  the lifted double commutator is the double commutator of the lifted operators.
-/

@[expose] public noncomputable section

open Matrix TransportPosition PathGraph3DNRS AxisDefectEntangled

namespace ClosedAxisAlgebra

/-- `T°`. -/
abbrev T : Matrix (Fin 3) (Fin 3) ℂ := ClosedThree.Tc

/-- `P₃`. -/
abbrev P : Matrix (Fin 3) (Fin 3) ℂ := Pd 3

/-- The seam: the link between the first and the last position. -/
def S : Matrix (Fin 3) (Fin 3) ℂ := !![0, 0, 1; 0, 0, 0; 1, 0, 0]

theorem T_eq : T = !![0, 1 / 2, 1 / 2; 1 / 2, 0, 1 / 2; 1 / 2, 1 / 2, 0] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [T, ClosedThree.Tc]

theorem P_eq : P = !![-1, 0, 0; 0, 0, 0; 0, 0, 1] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [P, Pd, posCoord] <;> norm_num

/-- **`[T°, P₃]`**: the seam weighs twice an open link. -/
theorem comm_eq : T * P - P * T = (1 / 2 : ℂ) • !![0, 1, 2; -1, 0, 1; -2, -1, 0] := by
  rw [T_eq, P_eq]
  ext i j; fin_cases i <;> fin_cases j <;> norm_num

/-- **`[P₃, [T°, P₃]] = −T° − (3/2) S`.** -/
theorem PC_eq : P * (T * P - P * T) - (T * P - P * T) * P = -T - (3 / 2 : ℂ) • S := by
  rw [comm_eq, T_eq, P_eq, S]
  ext i j; fin_cases i <;> fin_cases j <;> norm_num

/-- **`[T°, [T°, P₃]] = (3/2)(P₃ + P₃T° + T°P₃)`.** -/
theorem TC_eq : T * (T * P - P * T) - (T * P - P * T) * T = (3 / 2 : ℂ) • (P + P * T + T * P) := by
  rw [comm_eq, T_eq, P_eq]
  ext i j; fin_cases i <;> fin_cases j <;> norm_num

/-! ## Kernels -/

theorem mulVec_apply (M : Matrix (Fin 3) (Fin 3) ℂ) (v : Fin 3 → ℂ) (i : Fin 3) :
    M.mulVec v i = M i 0 * v 0 + M i 1 * v 1 + M i 2 * v 2 := by
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]

/-- **No state is annihilated by transport**: `T° v = 0` gives `v = 0`. -/
theorem eq_zero_of_Tc {v : Fin 3 → ℂ} (h : T.mulVec v = 0) : v = 0 := by
  have r0 := congrFun h 0
  have r1 := congrFun h 1
  have r2 := congrFun h 2
  simp only [mulVec_apply, T_eq, Pi.zero_apply] at r0 r1 r2
  simp at r0 r1 r2
  have h0 : v 0 = 0 := by linear_combination r1 + r2 - r0
  have h1 : v 1 = 0 := by linear_combination r0 + r2 - r1
  have h2 : v 2 = 0 := by linear_combination r0 + r1 - r2
  funext i
  fin_cases i
  exacts [h0, h1, h2]

/-- **`[P₃, [T°, P₃]]` annihilates no nonzero vector**, unlike `−h² T` on the open axis. -/
theorem eq_zero_of_PC {v : Fin 3 → ℂ}
    (h : (P * (T * P - P * T) - (T * P - P * T) * P).mulVec v = 0) : v = 0 := by
  rw [PC_eq] at h
  have r0 := congrFun h 0
  have r1 := congrFun h 1
  have r2 := congrFun h 2
  simp only [mulVec_apply, T_eq, S, Pi.zero_apply] at r0 r1 r2
  simp at r0 r1 r2
  norm_num at r0 r1 r2
  have h0 : v 0 = 0 := by linear_combination (-1 / 4 : ℂ) * (r2 - r0 + 4 * r1)
  have h1 : v 1 = 0 := by linear_combination -2 * r2 - 4 * h0
  have h2 : v 2 = 0 := by linear_combination -2 * r1 - h0
  funext i
  fin_cases i
  exacts [h0, h1, h2]

/-- The kernel of `[T°, P₃]` is the line of `(1, −2, 1)`. -/
theorem comm_mulVec_eq_zero_iff (v : Fin 3 → ℂ) :
    (T * P - P * T).mulVec v = 0 ↔ v 1 = -2 * v 0 ∧ v 2 = v 0 := by
  rw [comm_eq]
  constructor
  · intro h
    have r0 := congrFun h 0
    have r1 := congrFun h 1
    simp only [mulVec_apply, Pi.zero_apply] at r0 r1
    simp at r0 r1
    exact ⟨by linear_combination 2 * r0 - 4 * r1, by linear_combination 2 * r1⟩
  · rintro ⟨h1, h2⟩
    funext i
    fin_cases i <;> simp [mulVec_apply, h1, h2]

/-- The kernel of `[T°, [T°, P₃]]` is the same line. -/
theorem TC_mulVec_eq_zero_iff (v : Fin 3 → ℂ) :
    (T * (T * P - P * T) - (T * P - P * T) * T).mulVec v = 0 ↔
      v 1 = -2 * v 0 ∧ v 2 = v 0 := by
  rw [TC_eq, T_eq, P_eq]
  constructor
  · intro h
    have r0 := congrFun h 0
    have r1 := congrFun h 1
    simp only [mulVec_apply, Pi.zero_apply] at r0 r1
    simp at r0 r1
    norm_num at r0 r1
    exact ⟨by linear_combination (-4 / 3 : ℂ) * r0, by linear_combination (4 / 3 : ℂ) * r1⟩
  · rintro ⟨h1, h2⟩
    funext i
    fin_cases i <;> simp [mulVec_apply, h1, h2] <;> ring

/-! ## On a product -/

variable {ι β : Type*} [Fintype ι] [Fintype β] [DecidableEq ι] [DecidableEq β]

/-- **An invertible matrix lifted to a product annihilates no nonzero state**, column by
column. -/
theorem eq_zero_of_lift (e : ι ≃ Fin 3 × β) {M : Matrix (Fin 3) (Fin 3) ℂ}
    (hM : ∀ v, M.mulVec v = 0 → v = 0) {Φ : EuclideanSpace ℂ ι}
    (h : Matrix.toEuclideanLin (liftAlong e M) Φ = 0) : Φ = 0 := by
  ext q
  have hcol : M.mulVec (col e Φ (e q).2) = 0 := by
    funext i
    have := congrArg (fun x : EuclideanSpace ℂ ι => x (e.symm (i, (e q).2))) h
    simp only [PiLp.zero_apply] at this
    rw [liftAlong_apply_col] at this
    exact this
  have := congrFun (hM _ hcol) (e q).1
  simpa [AxisDefectEntangled.col] using this

omit [DecidableEq ι] in
theorem liftAlong_mul (e : ι ≃ Fin 3 × β) (A B : Matrix (Fin 3) (Fin 3) ℂ) :
    liftAlong e (A * B) = liftAlong e A * liftAlong e B := by
  ext p q
  simp only [liftAlong, Matrix.of_apply, Matrix.mul_apply]
  rw [Fintype.sum_equiv e _ (fun x => A (e p).1 x.1 * (if (e p).2 = x.2 then 1 else 0) *
    (B x.1 (e q).1 * if x.2 = (e q).2 then 1 else 0)) (fun r => by simp),
    Fintype.sum_prod_type, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  by_cases h : (e p).2 = (e q).2
  · rw [Finset.sum_eq_single (e p).2]
    · simp [h]
    · intro b _ hb; simp [Ne.symm hb]
    · intro h'; exact absurd (Finset.mem_univ _) h'
  · simp only [h, ite_false, mul_zero]
    refine (Finset.sum_eq_zero fun b _ => ?_).symm
    by_cases hb : (e p).2 = b
    · subst hb; simp [h]
    · simp [hb]

omit [Fintype ι] [Fintype β] [DecidableEq ι] in
theorem liftAlong_sub (e : ι ≃ Fin 3 × β) (A B : Matrix (Fin 3) (Fin 3) ℂ) :
    liftAlong e (A - B) = liftAlong e A - liftAlong e B := by
  ext p q; simp only [liftAlong, Matrix.of_apply, Matrix.sub_apply]; ring

/-- **On a product, transport annihilates no nonzero state.** -/
theorem eq_zero_of_lift_Tc (e : ι ≃ Fin 3 × β) {Φ : EuclideanSpace ℂ ι}
    (h : Matrix.toEuclideanLin (liftAlong e T) Φ = 0) : Φ = 0 :=
  eq_zero_of_lift e (fun _ hv => eq_zero_of_Tc hv) h

/-- **On a product, `[P₃, [T°, P₃]]` annihilates no nonzero state**, entangled or not. -/
theorem eq_zero_of_lift_PC (e : ι ≃ Fin 3 × β) {Φ : EuclideanSpace ℂ ι}
    (h : Matrix.toEuclideanLin (liftAlong e (P * (T * P - P * T) - (T * P - P * T) * P)) Φ = 0) :
    Φ = 0 :=
  eq_zero_of_lift e (fun _ hv => eq_zero_of_PC hv) h

omit [DecidableEq ι] in
/-- The lifted double commutator is the double commutator of the lifted operators. -/
theorem lift_PC (e : ι ≃ Fin 3 × β) :
    liftAlong e (P * (T * P - P * T) - (T * P - P * T) * P) =
      liftAlong e P * (liftAlong e T * liftAlong e P - liftAlong e P * liftAlong e T) -
        (liftAlong e T * liftAlong e P - liftAlong e P * liftAlong e T) * liftAlong e P := by
  simp only [liftAlong_sub, liftAlong_mul]

end ClosedAxisAlgebra
