/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NRS3Hopf.ClosedAxisAlgebra
public import Mathlib.Algebra.Lie.OfAssociative

/-!
# Two identities of `sl(2)` that the closed axis breaks

The open axes with `2` or `3` positions generate `sl(2)`: with the adjacency `A`, the position
`P` and `C = [A, P]`,

  `[A, C] = κ P`,  `[P, C] = −μ A`,

with `(κ, μ) = (4, 4)` for `d = 2` and `(2, 1)` for `d = 3`. Every such algebra satisfies two Lie
identities of degree `6` in two variables, `p₁` and `p₂`, checked on coordinates for every `κ`,
`μ`. So `p₁` and `p₂` vanish on any two combinations of `T_d` and `P_d`, `d = 2, 3`.

The closed axis with three positions generates `sl(3)`, which does not satisfy them:
`p₁(T°, P₃)` and `p₂(T°, P₃)` are antisymmetric with kernels the lines of `(1, 0, −1)` and
`(1, 1, 1)`, so together they annihilate no nonzero vector.

## Main results

- `SlTwoIdentity.map_p₁`, `SlTwoIdentity.map_p₂` : an additive map that respects the bracket
  respects `p₁`, `p₂`.
- `SlTwoIdentity.p₁_open`, `SlTwoIdentity.p₂_open` : both vanish on the open axes with `2` or `3`
  positions.
- `SlTwoIdentity.p₁_closed`, `SlTwoIdentity.p₂_closed` : their values on the closed axis.
- `SlTwoIdentity.eq_zero_of_p_closed` : together they annihilate no nonzero vector.
-/

@[expose] public noncomputable section

open Matrix TransportPosition PathGraph3DNRS

namespace SlTwoIdentity

/-! ## 1. The two identities, for any bracket -/

section Bracket

variable {A B : Type*} [AddCommGroup A] [AddCommGroup B]

/-- The first identity, of bidegree `(2, 4)`. -/
def p₁ (b : A → A → A) (x y : A) : A :=
  (5 : ℤ) • b x (b y (b y (b y (b x y)))) + b y (b x (b y (b y (b x y)))) -
    (3 : ℤ) • b y (b y (b x (b y (b x y)))) - (3 : ℤ) • b y (b y (b y (b x (b x y))))

/-- The second identity, of bidegree `(3, 3)`. -/
def p₂ (b : A → A → A) (x y : A) : A :=
  (3 : ℤ) • b x (b x (b y (b y (b x y)))) + b x (b y (b x (b y (b x y)))) +
    b x (b y (b y (b x (b x y)))) - b y (b x (b x (b y (b x y)))) -
    b y (b x (b y (b x (b x y)))) - (3 : ℤ) • b y (b y (b x (b x (b x y))))

variable (f : A →+ B) {b : A → A → A} {b' : B → B → B}
  (hf : ∀ x y, f (b x y) = b' (f x) (f y))
include hf

theorem map_p₁ (x y : A) : f (p₁ b x y) = p₁ b' (f x) (f y) := by
  simp only [p₁, map_add, map_sub, map_zsmul, hf]

theorem map_p₂ (x y : A) : f (p₂ b x y) = p₂ b' (f x) (f y) := by
  simp only [p₂, map_add, map_sub, map_zsmul, hf]

end Bracket

/-! ## 2. The identities hold on `sl(2)` -/

/-- The bracket of `sl(2)` on coordinates `(A, P, C)`. -/
def br (κ μ : ℂ) (u v : Fin 3 → ℂ) : Fin 3 → ℂ :=
  ![-μ * (u 1 * v 2 - u 2 * v 1), κ * (u 0 * v 2 - u 2 * v 0), u 0 * v 1 - u 1 * v 0]

theorem p₁_br (κ μ : ℂ) (u v : Fin 3 → ℂ) : p₁ (br κ μ) u v = 0 := by
  funext i
  fin_cases i <;> simp [p₁, br] <;> ring

theorem p₂_br (κ μ : ℂ) (u v : Fin 3 → ℂ) : p₂ (br κ μ) u v = 0 := by
  funext i
  fin_cases i <;> simp [p₂, br] <;> ring

section Sl2

attribute [local instance 100] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

variable {R : Type*} [Ring R] [Algebra ℂ R] {X Y : R} {κ μ : ℂ}

/-- The coordinates `(A, P, C)` as elements of `R`. -/
def coord (X Y : R) : (Fin 3 → ℂ) →+ R where
  toFun u := u 0 • X + u 1 • Y + u 2 • ⁅X, Y⁆
  map_zero' := by simp
  map_add' u v := by simp only [Pi.add_apply, add_smul]; abel

theorem coord_br (hX : ⁅X, ⁅X, Y⁆⁆ = κ • Y) (hY : ⁅Y, ⁅X, Y⁆⁆ = -μ • X) (u v : Fin 3 → ℂ) :
    coord X Y (br κ μ u v) = ⁅coord X Y u, coord X Y v⁆ := by
  have hYX : ⁅Y, X⁆ = -⁅X, Y⁆ := (lie_skew Y X).symm
  have hXYX : ⁅⁅X, Y⁆, X⁆ = -(κ • Y) := by rw [← lie_skew ⁅X, Y⁆ X, hX]
  have hXYY : ⁅⁅X, Y⁆, Y⁆ = μ • X := by rw [← lie_skew ⁅X, Y⁆ Y, hY, neg_smul, neg_neg]
  simp only [coord, AddMonoidHom.coe_mk, ZeroHom.coe_mk, br, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, add_lie,
    lie_add, smul_lie, lie_smul, lie_self, hX, hY, hYX, hXYX, hXYY]
  module

/-- **`p₁` vanishes on `sl(2)`.** -/
theorem p₁_sl2 (hX : ⁅X, ⁅X, Y⁆⁆ = κ • Y) (hY : ⁅Y, ⁅X, Y⁆⁆ = -μ • X) (α β γ δ : ℂ) :
    p₁ (fun a b : R => ⁅a, b⁆) (α • X + β • Y) (γ • X + δ • Y) = 0 := by
  have h := map_p₁ (coord X Y) (coord_br hX hY) ![α, β, 0] ![γ, δ, 0]
  rw [p₁_br, map_zero] at h
  simpa [coord] using h.symm

/-- **`p₂` vanishes on `sl(2)`.** -/
theorem p₂_sl2 (hX : ⁅X, ⁅X, Y⁆⁆ = κ • Y) (hY : ⁅Y, ⁅X, Y⁆⁆ = -μ • X) (α β γ δ : ℂ) :
    p₂ (fun a b : R => ⁅a, b⁆) (α • X + β • Y) (γ • X + δ • Y) = 0 := by
  have h := map_p₂ (coord X Y) (coord_br hX hY) ![α, β, 0] ![γ, δ, 0]
  rw [p₂_br, map_zero] at h
  simpa [coord] using h.symm

end Sl2

/-! ## 3. The open axes with `2` and `3` positions -/

theorem Ad_two : Ad 2 = !![0, 1; 1, 0] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Ad, MinStep]

theorem Pd_two : Pd 2 = !![-1, 0; 0, 1] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Pd, posCoord] <;> norm_num

theorem Ad_three : Ad 3 = !![0, 1, 0; 1, 0, 1; 0, 1, 0] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Ad, MinStep]

theorem Pd_three : Pd 3 = !![-1, 0, 0; 0, 0, 0; 0, 0, 1] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Pd, posCoord] <;> norm_num

theorem two_A : ⁅Ad 2, ⁅Ad 2, Pd 2⁆⁆ = (4 : ℂ) • Pd 2 := by
  rw [Ad_two, Pd_two]
  simp only [Ring.lie_def, Matrix.mul_fin_two, Matrix.of_sub_of, Matrix.smul_of]
  norm_num

theorem two_P : ⁅Pd 2, ⁅Ad 2, Pd 2⁆⁆ = -(4 : ℂ) • Ad 2 := by
  rw [Ad_two, Pd_two]
  simp only [Ring.lie_def, Matrix.mul_fin_two, Matrix.of_sub_of, Matrix.smul_of]
  norm_num

theorem three_A : ⁅Ad 3, ⁅Ad 3, Pd 3⁆⁆ = (2 : ℂ) • Pd 3 := by
  rw [Ad_three, Pd_three]
  simp only [Ring.lie_def, Matrix.mul_fin_three, Matrix.of_sub_of, Matrix.smul_of]
  norm_num

theorem three_P : ⁅Pd 3, ⁅Ad 3, Pd 3⁆⁆ = -(1 : ℂ) • Ad 3 := by
  rw [Ad_three, Pd_three]
  simp only [Ring.lie_def, Matrix.mul_fin_three, Matrix.of_sub_of, Matrix.smul_of]
  norm_num

theorem Td_eq (d : ℕ) : Td d = ((rho d : ℂ)⁻¹) • Ad d := by
  ext i j; simp [Td, div_eq_inv_mul]

theorem comb_eq (d : ℕ) (α β : ℂ) :
    α • Td d + β • Pd d = (α * (rho d : ℂ)⁻¹) • Ad d + β • Pd d := by
  rw [Td_eq, smul_smul]

/-- **`p₁` vanishes on an open axis with `2` or `3` positions.** -/
theorem p₁_open {d : ℕ} (hd : d = 2 ∨ d = 3) (α β γ δ : ℂ) :
    p₁ (fun a b : Matrix (Fin d) (Fin d) ℂ => ⁅a, b⁆) (α • Td d + β • Pd d)
      (γ • Td d + δ • Pd d) = 0 := by
  rw [comb_eq, comb_eq]
  rcases hd with rfl | rfl
  · exact p₁_sl2 two_A two_P _ _ _ _
  · exact p₁_sl2 three_A three_P _ _ _ _

/-- **`p₂` vanishes on an open axis with `2` or `3` positions.** -/
theorem p₂_open {d : ℕ} (hd : d = 2 ∨ d = 3) (α β γ δ : ℂ) :
    p₂ (fun a b : Matrix (Fin d) (Fin d) ℂ => ⁅a, b⁆) (α • Td d + β • Pd d)
      (γ • Td d + δ • Pd d) = 0 := by
  rw [comb_eq, comb_eq]
  rcases hd with rfl | rfl
  · exact p₂_sl2 two_A two_P _ _ _ _
  · exact p₂_sl2 three_A three_P _ _ _ _

/-! ## 4. The closed axis breaks them -/

open ClosedAxisAlgebra in
/-- `p₁(T°, P₃)`, antisymmetric with kernel the line of `(1, 0, −1)`. -/
theorem p₁_closed :
    p₁ (fun a b : Matrix (Fin 3) (Fin 3) ℂ => ⁅a, b⁆) T P =
      !![0, 33 / 2, 0; -33 / 2, 0, -33 / 2; 0, 33 / 2, 0] := by
  rw [T_eq, P_eq]
  simp only [p₁, Ring.lie_def, Matrix.mul_fin_three, Matrix.of_sub_of]
  norm_num [Matrix.smul_cons, Matrix.smul_empty, Matrix.empty_eq]
  all_goals (funext i; fin_cases i; rfl)

open ClosedAxisAlgebra in
/-- `p₂(T°, P₃)`, antisymmetric with kernel the line of `(1, 1, 1)`. -/
theorem p₂_closed :
    p₂ (fun a b : Matrix (Fin 3) (Fin 3) ℂ => ⁅a, b⁆) T P =
      !![0, 33 / 4, -33 / 4; -33 / 4, 0, 33 / 4; 33 / 4, -33 / 4, 0] := by
  rw [T_eq, P_eq]
  simp only [p₂, Ring.lie_def, Matrix.mul_fin_three, Matrix.of_sub_of]
  norm_num [Matrix.smul_cons, Matrix.smul_empty, Matrix.empty_eq]
  all_goals (funext i; fin_cases i; rfl)

open ClosedAxisAlgebra in
/-- **Together, `p₁(T°, P₃)` and `p₂(T°, P₃)` annihilate no nonzero vector.** -/
theorem eq_zero_of_p_closed {v : Fin 3 → ℂ}
    (h₁ : (p₁ (fun a b : Matrix (Fin 3) (Fin 3) ℂ => ⁅a, b⁆) T P).mulVec v = 0)
    (h₂ : (p₂ (fun a b : Matrix (Fin 3) (Fin 3) ℂ => ⁅a, b⁆) T P).mulVec v = 0) : v = 0 := by
  rw [p₁_closed] at h₁
  rw [p₂_closed] at h₂
  have r0 := congrFun h₁ 0
  have r1 := congrFun h₁ 1
  have s0 := congrFun h₂ 0
  have s1 := congrFun h₂ 1
  simp only [mulVec_apply, Pi.zero_apply] at r0 r1 s0 s1
  simp at r0 r1 s0 s1
  have e2 : v 2 = 0 := by linear_combination (-4 / 33 : ℂ) * s0 + r0
  have e0 : v 0 = 0 := by linear_combination (-2 / 33 : ℂ) * r1 - e2
  funext i
  fin_cases i
  exacts [e0, r0, e2]

end SlTwoIdentity
