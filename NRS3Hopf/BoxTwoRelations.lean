/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NRS3Hopf.SlTwoIdentity
public import NRS3Hopf.BoxCommute

/-!
# Two relations through the closed fiber leave no state

On the box `dx × dy × dz × 3` with `dx, dy, dz ∈ {2, 3}` and the closed fiber, take two
relations among the fluctuation vectors, `Σ_p a_p (A_p − ⟨A_p⟩) Φ = 0` and the same for `b`,
whose parts on the fiber are `T°` and `P₃`. Then `Φ` is an eigenvector of `L_a = Σ a_p A_p` and
of `L_b`, so every bracket of `L_a` and `L_b` annihilates `Φ`, in particular `p₁(L_a, L_b)` and
`p₂(L_a, L_b)`.

The axes commute, so a bracket of sums over the axes is the sum of the brackets axis by axis:
`p(L_a, L_b)` is `p` on `x`, plus `p` on `y`, plus `p` on `z`, plus `p` on the fiber. On the open
axes with `2` or `3` positions both identities vanish (`SlTwoIdentity`), so only the fiber is
left: `p₁(T°, P₃)` and `p₂(T°, P₃)` annihilate `Φ`, and together they annihilate no nonzero
state. So `Φ = 0`.

## Main results

- `BoxTwoRelations.lie_apply_eq_zero` : two operators with a common eigenvector `Φ`: their
  bracket annihilates `Φ`.
- `BoxTwoRelations.lam_lie` : the sum over the axes respects the bracket.
- `BoxTwoRelations.eq_zero_of_relations` : two relations through `T°` and `P₃` leave no state.
-/

@[expose] public noncomputable section

open Matrix TransportPosition PathGraph3DNRS FourAxes CubeInBox SlTwoIdentity

namespace BoxTwoRelations

/-! ## 1. A common eigenvector -/

section Eigen

variable {V : Type*} [AddCommGroup V] [Module ℂ V] {X Y Z : Module.End ℂ V} {v : V}

theorem lie_apply_of_eig {c : ℂ} (hX : X v = c • v) (hZ : Z v = 0) : ⁅X, Z⁆ v = 0 := by
  simp [Ring.lie_def, hX, hZ]

/-- **Two operators with a common eigenvector: their bracket annihilates it.** -/
theorem lie_apply_eq_zero {a b : ℂ} (hX : X v = a • v) (hY : Y v = b • v) : ⁅X, Y⁆ v = 0 := by
  simp [Ring.lie_def, hX, hY, smul_smul, mul_comm]

theorem p₁_apply_eq_zero {a b : ℂ} (hX : X v = a • v) (hY : Y v = b • v) :
    p₁ (fun A B : Module.End ℂ V => ⁅A, B⁆) X Y v = 0 := by
  have hXY := lie_apply_eq_zero hX hY
  unfold p₁
  simp (maxDischargeDepth := 6) [lie_apply_of_eig hX, lie_apply_of_eig hY, hXY]

theorem p₂_apply_eq_zero {a b : ℂ} (hX : X v = a • v) (hY : Y v = b • v) :
    p₂ (fun A B : Module.End ℂ V => ⁅A, B⁆) X Y v = 0 := by
  have hXY := lie_apply_eq_zero hX hY
  unfold p₂
  simp (maxDischargeDepth := 6) [lie_apply_of_eig hX, lie_apply_of_eig hY, hXY]

end Eigen

/-! ## 2. Lifting to the box -/

section Lift

variable {ι α β : Type*} [DecidableEq β] (e : ι ≃ α × β)

theorem liftAlong_add (A B : Matrix α α ℂ) :
    liftAlong e (A + B) = liftAlong e A + liftAlong e B := by
  ext p q; simp only [liftAlong, Matrix.of_apply, Matrix.add_apply]; ring

theorem liftAlong_smul (c : ℂ) (A : Matrix α α ℂ) :
    liftAlong e (c • A) = c • liftAlong e A := by
  ext p q; simp only [liftAlong, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]; ring

theorem liftAlong_sub (A B : Matrix α α ℂ) :
    liftAlong e (A - B) = liftAlong e A - liftAlong e B := by
  ext p q; simp only [liftAlong, Matrix.of_apply, Matrix.sub_apply]; ring

theorem liftAlong_zero : liftAlong e (0 : Matrix α α ℂ) = 0 := by
  ext p q; simp [liftAlong]

theorem liftAlong_mul [Fintype α] [Fintype ι] [Fintype β] (A B : Matrix α α ℂ) :
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

end Lift

variable {dx dy dz : ℕ}

/-- One matrix per axis of the box. -/
abbrev Axes (dx dy dz : ℕ) :=
  Matrix (Fin dx) (Fin dx) ℂ × Matrix (Fin dy) (Fin dy) ℂ × Matrix (Fin dz) (Fin dz) ℂ ×
    Matrix (Fin 3) (Fin 3) ℂ

/-- The sum over the axes of the lifted matrices. -/
def lam : Axes dx dy dz →+ Matrix (Site4D dx dy dz 3) (Site4D dx dy dz 3) ℂ where
  toFun X := liftAlong (eX dx dy dz 3) X.1 + liftAlong (eY dx dy dz 3) X.2.1 +
    liftAlong (eZ dx dy dz 3) X.2.2.1 + liftAlong (eW dx dy dz 3) X.2.2.2
  map_zero' := by simp only [Prod.fst_zero, Prod.snd_zero, liftAlong_zero, add_zero]
  map_add' X Y := by
    simp only [Prod.fst_add, Prod.snd_add, liftAlong_add]; abel

/-- **The sum over the axes respects the bracket**, since different axes commute. -/
theorem lam_lie (X Y : Axes dx dy dz) : lam ⁅X, Y⁆ = ⁅lam X, lam Y⁆ := by
  simp only [lam, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Ring.lie_def, Prod.fst_sub,
    Prod.snd_sub, Prod.fst_mul, Prod.snd_mul, liftAlong_sub, liftAlong_mul, add_mul, mul_add]
  rw [BoxCommute.liftAlong_xy_comm X.1 Y.2.1, BoxCommute.liftAlong_xz_comm X.1 Y.2.2.1,
    BoxCommute.liftAlong_xw_comm X.1 Y.2.2.2, BoxCommute.liftAlong_yz_comm X.2.1 Y.2.2.1,
    BoxCommute.liftAlong_yw_comm X.2.1 Y.2.2.2, BoxCommute.liftAlong_zw_comm X.2.2.1 Y.2.2.2,
    ← BoxCommute.liftAlong_xy_comm Y.1 X.2.1, ← BoxCommute.liftAlong_xz_comm Y.1 X.2.2.1,
    ← BoxCommute.liftAlong_xw_comm Y.1 X.2.2.2, ← BoxCommute.liftAlong_yz_comm Y.2.1 X.2.2.1,
    ← BoxCommute.liftAlong_yw_comm Y.2.1 X.2.2.2, ← BoxCommute.liftAlong_zw_comm Y.2.2.1 X.2.2.2]
  abel

end BoxTwoRelations
