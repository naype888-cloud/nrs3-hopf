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

/-! ## 3. The identities on the box -/

/-- Each component respects the bracket. -/
theorem lie_fst (X Y : Axes dx dy dz) : (⁅X, Y⁆).1 = ⁅X.1, Y.1⁆ := by simp [Ring.lie_def]
theorem lie_snd_fst (X Y : Axes dx dy dz) : (⁅X, Y⁆).2.1 = ⁅X.2.1, Y.2.1⁆ := by
  simp [Ring.lie_def]
theorem lie_snd_snd_fst (X Y : Axes dx dy dz) : (⁅X, Y⁆).2.2.1 = ⁅X.2.2.1, Y.2.2.1⁆ := by
  simp [Ring.lie_def]
theorem lie_snd_snd_snd (X Y : Axes dx dy dz) : (⁅X, Y⁆).2.2.2 = ⁅X.2.2.2, Y.2.2.2⁆ := by
  simp [Ring.lie_def]

/-- The four projections of the axes. -/
def prX : Axes dx dy dz →+ Matrix (Fin dx) (Fin dx) ℂ := AddMonoidHom.fst _ _
def prY : Axes dx dy dz →+ Matrix (Fin dy) (Fin dy) ℂ :=
  (AddMonoidHom.fst _ _).comp (AddMonoidHom.snd _ _)
def prZ : Axes dx dy dz →+ Matrix (Fin dz) (Fin dz) ℂ :=
  (AddMonoidHom.fst _ _).comp ((AddMonoidHom.snd _ _).comp (AddMonoidHom.snd _ _))
def prW : Axes dx dy dz →+ Matrix (Fin 3) (Fin 3) ℂ :=
  (AddMonoidHom.snd _ _).comp ((AddMonoidHom.snd _ _).comp (AddMonoidHom.snd _ _))

/-- The matrices of a combination `Σ_p a_p A_p`, axis by axis. -/
def axesOf (a : Fin 2 × Fin 4 → ℂ) : Axes dx dy dz :=
  (a (0, 0) • Td dx + a (1, 0) • Pd dx, a (0, 1) • Td dy + a (1, 1) • Pd dy,
    a (0, 2) • Td dz + a (1, 2) • Pd dz, a (0, 3) • ClosedThree.Tc + a (1, 3) • Pd 3)

/-- **On axes with `2` or `3` positions, `p` of two combinations lives on the fiber alone.** -/
theorem lam_p₁ (hx : dx = 2 ∨ dx = 3) (hy : dy = 2 ∨ dy = 3) (hz : dz = 2 ∨ dz = 3)
    (a b : Fin 2 × Fin 4 → ℂ) :
    lam (p₁ (fun X Y : Axes dx dy dz => ⁅X, Y⁆) (axesOf a) (axesOf b)) =
      liftAlong (eW dx dy dz 3) (p₁ (fun X Y : Matrix (Fin 3) (Fin 3) ℂ => ⁅X, Y⁆)
        (axesOf (dx := dx) (dy := dy) (dz := dz) a).2.2.2
        (axesOf (dx := dx) (dy := dy) (dz := dz) b).2.2.2) := by
  have h1 := map_p₁ (b := fun X Y : Axes dx dy dz => ⁅X, Y⁆) (b' := fun X Y => ⁅X, Y⁆) prX
    (fun X Y => lie_fst X Y) (axesOf a) (axesOf b)
  have h2 := map_p₁ (b := fun X Y : Axes dx dy dz => ⁅X, Y⁆) (b' := fun X Y => ⁅X, Y⁆) prY
    (fun X Y => lie_snd_fst X Y) (axesOf a) (axesOf b)
  have h3 := map_p₁ (b := fun X Y : Axes dx dy dz => ⁅X, Y⁆) (b' := fun X Y => ⁅X, Y⁆) prZ
    (fun X Y => lie_snd_snd_fst X Y) (axesOf a) (axesOf b)
  have h4 := map_p₁ (b := fun X Y : Axes dx dy dz => ⁅X, Y⁆) (b' := fun X Y => ⁅X, Y⁆) prW
    (fun X Y => lie_snd_snd_snd X Y) (axesOf a) (axesOf b)
  simp only [prX, prY, prZ, prW, AddMonoidHom.coe_fst, AddMonoidHom.coe_snd,
    AddMonoidHom.coe_comp, Function.comp_apply, axesOf] at h1 h2 h3 h4
  rw [p₁_open hx] at h1
  rw [p₁_open hy] at h2
  rw [p₁_open hz] at h3
  simp only [lam, AddMonoidHom.coe_mk, ZeroHom.coe_mk, h1, h2, h3, h4, liftAlong_zero, zero_add,
    axesOf]

theorem lam_p₂ (hx : dx = 2 ∨ dx = 3) (hy : dy = 2 ∨ dy = 3) (hz : dz = 2 ∨ dz = 3)
    (a b : Fin 2 × Fin 4 → ℂ) :
    lam (p₂ (fun X Y : Axes dx dy dz => ⁅X, Y⁆) (axesOf a) (axesOf b)) =
      liftAlong (eW dx dy dz 3) (p₂ (fun X Y : Matrix (Fin 3) (Fin 3) ℂ => ⁅X, Y⁆)
        (axesOf (dx := dx) (dy := dy) (dz := dz) a).2.2.2
        (axesOf (dx := dx) (dy := dy) (dz := dz) b).2.2.2) := by
  have h1 := map_p₂ (b := fun X Y : Axes dx dy dz => ⁅X, Y⁆) (b' := fun X Y => ⁅X, Y⁆) prX
    (fun X Y => lie_fst X Y) (axesOf a) (axesOf b)
  have h2 := map_p₂ (b := fun X Y : Axes dx dy dz => ⁅X, Y⁆) (b' := fun X Y => ⁅X, Y⁆) prY
    (fun X Y => lie_snd_fst X Y) (axesOf a) (axesOf b)
  have h3 := map_p₂ (b := fun X Y : Axes dx dy dz => ⁅X, Y⁆) (b' := fun X Y => ⁅X, Y⁆) prZ
    (fun X Y => lie_snd_snd_fst X Y) (axesOf a) (axesOf b)
  have h4 := map_p₂ (b := fun X Y : Axes dx dy dz => ⁅X, Y⁆) (b' := fun X Y => ⁅X, Y⁆) prW
    (fun X Y => lie_snd_snd_snd X Y) (axesOf a) (axesOf b)
  simp only [prX, prY, prZ, prW, AddMonoidHom.coe_fst, AddMonoidHom.coe_snd,
    AddMonoidHom.coe_comp, Function.comp_apply, axesOf] at h1 h2 h3 h4
  rw [p₂_open hx] at h1
  rw [p₂_open hy] at h2
  rw [p₂_open hz] at h3
  simp only [lam, AddMonoidHom.coe_mk, ZeroHom.coe_mk, h1, h2, h3, h4, liftAlong_zero, zero_add,
    axesOf]

/-! ## 4. From relations to operators -/

/-- Matrices to operators, as an additive map. -/
def toOp : Matrix (Site4D dx dy dz 3) (Site4D dx dy dz 3) ℂ →+
    Module.End ℂ (H4D dx dy dz 3) where
  toFun A := Matrix.toEuclideanLin A
  map_zero' := map_zero _
  map_add' := map_add _

theorem toOp_apply (A : Matrix (Site4D dx dy dz 3) (Site4D dx dy dz 3) ℂ) :
    toOp A = Matrix.toEuclideanLin A := rfl

theorem toOp_lie (A B : Matrix (Site4D dx dy dz 3) (Site4D dx dy dz 3) ℂ) :
    toOp ⁅A, B⁆ = ⁅toOp A, toOp B⁆ := by
  simp only [toOp_apply, Ring.lie_def, map_sub]
  congr 1 <;> exact Matrix.toLpLin_mul_same _ _ _

/-- The combination `Σ_p a_p A_p` of the eight observables is the sum over the axes. -/
theorem sum_boxPairs (a : Fin 2 × Fin 4 → ℂ) :
    ∑ p, a p • boxPairs dx dy dz 3 closedPair p = toOp (lam (axesOf a)) := by
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two, Fin.sum_univ_four, toOp_apply, lam,
    axesOf, AddMonoidHom.coe_mk, ZeroHom.coe_mk, liftAlong_add, liftAlong_smul, map_add, map_smul,
    BoxCommute.box_x, BoxCommute.box_y, BoxCommute.box_z, BoxCommute.box_w]
  simp only [closedPair, Matrix.cons_val_zero, Matrix.cons_val_one]
  abel

/-- **A relation makes `Φ` an eigenvector of the combination.** -/
theorem eig_of_relation {Φ : H4D dx dy dz 3} {a : Fin 2 × Fin 4 → ℂ}
    (ha : ∑ p, a p • centeredG (boxPairs dx dy dz 3 closedPair p) Φ = 0) :
    toOp (lam (axesOf a)) Φ =
      (∑ p, a p * (meanG (boxPairs dx dy dz 3 closedPair p) Φ : ℂ)) • Φ := by
  have h : ∑ p, a p • boxPairs dx dy dz 3 closedPair p Φ =
      ∑ p, (a p * (meanG (boxPairs dx dy dz 3 closedPair p) Φ : ℂ)) • Φ := by
    simpa only [centeredG, smul_sub, Finset.sum_sub_distrib, sub_eq_zero, smul_smul] using ha
  rw [← sum_boxPairs, LinearMap.sum_apply, Finset.sum_smul]
  simpa only [LinearMap.smul_apply] using h

/-! ## 5. No state is left -/

/-- Two matrices on the fiber with no common kernel annihilate no nonzero state. -/
theorem eq_zero_of_lift₂ {ι β : Type*} [Fintype ι] [Fintype β] [DecidableEq ι] [DecidableEq β]
    (e : ι ≃ Fin 3 × β) {M N : Matrix (Fin 3) (Fin 3) ℂ}
    (hMN : ∀ v, M.mulVec v = 0 → N.mulVec v = 0 → v = 0) {Φ : EuclideanSpace ℂ ι}
    (hM : Matrix.toEuclideanLin (liftAlong e M) Φ = 0)
    (hN : Matrix.toEuclideanLin (liftAlong e N) Φ = 0) : Φ = 0 := by
  have hcol (K : Matrix (Fin 3) (Fin 3) ℂ) (hK : Matrix.toEuclideanLin (liftAlong e K) Φ = 0)
      (b : β) : K.mulVec (AxisDefectEntangled.col e Φ b) = 0 := by
    funext i
    have := congrArg (fun x : EuclideanSpace ℂ ι => x (e.symm (i, b))) hK
    simp only [PiLp.zero_apply] at this
    rw [AxisDefectEntangled.liftAlong_apply_col] at this
    exact this
  ext q
  have := congrFun (hMN _ (hcol M hM (e q).2) (hcol N hN (e q).2)) (e q).1
  simpa [AxisDefectEntangled.col] using this

section Relations

variable (hx : dx = 2 ∨ dx = 3) (hy : dy = 2 ∨ dy = 3) (hz : dz = 2 ∨ dz = 3)
  {Φ : H4D dx dy dz 3} {a b : Fin 2 × Fin 4 → ℂ}
  (ha : ∑ p, a p • centeredG (boxPairs dx dy dz 3 closedPair p) Φ = 0)
  (hb : ∑ p, b p • centeredG (boxPairs dx dy dz 3 closedPair p) Φ = 0)
  (ha0 : a (0, 3) = 1) (ha1 : a (1, 3) = 0) (hb0 : b (0, 3) = 0) (hb1 : b (1, 3) = 1)
include hx hy hz ha hb ha0 ha1 hb0 hb1

omit hx hy hz ha hb in
theorem fiber_parts : (axesOf (dx := dx) (dy := dy) (dz := dz) a).2.2.2 = ClosedThree.Tc ∧
    (axesOf (dx := dx) (dy := dy) (dz := dz) b).2.2.2 = Pd 3 := by
  simp [axesOf, ha0, ha1, hb0, hb1]

/-- `p₁(T°, P₃)` on the fiber annihilates `Φ`. -/
theorem lift_p₁_apply :
    Matrix.toEuclideanLin (liftAlong (eW dx dy dz 3)
      (p₁ (fun X Y : Matrix (Fin 3) (Fin 3) ℂ => ⁅X, Y⁆) ClosedThree.Tc (Pd 3))) Φ = 0 := by
  have hw := fiber_parts (dx := dx) (dy := dy) (dz := dz) ha0 ha1 hb0 hb1
  have k : (p₁ (fun X Y => ⁅X, Y⁆) (toOp (lam (axesOf a))) (toOp (lam (axesOf b)))) Φ = 0 :=
    p₁_apply_eq_zero (eig_of_relation ha) (eig_of_relation hb)
  have m := map_p₁ (b := fun X Y => ⁅X, Y⁆) (b' := fun X Y => ⁅X, Y⁆)
    (toOp (dx := dx) (dy := dy) (dz := dz)) toOp_lie (lam (axesOf a)) (lam (axesOf b))
  have l := map_p₁ (b := fun X Y => ⁅X, Y⁆) (b' := fun X Y => ⁅X, Y⁆)
    (lam (dx := dx) (dy := dy) (dz := dz)) lam_lie (axesOf a) (axesOf b)
  rw [lam_p₁ hx hy hz, hw.1, hw.2] at l
  rwa [← m, ← l, toOp_apply] at k

/-- `p₂(T°, P₃)` on the fiber annihilates `Φ`. -/
theorem lift_p₂_apply :
    Matrix.toEuclideanLin (liftAlong (eW dx dy dz 3)
      (p₂ (fun X Y : Matrix (Fin 3) (Fin 3) ℂ => ⁅X, Y⁆) ClosedThree.Tc (Pd 3))) Φ = 0 := by
  have hw := fiber_parts (dx := dx) (dy := dy) (dz := dz) ha0 ha1 hb0 hb1
  have k : (p₂ (fun X Y => ⁅X, Y⁆) (toOp (lam (axesOf a))) (toOp (lam (axesOf b)))) Φ = 0 :=
    p₂_apply_eq_zero (eig_of_relation ha) (eig_of_relation hb)
  have m := map_p₂ (b := fun X Y => ⁅X, Y⁆) (b' := fun X Y => ⁅X, Y⁆)
    (toOp (dx := dx) (dy := dy) (dz := dz)) toOp_lie (lam (axesOf a)) (lam (axesOf b))
  have l := map_p₂ (b := fun X Y => ⁅X, Y⁆) (b' := fun X Y => ⁅X, Y⁆)
    (lam (dx := dx) (dy := dy) (dz := dz)) lam_lie (axesOf a) (axesOf b)
  rw [lam_p₂ hx hy hz, hw.1, hw.2] at l
  calc Matrix.toEuclideanLin (liftAlong (eW dx dy dz 3)
        (p₂ (fun X Y : Matrix (Fin 3) (Fin 3) ℂ => ⁅X, Y⁆) ClosedThree.Tc (Pd 3))) Φ
      = toOp (p₂ (fun X Y => ⁅X, Y⁆) (lam (axesOf a)) (lam (axesOf b))) Φ := by
        rw [← l]; rfl
    _ = (p₂ (fun X Y => ⁅X, Y⁆) (toOp (lam (axesOf a))) (toOp (lam (axesOf b)))) Φ := by
        rw [m]
    _ = 0 := k

/-- **Two relations through `T°` and `P₃` leave no state.** On the box with `2` or `3` positions
on `x`, `y`, `z` and the closed fiber, two relations among the fluctuation vectors whose fiber
parts are `T°` and `P₃` force `Φ = 0`. -/
theorem eq_zero_of_relations : Φ = 0 :=
  eq_zero_of_lift₂ (eW dx dy dz 3) (fun _ h₁ h₂ => eq_zero_of_p_closed h₁ h₂)
    (lift_p₁_apply hx hy hz ha hb ha0 ha1 hb0 hb1) (lift_p₂_apply hx hy hz ha hb ha0 ha1 hb0 hb1)

end Relations

end BoxTwoRelations
