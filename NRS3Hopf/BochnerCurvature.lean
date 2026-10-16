/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import NRS3Hopf.Cell16Symmetry
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Tactic.Linarith
public import Mathlib.Basic.Real.Basic

/-!
# Discrete Ricci curvature by Bochner: the closed fibered space has `K = 4`

On a graph with adjacency `A` the Laplacian is `Δf(x) = Σ_y A_xy (f(y) − f(x))`. Bochner's
formula `½ Δ|∇f|² = |Hess f|² + ⟨∇f, ∇Δf⟩ + Ric(∇f, ∇f)` becomes the carré du champ and its
iterate (Bakry–Émery):

  `Γ(f, g)(x) = ½ Σ_y A_xy (f(y) − f(x)) (g(y) − g(x))`,
  `Γ₂(f)(x) = ½ ΔΓ(f, f)(x) − Γ(f, Δf)(x)`,

and the curvature is at least `K` when `Γ₂(f) ≥ K Γ(f, f)` at every point for every `f`.

* **Bridge with NRS.** `Γ(f, f)(x) = ½ ([f, [f, A]] 1)(x)`: the carré du champ is the double
  commutator of the position `f` with transport, the bracket of `D49i`.
* **The 16-cell has `K = 4`.** At a point `x` on axis `a`, with `s_b = f(+b) + f(−b)` and
  `d_b = f(+b) − f(−b)`, `Γ₂(f)(x) − 4 Γ(f, f)(x) = ½ Σ_{b<c} (s_b − s_c)² + Σ_{b≠a} d_b² ≥ 0`.
  The bound is sharp: `f = 1` at `x`, `−1` at its opposite, `0` elsewhere, gives equality with
  `Γ(f, f)(x) = 3`. The closed fibered space has positive Ricci curvature, the same at every
  point, as the round three-sphere.
* **One point is enough.** `Δ`, `Γ` and `Γ₂` commute with every symmetry of the graph, and the
  signed permutations of the axes (`Cell16Symmetry`) move `(x, +)` to any point, so the bound
  is proved once, at `(x, +)`, and carried to every point by the group.

## Main results

- `BochnerCurvature.gamma_eq_lie` : `Γ(f, f) = ½ [f, [f, A]] 1`.
- `BochnerCurvature.lap_comp`, `BochnerCurvature.gam_comp`, `BochnerCurvature.gam2_comp` : `Δ`,
  `Γ`, `Γ₂` commute with the symmetries of the graph.
- `BochnerCurvature.cell16_curvature_origin` : `Γ₂(f) ≥ 4 Γ(f, f)` at `(x, +)`.
- `BochnerCurvature.cell16_curvature` : `Γ₂(f) ≥ 4 Γ(f, f)` at every point of the 16-cell.
- `BochnerCurvature.cell16_sharp` : equality with `Γ(f, f) > 0`.
-/

@[expose] public noncomputable section

open Matrix

attribute [local instance 100] LieRing.ofAssociativeRing

namespace BochnerCurvature

variable {V : Type*} [Fintype V] [DecidableEq V] (A : Matrix V V ℝ)

/-- The Laplacian `Δf(x) = Σ_y A_xy (f(y) − f(x))`. -/
def lap (f : V → ℝ) (x : V) : ℝ := ∑ y, A x y * (f y - f x)

/-- The carré du champ `Γ(f, g)(x) = ½ Σ_y A_xy (f(y) − f(x)) (g(y) − g(x))`. -/
def gam (f g : V → ℝ) (x : V) : ℝ := (1 / 2) * ∑ y, A x y * ((f y - f x) * (g y - g x))

/-- Its iterate `Γ₂(f)(x) = ½ ΔΓ(f, f)(x) − Γ(f, Δf)(x)`. -/
def gam2 (f : V → ℝ) (x : V) : ℝ := (1 / 2) * lap A (gam A f f) x - gam A f (lap A f) x

/-- **The carré du champ is the double commutator with transport**:
`Γ(f, f)(x) = ½ ([f, [f, A]] 1)(x)`, `f` acting as a diagonal matrix. -/
theorem gamma_eq_lie (f : V → ℝ) (x : V) :
    gam A f f x = (1 / 2) * (⁅diagonal f, ⁅diagonal f, A⁆⁆ *ᵥ fun _ => 1) x := by
  simp only [gam, Ring.lie_def, mulVec, dotProduct, mul_one, Matrix.sub_apply,
    Matrix.diagonal_mul, Matrix.mul_diagonal]
  congr 1
  refine Finset.sum_congr rfl fun y _ => ?_
  ring

/-! ## Symmetries -/

section Symm

variable (g : V ≃ V) (hA : ∀ u v, A (g u) (g v) = A u v)
include hA

omit [DecidableEq V] in
/-- `Δ` commutes with the symmetries of the graph. -/
lemma lap_comp (f : V → ℝ) (x : V) : lap A (f ∘ g) x = lap A f (g x) := by
  simp only [lap, Function.comp_apply]
  rw [← Equiv.sum_comp g fun y => A (g x) y * (f y - f (g x))]
  simp only [hA]

omit [DecidableEq V] in
/-- `Γ` commutes with the symmetries of the graph. -/
lemma gam_comp (f h : V → ℝ) (x : V) : gam A (f ∘ g) (h ∘ g) x = gam A f h (g x) := by
  simp only [gam, Function.comp_apply]
  rw [← Equiv.sum_comp g fun y => A (g x) y * ((f y - f (g x)) * (h y - h (g x)))]
  simp only [hA]

omit [DecidableEq V] in
/-- `Γ₂` commutes with the symmetries of the graph. -/
lemma gam2_comp (f : V → ℝ) (x : V) : gam2 A (f ∘ g) x = gam2 A f (g x) := by
  have h1 : gam A (f ∘ g) (f ∘ g) = gam A f f ∘ g := funext (gam_comp A g hA f f)
  have h2 : lap A (f ∘ g) = lap A f ∘ g := funext (lap_comp A g hA f)
  rw [gam2, gam2, h1, h2, lap_comp A g hA, gam_comp A g hA]

end Symm

/-! ## The 16-cell -/

open Cell16

/-- The adjacency of the 16-cell. -/
def A16 : Matrix Pt Pt ℝ := of fun u v => if Adj u v then 1 else 0

/-- `A` is invariant under the signed permutations of the axes. -/
lemma A16_signedPerm (π : Equiv.Perm (Fin 4)) (σ : Fin 4 → Bool) (u v : Pt) :
    A16 (signedPerm π σ u) (signedPerm π σ v) = A16 u v := by
  simp only [A16, of_apply, adj_signedPerm]

/-- The curvature bound at the point `(x, +)`. -/
lemma cell16_curvature_origin (f : Pt → ℝ) : 4 * gam A16 f f (0, true) ≤ gam2 A16 f (0, true) := by
  have s (b c : Fin 4) := sq_nonneg ((f (b, true) + f (b, false)) - (f (c, true) + f (c, false)))
  have d (b : Fin 4) := sq_nonneg (f (b, true) - f (b, false))
  have s01 := s 0 1; have s02 := s 0 2; have s03 := s 0 3
  have s12 := s 1 2; have s13 := s 1 3; have s23 := s 2 3
  have d1 := d 1; have d2 := d 2; have d3 := d 3
  simp only [gam2, gam, lap, A16, of_apply, Adj, Fintype.sum_prod_type, Fin.sum_univ_four,
    Fintype.sum_bool]
  norm_num
  linarith

/-- **The closed fibered space has Ricci curvature `≥ 4`**, at every point, for every `f`: the
bound at `(x, +)` is carried to every point by a signed permutation of the axes. -/
theorem cell16_curvature (f : Pt → ℝ) (x : Pt) : 4 * gam A16 f f x ≤ gam2 A16 f x := by
  set g := signedPerm (Equiv.swap 0 x.1) (fun _ => !x.2)
  have hg : g (0, true) = x := signedPerm_transitive x
  have h := cell16_curvature_origin (f ∘ g)
  rwa [gam_comp A16 g (A16_signedPerm _ _), gam2_comp A16 g (A16_signedPerm _ _), hg] at h

/-- **The bound `4` is sharp**: `f = 1` at `x`, `−1` at its opposite, `0` elsewhere. -/
theorem cell16_sharp :
    ∃ f : Pt → ℝ, gam2 A16 f (0, true) = 4 * gam A16 f f (0, true) ∧
      gam A16 f f (0, true) = 3 := by
  refine ⟨fun p => if p = (0, true) then 1 else if p = (0, false) then -1 else 0, ?_⟩
  simp only [gam2, gam, lap, A16, of_apply, Adj, Fintype.sum_prod_type, Fin.sum_univ_four,
    Fintype.sum_bool]
  norm_num

end BochnerCurvature
